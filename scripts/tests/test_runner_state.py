#!/usr/bin/env python3
"""Tests for runner path and resource admission invariants."""

from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from scripts import runner_state


def path_entry(path: str, writable: bool) -> dict:
    return {"path": path, "resolved_path": path, "writable": writable}


def record(namespace: str, *, root: str = r"C:\actions\runner-a") -> dict:
    return {
        "host_id": "windows-host-1",
        "runner_id": namespace,
        "job_id": f"job-{namespace}",
        "run_id": 100,
        "run_attempt": 1,
        "namespace": namespace,
        "resources": {"cpu_threads": 2, "memory_bytes": 100, "disk_bytes": 100},
        "paths": {
            "checkout": path_entry(root + r"\_work\repo", True),
            "git_index": path_entry(root + r"\_work\repo\.git\index", True),
            "lake_build": path_entry(root + r"\_work\repo\.lake\build", True),
            "lake_packages": path_entry(r"C:\actions\packages", False),
            "elan": path_entry(root + r"\.elan", True),
            "temp": path_entry(root + r"\_work\_temp\job", True),
            "outputs": path_entry(root + r"\_work\repo\outputs", True),
            "artifacts": path_entry(root + r"\_work\repo\artifacts", True),
        },
    }


def snapshot(*jobs: dict, cpu_threads: int = 8) -> dict:
    return {
        "host_capacity": {
            host_id: {
                "cpu_threads": cpu_threads,
                "memory_bytes": 1000,
                "disk_bytes": 1000,
            }
            for host_id in {job["host_id"] for job in jobs}
        },
        "jobs": list(jobs),
    }


class RunnerStateTests(unittest.TestCase):
    def test_canonical_path_normalizes_case_and_separators(self) -> None:
        left = runner_state.canonical_path(r"C:\Actions\Runner\..\Runner\_work")
        right = runner_state.canonical_path(r"c:/actions/runner/_work")
        self.assertEqual(left, right)

    def test_valid_isolated_snapshot_passes(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertTrue(result["valid"], result)

    def test_resource_capacity_is_scoped_per_physical_host(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["host_id"] = "windows-host-2"
        result = runner_state.validate_snapshot(snapshot(first, second, cpu_threads=2))
        self.assertTrue(result["valid"], result)

    def test_writable_build_collision_fails_closed(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["lake_build"]["path"] = first["paths"]["lake_build"]["path"]
        second["paths"]["lake_build"]["resolved_path"] = first["paths"]["lake_build"]["resolved_path"]
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertFalse(result["valid"])
        self.assertTrue(any("writable path collision" in item for item in result["errors"]))

    def test_read_only_packages_can_be_shared(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["lake_packages"] = copy.deepcopy(first["paths"]["lake_packages"])
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertTrue(result["valid"], result)

    def test_resource_overcommit_fails(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        result = runner_state.validate_snapshot(snapshot(first, second, cpu_threads=2))
        self.assertFalse(result["valid"])
        self.assertTrue(any("cpu_threads" in item for item in result["errors"]))

    def test_invalid_record_is_rejected(self) -> None:
        candidate = record("job-a")
        del candidate["paths"]["git_index"]
        self.assertTrue(runner_state.validate_record(candidate))

    def test_windows_path_without_resolved_identity_is_rejected(self) -> None:
        candidate = record("job-a")
        del candidate["paths"]["checkout"]["resolved_path"]
        errors = runner_state.validate_record(candidate)
        self.assertTrue(any("resolved_path" in item for item in errors), errors)

    def test_drive_relative_windows_path_is_rejected(self) -> None:
        candidate = record("job-a")
        candidate["paths"]["checkout"]["path"] = r"C:relative\repo"
        errors = runner_state.validate_record(candidate)
        self.assertTrue(any("absolute" in item for item in errors), errors)

    def test_resolved_junction_alias_collides(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["checkout"]["resolved_path"] = first["paths"]["checkout"]["resolved_path"]
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertFalse(result["valid"])
        self.assertTrue(any("writable path collision" in item for item in result["errors"]))

    def test_namespace_is_safe_for_lease_filename(self) -> None:
        candidate = record("job-a/../escape")
        errors = runner_state.validate_record(candidate)
        self.assertTrue(any("safe filename" in item for item in errors), errors)
        reserved = record("CON")
        reserved_errors = runner_state.validate_record(reserved)
        self.assertTrue(any("safe filename" in item for item in reserved_errors), reserved_errors)

    def test_lease_lifecycle_is_exact_and_non_destructive(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            acquired = runner_state.acquire_lease(candidate, lease_dir)
            self.assertTrue(acquired["acquired"])
            self.assertTrue(acquired["owner_digest"])
            with self.assertRaises(ValueError):
                runner_state.acquire_lease(candidate, lease_dir)
            changed = copy.deepcopy(candidate)
            changed["job_id"] = "different-owner"
            with self.assertRaises(ValueError):
                runner_state.release_lease(changed, lease_dir)
            released = runner_state.release_lease(candidate, lease_dir)
            self.assertTrue(released["released"])
            self.assertFalse((lease_dir / "job-a.json").exists())


if __name__ == "__main__":
    unittest.main()
