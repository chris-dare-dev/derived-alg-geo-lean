#!/usr/bin/env python3
"""Tests for runner path and resource admission invariants."""

from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from scripts import runner_state


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
            "checkout": {"path": root + r"\_work\repo", "writable": True},
            "git_index": {"path": root + r"\_work\repo\.git\index", "writable": True},
            "lake_build": {"path": root + r"\_work\repo\.lake\build", "writable": True},
            "lake_packages": {"path": r"C:\actions\packages", "writable": False},
            "elan": {"path": root + r"\.elan", "writable": True},
            "temp": {"path": root + r"\_work\_temp\job", "writable": True},
            "outputs": {"path": root + r"\_work\repo\outputs", "writable": True},
            "artifacts": {"path": root + r"\_work\repo\artifacts", "writable": True},
        },
    }


class RunnerStateTests(unittest.TestCase):
    def test_canonical_path_normalizes_case_and_separators(self) -> None:
        left = runner_state.canonical_path(r"C:\Actions\Runner\..\Runner\_work")
        right = runner_state.canonical_path(r"c:/actions/runner/_work")
        self.assertEqual(left, right)

    def test_valid_isolated_snapshot_passes(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        snapshot = {
            "capacity": {"cpu_threads": 8, "memory_bytes": 1000, "disk_bytes": 1000},
            "jobs": [first, second],
        }
        result = runner_state.validate_snapshot(snapshot)
        self.assertTrue(result["valid"], result)

    def test_writable_build_collision_fails_closed(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["lake_build"]["path"] = first["paths"]["lake_build"]["path"]
        snapshot = {
            "capacity": {"cpu_threads": 8, "memory_bytes": 1000, "disk_bytes": 1000},
            "jobs": [first, second],
        }
        result = runner_state.validate_snapshot(snapshot)
        self.assertFalse(result["valid"])
        self.assertTrue(any("writable path collision" in item for item in result["errors"]))

    def test_read_only_packages_can_be_shared(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["lake_packages"] = copy.deepcopy(first["paths"]["lake_packages"])
        snapshot = {
            "capacity": {"cpu_threads": 8, "memory_bytes": 1000, "disk_bytes": 1000},
            "jobs": [first, second],
        }
        result = runner_state.validate_snapshot(snapshot)
        self.assertTrue(result["valid"], result)

    def test_resource_overcommit_fails(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        snapshot = {
            "capacity": {"cpu_threads": 2, "memory_bytes": 1000, "disk_bytes": 1000},
            "jobs": [first, second],
        }
        result = runner_state.validate_snapshot(snapshot)
        self.assertFalse(result["valid"])
        self.assertTrue(any("cpu_threads" in item for item in result["errors"]))

    def test_invalid_record_is_rejected(self) -> None:
        candidate = record("job-a")
        del candidate["paths"]["git_index"]
        self.assertTrue(runner_state.validate_record(candidate))

    def test_lease_lifecycle_is_exact_and_non_destructive(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            acquired = runner_state.acquire_lease(candidate, lease_dir)
            self.assertTrue(acquired["acquired"])
            with self.assertRaises(ValueError):
                runner_state.acquire_lease(candidate, lease_dir)
            released = runner_state.release_lease(candidate, lease_dir)
            self.assertTrue(released["released"])
            self.assertFalse((lease_dir / "job-a.json").exists())


if __name__ == "__main__":
    unittest.main()
