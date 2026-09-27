#!/usr/bin/env python3
"""Tests for runner path and resource admission invariants."""

from __future__ import annotations

import copy
from concurrent.futures import ThreadPoolExecutor
from contextlib import redirect_stdout
import io
import json
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
            "lake_packages": path_entry(root + r"\_work\repo\.lake\packages", True),
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
        self.assertTrue(any("resolves outside" in item or "writable path collision" in item
                            for item in result["errors"]))

    def test_shared_package_tree_cannot_be_declared_read_only(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["lake_packages"] = copy.deepcopy(first["paths"]["lake_packages"])
        second["paths"]["lake_packages"]["writable"] = False
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertFalse(result["valid"])
        self.assertTrue(any("job-owned writable" in item for item in result["errors"]))

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
        self.assertTrue(any("resolves outside" in item or "writable path collision" in item
                            for item in result["errors"]))

    def test_posix_package_symlink_to_another_workspace_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout = root / "job/checkout"
            (checkout / ".lake").mkdir(parents=True)
            shared = root / "other/packages"
            shared.mkdir(parents=True)
            (checkout / ".lake/packages").symlink_to(shared)
            candidate = record("job-a")
            paths = {
                "checkout": checkout,
                "git_index": root / "job/git/index",
                "lake_build": checkout / ".lake/build",
                "lake_packages": checkout / ".lake/packages",
                "elan": root / "job/elan",
                "temp": root / "job/temp",
                "outputs": root / "job/outputs",
                "artifacts": root / "job/artifacts",
            }
            candidate["paths"] = {
                name: {"path": str(path), "writable": True} for name, path in paths.items()
            }
            errors = runner_state.validate_record(candidate)
            self.assertTrue(any("lake_packages resolves outside" in item for item in errors), errors)

    def test_namespace_is_safe_for_lease_filename(self) -> None:
        candidate = record("job-a/../escape")
        errors = runner_state.validate_record(candidate)
        self.assertTrue(any("safe filename" in item for item in errors), errors)
        reserved = record("CON")
        reserved_errors = runner_state.validate_record(reserved)
        self.assertTrue(any("safe filename" in item for item in reserved_errors), reserved_errors)

    def test_lease_lifecycle_is_exact_and_non_destructive(self) -> None:
        candidate = record("job-a")
        capacity = snapshot(candidate)["host_capacity"]
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            acquired = runner_state.acquire_lease(candidate, lease_dir, capacity)
            self.assertTrue(acquired["acquired"])
            self.assertTrue(acquired["owner_digest"])
            with self.assertRaises(ValueError):
                runner_state.acquire_lease(candidate, lease_dir, capacity)
            changed = copy.deepcopy(candidate)
            changed["job_id"] = "different-owner"
            with self.assertRaises(ValueError):
                runner_state.release_lease(changed, lease_dir)
            released = runner_state.release_lease(candidate, lease_dir)
            self.assertTrue(released["released"])
            self.assertFalse((lease_dir / "job-a.json").exists())

    def test_atomic_admission_rejects_writable_overlap_with_active_lease(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["git_index"] = copy.deepcopy(first["paths"]["git_index"])
        capacity = snapshot(first, second)["host_capacity"]
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            runner_state.acquire_lease(first, lease_dir, capacity)
            with self.assertRaisesRegex(ValueError, "writable path collision"):
                runner_state.acquire_lease(second, lease_dir, capacity)
            self.assertFalse((lease_dir / "job-b.json").exists())

    def test_atomic_admission_rejects_shared_temporary_output(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["temp"] = copy.deepcopy(first["paths"]["temp"])
        capacity = snapshot(first, second)["host_capacity"]
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            runner_state.acquire_lease(first, lease_dir, capacity)
            with self.assertRaisesRegex(ValueError, "writable path collision"):
                runner_state.acquire_lease(second, lease_dir, capacity)

    def test_atomic_admission_reserves_capacity_for_one_physical_host(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        capacity = snapshot(first, second, cpu_threads=2)["host_capacity"]
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            runner_state.acquire_lease(first, lease_dir, capacity)
            with self.assertRaisesRegex(ValueError, "cpu_threads"):
                runner_state.acquire_lease(second, lease_dir, capacity)

    def test_corrupt_active_lease_denies_new_admission(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            (lease_dir / "other.json").write_text("{}", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "invalid active lease"):
                runner_state.acquire_lease(candidate, lease_dir, snapshot(candidate)["host_capacity"])

    def test_group_writable_lease_directory_is_rejected(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory) / "leases"
            lease_dir.mkdir()
            lease_dir.chmod(0o770)
            with self.assertRaisesRegex(ValueError, "not group/world-writable"):
                runner_state.acquire_lease(candidate, lease_dir, snapshot(candidate)["host_capacity"])

    def test_two_simultaneous_contenders_cannot_take_the_same_writable_path(self) -> None:
        first = record("job-a")
        second = record("job-b")
        capacity = snapshot(first, second)["host_capacity"]
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            def try_admit(candidate: dict) -> bool:
                try:
                    runner_state.acquire_lease(candidate, lease_dir, capacity)
                    return True
                except ValueError:
                    return False
            with ThreadPoolExecutor(max_workers=2) as pool:
                admitted = list(pool.map(try_admit, (first, second)))
            self.assertEqual(sum(admitted), 1)
            self.assertEqual(len(list(lease_dir.glob("*.json"))), 1)

    def test_admit_cli_uses_physical_host_capacity_file(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            record_file = root / "candidate.json"
            capacity_file = root / "capacity.json"
            record_file.write_text(json.dumps(candidate), encoding="utf-8")
            capacity_file.write_text(json.dumps(snapshot(candidate)["host_capacity"]), encoding="utf-8")
            output = io.StringIO()
            with redirect_stdout(output):
                exit_code = runner_state.main([
                    "admit", str(record_file), "--lease-dir", str(root / "leases"),
                    "--host-capacity", str(capacity_file),
                ])
            self.assertEqual(exit_code, 0, output.getvalue())
            self.assertTrue((root / "leases/job-a.json").is_file())


if __name__ == "__main__":
    unittest.main()
