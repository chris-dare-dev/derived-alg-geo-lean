#!/usr/bin/env python3
"""Tests for runner path and resource admission invariants."""

from __future__ import annotations

import copy
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager, redirect_stdout
import io
import json
import tempfile
import unittest
from unittest.mock import patch
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

    def test_namespace_is_scoped_per_physical_host(self) -> None:
        first = record("same")
        second = record("same")
        second["host_id"] = "windows-host-2"
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertTrue(result["valid"], result)

    def test_same_paths_on_distinct_physical_hosts_do_not_collide(self) -> None:
        first = record("job-a")
        second = record("job-b")
        second["host_id"] = "windows-host-2"
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertTrue(result["valid"], result)

    def test_posix_path_identity_preserves_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            upper = Path(directory) / "Cache"
            lower = Path(directory) / "cache"
            upper.mkdir()
            lower.mkdir()
            self.assertNotEqual(runner_state.canonical_path(str(upper)),
                                runner_state.canonical_path(str(lower)))
            first = record("job-a")
            second = record("job-b", root=r"C:\actions\runner-b")
            first["paths"]["temp"] = path_entry(str(upper), True)
            second["paths"]["temp"] = path_entry(str(lower), True)
            result = runner_state.validate_snapshot(snapshot(first, second))
            self.assertTrue(result["valid"], result)

    def test_double_slash_posix_alias_collides(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            shared = Path(directory) / "shared"
            shared.mkdir()
            first = record("job-a")
            second = record("job-b", root=r"C:\actions\runner-b")
            first["paths"]["temp"] = path_entry(str(shared), True)
            second["paths"]["temp"] = path_entry("/" + str(shared), True)
            result = runner_state.validate_snapshot(snapshot(first, second))
            self.assertFalse(result["valid"], result)
            self.assertTrue(any("writable path collision" in error for error in result["errors"]))

    def test_detached_posix_report_uses_observed_identity(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        first["paths"]["temp"] = path_entry("/remote/a", True)
        second["paths"]["temp"] = path_entry("/remote/b", True)
        first["paths"]["temp"]["resolved_path"] = "/remote/shared"
        second["paths"]["temp"]["resolved_path"] = "/remote/shared"
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertFalse(result["valid"], result)
        self.assertTrue(any("writable path collision" in error for error in result["errors"]))

    def test_windows_extended_drive_spelling_collides(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        first["paths"]["temp"] = path_entry(r"C:\shared\temp", True)
        second["paths"]["temp"] = path_entry(r"\\?\C:\shared\temp", True)
        result = runner_state.validate_snapshot(snapshot(first, second))
        self.assertFalse(result["valid"], result)
        self.assertTrue(any("writable path collision" in error for error in result["errors"]))

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

    def test_every_mandatory_mutable_root_rejects_false_writability(self) -> None:
        for name in runner_state.WRITABLE_PATHS:
            with self.subTest(path=name):
                candidate = record("job-a")
                candidate["paths"][name]["writable"] = False
                errors = runner_state.validate_record(candidate)
                self.assertTrue(any(f"paths.{name} must be job-owned writable state" in error
                                    for error in errors), errors)

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

    def test_false_writability_cannot_hide_shared_index_from_admission(self) -> None:
        first = record("job-a")
        second = record("job-b", root=r"C:\actions\runner-b")
        second["paths"]["git_index"] = copy.deepcopy(first["paths"]["git_index"])
        second["paths"]["git_index"]["writable"] = False
        capacity = snapshot(first, second)["host_capacity"]
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory)
            runner_state.acquire_lease(first, lease_dir, capacity)
            with self.assertRaisesRegex(ValueError, "paths.git_index must be job-owned writable state"):
                runner_state.acquire_lease(second, lease_dir, capacity)
            self.assertTrue((lease_dir / "job-a.json").is_file())
            self.assertFalse((lease_dir / "job-b.json").exists())

    def test_admission_rejects_false_observed_posix_identity(self) -> None:
        candidate = record("job-a")
        candidate["paths"]["temp"] = path_entry("/tmp/actual", True)
        candidate["paths"]["temp"]["resolved_path"] = "/tmp/claimed"
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "resolved_path differs from host identity"):
                runner_state.acquire_lease(
                    candidate, Path(directory), snapshot(candidate)["host_capacity"]
                )

    def test_candidate_temp_root_cannot_contain_host_lease_directory(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            temp_root = Path(directory) / "job-temp"
            lease_dir = temp_root / "leases"
            candidate["paths"]["temp"] = path_entry(str(temp_root), True)
            with self.assertRaisesRegex(ValueError, "overlaps job-a:temp"):
                runner_state.acquire_lease(candidate, lease_dir, snapshot(candidate)["host_capacity"])
            self.assertFalse(lease_dir.exists())

    def test_existing_temp_root_cannot_contain_host_lease_directory(self) -> None:
        active = record("job-a")
        candidate = record("job-b", root=r"C:\actions\runner-b")
        with tempfile.TemporaryDirectory() as directory:
            lease_dir = Path(directory) / "job-temp" / "leases"
            lease_dir.mkdir(parents=True)
            lease_dir.chmod(0o700)
            active["paths"]["temp"] = path_entry(str(lease_dir.parent), True)
            (lease_dir / "job-a.json").write_text(json.dumps({
                "owner_digest": runner_state._record_digest(active), "record": active,
            }), encoding="utf-8")
            (lease_dir / "job-a.json").chmod(0o600)
            with self.assertRaisesRegex(ValueError, "overlaps job-a:temp"):
                runner_state.acquire_lease(candidate, lease_dir, snapshot(active, candidate)["host_capacity"])
            self.assertFalse((lease_dir / "job-b.json").exists())

    def test_candidate_retargets_temp_symlink_before_lock(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            safe = root / "safe"
            safe.mkdir()
            temp_link = root / "job-temp"
            temp_link.symlink_to(safe, target_is_directory=True)
            host_temp = root / "host-temp"
            host_temp.mkdir()
            lease_dir = host_temp / "leases"
            candidate["paths"]["temp"] = {"path": str(temp_link), "writable": True}
            original_lock = runner_state._locked_lease_dir

            @contextmanager
            def retarget_at_lock(path: Path):
                temp_link.unlink()
                temp_link.symlink_to(host_temp, target_is_directory=True)
                with original_lock(path) as directory_fd:
                    yield directory_fd

            with patch.object(runner_state, "_locked_lease_dir", retarget_at_lock):
                with self.assertRaisesRegex(ValueError, "overlaps job-a:temp"):
                    runner_state.acquire_lease(candidate, lease_dir, snapshot(candidate)["host_capacity"])
            self.assertFalse((lease_dir / "job-a.json").exists())

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
            (lease_dir / "other.json").chmod(0o600)
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

    def test_lease_directory_parent_symlink_is_rejected(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actual = root / "actual"
            actual.mkdir()
            alias = root / "alias"
            alias.symlink_to(actual, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "symlink or non-directory"):
                runner_state.acquire_lease(
                    candidate, alias / "leases", snapshot(candidate)["host_capacity"]
                )
            self.assertFalse((actual / "leases/job-a.json").exists())

    def test_parent_rename_while_locked_denies_admission(self) -> None:
        candidate = record("job-a")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            parent = root / "parent"
            parent.mkdir()
            lease_dir = parent / "leases"
            original_lock = runner_state._locked_lease_dir

            @contextmanager
            def rename_after_lock(path: Path):
                with original_lock(path) as directory_fd:
                    parent.rename(root / "renamed")
                    parent.mkdir()
                    (parent / "leases").mkdir()
                    yield directory_fd

            with patch.object(runner_state, "_locked_lease_dir", rename_after_lock):
                with self.assertRaisesRegex(ValueError, "moved while locked"):
                    runner_state.acquire_lease(
                        candidate, lease_dir, snapshot(candidate)["host_capacity"]
                    )
            self.assertFalse((root / "renamed/leases/job-a.json").exists())
            self.assertFalse((parent / "leases/job-a.json").exists())

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
