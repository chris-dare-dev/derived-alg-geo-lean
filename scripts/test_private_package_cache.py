#!/usr/bin/env python3
"""Focused contract tests for private run-loop package seeding."""

import json
import contextlib
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

import private_package_cache as cache


def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, capture_output=True,
                          text=True).stdout.strip()


class PrivatePackageCacheTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / "snapshots"
        self.env = patch.dict(os.environ, {"DAG_PRIVATE_PACKAGE_SNAPSHOT_DIR": str(self.store)})
        self.env.start()
        self.addCleanup(self.env.stop)
        self.quiet = patch.object(cache, "QUIET_SECONDS", 0)
        self.quiet.start()
        self.addCleanup(self.quiet.stop)
        self.space = patch.object(cache, "MIN_FREE_BYTES", 0)
        self.space.start()
        self.addCleanup(self.space.stop)

        self.donor = self.root / "donor"
        self.donor.mkdir()
        package = self.donor / ".lake/packages/mathlib"
        package.mkdir(parents=True)
        git("-C", str(package), "init", "-q")
        git("-C", str(package), "config", "user.name", "Fixture")
        git("-C", str(package), "config", "user.email", "fixture@example.test")
        (package / "Mathlib.lean").write_text("-- fixture\n")
        (package / ".gitignore").write_text(".lake/\n")
        git("-C", str(package), "add", "Mathlib.lean", ".gitignore")
        git("-C", str(package), "commit", "-qm", "fixture")
        revision = git("-C", str(package), "rev-parse", "HEAD")
        self.manifest = json.dumps({"packages": [{"name": "mathlib", "rev": revision}]})
        (package / ".lake/build/lib").mkdir(parents=True)
        (package / ".lake/build/lib/Mathlib.olean").write_bytes(b"dependency cache")
        (self.donor / ".lake/build/lib").mkdir(parents=True)
        (self.donor / ".lake/build/lib/Project.olean").write_bytes(b"project cache")
        self._project(self.donor)

    def _project(self, path: Path) -> None:
        path.mkdir(exist_ok=True)
        (path / "lean-toolchain").write_text("leanprover/lean:v4.23.0\n")
        (path / "lake-manifest.json").write_text(self.manifest)

    def _target(self, name: str) -> Path:
        target = self.root / name
        self._project(target)
        return target

    def test_two_seeds_have_distinct_writable_trees(self) -> None:
        first, second = self._target("first"), self._target("second")
        cache.seed(first, self.donor, False, False)
        cache.seed(second, self.donor, False, False)
        one = first / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        two = second / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        source = self.donor / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        self.assertEqual(len({one.stat().st_ino, two.stat().st_ino, source.stat().st_ino}), 3)
        one.write_bytes(b"changed in first")
        self.assertEqual(two.read_bytes(), b"dependency cache")
        self.assertEqual(source.read_bytes(), b"dependency cache")
        self.assertFalse((first / ".lake/packages").is_symlink())
        self.assertTrue((first / ".lake" / cache.READY).is_file())

    def test_failure_leaves_no_usable_private_tree(self) -> None:
        target = self._target("low-disk")
        with patch.object(cache, "disk_headroom", side_effect=ValueError("low disk")):
            with self.assertRaisesRegex(ValueError, "low disk"):
                cache.seed(target, self.donor, False, False)
        self.assertFalse((target / ".lake/packages").exists())
        self.assertFalse((target / ".lake" / cache.READY).exists())
        self.assertEqual(list((target / ".lake").glob(".*seeding*")), [])

    def test_pin_mismatch_fails_before_publication(self) -> None:
        target = self._target("mismatched")
        (target / "lean-toolchain").write_text("different\n")
        with self.assertRaisesRegex(ValueError, "different lean-toolchain"):
            cache.seed(target, self.donor, False, False)
        self.assertFalse((target / ".lake/packages").exists())

    def test_quiescent_link_migration_preserves_donor(self) -> None:
        target = self._target("migrate")
        (target / ".lake").mkdir()
        (target / ".lake/packages").symlink_to(self.donor / ".lake/packages")
        cache.seed(target, self.donor, True, False)
        self.assertFalse((target / ".lake/packages").is_symlink())
        self.assertTrue((self.donor / ".lake/packages/mathlib").exists())
        self.assertTrue((target / ".lake" / cache.READY).is_file())

    def test_publish_failure_restores_existing_link_and_build(self) -> None:
        initial = self._target("prepare-snapshot")
        cache.seed(initial, self.donor, False, False)
        target = self._target("rollback")
        (target / ".lake/build/lib").mkdir(parents=True)
        old_build = target / ".lake/build/lib/Old.olean"
        old_build.write_bytes(b"old private build")
        (target / ".lake/packages").symlink_to(self.donor / ".lake/packages")
        original_replace = os.replace

        def fail_marker(source: str, destination: str) -> None:
            if Path(destination).name == cache.READY:
                raise OSError("injected marker failure")
            original_replace(source, destination)

        with patch.object(cache.os, "replace", side_effect=fail_marker):
            with self.assertRaisesRegex(OSError, "injected marker failure"):
                cache.seed(target, self.donor, True, False)
        self.assertTrue((target / ".lake/packages").is_symlink())
        self.assertEqual(old_build.read_bytes(), b"old private build")
        self.assertFalse((target / ".lake" / cache.READY).exists())
        self.assertEqual(list((target / ".lake").glob(".*seeding*")), [])

    def test_changed_archive_is_rejected_without_partial_seed(self) -> None:
        first = self._target("initial")
        cache.seed(first, self.donor, False, False)
        key, _ = cache.pins(first)
        archive = self.store / key / "current/packages.tar"
        archive.chmod(0o644)
        with archive.open("ab") as stream:
            stream.write(b"corrupt")
        archive.chmod(0o444)
        target = self._target("after-corruption")
        with self.assertRaisesRegex(ValueError, "checksum failed"):
            cache.seed(target, self.donor, False, False)
        self.assertFalse((target / ".lake/packages").exists())
        self.assertFalse((target / ".lake" / cache.READY).exists())

    def test_linked_lake_root_cannot_write_into_sibling(self) -> None:
        target = self._target("linked-lake")
        sibling = self.root / "sibling-cache"
        sibling.mkdir()
        (target / ".lake").symlink_to(sibling)
        with self.assertRaisesRegex(ValueError, "target .lake is linked"):
            cache.seed(target, self.donor, False, False)
        self.assertEqual(list(sibling.iterdir()), [])

    def test_linked_git_worktree_cannot_share_index(self) -> None:
        linked = self.root / "linked-donor"
        self._project(linked)
        (linked / ".lake/packages").mkdir(parents=True)
        package = linked / ".lake/packages/mathlib"
        git("-C", str(self.donor / ".lake/packages/mathlib"),
            "worktree", "add", "--detach", str(package), "HEAD")
        (package / ".lake/build/lib").mkdir(parents=True)
        (package / ".lake/build/lib/Mathlib.olean").write_bytes(b"dependency cache")
        (linked / ".lake/build/lib").mkdir(parents=True)
        (linked / ".lake/build/lib/Project.olean").write_bytes(b"project cache")
        target = self._target("linked-git-target")
        with self.assertRaisesRegex(ValueError, "external Git metadata"):
            cache.seed(target, linked, False, False)
        self.assertFalse((target / ".lake/packages").exists())

    def test_git_index_override_cannot_hide_shared_metadata(self) -> None:
        target = self._target("git-env")
        with patch.dict(os.environ, {"GIT_INDEX_FILE": str(self.root / "shared-index")}):
            with self.assertRaisesRegex(ValueError, "GIT_INDEX_FILE"):
                cache.seed(target, self.donor, False, False)
        self.assertFalse((target / ".lake").exists())

    def test_recent_target_package_write_blocks_forced_migration(self) -> None:
        cache.seed(self._target("snapshot-first"), self.donor, False, False)
        target = self._target("active-package")
        (target / ".lake").mkdir()
        (target / ".lake/packages").symlink_to(self.donor / ".lake/packages")
        old = time.time() - 200
        for parent, _, files in os.walk(self.donor / ".lake"):
            for name in files:
                os.utime(Path(parent) / name, (old, old))
        dependency = self.donor / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        os.utime(dependency, None)
        with patch.object(cache, "QUIET_SECONDS", 90):
            with self.assertRaisesRegex(ValueError, "package tree changed"):
                cache.seed(target, self.donor, True, False)
        self.assertTrue((target / ".lake/packages").is_symlink())
        self.assertFalse((target / ".lake" / cache.READY).exists())

    def test_parent_retarget_does_not_write_or_clean_sibling(self) -> None:
        cache.seed(self._target("snapshot-for-retarget"), self.donor, False, False)
        target = self._target("retarget")
        sibling = self.root / "unrelated"
        sibling.mkdir()
        sentinel = sibling / "keep"
        sentinel.write_text("unchanged")
        real_extract = cache.safe_extract

        def retarget_during_extract(archive: Path, destination: Path) -> None:
            (target / ".lake").rename(target / ".lake-moved")
            (target / ".lake").symlink_to(sibling)
            real_extract(archive, destination)

        with patch.object(cache, "safe_extract", side_effect=retarget_during_extract):
            with self.assertRaisesRegex(ValueError, "changed identity"):
                cache.seed(target, self.donor, False, False)
        self.assertEqual(sentinel.read_text(), "unchanged")
        self.assertEqual(sorted(p.name for p in sibling.iterdir()), ["keep"])
        self.assertFalse((target / ".lake-moved" / cache.READY).exists())

    def test_generation_publish_failure_recovers_without_partial_snapshot(self) -> None:
        target = self._target("publish-fails")
        original_replace = os.replace

        def fail_generation(source: str, destination: str) -> None:
            if Path(destination).name == "current":
                raise OSError("injected generation publish failure")
            original_replace(source, destination)

        with patch.object(cache.os, "replace", side_effect=fail_generation):
            with self.assertRaisesRegex(OSError, "generation publish failure"):
                cache.seed(target, self.donor, False, False)
        key, _ = cache.pins(target)
        directory = self.store / key
        self.assertFalse((directory / "current").exists())
        self.assertFalse((target / ".lake" / cache.READY).exists())
        orphan = directory / ".stage-abandoned"
        orphan.mkdir()
        (orphan / "partial").write_text("interrupted earlier generation")
        cache.seed(target, self.donor, False, False)
        self.assertFalse(orphan.exists())
        self.assertTrue((directory / "current/snapshot.json").is_file())

    def test_checked_snapshot_reuses_without_donor_package_checkout(self) -> None:
        cache.seed(self._target("build-snapshot"), self.donor, False, False)
        (self.donor / ".lake/packages").rename(self.donor / ".lake/packages-removed")
        target = self._target("reuse-no-source")
        cache.seed(target, self.donor, False, False)
        self.assertTrue((target / ".lake" / cache.READY).is_file())

    def test_concurrent_same_target_seeds_only_once(self) -> None:
        target = self._target("two-callers")
        barrier = threading.Barrier(2)
        real_lock = cache.snapshot_lock

        @contextlib.contextmanager
        def coordinated_lock(directory: Path):
            barrier.wait(timeout=5)
            with real_lock(directory) as locked_directory:
                yield locked_directory

        with patch.object(cache, "snapshot_lock", coordinated_lock):
            with ThreadPoolExecutor(max_workers=2) as workers:
                futures = [workers.submit(cache.seed, target, self.donor, False, False)
                           for _ in range(2)]
                outcomes = [future.exception(timeout=10) for future in futures]
        self.assertEqual(sum(error is None for error in outcomes), 1)
        self.assertEqual(sum(isinstance(error, ValueError) and
                             "target cache changed while waiting" in str(error)
                             for error in outcomes), 1)
        self.assertTrue((target / ".lake" / cache.READY).is_file())

    def test_snapshot_directory_link_is_rejected(self) -> None:
        target = self._target("linked-snapshot-store")
        key, _ = cache.pins(target)
        self.store.mkdir()
        sibling = self.root / "sibling-store"
        sibling.mkdir()
        (self.store / key).symlink_to(sibling)
        with self.assertRaisesRegex(ValueError, "snapshot directory is linked"):
            cache.seed(target, self.donor, False, False)
        self.assertEqual(list(sibling.iterdir()), [])

    def test_snapshot_lock_link_is_not_followed(self) -> None:
        target = self._target("linked-snapshot-lock")
        key, _ = cache.pins(target)
        directory = self.store / key
        directory.mkdir(parents=True)
        sentinel = self.root / "lock-sentinel"
        sentinel.write_text("unchanged")
        (directory / ".lock").symlink_to(sentinel)
        with self.assertRaises(OSError):
            cache.seed(target, self.donor, False, False)
        self.assertEqual(sentinel.read_text(), "unchanged")


if __name__ == "__main__":
    unittest.main()
