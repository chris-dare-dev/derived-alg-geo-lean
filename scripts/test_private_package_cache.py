#!/usr/bin/env python3
"""Focused contract tests for private run-loop package seeding."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
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
        archive = self.store / key / "packages.tar"
        archive.chmod(0o644)
        with archive.open("ab") as stream:
            stream.write(b"corrupt")
        archive.chmod(0o444)
        target = self._target("after-corruption")
        with self.assertRaisesRegex(ValueError, "checksum failed"):
            cache.seed(target, self.donor, False, False)
        self.assertFalse((target / ".lake/packages").exists())
        self.assertFalse((target / ".lake" / cache.READY).exists())


if __name__ == "__main__":
    unittest.main()
