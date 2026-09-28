#!/usr/bin/env python3
"""Focused failure and isolation tests for fresh private Lake cache bootstrap."""

from concurrent.futures import ThreadPoolExecutor
import io
import json
import multiprocessing
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import private_package_cache as cache
import private_archive_io as archive_io
from private_archive_io import extract_checked_archive


def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, capture_output=True,
                          text=True).stdout.strip()


def killed_seed(target: str, donor: str, kill_after: bool) -> None:
    original = cache.no_replace_rename

    def stop(*args):
        if kill_after:
            original(*args)
        os.kill(os.getpid(), signal.SIGKILL)

    with patch.object(cache, "no_replace_rename", side_effect=stop):
        cache.seed(Path(target), Path(donor), verify=False, dry_run=False, force=False)


def killed_snapshot(target: str, donor: str) -> None:
    def stop(*args):
        os.kill(os.getpid(), signal.SIGKILL)
    with patch.object(cache, "no_replace_rename", side_effect=stop):
        cache.seed(Path(target), Path(donor), verify=False, dry_run=False, force=False)


class PrivatePackageCacheTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / "snapshots"
        for context in (patch.dict(os.environ, {"DAG_PRIVATE_PACKAGE_SNAPSHOT_DIR": str(self.store)}),
                        patch.object(cache, "QUIET_SECONDS", 0),
                        patch.object(cache, "MIN_FREE_BYTES", 0)):
            context.start()
            self.addCleanup(context.stop)
        self.donor = self.root / "donor"
        self.donor.mkdir()
        package = self.donor / ".lake/packages/mathlib"
        package.mkdir(parents=True)
        git("-C", str(package), "init", "-q")
        git("-C", str(package), "config", "user.name", "Fixture")
        git("-C", str(package), "config", "user.email", "fixture@example.test")
        (package / "Mathlib.lean").write_text("-- committed fixture\n")
        (package / ".gitignore").write_text(".lake/\n")
        git("-C", str(package), "add", "Mathlib.lean", ".gitignore")
        git("-C", str(package), "commit", "-qm", "fixture")
        revision = git("-C", str(package), "rev-parse", "HEAD")
        self.manifest = json.dumps({"packages": [{"name": "mathlib", "rev": revision,
                                                  "url": "https://example.invalid/mathlib"}]})
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

    def _seed(self, target: Path, donor: Path | None = None) -> None:
        cache.seed(target, self.donor if donor is None else donor,
                   verify=False, dry_run=False, force=False)

    def test_two_targets_have_distinct_writable_caches(self) -> None:
        first, second = self._target("first"), self._target("second")
        self._seed(first)
        self._seed(second)
        a = first / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        b = second / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        donor = self.donor / ".lake/packages/mathlib/.lake/build/lib/Mathlib.olean"
        self.assertEqual(len({a.stat().st_ino, b.stat().st_ino, donor.stat().st_ino}), 3)
        a.write_bytes(b"private edit")
        self.assertEqual(b.read_bytes(), b"dependency cache")
        cache.verify_ready(second)
        self.assertEqual(git("-C", str(second / ".lake/packages/mathlib"),
                             "remote", "get-url", "origin"),
                         "https://example.invalid/mathlib")
        cache.verify_ready(first)  # Private build output is writable after seeding.

    def test_git_suppressed_tracked_modification_is_not_snapshotted(self) -> None:
        package = self.donor / ".lake/packages/mathlib"
        for flag in ("--assume-unchanged", "--skip-worktree"):
            with self.subTest(flag=flag):
                git("-C", str(package), "update-index", flag, "Mathlib.lean")
                (package / "Mathlib.lean").write_text(f"-- hidden {flag}\n")
                self.assertEqual(git("-C", str(package), "status", "--porcelain"), "")
                target = self._target(flag.lstrip("-"))
                self._seed(target)
                self.assertEqual((target / ".lake/packages/mathlib/Mathlib.lean").read_text(),
                                 "-- committed fixture\n")
                shutil.rmtree(self.store)
                git("-C", str(package), "update-index", "--no-assume-unchanged",
                    "Mathlib.lean")
                git("-C", str(package), "update-index", "--no-skip-worktree",
                    "Mathlib.lean")

    def test_tracked_lake_symlink_never_receives_build_copy(self) -> None:
        package = self.donor / ".lake/packages/mathlib"
        outside = self.root / "outside-package"
        outside.mkdir()
        saved = self.root / "saved-package-lake"
        (package / ".lake").rename(saved)
        (package / ".lake").symlink_to(outside, target_is_directory=True)
        git("-C", str(package), "add", "-f", ".lake")
        git("-C", str(package), "commit", "-qm", "tracked lake symlink")
        revision = git("-C", str(package), "rev-parse", "HEAD")
        (package / ".lake").unlink()
        saved.rename(package / ".lake")
        self.manifest = json.dumps({"packages": [{"name": "mathlib", "rev": revision,
                                                  "url": "https://example.invalid/mathlib"}]})
        (self.donor / "lake-manifest.json").write_text(self.manifest)
        target = self._target("tracked-lake-link")
        with self.assertRaises(OSError):
            self._seed(target)
        self.assertEqual(list(outside.iterdir()), [])
        self.assertFalse((target / ".lake").exists())

    def test_existing_lake_and_force_preserve_sibling(self) -> None:
        target = self._target("existing")
        sibling = self.root / "sibling"
        sibling.mkdir()
        sentinel = sibling / "keep"
        sentinel.write_text("unchanged")
        (target / ".lake").symlink_to(sibling)
        with self.assertRaisesRegex(ValueError, "already has .lake"):
            self._seed(target)
        with self.assertRaisesRegex(ValueError, "forced migration"):
            cache.seed(target, self.donor, verify=False, dry_run=False, force=True)
        self.assertEqual(sentinel.read_text(), "unchanged")
        self.assertTrue((target / ".lake").is_symlink())

    def test_snapshot_reuse_needs_no_donor_cache(self) -> None:
        self._seed(self._target("initial"))
        shutil.rmtree(self.donor / ".lake")
        second = self._target("no-donor")
        self._seed(second)
        cache.verify_ready(second)

    def test_dry_run_leaves_no_locks_or_stages(self) -> None:
        target = self._target("dry-run")
        cache.seed(target, self.donor, verify=False, dry_run=True, force=False)
        self.assertFalse((target / ".private-cache-seed.lock").exists())
        self.assertFalse((target / ".lake").exists())
        self.assertFalse(self.store.exists())

    def test_dry_run_checks_snapshot_headroom_without_writing(self) -> None:
        target = self._target("dry-run-low-disk")
        with patch.object(cache.os, "fstatvfs", return_value=SimpleNamespace(
                f_bavail=1, f_frsize=1)):
            with self.assertRaisesRegex(ValueError, "insufficient disk"):
                cache.seed(target, self.donor, verify=False, dry_run=True, force=False)
        self.assertFalse((target / ".private-cache-seed.lock").exists())
        self.assertFalse(self.store.exists())

    def test_missing_dependency_build_refuses_warm_seed(self) -> None:
        shutil.rmtree(self.donor / ".lake/packages/mathlib/.lake/build")
        target = self._target("missing-cache")
        with self.assertRaisesRegex(ValueError, "required warm build cache missing"):
            self._seed(target)
        self.assertFalse((target / ".lake").exists())

    def test_archive_corruption_refuses_without_public_tree(self) -> None:
        self._seed(self._target("initial"))
        key, _ = cache.pins(self.donor)
        archive = self.store / key / "current/cache.tar"
        archive.chmod(0o644)
        with archive.open("ab") as stream:
            stream.write(b"corrupt")
        archive.chmod(0o444)
        target = self._target("corrupt")
        with self.assertRaisesRegex(ValueError, "checksum failed"):
            self._seed(target)
        self.assertFalse((target / ".lake").exists())

    def test_receipt_binds_manifest_and_refuses_escaping_mutations(self) -> None:
        target = self._target("receipt")
        self._seed(target)
        (target / "lean-toolchain").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "receipt pins"):
            cache.verify_ready(target)
        (target / "lean-toolchain").write_text("leanprover/lean:v4.23.0\n")
        (target / ".lake/build/lib/Project.olean").write_bytes(b"tampered")
        cache.verify_ready(target)  # Lake is expected to rewrite its private cache.
        (target / ".lake/build/lib/Project.olean").unlink()
        outside = self.root / "external-olean"
        outside.write_bytes(b"external")
        (target / ".lake/build/lib/Project.olean").symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "link escapes tree"):
            cache.verify_ready(target)

    def test_receipt_requires_writable_build_roots(self) -> None:
        target = self._target("read-only-build")
        self._seed(target)
        project_build = target / ".lake/build"
        project_build.chmod(0o555)
        try:
            with self.assertRaisesRegex(ValueError, "not owner-writable"):
                cache.verify_ready(target)
        finally:
            project_build.chmod(0o755)

    def test_compound_lake_symlink_cannot_reach_sibling(self) -> None:
        target = self._target("compound-link")
        self._seed(target)
        sibling = self.root / "sibling-worktree"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        (target / ".lake/dir").mkdir()
        (target / ".lake/dir/back").symlink_to("..")
        (target / ".lake/config").symlink_to("dir/back/../../sibling-worktree")
        with self.assertRaisesRegex(ValueError, "not pinned"):
            cache.verify_ready(target)
        self.assertEqual((sibling / "keep").read_text(), "unchanged")

    def test_legacy_receipt_is_read_only_and_rejects_duplicate_keys(self) -> None:
        target = self._target("legacy-receipt")
        self._seed(target)
        receipt = target / ".lake/private-cache-ready.json"
        original = receipt.read_bytes()
        (target / ".lake/build/lib/Project.olean").write_bytes(b"normal Lake update")
        cache.verify_ready(target)
        self.assertEqual(receipt.read_bytes(), original)
        receipt.write_bytes(original[:-2] + b',"format":4}\n')
        with self.assertRaisesRegex(ValueError, "duplicate private-cache record key"):
            cache.verify_ready(target)
        self.assertEqual((target / ".lake/build/lib/Project.olean").read_bytes(),
                         b"normal Lake update")

    def test_oversized_receipt_refuses_without_repair(self) -> None:
        target = self._target("oversized-receipt")
        self._seed(target)
        receipt = target / ".lake/private-cache-ready.json"
        receipt.write_bytes(b" " * (cache.MAX_RECORD_BYTES + 1))
        with self.assertRaisesRegex(ValueError, "bounded private file"):
            cache.verify_ready(target)
        self.assertEqual(receipt.stat().st_size, cache.MAX_RECORD_BYTES + 1)

    def test_preplaced_target_stage_link_refuses_without_sibling_write(self) -> None:
        self._seed(self._target("snapshot-first"))
        target = self._target("stage-link")
        sibling = self.root / "sibling-stage"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        (target / ".lake-stage-fixed").symlink_to(sibling)
        with patch.object(cache.uuid, "uuid4", return_value=type("Token", (), {"hex": "fixed"})()):
            with self.assertRaises(FileExistsError):
                self._seed(target)
        self.assertEqual((sibling / "keep").read_text(), "unchanged")
        self.assertFalse((target / ".lake").exists())

    def test_preplaced_snapshot_stage_link_refuses_without_sibling_write(self) -> None:
        target = self._target("snapshot-stage-link")
        key, _ = cache.pins(target)
        directory = self.store / key
        directory.mkdir(parents=True)
        sibling = self.root / "snapshot-sibling"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        (directory / ".stage-fixed").symlink_to(sibling)
        with patch.object(cache.uuid, "uuid4", return_value=type("Token", (), {"hex": "fixed"})()):
            with self.assertRaises(FileExistsError):
                self._seed(target)
        self.assertEqual((sibling / "keep").read_text(), "unchanged")
        self.assertFalse((target / ".lake").exists())

    def test_extractor_refuses_symlink_ancestor(self) -> None:
        archive = self.root / "malicious.tar"
        with tarfile.open(archive, "w") as tar:
            payload = b"overwrite"
            info = tarfile.TarInfo("packages/mathlib/keep")
            info.size = len(payload)
            tar.addfile(info, io.BytesIO(payload))
        stage = self.root / "stage"
        stage.mkdir()
        sibling = self.root / "sibling-extract"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        (stage / "packages").symlink_to(sibling)
        fd = os.open(stage, os.O_RDONLY | os.O_DIRECTORY)
        try:
            with self.assertRaises(OSError):
                extract_checked_archive(archive, fd, cache.digest_file(archive), {"mathlib"})
        finally:
            os.close(fd)
        self.assertEqual((sibling / "keep").read_text(), "unchanged")

    def test_same_target_concurrency_has_one_success(self) -> None:
        self._seed(self._target("snapshot-first"))
        target = self._target("contended")
        def call() -> str:
            try:
                self._seed(target)
                return "seeded"
            except (ValueError, OSError):
                return "refused"
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(lambda _: call(), range(2)))
        self.assertEqual(sorted(results), ["refused", "seeded"])
        cache.verify_ready(target)

    def test_sigkill_before_and_after_atomic_publish(self) -> None:
        self._seed(self._target("snapshot-first"))
        before = self._target("killed-before")
        context = multiprocessing.get_context("fork")
        process = context.Process(target=killed_seed, args=(str(before), str(self.donor), False))
        process.start(); process.join(10)
        self.assertEqual(process.exitcode, -signal.SIGKILL)
        self.assertFalse((before / ".lake").exists())
        self.assertTrue(list(before.glob(".lake-stage-*")))
        self._seed(before)  # The dead stage is never treated as ready.
        self.assertFalse(list(before.glob(".lake-stage-*")))
        cache.verify_ready(before)
        after = self._target("killed-after")
        process = context.Process(target=killed_seed, args=(str(after), str(self.donor), True))
        process.start(); process.join(10)
        self.assertEqual(process.exitcode, -signal.SIGKILL)
        cache.verify_ready(after)
        with self.assertRaisesRegex(ValueError, "already has .lake"):
            self._seed(after)

    def test_no_replace_does_not_overwrite_existing_lake(self) -> None:
        target = self._target("race-existing")
        self._seed(self._target("snapshot-first"))
        original = cache.no_replace_rename
        def occupy(src_fd: int, src: str, dst_fd: int, dst: str,
                   expected: tuple[int, int]) -> None:
            os.mkdir(dst, dir_fd=dst_fd)
            original(src_fd, src, dst_fd, dst, expected)
        with patch.object(cache, "no_replace_rename", side_effect=occupy):
            with self.assertRaises(OSError):
                self._seed(target)
        self.assertTrue((target / ".lake").is_dir())
        self.assertEqual(list((target / ".lake").iterdir()), [])

    def test_swapped_target_stage_is_not_published(self) -> None:
        self._seed(self._target("snapshot-first"))
        target = self._target("swap-stage")
        sibling = self.root / "swap-sibling"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        original = cache.no_replace_rename

        def swap(src_fd: int, src: str, dst_fd: int, dst: str,
                 expected: tuple[int, int]) -> None:
            if dst == ".lake":
                os.rename(src, src + "-moved", src_dir_fd=src_fd, dst_dir_fd=src_fd)
                os.symlink(sibling, src, dir_fd=src_fd)
            original(src_fd, src, dst_fd, dst, expected)

        with patch.object(cache, "no_replace_rename", side_effect=swap):
            with self.assertRaisesRegex(ValueError, "changed identity"):
                self._seed(target)
        self.assertFalse((target / ".lake").exists())
        self.assertEqual((sibling / "keep").read_text(), "unchanged")

    def test_stage_swap_at_publish_is_rolled_back(self) -> None:
        self._seed(self._target("snapshot-first"))
        target = self._target("swap-at-publish")
        original = cache._rename_noreplace
        swapped = False

        def swap(src_fd: int, src: str, dst_fd: int, dst: str) -> None:
            nonlocal swapped
            if dst == ".lake" and not swapped:
                swapped = True
                os.rename(src, src + "-owned", src_dir_fd=src_fd, dst_dir_fd=src_fd)
                os.mkdir(src, dir_fd=src_fd)
                with open(f"/proc/self/fd/{src_fd}/{src}/foreign", "w") as stream:
                    stream.write("preserved")
            original(src_fd, src, dst_fd, dst)

        with patch.object(cache, "_rename_noreplace", side_effect=swap):
            with self.assertRaisesRegex(ValueError, "published generation differs"):
                self._seed(target)
        self.assertFalse((target / ".lake").exists())
        self.assertEqual(next(target.glob(".lake-stage-*/foreign")).read_text(),
                         "preserved")

    def test_swapped_snapshot_stage_is_not_published(self) -> None:
        target = self._target("swap-snapshot")
        sibling = self.root / "snapshot-swap-sibling"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        original = cache.no_replace_rename

        def swap(src_fd: int, src: str, dst_fd: int, dst: str,
                 expected: tuple[int, int]) -> None:
            if dst == "current":
                os.rename(src, src + "-moved", src_dir_fd=src_fd, dst_dir_fd=src_fd)
                os.symlink(sibling, src, dir_fd=src_fd)
            original(src_fd, src, dst_fd, dst, expected)

        with patch.object(cache, "no_replace_rename", side_effect=swap):
            with self.assertRaisesRegex(ValueError, "changed identity"):
                self._seed(target)
        key, _ = cache.pins(target)
        self.assertFalse((self.store / key / "current").exists())
        self.assertEqual((sibling / "keep").read_text(), "unchanged")

    def test_target_parent_retarget_preserves_sibling(self) -> None:
        self._seed(self._target("snapshot-first"))
        target = self._target("retarget")
        moved = self.root / "retarget-moved"
        sibling = self.root / "sibling-retarget"
        sibling.mkdir()
        sentinel = sibling / "keep"
        sentinel.write_text("unchanged")
        original = cache.extract_checked_archive

        def retarget(*args):
            target.rename(moved)
            target.symlink_to(sibling)
            original(*args)

        with patch.object(cache, "extract_checked_archive", side_effect=retarget):
            with self.assertRaisesRegex(ValueError, "changed identity"):
                self._seed(target)
        self.assertEqual(sentinel.read_text(), "unchanged")
        self.assertFalse((moved / ".lake").exists())

    def test_sigkill_during_snapshot_publish_retries(self) -> None:
        target = self._target("snapshot-killed")
        context = multiprocessing.get_context("fork")
        process = context.Process(target=killed_snapshot,
                                  args=(str(target), str(self.donor)))
        process.start(); process.join(10)
        self.assertEqual(process.exitcode, -signal.SIGKILL)
        self.assertFalse((target / ".lake").exists())
        key, _ = cache.pins(target)
        self.assertTrue(list((self.store / key).glob(".stage-*")))
        self._seed(target)
        self.assertFalse(list((self.store / key).glob(".stage-*")))
        cache.verify_ready(target)

    def test_cleanup_refuses_swapped_foreign_file(self) -> None:
        parent = self.root / "cleanup-parent"
        stage = parent / "stage"
        stage.mkdir(parents=True)
        (stage / "child").write_text("owned")
        sibling = self.root / "cleanup-sibling"
        sibling.mkdir()
        (sibling / "keep").write_text("foreign")
        fd = os.open(parent, archive_io.DIR_FLAGS)
        info = stage.stat()
        original = archive_io._quarantine

        def swap(parent_fd: int, name: str, expected: tuple[int, int]) -> str:
            if name == "child":
                os.rename("child", "child-moved", src_dir_fd=parent_fd,
                          dst_dir_fd=parent_fd)
                os.rename(sibling / "keep", f"/proc/self/fd/{parent_fd}/child")
            return original(parent_fd, name, expected)

        try:
            with patch.object(archive_io, "_quarantine", side_effect=swap):
                with self.assertRaisesRegex(ValueError, "changed identity"):
                    archive_io.remove_owned_tree(fd, "stage", (info.st_dev, info.st_ino))
        finally:
            os.close(fd)
        self.assertEqual(list(parent.glob(".removing-*/child"))[0].read_text(), "foreign")

    def test_cleanup_refuses_quarantine_alias_substitution(self) -> None:
        parent = self.root / "cleanup-alias-parent"
        stage = parent / "stage"
        stage.mkdir(parents=True)
        (stage / "child").write_text("owned")
        foreign = self.root / "foreign-alias"
        foreign.write_text("preserve")
        fd = os.open(parent, archive_io.DIR_FLAGS)
        info = stage.stat()
        original = archive_io._quarantine

        def swap(parent_fd: int, name: str, expected: tuple[int, int]) -> str:
            alias = original(parent_fd, name, expected)
            if name == "child":
                os.rename(alias, alias + "-owned", src_dir_fd=parent_fd,
                          dst_dir_fd=parent_fd)
                os.rename(foreign, f"/proc/self/fd/{parent_fd}/{alias}")
            return alias

        try:
            with patch.object(archive_io, "_quarantine", side_effect=swap):
                with self.assertRaisesRegex(ValueError, "changed identity"):
                    archive_io.remove_owned_tree(fd, "stage", (info.st_dev, info.st_ino))
        finally:
            os.close(fd)
        self.assertIn("preserve", [path.read_text() for path in
                                   parent.glob(".removing-*/.removing-*")])

    def test_snapshot_parent_retarget_does_not_write_sibling(self) -> None:
        parent = self.root / "snapshot-parent"
        sibling = self.root / "snapshot-unrelated"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        path = parent / "store" / "key"
        moved = self.root / "snapshot-parent-moved"
        original = cache.os.mkdir
        changed = False

        def retarget(name, mode=0o777, *, dir_fd=None):
            nonlocal changed
            if name == "key" and dir_fd is not None and not changed:
                changed = True
                parent.rename(moved)
                parent.symlink_to(sibling)
            return original(name, mode, dir_fd=dir_fd)

        try:
            with patch.object(cache.os, "mkdir", side_effect=retarget):
                with self.assertRaises(OSError):
                    with cache.locked_directory(path, ".lock", create=True):
                        pass
        finally:
            if parent.is_symlink():
                parent.unlink()
            if moved.exists():
                moved.rename(parent)
        self.assertEqual((sibling / "keep").read_text(), "unchanged")
        self.assertEqual([p.name for p in sibling.iterdir()], ["keep"])


if __name__ == "__main__":
    unittest.main()
