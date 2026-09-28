#!/usr/bin/env python3
"""Filesystem alias regressions for private Lake worktrees."""

import os
from pathlib import Path
import tempfile
import unittest

from private_alias_scan import scan_private_lake


class PrivateAliasScanTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.target = self.root / "worktree"
        self.target.mkdir()
        (self.target / ".lake/packages/mathlib/.git/objects").mkdir(parents=True)
        (self.target / ".lake/build").mkdir()
        (self.target / ".lake/packages/mathlib/Mathlib.lean").write_bytes(b"source")
        (self.target / ".lake/build/Project.olean").write_bytes(b"artifact")

    def test_private_regular_files_pass(self) -> None:
        scan_private_lake(self.target)

    def test_hardlinked_existing_artifact_refuses_without_changing_sibling(self) -> None:
        sibling = self.root / "sibling.olean"
        sibling.write_bytes(b"sibling")
        artifact = self.target / ".lake/build/Project.olean"
        artifact.unlink()
        os.link(sibling, artifact)
        before = (sibling.stat().st_ino, sibling.read_bytes())
        with self.assertRaisesRegex(ValueError, "hardlinked file"):
            scan_private_lake(self.target)
        self.assertEqual((sibling.stat().st_ino, sibling.read_bytes()), before)

    def test_hardlinked_new_source_and_git_object_refuse(self) -> None:
        sibling = self.root / "sibling"
        sibling.write_bytes(b"keep")
        for relative in ("packages/mathlib/Mathlib.lean",
                         "packages/mathlib/.git/objects/alias"):
            with self.subTest(relative=relative):
                path = self.target / ".lake" / relative
                if path.exists():
                    path.unlink()
                os.link(sibling, path)
                with self.assertRaisesRegex(ValueError, "hardlinked file"):
                    scan_private_lake(self.target)
                path.unlink()
                self.assertEqual(sibling.read_bytes(), b"keep")

    def test_special_file_refuses(self) -> None:
        fifo = self.target / ".lake/build/pipe"
        os.mkfifo(fifo)
        with self.assertRaisesRegex(ValueError, "special file"):
            scan_private_lake(self.target)

    def test_top_level_lake_link_cannot_escape_to_sibling(self) -> None:
        sibling = self.root / "sibling-config"
        sibling.mkdir()
        (sibling / "keep").write_text("unchanged")
        (self.target / ".lake/config").symlink_to(sibling, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "link escapes tree"):
            scan_private_lake(self.target)
        self.assertEqual((sibling / "keep").read_text(), "unchanged")


if __name__ == "__main__":
    unittest.main()
