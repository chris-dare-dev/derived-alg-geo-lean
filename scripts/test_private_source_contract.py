#!/usr/bin/env python3
"""Disposable Git falsification fixtures for the pinned source contract."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import zlib

from private_source_contract import verify_source_packages


def git(*args: str, input: bytes | None = None) -> str:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
    result = subprocess.run(["git", *args], input=input, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=True, env=env)
    return result.stdout.decode().strip()


class SourceContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="private-source-contract-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.packages = self.root / "packages"
        self.packages.mkdir()
        self.reader = self.root / "reader.git"
        self.reader.mkdir()
        (self.reader / "objects").mkdir()
        (self.reader / "refs").mkdir()
        (self.reader / "HEAD").write_text("ref: refs/heads/master\n")
        (self.reader / "config").write_text(
            "[core]\n\trepositoryformatversion = 0\n\tfilemode = true\n\tbare = true\n")
        self.package = self.packages / "mathlib"
        self.package.mkdir()
        git("-C", str(self.package), "init", "-q")
        git("-C", str(self.package), "config", "user.name", "Fixture")
        git("-C", str(self.package), "config", "user.email", "fixture@example.test")
        (self.package / "Source.lean").write_text("-- pinned source\n")
        (self.package / "Run.sh").write_text("#!/bin/sh\ntrue\n")
        (self.package / "Run.sh").chmod(0o755)
        (self.package / "docs").mkdir()
        (self.package / "docs/link").symlink_to("../Source.lean")
        (self.package / ".gitignore").write_text(".lake/\nignored.tmp\n")
        git("-C", str(self.package), "add", ".")
        git("-C", str(self.package), "commit", "-qm", "pin")
        git("-C", str(self.package), "checkout", "--detach", "-q", "HEAD")
        self.revisions = {"mathlib": git("-C", str(self.package), "rev-parse", "HEAD")}

    def check(self) -> None:
        verify_source_packages(self.packages, self.revisions, reader_git_dir=self.reader)

    def refused(self) -> None:
        with self.assertRaises((ValueError, OSError, BrokenPipeError)):
            self.check()

    def test_clean_and_legitimate_mutable_index_and_build(self) -> None:
        self.check()
        git("-C", str(self.package), "update-index", "--assume-unchanged", "Source.lean")
        git("-C", str(self.package), "update-index", "--skip-worktree", "Run.sh")
        (self.package / ".lake/build/lib").mkdir(parents=True)
        (self.package / ".lake/build/lib/Source.olean").write_bytes(b"mutable output")
        self.check()
        git("-C", str(self.package), "update-index", "--no-assume-unchanged", "Source.lean")
        git("-C", str(self.package), "update-index", "--no-skip-worktree", "Run.sh")

    def test_ordinary_and_suppressed_tracked_edits(self) -> None:
        path = self.package / "Source.lean"
        for flag in (None, "--assume-unchanged", "--skip-worktree"):
            with self.subTest(flag=flag):
                if flag:
                    git("-C", str(self.package), "update-index", flag, "Source.lean")
                path.write_text("-- edited source\n")
                self.refused()
                path.write_text("-- pinned source\n")
                self.check()
                if flag:
                    git("-C", str(self.package), "update-index", "--no-" + flag[2:], "Source.lean")

    def test_untracked_ignored_and_mode_edits(self) -> None:
        (self.package / "ignored.tmp").write_text("ignored by Git")
        self.refused()
        (self.package / "ignored.tmp").unlink()
        (self.package / "Run.sh").chmod(0o644)
        self.refused()

    def test_tracked_symlink_text_and_target(self) -> None:
        link = self.package / "docs/link"
        link.unlink()
        link.symlink_to("../../outside")
        self.refused()
        link.unlink()
        link.symlink_to("../Source.lean")
        (self.package / "Source.lean").unlink()
        self.refused()

    def test_untracked_runtime_symlink_refused(self) -> None:
        (self.package / ".lake").symlink_to(self.root)
        self.refused()

    def test_forged_loose_commit_tree_and_blob(self) -> None:
        package = self.package
        commit = self.revisions["mathlib"]
        tree = git("-C", str(package), "rev-parse", "HEAD^{tree}")
        blob = git("-C", str(package), "rev-parse", "HEAD:Source.lean")
        for oid, kind, payload in ((commit, b"commit", b"tree " + tree.encode() + b"\n\nforged\n"),
                                   (tree, b"tree", b""),
                                   (blob, b"blob", b"-- forged source\n")):
            with self.subTest(kind=kind):
                object_path = package / ".git/objects" / oid[:2] / oid[2:]
                original = object_path.read_bytes()
                object_path.chmod(0o644)
                object_path.write_bytes(zlib.compress(kind + b" " + str(len(payload)).encode() + b"\0" + payload))
                self.refused()
                object_path.write_bytes(original)
                self.check()

    def test_packed_objects_and_corruption(self) -> None:
        self.check()
        git("-C", str(self.package), "gc", "--prune=now")
        self.check()
        pack = next((self.package / ".git/objects/pack").glob("*.pack"))
        content = bytearray(pack.read_bytes())
        content[len(content) // 2] ^= 1
        pack.chmod(0o644)
        pack.write_bytes(content)
        self.refused()

    def test_packed_delta_objects(self) -> None:
        path = self.package / "Large.lean"
        base = bytearray(b"a" * 100_000)
        for index in range(12):
            base[index * 1000:index * 1000 + 10] = f"{index:010d}".encode()
            path.write_bytes(base)
            git("-C", str(self.package), "add", "Large.lean")
            git("-C", str(self.package), "commit", "-qm", f"revision {index}")
        self.revisions["mathlib"] = git("-C", str(self.package), "rev-parse", "HEAD")
        git("-C", str(self.package), "gc", "--aggressive", "--prune=now")
        index = next((self.package / ".git/objects/pack").glob("*.idx"))
        inspection = git("verify-pack", "-v", str(index))
        self.assertTrue(any(len(line.split()) >= 7 for line in inspection.splitlines()),
                        "fixture did not produce a deltified object")
        self.check()

    def test_hardlinked_source_refused(self) -> None:
        source = self.package / "Source.lean"
        sentinel = self.root / "sibling-source"
        source.rename(sentinel)
        os.link(sentinel, source)
        self.refused()
        self.assertEqual(sentinel.read_text(), "-- pinned source\n")

    def test_replacements_alternates_and_nonminimal_reader(self) -> None:
        git("-C", str(self.package), "replace", self.revisions["mathlib"],
            self.revisions["mathlib"])
        self.refused()
        shutil.rmtree(self.package / ".git/refs/replace")
        (self.package / ".git/objects/info/alternates").write_text(str(self.root))
        self.refused()
        (self.package / ".git/objects/info/alternates").unlink()
        (self.package / ".git/objects/info/http-alternates").write_text("https://elsewhere.invalid/objects\n")
        self.refused()
        (self.package / ".git/objects/info/http-alternates").unlink()
        (self.reader / "config").write_text((self.reader / "config").read_text() +
                                            "[include]\npath = /tmp/elsewhere\n")
        self.refused()

    def test_aesop_empty_gitlink_only(self) -> None:
        self.package.rename(self.packages / "aesop")
        self.package = self.packages / "aesop"
        (self.package / "lean_packages").mkdir()
        # An index gitlink may refer to an unavailable commit; only its tree
        # entry is expected from the pinned package object store.
        git("-C", str(self.package), "update-index", "--add", "--cacheinfo",
            "160000," + self.revisions["mathlib"] + ",lean_packages/std")
        git("-C", str(self.package), "commit", "-qm", "gitlink")
        git("-C", str(self.package), "checkout", "--detach", "-q", "HEAD")
        self.revisions = {"aesop": git("-C", str(self.package), "rev-parse", "HEAD")}
        self.check()
        (self.package / "lean_packages/std").mkdir()
        self.check()
        (self.package / "lean_packages/std/populated").write_text("x")
        self.refused()

    def test_tracked_lake_precedes_runtime_exemption(self) -> None:
        (self.package / ".lake").mkdir()
        (self.package / ".lake/pinned").write_text("pinned")
        git("-C", str(self.package), "add", "-f", ".lake/pinned")
        git("-C", str(self.package), "commit", "-qm", "tracked lake")
        git("-C", str(self.package), "checkout", "--detach", "-q", "HEAD")
        self.revisions["mathlib"] = git("-C", str(self.package), "rev-parse", "HEAD")
        self.check()
        (self.package / ".lake/pinned").write_text("changed")
        self.refused()


if __name__ == "__main__":
    unittest.main()
