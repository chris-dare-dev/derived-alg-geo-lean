#!/usr/bin/env python3
"""Tests for the loop worktree root, disk budget and retirement."""

from __future__ import annotations

import contextlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

from scripts import loop_worktrees

IDENTITY = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.com",
            "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.com"}


def run(*args: str, cwd: Path) -> str:
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True,
                          env={**os.environ, **IDENTITY}).stdout.strip()


class LoopWorktreesTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        origin = self.tmp / "origin.git"
        run("git", "init", "-q", "--bare", "-b", "main", str(origin), cwd=self.tmp)
        self.repo = self.tmp / "repo"
        run("git", "clone", "-q", str(origin), str(self.repo), cwd=self.tmp)
        (self.repo / ".gitignore").write_text("/.lake/\n")
        (self.repo / "README").write_text("x\n")
        run("git", "add", "-A", cwd=self.repo)
        run("git", "commit", "-qm", "init", cwd=self.repo)
        run("git", "push", "-q", "origin", "HEAD:main", cwd=self.repo)
        self.root = self.tmp / "wt"
        bin_dir = self.tmp / "bin"
        bin_dir.mkdir()
        fake_gh = bin_dir / "gh"
        fake_gh.write_text('#!/bin/sh\nprintf "%s" "${FAKE_GH_MERGED:-[]}"\n')
        fake_gh.chmod(0o755)
        environment = mock.patch.dict(os.environ, {
            **IDENTITY, "HOME": str(self.tmp / "home"), "DAG_WORKTREE_ROOT": str(self.root),
            "PATH": f"{bin_dir}:{os.environ['PATH']}"})
        environment.start()
        self.addCleanup(environment.stop)
        for key in ("DAG_WORKTREE_MIN_FREE_GIB", "DAG_WORKTREE_SEED_GIB", "DAG_WORKTREE_MAX",
                    "FAKE_GH_MERGED"):
            os.environ.pop(key, None)
        # The host's /tmp may itself be tmpfs; the volatile-root refusal has its own test.
        filesystem = mock.patch.object(loop_worktrees, "fs_type", return_value="ext4")
        filesystem.start()
        self.addCleanup(filesystem.stop)

    def cli(self, *argv: str) -> tuple[int, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = loop_worktrees.main(["--repo", str(self.repo), *argv])
        return code, out.getvalue() + err.getvalue()

    def add(self, name: str, *, path: Path | None = None, detach: bool = False) -> Path:
        path = path or self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        branch = ["--detach"] if detach else ["-b", f"agent/{name}"]
        run("git", "worktree", "add", "-q", *branch, str(path), "origin/main", cwd=self.repo)
        return path

    def commit(self, worktree: Path, name: str = "work") -> None:
        (worktree / name).write_text(name)
        run("git", "add", "-A", cwd=worktree)
        run("git", "commit", "-qm", name, cwd=worktree)

    def has_branch(self, name: str) -> bool:
        return subprocess.run(["git", "rev-parse", "-q", "--verify", f"refs/heads/{name}"],
                              cwd=self.repo, capture_output=True).returncode == 0

    # root ---------------------------------------------------------------

    def test_root_prefers_environment_then_config_then_home(self) -> None:
        self.assertEqual(loop_worktrees.worktree_root(self.repo), self.root)
        del os.environ["DAG_WORKTREE_ROOT"]
        self.assertEqual(loop_worktrees.worktree_root(self.repo), self.tmp / "home/wt/repo")
        run("git", "config", "dag.worktreeRoot", str(self.tmp / "configured"), cwd=self.repo)
        self.assertEqual(loop_worktrees.worktree_root(self.repo), self.tmp / "configured")
        code, out = self.cli("root")
        self.assertEqual((code, out.strip()), (0, str(self.tmp / "configured")))
        self.assertTrue((self.tmp / "configured").is_dir())

    def test_root_refuses_codex_home_checkout_relative_and_volatile(self) -> None:
        for bad in (self.tmp / "home/.codex/worktrees", self.tmp / ".codex-accounts/a/worktrees",
                    self.repo / ".claude/worktrees", Path("relative/wt")):
            os.environ["DAG_WORKTREE_ROOT"] = str(bad)
            with self.assertRaises(loop_worktrees.Refused, msg=str(bad)):
                loop_worktrees.worktree_root(self.repo)
        os.environ["DAG_WORKTREE_ROOT"] = str(self.root)
        with mock.patch.object(loop_worktrees, "fs_type", return_value="tmpfs"):
            code, out = self.cli("root")
        self.assertEqual(code, 1)
        self.assertIn("tmpfs", out)

    # check --------------------------------------------------------------

    def test_check_enforces_the_cap_on_worktrees_under_the_root(self) -> None:
        os.environ.update(DAG_WORKTREE_MIN_FREE_GIB="0", DAG_WORKTREE_SEED_GIB="0",
                          DAG_WORKTREE_MAX="2")
        self.assertEqual(self.cli("check")[0], 0)
        self.add("one")
        self.add("elsewhere", path=self.tmp / "outside/elsewhere")
        self.assertEqual(self.cli("check")[0], 0, "a worktree outside the root does not count")
        self.add("two")
        code, out = self.cli("check")
        self.assertEqual(code, 1)
        self.assertIn("2 worktrees under", out)

    def test_check_enforces_the_disk_floor(self) -> None:
        os.environ.update(DAG_WORKTREE_MIN_FREE_GIB="1000000000")
        code, out = self.cli("check")
        self.assertEqual(code, 1)
        self.assertIn("must stay free", out)
        run("git", "config", "dag.worktreeMax", "not-a-number", cwd=self.repo)
        os.environ["DAG_WORKTREE_MIN_FREE_GIB"] = "0"
        self.assertIn("not a number", self.cli("check")[1])

    # retire -------------------------------------------------------------

    def test_retire_pushed_branch_keeps_the_branch(self) -> None:
        worktree = self.add("pushed")
        self.commit(worktree)
        run("git", "push", "-q", "origin", "agent/pushed", cwd=worktree)
        code, out = self.cli("retire", str(worktree))
        self.assertEqual(code, 0, out)
        self.assertFalse(worktree.exists())
        self.assertTrue(self.has_branch("agent/pushed"))

    def test_retire_refuses_unpushed_work(self) -> None:
        worktree = self.add("unpushed")
        self.commit(worktree)
        code, out = self.cli("retire", str(worktree))
        self.assertEqual(code, 1)
        self.assertIn("push branch agent/unpushed first", out)
        self.assertTrue(worktree.is_dir())

    def test_retire_after_merge_deletes_the_squashed_branch(self) -> None:
        worktree = self.add("merged")
        self.commit(worktree)
        os.environ["FAKE_GH_MERGED"] = '[{"number": 7}]'
        code, out = self.cli("retire", str(worktree))
        self.assertEqual(code, 0, out)
        self.assertFalse(worktree.exists())
        self.assertFalse(self.has_branch("agent/merged"))

    def test_retire_detached_head_needs_a_remote_ref(self) -> None:
        clean = self.add("clean", detach=True)
        self.assertEqual(self.cli("retire", str(clean))[0], 0)
        probe = self.add("probe", detach=True)
        self.commit(probe)
        code, out = self.cli("retire", str(probe))
        self.assertEqual(code, 1)
        self.assertIn("to a branch first", out)

    def test_retire_refuses_uncommitted_changes_but_not_ignored_build_output(self) -> None:
        worktree = self.add("dirty")
        (worktree / "README").write_text("edited\n")
        self.assertEqual(self.cli("retire", str(worktree))[0], 1)
        run("git", "checkout", "--", "README", cwd=worktree)
        (worktree / "stray").write_text("untracked\n")
        self.assertEqual(self.cli("retire", str(worktree))[0], 1)
        (worktree / "stray").unlink()
        (worktree / ".lake/build").mkdir(parents=True)
        (worktree / ".lake/build/x.olean").write_bytes(b"olean")
        code, out = self.cli("retire", str(worktree))
        self.assertEqual(code, 0, out)
        self.assertFalse(worktree.exists())

    def test_retire_refuses_a_package_donor_until_its_users_are_gone(self) -> None:
        donor, user = self.add("donor"), self.add("user")
        (donor / ".lake/packages/mathlib").mkdir(parents=True)
        (user / ".lake").mkdir()
        (user / ".lake/packages").symlink_to(donor / ".lake/packages")
        code, out = self.cli("retire", str(donor))
        self.assertEqual(code, 1)
        self.assertIn(str(user), out)
        self.assertEqual(self.cli("retire", str(user))[0], 0)
        self.assertTrue((donor / ".lake/packages/mathlib").is_dir(), "the link was not followed")
        self.assertEqual(self.cli("retire", str(donor))[0], 0)

    def test_retire_refuses_the_shared_checkout_and_strangers(self) -> None:
        self.assertIn("never retired", self.cli("retire", str(self.repo))[1])
        stranger = self.tmp / "stranger"
        stranger.mkdir()
        self.assertEqual(self.cli("retire", str(stranger))[0], 1)

    def test_retire_refuses_a_worktree_a_process_is_working_in(self) -> None:
        worktree = self.add("busy")
        sleeper = subprocess.Popen(["sleep", "60"], cwd=worktree)
        self.addCleanup(sleeper.wait)
        self.addCleanup(sleeper.kill)
        code, out = self.cli("retire", str(worktree))
        self.assertEqual(code, 1)
        self.assertIn(str(sleeper.pid), out)

    def test_retire_removes_an_empty_codex_wrapper(self) -> None:
        wrapper = self.root / "3f2a"
        wrapper.mkdir(parents=True)
        (wrapper / ".codex-worktree-name").touch()
        worktree = self.add("wrapped", path=wrapper / "repo")
        code, out = self.cli("retire", str(worktree))
        self.assertEqual(code, 0, out)
        self.assertFalse(wrapper.exists())

    def test_dry_run_changes_nothing(self) -> None:
        worktree = self.add("dry")
        os.environ["FAKE_GH_MERGED"] = '[{"number": 3}]'
        code, out = self.cli("retire", "--dry-run", str(worktree))
        self.assertEqual(code, 0, out)
        self.assertIn("would git worktree remove", out)
        self.assertTrue(worktree.is_dir())
        self.assertTrue(self.has_branch("agent/dry"))


class FilesystemTypeTest(unittest.TestCase):
    def test_reports_the_mount_holding_a_missing_path(self) -> None:
        self.assertEqual(loop_worktrees.fs_type(Path("/proc/self/not-created-yet")), "proc")
        self.assertTrue(loop_worktrees.fs_type(Path("/")))


if __name__ == "__main__":
    unittest.main()
