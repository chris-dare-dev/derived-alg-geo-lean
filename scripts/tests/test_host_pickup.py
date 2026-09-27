"""Focused host pickup tests; live scope and runner migration need host evidence."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import Mock, patch

from scripts import host_pickup


def fixture(root: Path) -> tuple[Path, Path, str]:
    base = root / "controller"
    base.mkdir(mode=0o700)
    for name in ("jobs", "leases", "logs"):
        (base / name).mkdir(mode=0o700)
    repo = root / "repo"
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    (repo / "hello.txt").write_text("isolated\n", encoding="utf-8")
    subprocess.run(["git", "-C", str(repo), "add", "hello.txt"], check=True)
    subprocess.run([
        "git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
        "commit", "-qm", "fixture",
    ], check=True)
    revision = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    return base, repo, revision


def capacity(base: Path) -> dict[str, dict[str, int]]:
    return {host_pickup._host_id(): {
        "cpu_threads": 4,
        "memory_bytes": 16 * host_pickup.GIB,
        "disk_bytes": 40 * host_pickup.GIB,
    }}


class HostPickupTests(unittest.TestCase):
    def test_ephemeral_runner_lease_precedes_first_runner_write_and_archives_logs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            archive = Path(directory) / "runner.tar.gz"
            with tarfile.open(archive, "w:gz") as bundle:
                for name, body in (
                    ("config.sh", "#!/bin/sh\nexit 0\n"),
                    ("run.sh", "#!/bin/sh\nmkdir -p _diag _work/derived-alg-geo-lean/derived-alg-geo-lean\necho kept > _diag/trace.log\n"),
                ):
                    data = body.encode()
                    member = tarfile.TarInfo(name)
                    member.mode = 0o755
                    member.size = len(data)
                    bundle.addfile(member, io.BytesIO(data))
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            def run_scope(unit: str, root: Path, profile: str, command: list[str]) -> int:
                self.assertTrue((base / "leases" / f"{root.name}.json").is_file())
                self.assertTrue((root / "registration-token").is_file())
                info = root.stat()
                return host_pickup._runner_worker(
                    archive, digest, "owner-linux", root, (info.st_dev, info.st_ino)
                )
            with patch.object(host_pickup, "_capacity", side_effect=capacity), \
                 patch.object(host_pickup, "_registration_token", return_value="test-token"), \
                 patch.object(host_pickup, "_run_scope", side_effect=run_scope), \
                 patch.object(host_pickup, "_scope_cleared", return_value=True), \
                 patch.object(host_pickup, "_runner_registered", return_value=False):
                host_pickup.runner_once(base, archive, digest, "owner-linux")
            self.assertEqual(list((base / "jobs").iterdir()), [])
            self.assertEqual(list((base / "leases").glob("*.json")), [])
            logs = list((base / "logs").iterdir())
            self.assertEqual(len(logs), 1)
            self.assertEqual((logs[0] / "diag/trace.log").read_text(encoding="utf-8"), "kept\n")

    def test_runner_diagnostic_symlink_cannot_overwrite_archive_metadata_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            root, _ = host_pickup._prepare(base, "abc123")
            checkout = root / "runner/_work/derived-alg-geo-lean/derived-alg-geo-lean"
            checkout.mkdir(parents=True)
            diagnostics = root / "runner/_diag"
            diagnostics.mkdir()
            sentinel = Path(directory) / "sentinel"
            sentinel.write_text("keep", encoding="utf-8")
            (diagnostics / "pickup.json").symlink_to(sentinel)
            record = host_pickup._record("abc123", root, "build", kind="runner")
            host_pickup._archive_runner_logs(base, root, "abc123", record)
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "keep")
            archive = base / "logs/abc123"
            self.assertTrue((archive / "diag/pickup.json").is_symlink())
            self.assertTrue((archive / "pickup.json").is_file())

    def test_registered_runner_retains_lease_and_recovery_denies(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            archive = Path(directory) / "unused.tar.gz"
            archive.write_bytes(b"fixture")
            with patch.object(host_pickup, "_capacity", side_effect=capacity), \
                 patch.object(host_pickup, "_verify_runner_archive"), \
                 patch.object(host_pickup, "_registration_token", return_value="test-token"), \
                 patch.object(host_pickup, "_run_scope", return_value=0), \
                 patch.object(host_pickup, "_scope_cleared", return_value=True), \
                 patch.object(host_pickup, "_runner_registered", return_value=True):
                with self.assertRaisesRegex(ValueError, "remains registered"):
                    host_pickup.runner_once(base, archive, "0" * 64, "owner-linux")
                leases = list((base / "leases").glob("*.json"))
                self.assertEqual(len(leases), 1)
                with self.assertRaisesRegex(ValueError, "still registered"):
                    host_pickup.recover(base, leases[0].stem)
            self.assertEqual(len(list((base / "jobs").iterdir())), 1)

    def test_bad_archive_denies_before_token_or_lease(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            archive = Path(directory) / "bad.tar.gz"
            archive.write_bytes(b"bad archive")
            with patch.object(host_pickup, "_registration_token") as token:
                with self.assertRaisesRegex(ValueError, "digest does not match"):
                    host_pickup.runner_once(base, archive, "0" * 64, "owner-linux")
            token.assert_not_called()
            self.assertEqual(list((base / "jobs").iterdir()), [])
            self.assertEqual(list((base / "leases").glob("*.json")), [])

    def test_unsafe_archive_member_denies_before_token_or_lease(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            archive = Path(directory) / "unsafe.tar.gz"
            with tarfile.open(archive, "w:gz") as bundle:
                member = tarfile.TarInfo("../outside")
                member.size = 0
                bundle.addfile(member)
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            with patch.object(host_pickup, "_registration_token") as token:
                with self.assertRaisesRegex(ValueError, "unsafe member"):
                    host_pickup.runner_once(base, archive, digest, "owner-linux")
            token.assert_not_called()
            self.assertEqual(list((base / "jobs").iterdir()), [])
            self.assertEqual(list((base / "leases").glob("*.json")), [])

    def test_runner_failure_before_checkout_can_recover_without_token(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            archive = Path(directory) / "fixture.tar.gz"
            archive.write_bytes(b"fixture")
            with patch.object(host_pickup, "_verify_runner_archive"), \
                 patch.object(host_pickup, "_capacity", side_effect=capacity), \
                 patch.object(host_pickup, "_registration_token", return_value="test-token"), \
                 patch.object(host_pickup, "_run_scope", return_value=1), \
                 patch.object(host_pickup, "_scope_cleared", return_value=True), \
                 patch.object(host_pickup, "_runner_registered", return_value=False):
                with self.assertRaisesRegex(ValueError, "exited unsuccessfully"):
                    host_pickup.runner_once(base, archive, "0" * 64, "owner-linux")
                lease = next((base / "leases").glob("*.json"))
                root = base / "jobs" / lease.stem
                self.assertFalse((root / "registration-token").exists())
                host_pickup.recover(base, lease.stem)
            self.assertEqual(list((base / "jobs").iterdir()), [])
            self.assertFalse(lease.exists())
            metadata = json.loads((base / "logs" / lease.stem / "pickup.json").read_text())
            self.assertFalse(metadata["checkout_observed"])

    def test_recovery_rejects_replacement_root_with_forged_local_marker(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, repo, revision = fixture(Path(directory))
            with patch.object(host_pickup, "_capacity", side_effect=capacity), \
                 patch.object(host_pickup, "_run_scope", return_value=130), \
                 patch.object(host_pickup, "_scope_cleared", return_value=False):
                with self.assertRaisesRegex(ValueError, "still active"):
                    host_pickup.pickup(base, repo, revision, "probe", ["true"])
            lease = next((base / "leases").glob("*.json"))
            root = base / "jobs" / lease.stem
            moved = base / "jobs/original"
            root.rename(moved)
            root.mkdir(mode=0o700)
            replacement = root.stat()
            (root / ".owner.json").write_text(json.dumps({
                "namespace": root.name, "dev": replacement.st_dev, "ino": replacement.st_ino,
            }), encoding="utf-8")
            (root / ".owner.json").chmod(0o600)
            (root / "sentinel").write_text("keep", encoding="utf-8")
            with patch.object(host_pickup, "_scope_cleared", return_value=True):
                with self.assertRaisesRegex(ValueError, "differs from recorded inode"):
                    host_pickup.recover(base, lease.stem)
            self.assertEqual((root / "sentinel").read_text(encoding="utf-8"), "keep")
            self.assertTrue(moved.is_dir())
            self.assertTrue(lease.is_file())

    def test_enabled_idle_legacy_runner_keeps_its_reservation(self) -> None:
        def show(unit: str, *properties: str) -> dict[str, str]:
            return {
                "ActiveState": "inactive", "UnitFileState": "enabled",
                "CPUQuotaPerSecUSec": "3s", "MemoryMax": str(12 * host_pickup.GIB),
            }
        with patch.object(host_pickup, "_systemctl_show", side_effect=show):
            reservations = host_pickup._legacy_reservations()
        self.assertEqual(reservations["cpu_threads"], 12)
        self.assertEqual(reservations["memory_bytes"], 48 * host_pickup.GIB)

    def test_scope_clears_ambient_environment_before_worker(self) -> None:
        root = Path("/tmp/dag-pickup-fixture")
        with patch.object(host_pickup.subprocess, "run", return_value=Mock(returncode=0)) as call:
            host_pickup._run_scope("dag-pickup-abc.scope", root, "probe", ["/bin/true"])
        argv = call.call_args.args[0]
        env_start = argv.index("/usr/bin/env")
        self.assertEqual(argv[env_start + 1], "-i")
        self.assertIn(f"HOME={root / 'home'}", argv)
        self.assertIn(f"ELAN_HOME={root / 'home/.elan'}", argv)
        self.assertIn(f"TMPDIR={root / 'tmp'}", argv)
        self.assertIn("--property=MemoryMax=2147483648", argv)

    def test_pickup_clones_independently_then_cleans_exact_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, repo, revision = fixture(Path(directory))
            def run_scope(unit: str, root: Path, profile: str, command: list[str]) -> int:
                self.assertTrue((base / "leases" / f"{root.name}.json").is_file())
                info = root.stat()
                self.assertEqual(host_pickup._worker(repo, revision, root,
                                                   (info.st_dev, info.st_ino), [
                    "python3", "-c", "from pathlib import Path; assert Path('hello.txt').read_text() == 'isolated\\n'",
                ]), 0)
                self.assertFalse((root / "workspace/.git/objects/info/alternates").exists())
                self.assertFalse((root / "workspace/.lake/packages").is_symlink())
                return 0
            with patch.object(host_pickup, "_capacity", side_effect=capacity), \
                 patch.object(host_pickup, "_run_scope", side_effect=run_scope), \
                 patch.object(host_pickup, "_scope_cleared", return_value=True):
                self.assertEqual(host_pickup.pickup(base, repo, revision, "probe", ["true"]), 0)
            self.assertEqual(list((base / "jobs").iterdir()), [])
            self.assertEqual(list((base / "leases").glob("*.json")), [])
            self.assertEqual((repo / "hello.txt").read_text(encoding="utf-8"), "isolated\n")

    def test_uncleared_scope_retains_lease_and_workspace(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, repo, revision = fixture(Path(directory))
            with patch.object(host_pickup, "_capacity", side_effect=capacity), \
                 patch.object(host_pickup, "_run_scope", return_value=130), \
                 patch.object(host_pickup, "_scope_cleared", return_value=False):
                with self.assertRaisesRegex(ValueError, "still active"):
                    host_pickup.pickup(base, repo, revision, "probe", ["true"])
            self.assertEqual(len(list((base / "jobs").iterdir())), 1)
            leases = list((base / "leases").glob("*.json"))
            self.assertEqual(len(leases), 1)
            with patch.object(host_pickup, "_scope_cleared", return_value=False):
                with self.assertRaisesRegex(ValueError, "still active"):
                    host_pickup.recover(base, leases[0].stem)
            with patch.object(host_pickup, "_scope_cleared", return_value=True):
                host_pickup.recover(base, leases[0].stem)
            self.assertEqual(list((base / "jobs").iterdir()), [])
            self.assertEqual(list((base / "leases").glob("*.json")), [])

    def test_cleanup_rejects_replaced_root_and_preserves_sibling(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            root, identity = host_pickup._prepare(base, "abc123")
            sibling = base / "jobs/sibling"
            sibling.mkdir(mode=0o700)
            (sibling / "sentinel").write_text("keep", encoding="utf-8")
            root.rename(base / "jobs/original")
            root.symlink_to(sibling, target_is_directory=True)
            with self.assertRaises(OSError):
                host_pickup._cleanup(base, "abc123", identity)
            self.assertEqual((sibling / "sentinel").read_text(encoding="utf-8"), "keep")
            root.unlink()
            (base / "jobs/original").rename(root)
            host_pickup._cleanup(base, "abc123", identity)
            self.assertFalse(root.exists())
            self.assertEqual((sibling / "sentinel").read_text(encoding="utf-8"), "keep")

    def test_cleanup_rejects_rename_before_recursive_delete(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, _, _ = fixture(Path(directory))
            root, identity = host_pickup._prepare(base, "abc123")
            (root / "sentinel").write_text("keep", encoding="utf-8")
            moved = base / "jobs/moved"
            def rename_during_check() -> list[Path]:
                root.rename(moved)
                return []
            with patch.object(host_pickup, "_mount_points", side_effect=rename_during_check):
                with self.assertRaises(FileNotFoundError):
                    host_pickup._cleanup(base, "abc123", identity)
            self.assertEqual((moved / "sentinel").read_text(encoding="utf-8"), "keep")

    def test_worker_rejects_shared_package_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, repo, revision = fixture(Path(directory))
            donor = Path(directory) / "donor"
            donor.mkdir()
            (repo / ".lake").mkdir()
            (repo / ".lake/packages").symlink_to(donor, target_is_directory=True)
            subprocess.run(["git", "-C", str(repo), "add", ".lake/packages"], check=True)
            subprocess.run([
                "git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                "commit", "-qm", "symlink fixture",
            ], check=True)
            revision = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
            root, _ = host_pickup._prepare(base, "abc123")
            with self.assertRaisesRegex(ValueError, "shared mutable package/build symlink"):
                info = root.stat()
                host_pickup._worker(repo, revision, root,
                                    (info.st_dev, info.st_ino), ["true"])


if __name__ == "__main__":
    unittest.main()
