#!/usr/bin/env python3
"""Adversarial record and two-branch fixtures for CI1.10's exception pilot."""

from __future__ import annotations

from contextlib import redirect_stdout
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import check_single_instantiation as gate  # noqa: E402


CAT = "CategoryTheory\tCategoryTheory.Existing\tcategory reason\n"
ALG = "Algebra\tAlgebra.Existing\talgebra reason\n"
MODULES = {
    "CategoryTheory.Existing": "DerivedAlgGeo.CategoryTheory.Existing",
    "Algebra.Existing": "DerivedAlgGeo.Algebra.Existing",
    "CategoryTheory.New": "DerivedAlgGeo.CategoryTheory.New",
    "Algebra.New": "DerivedAlgGeo.Algebra.New",
}


class SingleInstantiationRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.legacy = self.root / "single_instantiation_baseline.txt"
        self.shards = self.root / "single_instantiation_records"
        self.shards.mkdir()
        self.legacy.write_text("", encoding="utf-8")
        (self.shards / "CategoryTheory.txt").write_text(CAT, encoding="utf-8")
        (self.shards / "Algebra.txt").write_text(ALG, encoding="utf-8")

    def records(self) -> dict[str, gate.BaselineRecord]:
        return gate.read_baseline(self.legacy, self.shards)

    def test_union_preserves_every_identity_owner_and_reason(self) -> None:
        self.legacy.write_text(
            "LinearAlgebra\tLinearAlgebra.Legacy\tlegacy reason\n", encoding="utf-8"
        )
        records = self.records()
        self.assertEqual(set(records), {
            "LinearAlgebra.Legacy", "CategoryTheory.Existing", "Algebra.Existing"
        })
        self.assertEqual(
            (records["LinearAlgebra.Legacy"].subject, records["LinearAlgebra.Legacy"].reason),
            ("LinearAlgebra", "legacy reason"),
        )
        self.assertEqual(records["CategoryTheory.Existing"].reason, "category reason")
        self.assertEqual(records["Algebra.Existing"].reason, "algebra reason")

    def test_duplicate_across_legacy_and_shard_is_rejected(self) -> None:
        self.legacy.write_text(CAT, encoding="utf-8")
        with self.assertRaisesRegex(gate.BaselineError, "duplicate CategoryTheory.Existing"):
            self.records()

    def test_conflicting_duplicate_owner_is_rejected(self) -> None:
        self.legacy.write_text(
            "Algebra\tCategoryTheory.Existing\tconflicting owner\n", encoding="utf-8"
        )
        with self.assertRaisesRegex(gate.BaselineError, "duplicate CategoryTheory.Existing"):
            self.records()

    def test_conflicting_owner_and_wrong_shard_are_rejected(self) -> None:
        (self.shards / "CategoryTheory.txt").write_text(ALG, encoding="utf-8")
        with self.assertRaisesRegex(gate.BaselineError, "conflicts with shard CategoryTheory"):
            self.records()

    def test_unknown_or_malformed_record_cannot_disappear_from_union(self) -> None:
        for filename, content, expected in (
            ("Unknown.txt", "Unknown\tUnknown.X\treason\n", "unknown subject owner"),
            ("CategoryTheory.txt", "CategoryTheory\tCategoryTheory.X\n", "expected subject"),
        ):
            with self.subTest(filename=filename, content=content):
                path = self.shards / filename
                original = path.read_text(encoding="utf-8") if path.exists() else None
                path.write_text(content, encoding="utf-8")
                with self.assertRaisesRegex(gate.BaselineError, expected):
                    self.records()
                if original is None:
                    path.unlink()
                else:
                    path.write_text(original, encoding="utf-8")

    def test_new_category_record_changes_only_its_owner_shard(self) -> None:
        self.legacy.write_text(
            "LinearAlgebra\tLinearAlgebra.Stale\tformer thin abstraction\n",
            encoding="utf-8",
        )
        before_legacy = self.legacy.read_bytes()
        before_algebra = (self.shards / "Algebra.txt").read_bytes()
        records = self.records()
        changed = gate.write_baseline(
            ["Algebra.Existing", "CategoryTheory.Existing", "CategoryTheory.New"],
            MODULES, records,
            self.shards,
        )
        self.assertEqual(changed, [self.shards / "CategoryTheory.txt"])
        self.assertEqual(self.legacy.read_bytes(), before_legacy)
        self.assertEqual((self.shards / "Algebra.txt").read_bytes(), before_algebra)
        self.assertEqual(self.records()["CategoryTheory.New"].reason, gate.TODO)
        self.assertIn("LinearAlgebra.Stale", self.records())

    def run_gate(self, rows: str, *, relax: bool = False) -> tuple[int, str]:
        sweep = self.root / "enum-inhabitants.txt"
        sweep.write_text(rows, encoding="utf-8")
        output = io.StringIO()
        with mock.patch.object(gate, "BASELINE", self.legacy), \
             mock.patch.object(gate, "RECORDS", self.shards), \
             mock.patch.object(sys, "argv", [
                 "check_single_instantiation.py", str(sweep),
                 *(["--relax"] if relax else []),
             ]), \
             redirect_stdout(output):
            status = gate.main()
        return status, output.getvalue()

    def test_dropped_or_renamed_record_fails_gate(self) -> None:
        rows = "structure\tDerivedAlgGeo.CategoryTheory.Existing\tCategoryTheory.Existing\n"
        self.assertEqual(self.run_gate(rows)[0], 0)
        (self.shards / "CategoryTheory.txt").write_text("", encoding="utf-8")
        status, output = self.run_gate(rows)
        self.assertEqual(status, 1)
        self.assertIn("CategoryTheory.Existing", output)
        (self.shards / "CategoryTheory.txt").write_text(
            "CategoryTheory\tCategoryTheory.Renamed\tcategory reason\n", encoding="utf-8"
        )
        status, output = self.run_gate(rows)
        self.assertEqual(status, 1)
        self.assertIn("CategoryTheory.Existing", output)

    def test_record_owner_must_match_emitted_module_subject(self) -> None:
        rows = "structure\tDerivedAlgGeo.Algebra.Existing\tCategoryTheory.Existing\n"
        status, output = self.run_gate(rows)
        self.assertEqual(status, 1)
        self.assertIn("belongs to module subject Algebra", output)

    def test_record_owner_check_includes_live_names_with_two_inhabitants(self) -> None:
        rows = (
            "structure\tDerivedAlgGeo.Algebra.Existing\tCategoryTheory.Existing\n"
            "inhabitant\tCategoryTheory.Existing\tfirst\n"
            "inhabitant\tCategoryTheory.Existing\tsecond\n"
        )
        status, output = self.run_gate(rows)
        self.assertEqual(status, 1)
        self.assertIn("belongs to module subject Algebra", output)

    def test_padded_todo_fails_both_check_and_relax(self) -> None:
        rows = "structure\tDerivedAlgGeo.CategoryTheory.Existing\tCategoryTheory.Existing\n"
        path = self.shards / "CategoryTheory.txt"
        for reason in (" " + gate.TODO, gate.TODO + " "):
            with self.subTest(reason=reason):
                content = f"CategoryTheory\tCategoryTheory.Existing\t{reason}\n"
                path.write_text(content, encoding="utf-8")
                for relax in (False, True):
                    status, output = self.run_gate(rows, relax=relax)
                    self.assertEqual(status, 1)
                    self.assertIn("surrounding whitespace", output)
                    self.assertEqual(path.read_text(encoding="utf-8"), content)

    def test_relax_adds_only_owner_shard_with_stale_legacy_record(self) -> None:
        self.legacy.write_text(
            "LinearAlgebra\tLinearAlgebra.Stale\tformer thin abstraction\n",
            encoding="utf-8",
        )
        before_legacy = self.legacy.read_bytes()
        before_algebra = (self.shards / "Algebra.txt").read_bytes()
        rows = (
            "structure\tDerivedAlgGeo.CategoryTheory.Existing\tCategoryTheory.Existing\n"
            "structure\tDerivedAlgGeo.Algebra.Existing\tAlgebra.Existing\n"
            "structure\tDerivedAlgGeo.CategoryTheory.New\tCategoryTheory.New\n"
        )
        status, output = self.run_gate(rows, relax=True)
        self.assertEqual(status, 1)  # New exceptions require a written reason.
        self.assertIn("CategoryTheory.New", output)
        self.assertEqual(self.legacy.read_bytes(), before_legacy)
        self.assertEqual((self.shards / "Algebra.txt").read_bytes(), before_algebra)
        self.assertEqual(self.records()["CategoryTheory.New"].reason, gate.TODO)
        self.assertIn("LinearAlgebra.Stale", self.records())

    def test_two_independent_git_branches_merge_without_shared_append_point(self) -> None:
        repo = self.root / "git-fixture"
        repo.mkdir()
        legacy = repo / "single_instantiation_baseline.txt"
        shards = repo / "single_instantiation_records"
        shards.mkdir()
        legacy.write_text("", encoding="utf-8")
        (shards / "CategoryTheory.txt").write_text(CAT, encoding="utf-8")
        (shards / "Algebra.txt").write_text(ALG, encoding="utf-8")

        def git(*args: str) -> str:
            return subprocess.check_output(
                ["git", *args], cwd=repo, text=True, stderr=subprocess.STDOUT
            ).strip()

        git("init", "-q", "-b", "base")
        git("config", "user.name", "CI1 fixture")
        git("config", "user.email", "fixture@example.invalid")
        git("add", ".")
        git("commit", "-qm", "base records")
        base = git("rev-parse", "HEAD")

        for branch, added in (("category", "CategoryTheory.New"), ("algebra", "Algebra.New")):
            git("switch", "-qc", branch, base)
            records = gate.read_baseline(legacy, shards)
            changed = gate.write_baseline(
                sorted([*records, added]), MODULES, records, shards
            )
            self.assertEqual(changed, [shards / f"{gate.subject_of(MODULES[added])}.txt"])
            git("add", ".")
            git("commit", "-qm", f"add {added}")

        self.assertEqual(
            git("diff", "--name-only", "base", "category"),
            "single_instantiation_records/CategoryTheory.txt",
        )
        self.assertEqual(
            git("diff", "--name-only", "base", "algebra"),
            "single_instantiation_records/Algebra.txt",
        )
        git("merge", "--no-edit", "category")
        self.assertEqual(
            set(gate.read_baseline(legacy, shards)),
            {"CategoryTheory.Existing", "Algebra.Existing", "CategoryTheory.New", "Algebra.New"},
        )


if __name__ == "__main__":
    unittest.main()
