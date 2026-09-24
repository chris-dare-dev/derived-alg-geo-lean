"""Pinned-Lean header parsing and fail-closed umbrella ownership regressions."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import check_umbrella_coverage as gate  # noqa: E402


FIXTURES = pathlib.Path(__file__).parent / "fixtures" / "umbrella_headers"
PARENT = "DerivedAlgGeo.Fixture"
LEAF = f"{PARENT}.Leaf"


class UmbrellaCoverageTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="umbrella-headers-")
        self.addCleanup(temporary.cleanup)
        self.root = pathlib.Path(temporary.name)
        self.source = self.root / "DerivedAlgGeo"
        self.child_dir = self.source / "Fixture"
        self.child_dir.mkdir(parents=True)
        self.umbrella = self.source / "Fixture.lean"
        self.leaf = self.child_dir / "Leaf.lean"
        self.leaf.write_text("import Init\ndef leafValue : Nat := 7\n", encoding="utf-8")

    def put_fixture(self, name: str) -> str:
        source = (FIXTURES / name).read_text(encoding="utf-8")
        self.umbrella.write_text(source, encoding="utf-8")
        return source

    def compile_source(self, source: str, *, succeeds: bool = True) -> None:
        proc = subprocess.run(
            ["lean", "--stdin"],
            input=source,
            capture_output=True,
            text=True,
            cwd=gate.ROOT,
            check=False,
        )
        if succeeds:
            self.assertEqual(proc.returncode, 0, proc.stderr + proc.stdout)
        else:
            self.assertNotEqual(proc.returncode, 0)

    def compile_importing_fixture(self, name: str) -> None:
        self.put_fixture(name)
        if name in ("ModulePrivateHeader.lean", "ModulePublicHeader.lean"):
            # Pinned Lean forbids importing a non-`module` source from `module`.
            self.leaf.write_text(
                "module\npublic import Init\npublic def leafValue : Nat := 7\n",
                encoding="utf-8",
            )
        env = os.environ.copy()
        previous = env.get("LEAN_PATH")
        env["LEAN_PATH"] = str(self.root) + (os.pathsep + previous if previous else "")
        child = subprocess.run(
            ["lean", "-R", str(self.root), "-o", str(self.leaf.with_suffix(".olean")), str(self.leaf)],
            capture_output=True,
            text=True,
            cwd=gate.ROOT,
            env=env,
            check=False,
        )
        self.assertEqual(child.returncode, 0, child.stderr + child.stdout)
        parent = subprocess.run(
            ["lean", "-R", str(self.root), str(self.umbrella)],
            capture_output=True,
            text=True,
            cwd=gate.ROOT,
            env=env,
            check=False,
        )
        self.assertEqual(parent.returncode, 0, parent.stderr + parent.stdout)

    def check(self, *, owners=None, boundaries=None) -> tuple[int, list[str]]:
        return gate.check_coverage(
            self.root,
            owners={} if owners is None else owners,
            child_boundaries={} if boundaries is None else boundaries,
            export_route=None,  # These one-directory fixtures do not model geometry.
        )

    def test_compiled_fake_imports_never_cover_leaf(self) -> None:
        for name in (
            "DocText.lean",
            "Comments.lean",
            "RawHashes.lean",
            "CharLiteral.lean",
            "NestedInterpolation.lean",
            "Unicode.lean",
        ):
            with self.subTest(fixture=name):
                source = self.put_fixture(name)
                self.compile_source(source)
                imports = gate.lean_header_imports([self.umbrella])[self.umbrella].exported
                self.assertNotIn(LEAF, imports)
                checked, failures = self.check()
                self.assertEqual(checked, 1)
                self.assertEqual(len(failures), 1)
                self.assertIn("does not re-export", failures[0])

    def test_compiled_real_header_import_covers_leaf(self) -> None:
        self.compile_importing_fixture("RealHeader.lean")
        imports = gate.lean_header_imports([self.umbrella])[self.umbrella].exported
        self.assertIn(LEAF, imports)
        self.assertEqual(self.check(), (1, []))

    def test_module_header_requires_public_import_for_reexport(self) -> None:
        for fixture, exported in (
            ("ModulePrivateHeader.lean", False),
            ("ModulePublicHeader.lean", True),
        ):
            with self.subTest(fixture=fixture):
                self.compile_importing_fixture(fixture)
                imports = gate.lean_header_imports([self.umbrella])[self.umbrella].exported
                self.assertEqual(LEAF in imports, exported)
                checked, failures = self.check()
                self.assertEqual(checked, 1)
                if exported:
                    self.assertEqual(failures, [])
                else:
                    self.assertEqual(len(failures), 1)
                    self.assertIn("does not re-export", failures[0])

    def test_multiple_headers_are_parsed_in_one_ordered_batch(self) -> None:
        self.put_fixture("RealHeader.lean")
        parsed = gate.lean_header_imports([self.leaf, self.umbrella])
        self.assertNotIn(LEAF, parsed[self.leaf].exported)
        self.assertIn(LEAF, parsed[self.umbrella].exported)

    def test_malformed_header_is_fatal_even_when_lean_returns_json(self) -> None:
        source = self.put_fixture("MalformedHeader.lean")
        self.compile_source(source, succeeds=False)
        with self.assertRaisesRegex(gate.CoverageError, "Lean header errors"):
            self.check()

    def test_reviewed_owner_witness_and_changed_digest(self) -> None:
        source = self.put_fixture("OwnerModule.lean")
        self.compile_source(source)
        witness = gate.OwnerWitness(
            3, "def fixtureOwner : Nat := 1", hashlib.sha256(source.encode()).hexdigest()
        )
        self.assertEqual(self.check(owners={PARENT: witness}), (0, []))
        changed = source.replace("def fixtureOwner : Nat := 1", "-- def fixtureOwner : Nat := 1")
        self.umbrella.write_text(changed, encoding="utf-8")
        self.compile_source(changed)
        _, failures = self.check(owners={PARENT: witness})
        self.assertTrue(any("witness line changed" in failure for failure in failures))
        self.assertTrue(any("digest changed" in failure for failure in failures))

    def test_invalid_owner_exception_is_rejected(self) -> None:
        self.put_fixture("DocText.lean")
        witness = gate.OwnerWitness(4, "class Fake", "0" * 64)
        _, failures = self.check(owners={PARENT: witness})
        self.assertTrue(any("digest changed" in failure for failure in failures))
        _, failures = self.check(owners={f"{PARENT}.Wrong": witness})
        self.assertTrue(any("stale declaration-owner exception" in failure for failure in failures))
        self.assertTrue(any("does not re-export" in failure for failure in failures))

    def test_child_exception_is_exact_and_validated(self) -> None:
        self.put_fixture("DocText.lean")
        self.assertEqual(self.check(boundaries={PARENT: {LEAF}}), (1, []))
        _, failures = self.check(boundaries={PARENT: {f"{PARENT}.Wrong"}})
        self.assertTrue(any("stale umbrella/child exception" in failure for failure in failures))
        self.assertTrue(any("does not re-export" in failure for failure in failures))
        _, failures = self.check(boundaries={f"{PARENT}.Wrong": {LEAF}})
        self.assertTrue(any("stale umbrella/child exception" in failure for failure in failures))

    def test_json_count_error_and_result_shape_are_fatal(self) -> None:
        self.put_fixture("DocText.lean")
        bad_payloads = (
            {"imports": []},
            {"imports": [{"errors": []}]},
            {"imports": [{"result": {"imports": [], "isModule": False}}]},
            {"imports": [{"errors": [], "result": {"imports": ["bad"], "isModule": False}}]},
        )
        for payload in bad_payloads:
            with self.subTest(payload=payload):
                fake = subprocess.CompletedProcess([], 0, json.dumps(payload), "")
                with mock.patch.object(gate.subprocess, "run", return_value=fake):
                    with self.assertRaises(gate.CoverageError):
                        self.check()

    def test_missing_or_malformed_export_flag_is_fatal(self) -> None:
        self.put_fixture("RealHeader.lean")
        for record in (
            {"module": LEAF},
            {"module": LEAF, "isExported": None},
            {"module": LEAF, "isExported": "true"},
            {"module": LEAF, "isExported": 1},
        ):
            with self.subTest(record=record):
                payload = {
                    "imports": [{
                        "errors": [],
                        "result": {"imports": [record], "isModule": True},
                    }],
                }
                fake = subprocess.CompletedProcess([], 0, json.dumps(payload), "")
                with mock.patch.object(gate.subprocess, "run", return_value=fake):
                    with self.assertRaisesRegex(gate.CoverageError, "malformed Lean header import"):
                        self.check()

    def test_parser_process_failure_is_fatal(self) -> None:
        self.put_fixture("DocText.lean")
        fake = subprocess.CompletedProcess([], 1, "", "failed")
        with mock.patch.object(gate.subprocess, "run", return_value=fake):
            with self.assertRaisesRegex(gate.CoverageError, "exited 1"):
                self.check()

    def test_empty_candidate_set_is_not_a_green_gate(self) -> None:
        self.umbrella.write_text("import Init\n", encoding="utf-8")
        self.umbrella.unlink()
        with self.assertRaisesRegex(gate.CoverageError, "no same-named"):
            self.check()


class StabilityExportRouteTest(unittest.TestCase):
    """The one omitted child has a forbidden neutral edge and a required outer edge."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="umbrella-stability-route-")
        self.addCleanup(temporary.cleanup)
        self.root = pathlib.Path(temporary.name)
        self.neutral_name, self.child_name, self.outer_name = gate.STABILITY_EXPORT_ROUTE
        geometry = self.root / "DerivedAlgGeo" / "AlgebraicGeometry"
        derived = geometry / "DerivedCategory"
        derived.mkdir(parents=True)
        self.outer = self.root / "DerivedAlgGeo" / "AlgebraicGeometry.lean"
        self.neutral = geometry / "DerivedCategory.lean"
        self.child = derived / "Stability.lean"
        self.outer.write_text(
            f"import {self.neutral_name}\nimport {self.child_name}\n", encoding="utf-8"
        )
        self.neutral.write_text("import Init\n", encoding="utf-8")
        self.child.write_text("module\npublic import Init\n", encoding="utf-8")

    def assert_tree_compiles(self) -> None:
        env = os.environ.copy()
        previous = env.get("LEAN_PATH")
        env["LEAN_PATH"] = str(self.root) + (os.pathsep + previous if previous else "")
        for path in (self.child, self.neutral, self.outer):
            proc = subprocess.run(
                ["lean", "-R", str(self.root), "-o", str(path.with_suffix(".olean")), str(path)],
                capture_output=True,
                text=True,
                cwd=gate.ROOT,
                env=env,
                check=False,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr + proc.stdout)

    def check_route(self, *, boundaries=None) -> tuple[int, list[str]]:
        return gate.check_coverage(
            self.root,
            owners={},
            child_boundaries=(
                {self.neutral_name: {self.child_name}} if boundaries is None else boundaries
            ),
        )

    def test_current_valid_header_route(self) -> None:
        self.assert_tree_compiles()
        parsed = gate.lean_header_imports([self.neutral, self.outer])
        self.assertNotIn(self.child_name, parsed[self.neutral].all)
        self.assertIn(self.child_name, parsed[self.outer].exported)
        self.assertEqual(self.check_route(), (2, []))

    def test_neutral_umbrella_must_not_import_child_even_privately(self) -> None:
        for source in (
            f"import {self.child_name}\n",
            f"module\nimport {self.child_name}\n",
        ):
            with self.subTest(source=source):
                self.neutral.write_text(source, encoding="utf-8")
                self.assert_tree_compiles()
                parsed = gate.lean_header_imports([self.neutral])[self.neutral]
                self.assertIn(self.child_name, parsed.all)
                _, failures = self.check_route()
                self.assertTrue(any("must not import omitted child" in f for f in failures))

    def test_outer_umbrella_must_publicly_import_child(self) -> None:
        for source in (
            f"import {self.neutral_name}\n",
            f"module\npublic import {self.neutral_name}\nimport {self.child_name}\n",
        ):
            with self.subTest(source=source):
                self.outer.write_text(source, encoding="utf-8")
                if source.startswith("module"):
                    self.neutral.write_text("module\npublic import Init\n", encoding="utf-8")
                self.assert_tree_compiles()
                parsed = gate.lean_header_imports([self.outer])[self.outer]
                self.assertNotIn(self.child_name, parsed.exported)
                _, failures = self.check_route()
                self.assertTrue(any("must publicly re-export omitted child" in f for f in failures))

    def test_child_exception_cannot_lose_its_export_route(self) -> None:
        _, failures = self.check_route(boundaries={})
        self.assertTrue(any("boundary must remain exact" in f for f in failures))

    def test_child_exception_cannot_gain_an_unreviewed_child(self) -> None:
        other = self.neutral.parent / "DerivedCategory" / "Other.lean"
        other.write_text("import Init\n", encoding="utf-8")
        _, failures = self.check_route(
            boundaries={self.neutral_name: {self.child_name, f"{self.neutral_name}.Other"}}
        )
        self.assertTrue(any("boundary must remain exact" in f for f in failures))


if __name__ == "__main__":
    unittest.main()
