"""Compiled Lean-header fixtures for the focused neutral Stability graph gate."""

from __future__ import annotations

from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import check_neutral_stability_imports as gate  # noqa: E402


N = gate.NEUTRAL
O = gate.OUTER
S = gate.GEOMETRIC_STABILITY
SL = S + ".Leaf"
B = gate.TRIANGULATED_STABILITY
BL = B + ".Leaf"
BRIDGE = N + ".Bridge"
EXTRA = N + ".StabilityExtra"


def source(*imports: str, body: str = "") -> str:
    return "module\n" + "".join(line + "\n" for line in imports) + body


class NeutralStabilityImportsTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="neutral-stability-headers-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.sources: dict[str, str] = {
            O: source(f"public import {N}", f"public import {S}"),
            N: source("public import Init"),
            S: source("public import Init"),
            SL: source("public import Init"),
            B: source("public import Init"),
            BL: source("public import Init"),
            BRIDGE: source("public import Init"),
            EXTRA: source("public import Init"),
        }

    def put(self, name: str, content: str) -> None:
        self.sources[name] = content

    def write_sources(self) -> list[Path]:
        paths = []
        for name, content in sorted(self.sources.items()):
            path = self.root / (name.replace(".", "/") + ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
            paths.append(path)
        return paths

    def compile_sources(self, paths: list[Path]) -> None:
        headers = gate.parse_headers(paths)
        names = {gate.module_name(path, self.root): path for path in paths}
        dependencies = {
            name: set(headers[path].all_imports & names.keys())
            for name, path in names.items()
        }
        env = os.environ.copy()
        previous = env.get("LEAN_PATH")
        env["LEAN_PATH"] = str(self.root) + (os.pathsep + previous if previous else "")
        for name in TopologicalSorter(dependencies).static_order():
            path = names[name]
            proc = subprocess.run(
                ["lean", "-R", str(self.root), "-o", str(path.with_suffix(".olean")), str(path)],
                cwd=gate.ROOT,
                env=env,
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
            self.assertEqual(proc.returncode, 0, f"{name}: {proc.stderr}{proc.stdout}")

    def check(self, *, compiles: bool = True) -> list[str]:
        paths = self.write_sources()
        if compiles:
            self.compile_sources(paths)
        count, failures = gate.check_neutrality(self.root, paths)
        self.assertEqual(count, len(paths))
        return failures

    def test_valid_route_and_distinct_stability_extra_compile(self) -> None:
        self.put(N, source(f"public import {EXTRA}"))
        self.assertEqual(self.check(), [])

    def test_exact_descendant_indirect_private_and_meta_forbidden_edges_compile(self) -> None:
        cases = (
            ("exact", source(f"public import {S}"), S),
            ("descendant", source(f"public import {SL}"), SL),
            ("private", source(f"import {SL}"), SL),
            ("meta", source(f"meta import {SL}"), SL),
            ("indirect", source(f"public import {BRIDGE}"), SL),
            ("abstract exact", source(f"public import {B}"), B),
            ("abstract descendant", source(f"public import {BL}"), BL),
        )
        for label, neutral_source, forbidden in cases:
            with self.subTest(case=label):
                self.put(N, neutral_source)
                self.put(BRIDGE, source(f"import {SL}"))
                failures = self.check()
                self.assertTrue(any("forbidden neutral import path" in f and forbidden in f
                                    for f in failures), failures)
                self.sources[N] = source("public import Init")

    def test_indirect_abstract_meta_edge_compiles(self) -> None:
        self.put(N, source(f"import {BRIDGE}"))
        self.put(BRIDGE, source(f"meta import {BL}"))
        failures = self.check()
        self.assertTrue(any(f"{N} -> {BRIDGE} -> {BL}" in f for f in failures), failures)

    def test_doc_and_nested_raw_interpolation_are_not_edges(self) -> None:
        self.put(N, source(
            "public import Init",
            body=(
                "/-! import " + SL + "\nclass Fake\n-/\n"
                "public def quoted : Char := '\"'\n"
                "-- π is documentation, not an import modifier\n"
                "#eval s!\"{r#\"before\nimport " + SL +
                "\nclass Fake\nafter\"#}\"\n"
            ),
        ))
        self.assertEqual(self.check(), [])

    def test_outer_missing_private_descendant_and_meta_export_fail(self) -> None:
        cases = (
            ("missing", source(f"public import {N}")),
            ("private", source(f"public import {N}", f"import {S}")),
            ("descendant", source(f"public import {N}", f"public import {SL}")),
            ("meta", source(f"public import {N}", f"public meta import {S}")),
        )
        for label, outer_source in cases:
            with self.subTest(case=label):
                self.put(O, outer_source)
                failures = self.check()
                self.assertTrue(any("must directly publicly import non-meta" in f
                                    for f in failures), failures)

    def test_unknown_internal_import_fails_closed(self) -> None:
        # Even an unrelated tracked header must not silently leave a graph hole.
        self.put(EXTRA, source(f"import {N}.Missing"))
        with self.assertRaisesRegex(gate.GateError, "unknown internal import"):
            self.check(compiles=False)

    def test_cycle_fails_closed(self) -> None:
        # A disconnected cycle still makes the complete import graph invalid.
        self.put(BRIDGE, source(f"import {EXTRA}"))
        self.put(EXTRA, source(f"import {BRIDGE}"))
        with self.assertRaisesRegex(gate.GateError, "internal import cycle"):
            self.check(compiles=False)

    def test_malformed_header_reports_lean_error(self) -> None:
        self.put(EXTRA, "module\nimport )\n")
        paths = self.write_sources()
        path = next(path for path in paths if gate.module_name(path, self.root) == EXTRA)
        bad_compile = subprocess.run(
            ["lean", str(path)], cwd=gate.ROOT, capture_output=True, text=True, check=False
        )
        self.assertNotEqual(bad_compile.returncode, 0)
        with self.assertRaisesRegex(gate.GateError, "Lean header errors"):
            gate.check_neutrality(self.root, paths)

    def test_missing_result_and_malformed_flags_fail_closed(self) -> None:
        path = self.write_sources()[0]
        valid = {"module": "Init", "isExported": True, "isMeta": False,
                 "importAll": False}
        entries = (
            [],
            [{"errors": [], "result": {"isModule": True, "imports": [{**valid,
                "isMeta": "false"}]}}],
            [{"errors": [], "result": {"isModule": True, "imports": [{k: v for k, v
                in valid.items() if k != "isExported"}]}}],
            [{"errors": [], "result": {"isModule": True, "imports": [{**valid,
                "importAll": 0}]}}],
            [{"errors": [], "result": {"isModule": "true", "imports": [valid]}}],
        )
        for imports in entries:
            with self.subTest(result=imports):
                fake = subprocess.CompletedProcess(
                    args=[], returncode=0, stdout=json.dumps({"imports": imports}), stderr=""
                )
                with mock.patch.object(gate.subprocess, "run", return_value=fake):
                    with self.assertRaises(gate.GateError):
                        gate.parse_headers([path])

    def test_invalid_json_missing_errors_and_process_failure_fail_closed(self) -> None:
        path = self.write_sources()[0]
        cases = (
            ("not json", 0, ""),
            (json.dumps({"imports": [{"result": {"isModule": True, "imports": []}}]}),
             0, ""),
            (json.dumps({"imports": []}), 1, "Lean failed"),
        )
        for stdout, code, stderr in cases:
            with self.subTest(stdout=stdout):
                fake = subprocess.CompletedProcess(
                    args=[], returncode=code, stdout=stdout, stderr=stderr
                )
                with mock.patch.object(gate.subprocess, "run", return_value=fake):
                    with self.assertRaises(gate.GateError):
                        gate.parse_headers([path])


if __name__ == "__main__":
    unittest.main()
