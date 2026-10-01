from __future__ import annotations

import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_emission_coverage as emission
import check_mathlib_style as style
import check_review_evidence as evidence
import review_dispatch as dispatch
import review_evaluation as evaluation

SHA = "a" * 40
COMPLETE = "# Test\n\nA useful summary.\n\n" + "\n\n".join(
    f"## {section}\n\nDocumented content." for section in evidence.SECTIONS
)


class DocumentationTests(unittest.TestCase):
    def test_changed_module_sections_are_complete_not_selected(self):
        entries = [("Leaf.lean", 1, COMPLETE, True), ("Companion.lean", 2, "# Short\nSummary", True)]
        errors = evidence.doc_errors(entries)
        self.assertEqual(len(errors), 5)
        self.assertTrue(all("Companion.lean" in e for e in errors))

    def test_inventory_preserves_repeated_and_draft_occurrences(self):
        entries = [("Leaf.lean", 10, "`CoversTop` and `CoversTop`", True),
                   ("scratch/pr.md", 1, "`CoversTop`\n```lean\n#check NotAProseReference\n```\n`PrimeSpectrum`", False)]
        refs = evidence.references(entries)
        self.assertEqual(len(refs["CoversTop"]), 3)
        self.assertNotIn("NotAProseReference", refs)
        self.assertEqual(evidence.kind_of("CoversTop", {}), "declaration")
        self.assertEqual(evidence.kind_of("M.fromTildeΓ", {"M.fromTildeΓ": "parameter"}), "parameter")
        self.assertEqual(evidence.kind_of("M → N", {}), "unclassified")
        self.assertEqual(evidence.kind_of("AGENTS.md", {}), "path")
        self.assertEqual(evidence.kind_of("A/B", {}), "unclassified")
        self.assertNotIn("UnusedName", evidence.references([("draft", 1,
                         "## Reference classifications\n| `UnusedName` | historical | old |\n", False)]))

    def test_docs_skip_strings_nested_comments_and_raw_literals(self):
        text = 'def x := " /-! fake -/ "\n/- ordinary /-! fake -/ -/\n'
        text += 'def y := r##" /-! fake -/ "##\n/-!\n# Real\n-/\n/-- Real declaration. -/'
        extracted = evidence.docs(text)
        self.assertEqual(len(extracted), 2)
        self.assertIn("# Real", extracted[0][1])
        with self.assertRaises(ValueError):
            evidence.docs("/-! unterminated")

    def test_fenced_examples_cannot_supply_references_or_required_sections(self):
        body = "`Real`\n  ````lean\n`Example`\n```\n`StillExample`\n  `````\n`After`\n~~~\n`OpenExample`"
        self.assertEqual(evidence.references([("sample", 1, body, False)]),
                         {"Real": ["sample:1"], "After": ["sample:7"]})
        self.assertTrue(evidence.doc_errors([("sample", 1, "```markdown\n" + COMPLETE + "\n```", True)]))
        self.assertEqual(evidence.classifications("```\n## Reference classifications\n| X | code | example |\n```"), {})

    def test_quote_character_cannot_hide_later_declaration_docstrings(self):
        sample = "/-! # Primary -/\ndef quote : Char := '\"'\n/-- Check `StaleName`. -/\n"
        extracted = evidence.docs(sample)
        self.assertEqual(len(extracted), 2)
        self.assertIn("StaleName", evidence.references([("sample", line, body, module)
                                                      for line, body, module in extracted]))

    def test_classifications_need_a_reason_and_cannot_conflict(self):
        draft = "## Reference classifications\n| `M.fromTildeΓ` | parameter | M is a local binder |\n"
        self.assertEqual(evidence.classifications(draft), {"M.fromTildeΓ": "parameter"})
        with self.assertRaises(ValueError):
            evidence.classifications(draft + "| `M.fromTildeΓ` | historical | old |\n")

    def test_notation_is_conditional_and_sections_have_order(self):
        reversed_sections = COMPLETE.replace("## Main definitions", "## Temporary").replace(
            "## Main results", "## Main definitions").replace("## Temporary", "## Main results")
        self.assertTrue(any("order" in e for e in evidence.doc_errors([("sample", 1, reversed_sections, True)])))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Notation.lean"
            path.write_text('scoped notation "foo" => 1\n')
            self.assertTrue(any("Notation" in e for e in evidence.doc_errors([(str(path), 1, COMPLETE, True)])))
            documented = COMPLETE.replace("## Implementation notes", "## Notation\n\nThe foo notation.\n\n## Implementation notes")
            self.assertEqual(evidence.doc_errors([(str(path), 1, documented, True)]), [])

    def test_style_cli_cannot_pass_without_checking_files(self):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(style.main([]), 1)
            self.assertEqual(style.main(["missing.lean"]), 1)
            self.assertEqual(style.main([__file__]), 1)


class GitCorpusTests(unittest.TestCase):
    def test_staged_new_files_and_unchanged_documentation(self):
        with tempfile.TemporaryDirectory() as directory:
            old_cwd = Path.cwd()
            try:
                os.chdir(directory)
                def git(*args):
                    return subprocess.check_output(["git", *args], text=True, stderr=subprocess.DEVNULL).strip()
                git("init")
                git("config", "user.email", "test@example.invalid")
                git("config", "user.name", "Test")
                Path("DerivedAlgGeo").mkdir()
                old = Path("DerivedAlgGeo/Old.lean")
                old.write_text("/-! # Existing incomplete doc -/\n/-- Existing declaration notes. -/\ndef x := 1\n")
                git("add", ".")
                git("commit", "-m", "base")
                base = git("rev-parse", "HEAD")
                old.write_text(old.read_text().replace("x := 1", "x := 2"))
                new = Path("DerivedAlgGeo/New.lean")
                new.write_text("#check PrimeSpectrum\n")
                git("add", str(new))
                self.assertTrue(any("missing primary" in e for e in
                                    evidence.doc_errors(evidence.corpus(evidence.changed_files(base), base))))
                new.write_text("/-!\n" + COMPLETE + "\n-/\n#check PrimeSpectrum\n")
                git("add", str(new))
                corpus = evidence.corpus(evidence.changed_files(base), base)
                self.assertEqual([e[0] for e in corpus], [str(new)])
                self.assertEqual(evidence.doc_errors(corpus), [])
                new.write_text(new.read_text() + "\n/-! ## An explanatory section\nSee `PrimeSpectrum`. -/\n")
                corpus = evidence.corpus(evidence.changed_files(base), base)
                self.assertEqual(evidence.doc_errors(corpus), [])
                self.assertFalse(corpus[-1][3])
                old.write_text(old.read_text() + "\n/-- Existing declaration notes. -/\ndef y := 2\n")
                corpus = evidence.corpus(evidence.changed_files(base), base)
                added = [entry for entry in corpus if entry[0] == str(old)]
                self.assertEqual(len(added), 1)
                self.assertFalse(added[0][3])
                self.assertIn("Existing declaration notes", added[0][2])
                draft = Path("draft.md")
                draft.write_text("Check `PrimeSpectrum`.\n")
                output = Path("scratch/Checks.lean")
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(evidence.main(["probe", "--base", base, "--draft", str(draft),
                                                   "--output", str(output)]), 0)
                self.assertIn("#check @PrimeSpectrum", output.read_text())
                git("add", str(old), str(new))
                git("commit", "-m", "reviewed change")
                head = git("rev-parse", "HEAD")
                draft.write_text("## Claim evidence\n| Claim | Declaration | Hypotheses | Owner | Pinned source | Check |\n"
                                 "| --- | --- | --- | --- | --- | --- |\n| C | D | H | O | SHA/path | compiled |\n")
                captured = io.StringIO()
                actual_run = subprocess.run
                def fake_lean(command, **kwargs):
                    if command[0].endswith("/lake"):
                        return subprocess.CompletedProcess(command, 0)
                    return actual_run(command, **kwargs)
                with patch.object(subprocess, "run", side_effect=fake_lean), contextlib.redirect_stdout(captured):
                    self.assertEqual(evidence.main(["probe", "--base", base, "--draft", str(draft),
                                                   "--output", str(output), "--run"]), 0)
                checks = Path("scratch/checks.txt")
                checks.write_text(captured.getvalue())
                args = ["prepare", "--role", "mathematics-adversary", "--worktree", directory,
                        "--issue", "1", "--commit", head, "--base", base, "--draft", str(draft),
                        "--checks", str(checks), "--model", "runtime-frontier", "--capability", "frontier",
                        "--maximum-effort", "ultra", "--effort", "ultra", "--task-name", "review_mathematics_adversary_r1"]
                prepared = io.StringIO()
                with contextlib.redirect_stdout(prepared):
                    self.assertEqual(dispatch.main(args), 0)
                self.assertEqual(json.loads(prepared.getvalue())["fork_turns"], "none")
                draft.write_text(draft.read_text() + "The prose changed after checking.\n")
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(dispatch.main(args), 1)
                git("add", str(output))
                with contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(evidence.main(["probe", "--base", base, "--draft", str(draft),
                                                   "--output", str(output)]), 1)
            finally:
                os.chdir(old_cwd)


class EmissionSourceTests(unittest.TestCase):
    def test_scratch_remains_ineligible_even_when_imported(self):
        tracked = {"DerivedAlgGeoSweep": "DerivedAlgGeoSweep.lean", "scratch.Checks": "scratch/Checks.lean"}
        graph = {"DerivedAlgGeoSweep": {"scratch.Checks"}}
        failures = emission.source_errors(tracked, graph, "DerivedAlgGeoSweep", ["DerivedAlgGeoSweep", "DerivedAlgGeo"])
        self.assertEqual(len(failures), 1)
        self.assertIn("outside emitter roots", failures[0])

    def test_orphan_and_development_are_distinguished(self):
        tracked = {"DerivedAlgGeo.Development.Probe": "DerivedAlgGeo/Development/Probe.lean"}
        filters = ["DerivedAlgGeoSweep", "DerivedAlgGeo"]
        self.assertIn("not imported", emission.source_errors(tracked, {}, "DerivedAlgGeoSweep", filters)[0])
        graph = {"DerivedAlgGeoSweep": {"DerivedAlgGeo.Development.Probe"}}
        self.assertEqual(emission.source_errors(tracked, graph, "DerivedAlgGeoSweep", filters), [])
        self.assertTrue(emission.source_errors({"DerivedAlgGeoOther": "Other.lean"}, {}, "DerivedAlgGeoOther", ["DerivedAlgGeo"]))


class DispatchTests(unittest.TestCase):
    def test_dispatch_cannot_inherit_context_model_or_lower_effort(self):
        good = {"message": "Role: mathematics-adversary.", "task_name": "review_mathematics_adversary_r1", "fork_turns": "none", "model": "runtime-frontier", "reasoning_effort": "ultra"}
        self.assertEqual(dispatch.dispatch_errors(good, "ultra"), [])
        for field, value in [("fork_turns", "all"), ("model", ""), ("reasoning_effort", "high")]:
            self.assertTrue(dispatch.dispatch_errors({**good, field: value}, "ultra"))
        self.assertTrue(dispatch.hook_errors({"tool_input": {"prompt": good["message"], "model": "inherit"}}))
        self.assertEqual(dispatch.hook_errors({"tool_input": {"prompt": "Research a lemma."}}), [])

    def test_verdict_requires_exact_head_and_mathematics_evidence(self):
        trailer = f"\nReviewed commit: {SHA}\nClose: PASS"
        self.assertTrue(dispatch.verdict_errors("No findings." + trailer, SHA, "mathematics-adversary"))
        report = "| Claim | Source |\n| --- | --- |\n| Claim | Proof |\nProbe output:\n```text\nexit 0\n```\n" + trailer
        self.assertEqual(dispatch.verdict_errors(report, SHA, "mathematics-adversary"), [])
        self.assertTrue(dispatch.verdict_errors(report, "b" * 40, "mathematics-adversary"))
        self.assertTrue(dispatch.verdict_errors(report + "\nextra", SHA, "mathematics-adversary"))

    def test_claim_matrix_cannot_be_empty_or_pending(self):
        table = "## Claim evidence\n| Claim | Declaration | Hypotheses | Owner | Pinned source | Check |\n| --- | --- | --- | --- | --- | --- |\n"
        self.assertTrue(dispatch.claim_table_errors(table))
        self.assertTrue(dispatch.claim_table_errors(table + "| C | D | H | O | pending | check |\n"))
        self.assertEqual(dispatch.claim_table_errors(table + "| C | D | H | O | SHA/path | compiled |\n"), [])


class EvaluationTests(unittest.TestCase):
    def test_misses_unsupported_severity_and_repaired_controls(self):
        cases = json.loads(evaluation.FIXTURE.read_text())["cases"]
        finding = {"id": "direction", "severity": "nit", "evidence": "criterion .mpr", "evidence_supported": True, "adjudication": "direction is reversed"}
        assessments = [{"case": "iff-direction", "findings": [finding]},
                       {"case": "repaired-direction", "findings": [{**finding, "evidence_supported": False}]},
                       {"case": "definition-owner", "findings": []}]
        result = evaluation.score(cases, assessments)
        self.assertEqual(result["missed_defects"], 2)
        self.assertEqual(result["unsupported_findings"], 1)
        self.assertEqual(result["severity_errors"], 1)
        self.assertEqual(result["recurrence_after_repair"], 1)
        self.assertEqual(result["precision"], 0.5)
        self.assertEqual(evaluation.score(cases, [assessments[2]])["precision"], None)
        with self.assertRaises(ValueError):
            evaluation.score(cases, [assessments[0], assessments[0]])


if __name__ == "__main__":
    unittest.main()
