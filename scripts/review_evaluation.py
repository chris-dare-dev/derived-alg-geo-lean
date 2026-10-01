#!/usr/bin/env python3
"""Replay synthetic review mistakes and score independently adjudicated reports.

No archived transcript is committed. The fixtures reconstruct failure classes.
Scoring uses explicit adjudications, not keyword matching against agent prose;
an evidence score reflects the adjudicator's check, not merely a cited filename.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from _output import force_utf8_output

FIXTURE = Path(__file__).parent / "fixtures/review-evaluation.json"


def score(cases: list[dict], assessments: list[dict]) -> dict:
    by_id = {case["id"]: case for case in cases}
    seen = set()
    expected_total = matched = findings_total = unsupported = evidence = severity_errors = recurrent = 0
    for assessment in assessments:
        case = by_id[assessment["case"]]
        if case["id"] in seen:
            raise ValueError("one assessment per case; score distinct review runs separately")
        seen.add(case["id"])
        expected = case["expected"]
        found = set()
        expected_total += len(expected)
        family = case.get("family", case["id"])
        for finding in assessment["findings"]:
            fid = finding["id"]
            if fid in found:
                raise ValueError("duplicate finding id within a case")
            found.add(fid)
            if not isinstance(finding.get("evidence_supported"), bool) or not finding.get("adjudication", "").strip():
                raise ValueError("every finding needs an evidence_supported boolean and an adjudication reason")
            if finding.get("severity") not in ("blocker", "should-fix", "nit"):
                raise ValueError("invalid severity")
            findings_total += 1
            if fid in expected:
                matched += 1
                severity_errors += finding["severity"] != expected[fid]
            else:
                unsupported += 1
            evidence += finding["evidence_supported"] and bool(finding.get("evidence", "").strip())
            if case.get("after_repair") and fid in by_id[family]["expected"]:
                recurrent += 1
    return {"cases_assessed": len(seen), "cases_unassessed": sorted(set(by_id) - seen),
            "expected_defects": expected_total, "detected_defects": matched,
            "missed_defects": expected_total - matched, "findings": findings_total,
            "unsupported_findings": unsupported, "severity_errors": severity_errors,
            "recurrence_after_repair": recurrent,
            "precision": (findings_total - unsupported) / findings_total if findings_total else None,
            "recall": matched / expected_total if expected_total else None,
            "supported_evidence_rate": evidence / findings_total if findings_total else None}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    prompt = sub.add_parser("prompt", help="give the reviewer the case without expected answers")
    prompt.add_argument("case")
    prompt.add_argument("--worktree", type=Path, required=True)
    grading = sub.add_parser("score", help="score a local JSON list of independent adjudications")
    grading.add_argument("assessments", type=Path)
    args = parser.parse_args(argv)
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if args.mode == "score":
        print(json.dumps(score(fixture["cases"], json.loads(args.assessments.read_text())), indent=2))
    else:
        case = next(c for c in fixture["cases"] if c["id"] == args.case)
        wt = args.worktree.resolve(strict=True)
        manifest = json.loads((wt / "lake-manifest.json").read_text())
        pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
        if pin != fixture["pin"]:
            print(f"case unavailable: expected Mathlib {fixture['pin']}, found {pin}", file=sys.stderr)
            return 1
        for source in case["sources"]:
            path = wt / ".lake/packages/mathlib" / source if source.startswith("Mathlib/") else wt / source
            if not path.is_file():
                print(f"case unavailable: missing source {path}", file=sys.stderr)
                return 1
            expected = case.get("source_sha256", {}).get(source)
            if not expected:
                print(f"case unavailable: missing source fingerprint: {source}", file=sys.stderr)
                return 1
            if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                print(f"case unavailable: source changed: {path}; re-adjudicate the case before refreshing its fingerprint", file=sys.stderr)
                return 1
        print(f"Role: {case['role']}.\nEvaluation case: {case['id']}\nWorktree: {args.worktree.resolve()}\n"
              f"Read .claude/agents/{case['role']}.md in this worktree.\n"
              f"Check this claim against the pinned sources; use your role's severity rules.\n\n{case['claim']}\n\n"
              f"Expected Mathlib pin: {fixture['pin']}. If it differs, report the case as unavailable.\n"
              "Sources (content fingerprints verified):\n" + "\n".join(case["sources"]) +
              "\nDo not read the evaluation fixture or its expected answers. Report findings and evidence; do not edit files.")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    raise SystemExit(main())
