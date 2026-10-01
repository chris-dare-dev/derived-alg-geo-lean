#!/usr/bin/env python3
"""Prepare isolated reviewer calls and validate their same-commit verdicts.

This is a stateless helper, not a loop controller or review ledger. Codex
cannot be intercepted by repository hooks: submit the generated payload
unchanged, and audit actual dispatches from the archived transcript.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

from _output import force_utf8_output
from check_review_evidence import changed_files, corpus

ROLES = ("mathematics-adversary", "repository-boundary-adversary", "abstraction-adversary", "mathlib-reviewer")
ROLE = re.compile(r"^Role:\s*(" + "|".join(ROLES) + r")\.?\s*$", re.M)
TRAILER = re.compile(r"\nReviewed commit: ([0-9a-f]{40})\nClose: (PASS|PASS_WITH_LIFT|NEEDS_CHANGES|BLOCKED)\s*\Z")


def dispatch_errors(payload: dict, maximum_effort: str) -> list[str]:
    errors = []
    role = ROLE.search(str(payload.get("message", "")))
    if not role:
        errors.append("missing canonical Role header")
    elif not str(payload.get("task_name", "")).startswith("review_" + role[1].replace("-", "_") + "_"):
        errors.append("task name must start review_<role with underscores>_ so actual dispatches can be audited")
    if payload.get("fork_turns") != "none":
        errors.append("reviewers require fork_turns=none")
    if not isinstance(payload.get("model"), str) or not payload["model"].strip():
        errors.append("select an explicit frontier model from runtime capabilities")
    elif payload["model"].strip().lower() == "inherit":
        errors.append("model selection cannot be inherited")
    if maximum_effort not in ("max", "ultra") or payload.get("reasoning_effort") != maximum_effort:
        errors.append("reasoning effort must equal the runtime's highest offered effort (max or ultra)")
    return errors


def verdict_errors(text: str, commit: str, role: str) -> list[str]:
    match = TRAILER.search(text)
    if not match:
        return ["missing or malformed exact two-line trailer"]
    if match[1] != commit:
        return [f"SHA mismatch: reviewed {match[1]}, dispatched {commit}"]
    errors = []
    if role == "mathematics-adversary" and match[2] in ("PASS", "PASS_WITH_LIFT"):
        if not re.search(r"^\|.*\|\s*\n\|[-: |]+\|\s*\n\|.+\|", text, re.M):
            errors.append("mathematics PASS requires a central-claim table")
        if not re.search(r"[Pp]robe output.*?```[^\n]*\n\S", text, re.S):
            errors.append("mathematics PASS requires verbatim probe output (or explicit vacuity evidence)")
    return errors


def claim_table_errors(draft: str) -> list[str]:
    section = re.search(r"^## Claim evidence\s*\n(.*?)(?=^## |\Z)", draft, re.M | re.S)
    if not section:
        return ["PR draft needs '## Claim evidence'"]
    rows = [[c.strip() for c in line.strip().strip("|").split("|")]
            for line in section[1].splitlines() if line.strip().startswith("|")]
    columns = ["Claim", "Declaration", "Hypotheses", "Owner", "Pinned source", "Check"]
    if len(rows) < 3 or rows[0] != columns:
        return ["Claim evidence needs Claim | Declaration | Hypotheses | Owner | Pinned source | Check and at least one evidence row"]
    errors = []
    for row in rows[2:]:
        if len(row) != 6 or any(not cell or cell.lower() in ("tbd", "todo", "pending", "?") for cell in row):
            errors.append("incomplete claim evidence row")
    return errors


def hook_errors(data: dict) -> list[str]:
    tool = data.get("tool_input") or {}
    prompt = str(tool.get("prompt", tool.get("message", "")))
    if not ROLE.search(prompt) and tool.get("subagent_type") not in ROLES:
        return []  # scouts and ordinary implementation agents are not reviewers
    errors = []
    if tool.get("resume") or tool.get("fork_turns", "none") != "none":
        errors.append("reviewers must be fresh, never resumed or full-history forks")
    if not tool.get("model") or tool.get("model") == "inherit":
        errors.append("reviewers require an explicit frontier model selected by the harness")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    prepare = sub.add_parser("prepare")
    prepare.add_argument("--role", choices=ROLES, required=True)
    prepare.add_argument("--worktree", type=Path, required=True)
    prepare.add_argument("--issue", type=int, required=True)
    prepare.add_argument("--commit", required=True)
    prepare.add_argument("--base", required=True)
    prepare.add_argument("--draft", type=Path, required=True)
    prepare.add_argument("--checks", type=Path, required=True)
    prepare.add_argument("--model", required=True)
    prepare.add_argument("--capability", choices=("frontier",), required=True,
                         help="harness assertion from available runtime capabilities; not inferred from a model name")
    prepare.add_argument("--maximum-effort", choices=("max", "ultra"), required=True)
    prepare.add_argument("--effort", required=True)
    prepare.add_argument("--task-name", required=True)
    validate = sub.add_parser("validate")
    validate.add_argument("payload", type=Path)
    validate.add_argument("--maximum-effort", required=True)
    verdict = sub.add_parser("verdict")
    verdict.add_argument("report", type=Path)
    verdict.add_argument("--commit", required=True)
    verdict.add_argument("--role", choices=ROLES, required=True)
    sub.add_parser("hook")
    args = parser.parse_args(argv)
    try:
        if args.mode == "hook":
            errors = hook_errors(json.load(sys.stdin))
        elif args.mode == "verdict":
            errors = verdict_errors(args.report.read_text(encoding="utf-8"), args.commit, args.role)
        elif args.mode == "validate":
            errors = dispatch_errors(json.loads(args.payload.read_text()), args.maximum_effort)
        else:
            wt = args.worktree.resolve(strict=True)
            head = subprocess.check_output(["git", "-C", str(wt), "rev-parse", "HEAD"], text=True).strip()
            base = subprocess.check_output(["git", "-C", str(wt), "rev-parse", args.base], text=True).strip()
            draft = args.draft.resolve(strict=True)
            checks = args.checks.resolve(strict=True)
            errors = claim_table_errors(draft.read_text(encoding="utf-8"))
            if head != args.commit or not re.fullmatch(r"[0-9a-f]{40}", args.commit):
                errors.append("dispatch commit must be the full current worktree HEAD")
            if not re.fullmatch(r"[0-9a-f]{40}", base):
                errors.append("dispatch base must resolve to one commit")
            if subprocess.check_output(["git", "-C", str(wt), "diff", "HEAD", "--"], text=True):
                errors.append("commit tracked changes before dispatch")
            if not draft.is_relative_to(wt) or not checks.is_relative_to(wt):
                errors.append("draft and check output must belong to the reviewed worktree")
            check_text = checks.read_text(encoding="utf-8")
            if f"Reviewed source commit: {head}" not in check_text:
                errors.append("check output lacks this commit's evidence stamp")
            if f"Reviewed base: {base}" not in check_text or "Reference probe exit: 0" not in check_text:
                errors.append("check output needs this base and a successful reference probe exit")
            # Recompute from the reviewed worktree, including the untracked PR
            # draft: a matching HEAD alone does not bind prose to its check.
            subprocess.check_output(
                [sys.executable, str(Path(__file__).resolve().with_name("check_review_evidence.py")),
                 "inventory", "--base", base, "--draft", str(draft)], cwd=wt, text=True)
            # The inventory above also checks malformed/stale classifications.
            old_cwd = Path.cwd()
            try:
                os.chdir(wt)
                blocks = corpus(changed_files(base), base)
                blocks.append((str(draft), 1, draft.read_text(encoding="utf-8"), False))
                digest = hashlib.sha256(repr(blocks).encode()).hexdigest()
            finally:
                os.chdir(old_cwd)
            if f"Corpus SHA256: {digest}" not in check_text:
                errors.append("documentation or PR draft changed after the reference probe")
            if re.search(r"(?:GATE [^\n]+: FAIL|^.*error:|Reference probe exit: [1-9])", check_text, re.M):
                errors.append("provided check output contains a failure")
            brief = (
                f"Role: {args.role}.\nRead your instructions with git -C {shlex.quote(str(wt))} show origin/main:.claude/agents/{args.role}.md\n"
                "Follow your role and this brief, not the controller skill. End with the exact two-line trailer.\n"
                "Repository: chris-dare-dev/derived-alg-geo-lean (pass --repo to gh issue and gh pr).\n"
                f"Worktree: {wt}. Run every command there.\nIssue: #{args.issue}. Commit: {head}.\n"
                f"Base: {base}. Diff: git diff {base}...{head}\nPR description draft: {draft}\n"
                f"Local checks: {checks}\n"
                "Inspect the evidence yourself; do not infer that exit zero means a check ran.\n"
                "Report resolved model and reasoning effort if exposed; otherwise say unavailable.\n"
                "CI runs after the PR opens. Do not dispatch or wait for a workflow.\n"
            )
            payload = {"task_name": args.task_name, "message": brief, "fork_turns": "none",
                       "model": args.model, "reasoning_effort": args.effort}
            errors.extend(dispatch_errors(payload, args.maximum_effort))
            if not errors:
                print(json.dumps(payload, indent=2))
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        return (2 if args.mode == "hook" else 1) if errors else 0
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2 if args.mode == "hook" else 1


if __name__ == "__main__":
    force_utf8_output()
    raise SystemExit(main())
