"""Regression tests for recovery's cumulative, evidence-preserving boundaries."""
from __future__ import annotations

import copy
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest import mock

import yaml

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))
import loop_recovery as recovery
import loop_engine
try:
    from scripts.tests.test_loop_engine import make_spec, passing_ledger_state
except ModuleNotFoundError:
    from test_loop_engine import make_spec, passing_ledger_state

ROLES = ["mathematics-adversary", "repository-boundary-adversary", "abstraction-adversary", "mathlib-reviewer"]
NOW = 1_800_000_000.0


def policy(**overrides):
    result = dict(objective_id="repair-controller", implementer="implementer",
                  max_episodes=2, max_total_rounds=9, max_plan_submissions=2,
                  max_elapsed_seconds=604800, history=[])
    result.update(overrides)
    return result


def ledger():
    return dict(status="initialized", rounds=[], reviewers=ROLES[:], max_review_rounds=3,
                issue={"number": 1458}, chunk={"id": "repair", "scope": "Validate controller",
                "files": ["scripts/loop_engine.py"], "requirements": ["Keep history"],
                "acceptance": ["All findings resolved"], "closure": "complete"})


def review(role, sha, verdict="needs_changes", resolutions=None):
    token = "PASS" if verdict == "pass" else "NEEDS_CHANGES"
    text = f"{role}: evidence demonstrating a concrete boundary.\nReviewed commit: {sha}\nClose: {token}"
    result = dict(reviewer=role, verdict=verdict, finding_text=text,
                  finding_digest=hashlib.sha256(text.encode()).hexdigest())
    if resolutions is not None:
        result["resolutions"] = resolutions
    return result


class RecoveryTests(unittest.TestCase):
    def fresh(self, **limits):
        state = ledger()
        recovery.initialize(state, policy(**limits), now=NOW)
        return state

    def panel(self, state, sha, verdict="needs_changes", resolutions=None):
        recovery.reserve_round(state, sha, now=NOW)
        current = state["rounds"][-1]
        current["reviews"] = [review(role, sha, verdict, resolutions) for role in ROLES]
        current["adjudication"] = {"verdict": verdict}
        state["status"] = "blocked" if len(state["rounds"]) == 3 else "needs_changes"
        if verdict == "pass":
            state["status"] = "passed"
        recovery.after_adjudication(state, now=NOW)

    def exhausted(self, **limits):
        state = self.fresh(**limits)
        for letter in "abc":
            self.panel(state, letter * 40)
        return state

    def plan(self, state):
        return dict(author="researcher", cause="inadequate boundary model",
                    diagnosis="The parser trusted an embedded token instead of the closing verdict.",
                    evidence=["Probe: contradictory trailer was accepted."],
                    strategy="Parse one final trailer and reject ambiguous closes.",
                    checks=["Reject mixed verdicts; accept a single exact close."],
                    finding_ids=list(recovery.inherited_findings(state)),
                    contract_digest=state["recovery"]["contract_digest"])

    def accept(self, state):
        recovery.submit_plan(state, self.plan(state), now=NOW)
        submission = state["recovery"]["episodes"][-1]["submissions"][-1]
        recovery.review_plan(state, dict(reviewer="independent-reviewer", plan_digest=submission["digest"],
                                        verdict="ready", assessment="The reproducer proves the new strategy addresses every finding."), now=NOW)

    def test_third_failure_schedules_research_and_forbids_fourth_round(self):
        state = self.exhausted()
        self.assertIn("investigat", json.dumps(recovery.next_action(state, now=NOW)).lower())
        snapshot = copy.deepcopy(state["rounds"])
        with self.assertRaises(ValueError):
            recovery.reserve_round(state, "d" * 40, now=NOW)
        self.assertEqual(snapshot, state["rounds"])
        self.assertEqual(len(recovery.inherited_findings(state)), 12)

    def test_missing_role_reuses_reserved_round_and_cannot_change_commit(self):
        state = self.fresh()
        recovery.reserve_round(state, "a" * 40, now=NOW)
        state["rounds"][-1]["reviews"] = [review(ROLES[0], "a" * 40)]
        before = copy.deepcopy(state)
        recovery.reserve_round(state, "a" * 40, now=NOW)
        self.assertEqual(len(state["rounds"]), 1)
        self.assertEqual(before["rounds"], state["rounds"])
        with self.assertRaises(ValueError):
            recovery.reserve_round(state, "b" * 40, now=NOW)
        action = json.dumps(recovery.next_action(state, now=NOW))
        self.assertIn(ROLES[1], action)

    def test_missing_evidence_or_inherited_finding_rejects_plan(self):
        for defect in ("evidence", "finding_ids", "contract_digest"):
            with self.subTest(defect=defect):
                state = self.exhausted()
                plan = self.plan(state)
                plan[defect] = [] if defect != "contract_digest" else "0" * 64
                with self.assertRaises(ValueError):
                    recovery.submit_plan(state, plan, now=NOW)

    def test_plan_review_requires_distinct_identity_and_exact_digest(self):
        for author, digest in (("researcher", None), ("implementer", None), ("independent", "0" * 64)):
            with self.subTest(author=author, digest=digest):
                state = self.exhausted()
                recovery.submit_plan(state, self.plan(state), now=NOW)
                submission = state["recovery"]["episodes"][-1]["submissions"][-1]
                with self.assertRaises(ValueError):
                    recovery.review_plan(state, dict(reviewer=author, plan_digest=digest or submission["digest"],
                                                    verdict="ready", assessment="Checked evidence."), now=NOW)

    def test_resume_preserves_failed_history_and_is_idempotent(self):
        state = self.exhausted()
        original = copy.deepcopy(state["rounds"])
        findings = copy.deepcopy(recovery.inherited_findings(state))
        self.accept(state)
        with self.assertRaises(ValueError):
            recovery.require_publishable(state)
        recovery.resume(state, now=NOW)
        snapshot = copy.deepcopy(state)
        recovery.resume(state, now=NOW)
        self.assertEqual(state, snapshot)
        self.assertEqual(recovery.inherited_findings(state), findings)
        self.assertIn(json.dumps(original, sort_keys=True), json.dumps(state, sort_keys=True))

    def test_passing_successor_must_resolve_every_inherited_finding(self):
        state = self.exhausted()
        self.accept(state)
        recovery.resume(state, now=NOW)
        with self.assertRaises(ValueError):
            self.panel(state, "d" * 40, "pass", {})
        resolutions = {key: "Regression probe verifies this boundary." for key in recovery.inherited_findings(state)}
        current = state["rounds"][-1]
        current["reviews"] = [review(role, "d" * 40, "pass", resolutions) for role in ROLES]
        recovery.after_adjudication(state, now=NOW)
        recovery.require_publishable(state)

    def test_exact_final_review_grammar_rejects_ambiguous_or_stale_evidence(self):
        sha = "a" * 40
        good = f"Evidence.\nReviewed commit: {sha}\nClose: PASS"
        recovery.validate_review(sha, "pass", good)
        for text in (good + ", NEEDS_CHANGES", good + "\nMore text", good.replace(sha, "b" * 40),
                     "PASS\n", good.replace("Close: PASS", "Close: PASS\nClose: NEEDS_CHANGES")):
            with self.subTest(text=text), self.assertRaises(ValueError):
                recovery.validate_review(sha, "pass", text)

    def test_final_panel_must_be_complete(self):
        state = self.fresh()
        recovery.reserve_round(state, "a" * 40, now=NOW)
        current = state["rounds"][-1]
        current["reviews"] = [review(ROLES[0], "a" * 40, "pass")]
        current["adjudication"] = {"verdict": "pass"}
        state["status"] = "passed"
        with self.assertRaises(ValueError):
            recovery.require_publishable(state)

    def test_expired_objective_parks_and_next_action_is_idempotent(self):
        state = self.fresh(max_elapsed_seconds=60)
        action = recovery.next_action(state, now=NOW + 61)
        self.assertIn("park", json.dumps(action).lower())
        self.assertEqual(action, recovery.next_action(state, now=NOW + 61))
        recovery.reserve_round(state, "a" * 40, now=NOW + 61)
        self.assertEqual(state["rounds"], [])
        self.assertIn("park", json.dumps(recovery.next_action(state, now=NOW + 61)).lower())

    def test_global_round_budget_cannot_be_replenished_by_recovery(self):
        state = self.exhausted(max_total_rounds=3)
        self.assertIn("park", json.dumps(recovery.next_action(state, now=NOW)).lower())
        with self.assertRaises(ValueError):
            recovery.submit_plan(state, self.plan(state), now=NOW)

    def test_two_rejected_plans_exhaust_same_episode(self):
        state = self.exhausted()
        for _ in range(2):
            recovery.submit_plan(state, self.plan(state), now=NOW)
            submission = state["recovery"]["episodes"][-1]["submissions"][-1]
            recovery.review_plan(state, dict(reviewer="independent-reviewer", plan_digest=submission["digest"],
                                            verdict="needs_changes", assessment="No credible new method yet."), now=NOW)
        self.assertEqual(len(state["recovery"]["episodes"]), 1)
        self.assertIn("park", json.dumps(recovery.next_action(state, now=NOW)).lower())
        with self.assertRaises(ValueError):
            recovery.submit_plan(state, self.plan(state), now=NOW)

    def test_frozen_contract_cannot_lose_requirement_or_reviewer_on_resume(self):
        for field in ("requirements", "acceptance", "files"):
            with self.subTest(field=field):
                state = self.exhausted()
                self.accept(state)
                state["chunk"][field] = []
                with self.assertRaises(ValueError):
                    recovery.resume(state, now=NOW)
        state = self.exhausted()
        self.accept(state)
        state["reviewers"].pop()
        with self.assertRaises(ValueError):
            recovery.resume(state, now=NOW)

    def test_abandoned_partial_panel_remains_charged_and_findings_survive(self):
        state = self.fresh(max_total_rounds=4)
        recovery.reserve_round(state, "a" * 40, now=NOW)
        state["rounds"][-1]["reviews"] = [review(ROLES[0], "a" * 40)]
        recovery.abandon(state, "Tool evidence proves the strategy needs new research.", now=NOW)
        findings = copy.deepcopy(recovery.inherited_findings(state))
        self.assertEqual(len(findings), 1)
        self.accept(state)
        recovery.resume(state, now=NOW)
        for letter in "bcd":
            self.panel(state, letter * 40)
        self.assertIn("park", json.dumps(recovery.next_action(state, now=NOW)).lower())
        for key, value in findings.items():
            self.assertEqual(recovery.inherited_findings(state)[key], value)

    def test_imported_failed_snapshots_preserved_and_all_rounds_charged(self):
        historical = ledger()
        historical["status"] = "blocked"
        historical["rounds"] = [dict(number=n, commit=letter * 40,
            reviews=[review(role, letter * 40) for role in ROLES],
            adjudication={"verdict": "needs_changes"}) for n, letter in enumerate("abc", 1)]
        original = copy.deepcopy(historical)
        state = ledger()
        recovery.initialize(state, policy(max_total_rounds=4, history=[{"path": "legacy.json", "sha256": "a" * 64}]),
                            [historical], now=NOW)
        self.assertEqual(historical, original)
        self.assertEqual(state["recovery"]["history"][0]["snapshot"], original)
        self.assertEqual(recovery.total_rounds(state), 3)
        self.assertEqual(len(recovery.inherited_findings(state)), 12)
        self.accept(state)
        recovery.resume(state, now=NOW)
        self.panel(state, "d" * 40)
        self.assertEqual(recovery.total_rounds(state), 4)
        self.assertIn("park", json.dumps(recovery.next_action(state, now=NOW)).lower())
        self.assertEqual(state["recovery"]["history"][0]["snapshot"], original)

    def test_imported_snapshot_tampering_is_detected(self):
        historical = ledger()
        historical["status"] = "blocked"
        historical["rounds"] = [dict(number=1, commit="a" * 40,
            reviews=[review(ROLES[0], "a" * 40)], adjudication=None)]
        state = ledger()
        recovery.initialize(state, policy(history=[{"path": "legacy.json", "sha256": "a" * 64}]),
                            [historical], now=NOW)
        state["recovery"]["history"][0]["snapshot"]["rounds"] = []
        with self.assertRaises(ValueError):
            recovery.validate(state)


class RecoveryCliTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-b", "main")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Recovery Test")
        self.spec_path, self.spec = make_spec(self.root)
        self.spec["limits"]["max_review_rounds_per_chunk"] = 3
        self.spec["recovery"] = policy()
        self.save_spec()
        self.git("add", ".")
        self.git("commit", "-m", "Fixture")
        self.sha = self.git("rev-parse", "HEAD").strip()
        self.state_path = self.root / ".loop-runs/test-chunk.json"

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True,
                              text=True, capture_output=True).stdout

    def save_spec(self):
        self.spec_path.write_text(yaml.safe_dump(self.spec, sort_keys=False), encoding="utf-8")

    def cli(self, *args, ok=True):
        result = subprocess.run([sys.executable, str(SCRIPT_DIR / "loop_engine.py"), *map(str, args)],
                                cwd=self.root, text=True, capture_output=True)
        if ok:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def initialize(self, *args, ok=True):
        return self.cli("ledger", "init", "--repo-root", self.root, "--spec", self.spec_path,
                        "--issue", "1", "--chunk-id", "test-chunk", *args, ok=ok)

    def assert_publication_actions_blocked(self):
        actions = [
            lambda: loop_engine.action_push(self.root, self.spec, None, False, False),
            lambda: loop_engine.action_create_pr(self.root, self.spec, 1, self.state_path,
                                                 "Repair", "body.md", False, False),
            lambda: loop_engine.action_approve(self.root, self.spec, 1, self.state_path, "Reviewed", False),
            lambda: loop_engine.action_merge(self.root, self.spec, 1, self.state_path,
                                             None, False, False, None, False),
        ]
        # Isolate the recovery gate from the separate provider-capability gate.
        # Real local Git reads still run; no provider invocation may be reached.
        for action in actions:
            with mock.patch.object(loop_engine, "authorize_action"), \
                    mock.patch.object(loop_engine, "run_command", wraps=loop_engine.run_command) as calls, \
                    mock.patch.object(loop_engine, "gh_json") as provider:
                with self.assertRaisesRegex((ValueError, loop_engine.LoopError), "publish|passing|recovery"):
                    action()
                provider.assert_not_called()
                for call in calls.call_args_list:
                    command = call.args[1]
                    self.assertNotEqual(command[0], "gh")
                    self.assertNotEqual(command[:2], ["git", "push"])

    def test_cli_reservation_is_durable_and_next_is_read_only(self):
        self.initialize()
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", self.sha)
        before = self.state_path.read_bytes()
        self.cli("recovery", "next", "--ledger", self.state_path)
        self.cli("recovery", "next", "--ledger", self.state_path)
        self.assertEqual(before, self.state_path.read_bytes())
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", self.sha)
        self.assertEqual(len(json.loads(self.state_path.read_text())["rounds"]), 1)

    def test_cli_cannot_reset_by_new_state_directory_or_manifest_identity(self):
        self.initialize()
        original = self.state_path.read_bytes()
        self.initialize("--state-dir", ".replacement-ledgers", ok=False)
        self.spec["id"] = "renamed-run"
        self.save_spec()
        self.initialize(ok=False)
        self.assertEqual(original, self.state_path.read_bytes())

    def test_repository_case_alias_cannot_reset_or_drop_recovery(self):
        self.initialize()
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", self.sha)
        original = self.state_path.read_bytes()
        self.spec["repository"] = self.spec["repository"].upper()
        self.save_spec()
        self.initialize("--state-dir", ".fresh-ledgers", ok=False)
        self.assertEqual(original, self.state_path.read_bytes())
        del self.spec["recovery"]
        with self.assertRaisesRegex(loop_engine.LoopError, "registered recovery"):
            loop_engine.recovery_publication_state(self.root, self.spec)

    def test_cli_restores_deleted_cache_without_replenishing_rounds(self):
        self.initialize()
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", self.sha)
        original = json.loads(self.state_path.read_text())
        self.state_path.unlink()
        self.initialize()
        self.assertEqual(original, json.loads(self.state_path.read_text()))

    def test_cli_edited_cache_cannot_erase_reserved_round(self):
        self.initialize()
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", self.sha)
        original = json.loads(self.state_path.read_text())
        tampered = copy.deepcopy(original)
        tampered["rounds"] = []
        tampered["status"] = "initialized"
        self.state_path.write_text(json.dumps(tampered), encoding="utf-8")
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", self.sha)
        self.assertEqual(original, json.loads(self.state_path.read_text()))

    def test_cli_shared_worktree_registry_forbids_second_initialization(self):
        self.initialize()
        other = self.root / "other-worktree"
        self.git("worktree", "add", "--detach", str(other), "HEAD")
        self.cli("ledger", "init", "--repo-root", other, "--spec", other / "run.yaml",
                 "--issue", "1", "--chunk-id", "test-chunk", ok=False)

    def test_history_content_digest_mismatch_fails_without_initializing(self):
        history = self.root / "terminal.json"
        history.write_text(json.dumps(ledger()), encoding="utf-8")
        self.spec["recovery"]["history"] = [{"path": "terminal.json", "sha256": "0" * 64}]
        self.save_spec()
        self.initialize(ok=False)
        self.assertFalse(self.state_path.exists())

    def test_cli_failure_research_resume_and_full_passing_panel(self):
        self.initialize()
        for index in range(3):
            self.git("commit", "--allow-empty", "-m", f"Candidate {index}")
            sha = self.git("rev-parse", "HEAD").strip()
            self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", sha)
            for role in ROLES:
                output = self.root / f"{role}.md"
                output.write_text(review(role, sha)["finding_text"], encoding="utf-8")
                self.cli("ledger", "record-review", "--state", self.state_path, "--reviewer", role,
                         "--commit", sha, "--verdict", "needs_changes", "--finding-file", output)
            self.cli("ledger", "adjudicate", "--state", self.state_path, "--verdict", "needs_changes")
        failed = json.loads(self.state_path.read_text())
        self.assertIn("investigat", self.cli("recovery", "next", "--ledger", self.state_path).lower())
        self.assert_publication_actions_blocked()
        with self.assertRaises((ValueError, loop_engine.LoopError)):
            loop_engine.recovery_publication_state(self.root, self.spec, self.state_path)
        plan_path = self.root / "plan.json"
        plan_path.write_text(json.dumps(RecoveryTests().plan(failed)), encoding="utf-8")
        self.cli("recovery", "submit-plan", "--ledger", self.state_path, "--file", plan_path)
        submitted = json.loads(self.state_path.read_text())
        plan_digest = submitted["recovery"]["episodes"][-1]["submissions"][-1]["digest"]
        acceptance_path = self.root / "acceptance.json"
        acceptance_path.write_text(json.dumps(dict(reviewer="independent-reviewer", plan_digest=plan_digest,
            verdict="ready", assessment="Reproducer and changed verification cover each inherited finding.")), encoding="utf-8")
        self.cli("recovery", "review-plan", "--ledger", self.state_path, "--file", acceptance_path)
        self.assert_publication_actions_blocked()
        with self.assertRaises((ValueError, loop_engine.LoopError)):
            loop_engine.recovery_publication_state(self.root, self.spec, self.state_path)
        self.cli("recovery", "resume", "--ledger", self.state_path)
        resumed = self.state_path.read_bytes()
        self.cli("recovery", "resume", "--ledger", self.state_path)
        self.assertEqual(resumed, self.state_path.read_bytes())
        self.git("commit", "--allow-empty", "-m", "Researched repair")
        sha = self.git("rev-parse", "HEAD").strip()
        self.cli("recovery", "start-round", "--ledger", self.state_path, "--commit", sha)
        resolutions = self.root / "resolutions.json"
        resolutions.write_text(json.dumps({key: "Confirmed by contradiction and containment regression probes."
            for key in recovery.inherited_findings(failed)}), encoding="utf-8")
        for role in ROLES:
            output = self.root / f"{role}.md"
            output.write_text(review(role, sha, "pass")["finding_text"], encoding="utf-8")
            self.cli("ledger", "record-review", "--state", self.state_path, "--reviewer", role,
                     "--commit", sha, "--verdict", "pass", "--finding-file", output,
                     "--resolutions-file", resolutions)
        self.cli("ledger", "adjudicate", "--state", self.state_path, "--verdict", "pass")
        final = json.loads(self.state_path.read_text())
        recovery.require_publishable(final)
        self.assertEqual(final["rounds"][-1]["commit"], sha)
        self.assertEqual(len(final["rounds"][-1]["reviews"]), 4)
        self.assertIn(json.dumps(failed["rounds"], sort_keys=True), json.dumps(final, sort_keys=True))
        self.git("remote", "add", "origin", "https://github.com/example/repository.git")
        self.git("commit", "--allow-empty", "-m", "Unreviewed revision")
        with mock.patch.object(loop_engine, "authorize_action"):
            with self.assertRaisesRegex(loop_engine.LoopError, "exact reviewed"):
                loop_engine.action_push(self.root, self.spec, None, False, False)
            with self.assertRaisesRegex(loop_engine.LoopError, "exact reviewed"):
                loop_engine.action_create_pr(self.root, self.spec, 1, self.state_path,
                                             "Repair", "body.md", False, False)

    def test_json_duplicate_fields_are_rejected(self):
        document = self.root / "ambiguous.json"
        document.write_text('{"reviewer":"independent","reviewer":"implementer"}', encoding="utf-8")
        with self.assertRaises(loop_engine.LoopError):
            loop_engine.read_json_object(document)

    def test_scope_check_includes_rename_source(self):
        source = self.root / "outside.txt"
        source.write_text("Existing content\n", encoding="utf-8")
        self.git("add", "outside.txt")
        self.git("commit", "-m", "Existing outside file")
        base = self.git("rev-parse", "HEAD").strip()
        self.git("mv", "outside.txt", "inside.txt")
        self.git("commit", "-m", "Move into allowed path")
        current = self.git("rev-parse", "HEAD").strip()
        state = {"chunk": {"files": ["inside.txt"]}, "rounds": []}
        with self.assertRaisesRegex(loop_engine.LoopError, "outside.txt"):
            loop_engine.recovery_scoped_paths(self.root, {"base_ref": base}, state, current)

    def provider_fixture(self):
        state = passing_ledger_state(self.root, self.spec)
        state["repo_root"] = str(self.root)
        state["recovery"] = {"policy": self.spec["recovery"]}
        pr = dict(state="MERGED", mergedAt="2026-09-22T12:00:00Z",
                  closingIssuesReferences=[{"number": 1}], headRefOid="a" * 40,
                  headRefName="agent/test-issue", baseRefName="main", body="Closes #1",
                  files=[{"path": "scripts/loop_engine.py"}])
        return state, pr

    @contextlib.contextmanager
    def provider_gates(self, state):
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.object(loop_engine, "authorize_action"))
            stack.enter_context(mock.patch.object(loop_engine, "recovery_publication_state", return_value=state))
            stack.enter_context(mock.patch.object(loop_engine, "load_state", return_value=state))
            stack.enter_context(mock.patch.object(loop_engine, "require_predecessor_prs", return_value=[]))
            stack.enter_context(mock.patch.object(loop_engine, "verify_local_chunk_files"))
            scope = stack.enter_context(mock.patch.object(loop_engine, "recovery_scoped_paths"))
            stack.enter_context(mock.patch.object(loop_engine, "recovery_registry", return_value=[
                (self.root / "registry.json", {"objective_id": self.spec["recovery"]["objective_id"],
                                              "spec_path": str(self.spec_path)})]))
            stack.enter_context(mock.patch.object(loop_engine, "git", side_effect=lambda root, *args:
                "a" * 40 if args == ("rev-parse", "HEAD") else
                "agent/test-issue" if args == ("branch", "--show-current") else ""))
            yield scope

    def test_create_pr_refuses_stale_remote_before_provider_write(self):
        state, _ = self.provider_fixture()
        body = self.root / "body.md"
        body.write_text("Closes #1\n", encoding="utf-8")
        with self.provider_gates(state), mock.patch.object(loop_engine, "gh_json", return_value={
                "object": {"sha": "b" * 40}}) as read, mock.patch.object(loop_engine, "run_command") as write:
            with self.assertRaisesRegex(loop_engine.LoopError, "remote|reviewed"):
                loop_engine.action_create_pr(self.root, self.spec, 1, self.state_path,
                                             "Repair", str(body), False, False)
            write.assert_not_called()
            self.assertTrue(any(call.args[1][0] == "api" for call in read.call_args_list))

    def test_created_pr_race_reports_url_and_fails_postcondition(self):
        state, pr = self.provider_fixture()
        pr.update(state="OPEN", mergedAt=None, headRefOid="b" * 40)
        body = self.root / "body.md"
        body.write_text("Closes #1\n", encoding="utf-8")
        url = "https://github.com/example/repository/pull/101"
        output = io.StringIO()
        with self.provider_gates(state), mock.patch.object(loop_engine, "gh_json", side_effect=[
                {"object": {"sha": "a" * 40}}, pr]), mock.patch.object(loop_engine, "run_command",
                return_value=subprocess.CompletedProcess([], 0, stdout=url + "\n", stderr="")) as write, \
                contextlib.redirect_stdout(output):
            with self.assertRaises(loop_engine.LoopError) as raised:
                loop_engine.action_create_pr(self.root, self.spec, 1, self.state_path,
                                             "Repair", str(body), False, False)
            self.assertEqual(write.call_count, 1)
            self.assertEqual(write.call_args.args[1][:3], ["gh", "pr", "create"])
            self.assertIn(url, output.getvalue() + str(raised.exception))
            self.assertNotIn("PASS PR created", output.getvalue())

    def test_close_rejects_unreviewed_or_unrelated_merged_pr(self):
        state, pr = self.provider_fixture()
        for field, value in (("headRefOid", "b" * 40), ("headRefName", "agent/other-issue"),
                             ("baseRefName", "other-base"), ("body", "Closes #2")):
            with self.subTest(field=field), self.provider_gates(state), \
                    mock.patch.object(loop_engine, "gh_json", return_value={**pr, field: value}), \
                    mock.patch.object(loop_engine, "run_command") as write:
                with self.assertRaises(loop_engine.LoopError):
                    loop_engine.action_close(self.root, self.spec, 1, 101, None, False)
                write.assert_not_called()

    def test_close_exact_reviewed_merged_pr_checks_scope_then_closes(self):
        state, pr = self.provider_fixture()
        with self.provider_gates(state) as scope, mock.patch.object(loop_engine, "gh_json", return_value=pr), \
                mock.patch.object(loop_engine, "run_command") as write:
            self.assertEqual(loop_engine.action_close(self.root, self.spec, 1, 101, None, False), 0)
            scope.assert_called_once()
            self.assertEqual(write.call_args.args[1][:4], ["gh", "issue", "close", "1"])
        with self.provider_gates(state) as scope, mock.patch.object(loop_engine, "gh_json", return_value=pr), \
                mock.patch.object(loop_engine, "run_command") as write:
            scope.side_effect = loop_engine.LoopError("outside frozen scope")
            with self.assertRaisesRegex(loop_engine.LoopError, "outside frozen scope"):
                loop_engine.action_close(self.root, self.spec, 1, 101, None, False)
            write.assert_not_called()


if __name__ == "__main__":
    unittest.main()
