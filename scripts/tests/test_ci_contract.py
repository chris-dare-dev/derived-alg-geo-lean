#!/usr/bin/env python3
"""Focused tests for the revision-bound CI evidence contract."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

from scripts import ci_contract


ROOT = Path(__file__).resolve().parents[2]
INVENTORY = json.loads((ROOT / "scripts/ci_gate_inventory.json").read_text())
SHA_A = "a" * 40
SHA_B = "b" * 40
SHA_C = "c" * 40


def evidence(*, event: str = "pull_request", workflow: str | None = None) -> dict:
    gates = []
    artifacts = []
    ref = "refs/heads/main" if event in {"push", "schedule", "workflow_dispatch"} else "refs/pull/1/merge"
    candidate_commit = SHA_B if event in {"push", "schedule", "workflow_dispatch"} else SHA_C
    base_commit = SHA_B if event in {"push", "schedule", "workflow_dispatch"} else SHA_A
    producer = f"github-actions/{workflow or ('Docs' if event == 'schedule' else 'CI')}"
    candidate_tree = SHA_C
    parents = [SHA_A, SHA_B] if event == "pull_request" else []
    for index, definition in enumerate(INVENTORY["gates"], start=1):
        applicable = ci_contract._event_applies(
            definition, {"event": event, "ref": ref, "producer": producer}
        )
        status = "passed" if applicable else "skipped"
        conclusion = "success" if applicable else "skipped"
        artifact_id = f"artifact-{index}"
        if applicable:
            artifacts.append(
                {
                    "id": artifact_id,
                    "path": f"results/{artifact_id}.json",
                    "sha256": f"{index:064x}",
                    "media_type": "application/json",
                    "size_bytes": 128,
                    "producer": definition["producer"],
                    "kind": definition["artifact"],
                    "subject": definition["id"],
                    "commit": candidate_commit,
                    "run_id": 35532316123,
                    "run_attempt": 1,
                }
            )
        gates.append(
            {
                "id": definition["id"],
                "name": definition["name"],
                "producer": definition["producer"],
                "platform": definition["platforms"][0],
                "provider_id": f"run-3553-job-{index}",
                "commit": candidate_commit,
                "run_id": 35532316123,
                "run_attempt": 1,
                "status": status,
                "conclusion": conclusion,
                "applicable": applicable,
                "prerequisites": definition["prerequisites"],
                "artifact_refs": [artifact_id] if applicable else [],
                **({"skip_reason": "event does not produce this auxiliary gate"} if not applicable else {}),
            }
        )
    return {
        "schema_version": 4,
        "repository": INVENTORY["repository"],
        "base_commit": base_commit,
        "head_commit": SHA_B,
        "candidate_commit": candidate_commit,
        "candidate_tree": candidate_tree,
        "event": event,
        "ref": ref,
        "revision_binding": {
            "base_commit": base_commit,
            "head_commit": SHA_B,
            "candidate_commit": candidate_commit,
            "candidate_tree": candidate_tree,
            "event": event,
            "ref": ref,
        },
        "policy_binding": {
            "source": "protected-base",
            "commit": base_commit,
            "inventory_sha256": ci_contract._canonical_sha256(INVENTORY),
        },
        "provider_binding": {
            "source": "github-api",
            "repository": INVENTORY["repository"],
            "producer": producer,
            "run_id": 35532316123,
            "run_attempt": 1,
            "event": event,
            "ref": ref,
            "commit": candidate_commit,
            "tree": candidate_tree,
            "parents": parents,
        },
        "platform": "github-actions",
        "run_id": 35532316123,
        "run_attempt": 1,
        "producer": producer,
        "toolchain": "lean-toolchain@fixture",
        "pins": {
            "lean-toolchain": "1" * 64,
            "lake-manifest.json": "2" * 64,
            "pins.json": "3" * 64,
        },
        "artifacts": artifacts,
        "gates": gates,
    }


def bind_provider_proof(candidate: dict) -> None:
    proof = candidate["provider_binding"]
    body = {key: value for key, value in proof.items() if key != "proof_sha256"}
    proof["proof_sha256"] = hashlib.sha256(
        json.dumps(body, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    ).hexdigest()


class ContractTests(unittest.TestCase):
    def evaluate(self, candidate: dict, inventory: dict = INVENTORY) -> dict:
        direct_ref_event = isinstance(candidate.get("event"), str) and candidate["event"] in {
            "push", "schedule", "workflow_dispatch"
        }
        return ci_contract.validate_evidence(
            inventory,
            candidate,
            trusted_base_commit=SHA_B if direct_ref_event else SHA_A,
            trusted_head_commit=SHA_B,
            trusted_inventory_sha256=ci_contract._canonical_sha256(inventory),
        )

    def assert_invalid(self, candidate: dict, fragment: str) -> None:
        result = self.evaluate(candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any(fragment in error for error in result["errors"]), result)

    def test_inventory_is_complete_and_well_formed(self) -> None:
        self.assertEqual(ci_contract.validate_inventory(INVENTORY), [])

    def test_inventory_rejects_unknown_scope_and_platform(self) -> None:
        inventory = copy.deepcopy(INVENTORY)
        inventory["gates"][0]["applies_to"].append("workflow_dispatch:Unknown")
        inventory["gates"][0]["platforms"] = ["unknown-platform"]
        errors = ci_contract.validate_inventory(inventory)
        self.assertTrue(any("unsupported selector" in error for error in errors))
        self.assertTrue(any("recognized platform" in error for error in errors))

    def test_malformed_fields_fail_closed_without_crashing(self) -> None:
        inventory = copy.deepcopy(INVENTORY)
        inventory["gates"][0].update(
            id=[],
            **{"class": []},
            applies_to=[{}],
            platforms=[{}],
            prerequisites=None,
        )
        self.assertTrue(ci_contract.validate_inventory(inventory))
        candidate = evidence()
        candidate["event"] = []
        candidate["gates"][0].update(status=[], platform=[], prerequisites=None, artifact_refs=[{}])
        bind_provider_proof(candidate)
        result = self.evaluate(candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(result["errors"])

    def test_revision_bound_evidence_passes(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        result = self.evaluate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertEqual(result["warnings"], [])

    def test_missing_candidate_identity_is_rejected(self) -> None:
        candidate = evidence()
        del candidate["candidate_tree"]
        self.assert_invalid(candidate, "evidence.candidate_tree is required")

    def test_push_ref_must_be_provider_canonical(self) -> None:
        candidate = evidence(event="push")
        bind_provider_proof(candidate)
        candidate["ref"] = "main"
        self.assert_invalid(candidate, "valid event-bound ref")

    def test_push_and_schedule_are_main_only(self) -> None:
        for event in ("push", "schedule"):
            with self.subTest(event=event):
                candidate = evidence(event=event)
                candidate["ref"] = "refs/heads/agent/other"
                candidate["revision_binding"]["ref"] = candidate["ref"]
                candidate["provider_binding"]["ref"] = candidate["ref"]
                bind_provider_proof(candidate)
                self.assert_invalid(candidate, "valid event-bound ref")

    def test_revision_binding_mismatch_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["revision_binding"]["candidate_commit"] = SHA_B
        self.assert_invalid(candidate, "revision_binding.candidate_commit")

    def test_push_candidate_must_be_the_pushed_head(self) -> None:
        candidate = evidence(event="push")
        candidate["candidate_commit"] = SHA_C
        candidate["revision_binding"]["candidate_commit"] = SHA_C
        candidate["provider_binding"]["commit"] = SHA_C
        bind_provider_proof(candidate)
        for gate in candidate["gates"]:
            gate["commit"] = SHA_C
        for artifact in candidate["artifacts"]:
            artifact["commit"] = SHA_C
        self.assert_invalid(candidate, "must equal head_commit")

    def test_pull_merge_candidate_must_prove_base_and_head_parents(self) -> None:
        candidate = evidence()
        candidate["provider_binding"]["parents"] = [SHA_A]
        bind_provider_proof(candidate)
        self.assert_invalid(candidate, "both base_commit and head_commit as parents")

    def test_provider_proof_digest_is_required(self) -> None:
        candidate = evidence()
        candidate["provider_binding"]["proof_sha256"] = "0" * 64
        self.assert_invalid(candidate, "proof_sha256 does not bind")

    def test_provider_producer_must_match_primary_record(self) -> None:
        candidate = evidence()
        candidate["provider_binding"]["producer"] = "github-actions/Docs"
        bind_provider_proof(candidate)
        self.assert_invalid(candidate, "provider_binding.producer does not match")

    def test_applicable_gate_requires_bound_artifact(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"][0]["artifact_refs"] = []
        self.assert_invalid(candidate, "artifact_refs must be non-empty")

    def test_gate_from_stale_revision_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"][0]["commit"] = SHA_B
        self.assert_invalid(candidate, "not bound to evidence.candidate_commit")

    def test_duplicate_provider_name_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        duplicate = copy.deepcopy(candidate["gates"][1])
        duplicate["id"] = "roadmap"
        candidate["gates"].append(duplicate)
        self.assert_invalid(candidate, "duplicates")

    def test_same_name_from_commit_status_and_check_run_is_unambiguous(self) -> None:
        inventory = copy.deepcopy(INVENTORY)
        status_definition = copy.deepcopy(inventory["gates"][0])
        status_definition.update(
            id="legacy-status",
            producer="github-status/legacy",
            artifact="commit-status:build",
            platforms=["github-status"],
            required=False,
            run_binding="status",
            **{"class": "auxiliary"},
        )
        inventory["gates"].append(status_definition)
        candidate = evidence()
        status_gate = copy.deepcopy(candidate["gates"][0])
        status_gate.update(
            id="legacy-status",
            producer="github-status/legacy",
            platform="github-status",
            provider_id="status-17",
            artifact_refs=["legacy-status-artifact"],
        )
        del status_gate["run_id"]
        del status_gate["run_attempt"]
        candidate["gates"].append(status_gate)
        status_artifact = copy.deepcopy(candidate["artifacts"][0])
        status_artifact.update(
            id="legacy-status-artifact",
            path="results/legacy-status.json",
            producer="github-status/legacy",
            kind="commit-status:build",
            subject="legacy-status",
        )
        del status_artifact["run_id"]
        del status_artifact["run_attempt"]
        candidate["artifacts"].append(status_artifact)
        candidate["policy_binding"]["inventory_sha256"] = ci_contract._canonical_sha256(inventory)
        bind_provider_proof(candidate)
        self.assertEqual(ci_contract.validate_inventory(inventory), [])
        self.assertTrue(self.evaluate(candidate, inventory)["valid"])

    def test_untrusted_inventory_edit_cannot_remove_a_required_gate(self) -> None:
        inventory = copy.deepcopy(INVENTORY)
        inventory["gates"] = [gate for gate in inventory["gates"] if gate["id"] != "build"]
        candidate = evidence()
        bind_provider_proof(candidate)
        result = ci_contract.validate_evidence(
            inventory,
            candidate,
            trusted_base_commit=SHA_A,
            trusted_head_commit=SHA_B,
            trusted_inventory_sha256=ci_contract._canonical_sha256(INVENTORY),
        )
        self.assertFalse(result["valid"])
        self.assertTrue(any("trusted_inventory_sha256" in error for error in result["errors"]))

    def test_cli_policy_loader_reads_commit_not_working_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            policy_path = root / "scripts/ci_gate_inventory.json"
            policy_path.parent.mkdir()
            policy_path.write_text(json.dumps(INVENTORY), encoding="utf-8")
            for command in (
                ["git", "init", "-q"],
                ["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.test", "add", "."],
                ["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.test", "commit", "-qm", "policy"],
            ):
                subprocess.run(command, cwd=root, check=True, capture_output=True)
            commit = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=root, check=True, capture_output=True, text=True
            ).stdout.strip()
            policy_path.write_text('{"schema_version": 999}', encoding="utf-8")
            self.assertEqual(ci_contract._load_trusted_inventory(root, commit), INVENTORY)

    def test_missing_trusted_adapter_anchor_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        result = ci_contract.validate_evidence(INVENTORY, candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any("trusted_base_commit" in error for error in result["errors"]))

    def test_stale_base_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        result = ci_contract.validate_evidence(
            INVENTORY,
            candidate,
            trusted_base_commit=SHA_C,
            trusted_head_commit=SHA_B,
            trusted_inventory_sha256=ci_contract._canonical_sha256(INVENTORY),
        )
        self.assertFalse(result["valid"])
        self.assertTrue(any("stale relative" in error for error in result["errors"]))

    def test_stale_head_is_rejected_even_when_record_is_self_consistent(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        result = ci_contract.validate_evidence(
            INVENTORY,
            candidate,
            trusted_base_commit=SHA_A,
            trusted_head_commit=SHA_C,
            trusted_inventory_sha256=ci_contract._canonical_sha256(INVENTORY),
        )
        self.assertFalse(result["valid"])
        self.assertTrue(any("head_commit is stale" in error for error in result["errors"]))

    def test_rerun_attempt_mismatch_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"][0]["run_attempt"] = 2
        self.assert_invalid(candidate, "run_attempt must equal evidence.run_attempt")

    def test_auxiliary_run_can_have_its_own_run_and_attempt(self) -> None:
        candidate = evidence(event="push")
        bind_provider_proof(candidate)
        warm = next(gate for gate in candidate["gates"] if gate["id"] == "cache-warm")
        warm["run_id"] = 987654321
        warm["run_attempt"] = 2
        artifact = next(item for item in candidate["artifacts"] if item["subject"] == "cache-warm")
        artifact["run_id"] = warm["run_id"]
        artifact["run_attempt"] = warm["run_attempt"]
        result = self.evaluate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertTrue(result["claims"]["all_pipelines_green"])

    def test_missing_auxiliary_is_visible_without_failing_required_ci(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"] = [
            gate for gate in candidate["gates"] if gate["id"] != "github-advanced-security"
        ]
        result = self.evaluate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertTrue(result["claims"]["required_ci_verified"])
        self.assertFalse(result["claims"]["all_pipelines_green"])
        self.assertTrue(any("github-advanced-security is missing" in w for w in result["warnings"]))

    def test_missing_required_gate_still_denies_ci_claim(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"] = [gate for gate in candidate["gates"] if gate["id"] != "build"]
        result = self.evaluate(candidate)
        self.assertFalse(result["valid"])
        self.assertFalse(result["claims"]["required_ci_verified"])
        self.assertTrue(any("missing required inventory gate 'build'" in e for e in result["errors"]))

    def test_auxiliary_artifact_must_match_its_own_run(self) -> None:
        candidate = evidence(event="push")
        bind_provider_proof(candidate)
        warm = next(gate for gate in candidate["gates"] if gate["id"] == "cache-warm")
        warm["run_id"] = 987654321
        self.assert_invalid(candidate, "artifact run_id must equal gate.run_id")

    def test_optional_cancellation_is_visible(self) -> None:
        candidate = evidence(event="push")
        bind_provider_proof(candidate)
        warm = next(gate for gate in candidate["gates"] if gate["id"] == "cache-warm")
        warm.update(status="cancelled", conclusion="cancelled")
        result = self.evaluate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertFalse(result["claims"]["all_pipelines_green"])
        self.assertTrue(any("cache-warm is cancelled" in w for w in result["warnings"]))

    def test_scheduled_docs_skip_is_explicit(self) -> None:
        candidate = evidence(event="schedule")
        bind_provider_proof(candidate)
        skipped = {"docs-build", "docs-deploy"}
        for gate in candidate["gates"]:
            if gate["id"] in skipped:
                gate.update(status="skipped", conclusion="skipped", skip_reason="no recent commits")
                gate["artifact_refs"] = []
        candidate["artifacts"] = [
            artifact for artifact in candidate["artifacts"] if artifact["subject"] not in skipped
        ]
        result = self.evaluate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertFalse(result["claims"]["required_ci_verified"])
        self.assertFalse(result["claims"]["all_pipelines_green"])
        self.assertTrue(any("docs-build skipped" in w for w in result["warnings"]))

    def test_manual_dispatch_applies_only_to_its_workflow(self) -> None:
        ci = evidence(event="workflow_dispatch")
        bind_provider_proof(ci)
        ci_result = self.evaluate(ci)
        self.assertTrue(ci_result["valid"], ci_result)
        self.assertTrue(ci_result["claims"]["required_ci_verified"])
        self.assertTrue(ci_result["claims"]["all_pipelines_green"])
        docs = evidence(event="workflow_dispatch", workflow="Docs")
        bind_provider_proof(docs)
        docs_result = self.evaluate(docs)
        self.assertTrue(docs_result["valid"], docs_result)
        self.assertFalse(docs_result["claims"]["required_ci_verified"])
        self.assertFalse(docs_result["claims"]["all_pipelines_green"])

    def test_inventory_names_match_checked_in_workflow_jobs(self) -> None:
        workflows = {
            "CI": ROOT / ".github/workflows/ci.yml",
            "Cache warm": ROOT / ".github/workflows/cache-warm.yml",
            "Docs": ROOT / ".github/workflows/docs.yml",
        }
        jobs = {
            producer: set(yaml.safe_load(path.read_text(encoding="utf-8"))["jobs"])
            for producer, path in workflows.items()
        }
        for gate in INVENTORY["gates"]:
            producer = gate["producer"]
            if not producer.startswith("github-actions/"):
                continue
            workflow = producer.removeprefix("github-actions/")
            self.assertIn(gate["name"], jobs[workflow], gate)

    def test_cancelled_and_timed_out_required_work_is_rejected(self) -> None:
        for status in ("cancelled", "timed_out"):
            with self.subTest(status=status):
                candidate = evidence()
                bind_provider_proof(candidate)
                candidate["gates"][0]["status"] = status
                candidate["gates"][0]["conclusion"] = status
                self.assert_invalid(candidate, f"required gate is '{status}'")

    def test_neutral_required_work_is_not_success(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"][0]["conclusion"] = "neutral"
        self.assert_invalid(candidate, "passed status requires a successful conclusion")

    def test_missing_pin_digest_and_wrong_artifact_subject_are_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        del candidate["pins"]["pins.json"]
        candidate["artifacts"][0]["subject"] = "roadmap"
        self.assert_invalid(candidate, "evidence.pins must contain")
        self.assert_invalid(candidate, "artifact subject does not match gate id")

    def test_pending_required_gate_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["gates"][2]["status"] = "pending"
        candidate["gates"][2]["conclusion"] = "in_progress"
        self.assert_invalid(candidate, "required gate is 'pending'")

    def test_optional_failure_is_visible_but_not_merge_failure(self) -> None:
        candidate = evidence(event="push")
        bind_provider_proof(candidate)
        cache_gate = next(item for item in candidate["gates"] if item["id"] == "cache-warm")
        cache_gate["status"] = "failed"
        cache_gate["conclusion"] = "failure"
        result = self.evaluate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertTrue(any("cache-warm" in warning for warning in result["warnings"]))

    def test_skipped_required_gate_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        gate = candidate["gates"][0]
        gate["status"] = "skipped"
        gate["conclusion"] = "skipped"
        gate["applicable"] = True
        self.assert_invalid(candidate, "required gate is 'skipped'")

    def test_unknown_schema_is_rejected(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        candidate["schema_version"] = 99
        self.assert_invalid(candidate, "evidence.schema_version must be 4")

    def test_passed_gate_requires_passed_prerequisites(self) -> None:
        candidate = evidence()
        bind_provider_proof(candidate)
        build = candidate["gates"][0]
        build["status"] = "failed"
        build["conclusion"] = "failure"
        self.assert_invalid(candidate, "required gate is 'failed'")


if __name__ == "__main__":
    unittest.main()
