#!/usr/bin/env python3
"""Focused tests for the revision-bound CI evidence contract."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts import ci_contract


ROOT = Path(__file__).resolve().parents[2]
INVENTORY = json.loads((ROOT / "scripts/ci_gate_inventory.json").read_text())
SHA_A = "a" * 40
SHA_B = "b" * 40
SHA_C = "c" * 40


def evidence(*, event: str = "pull_request") -> dict:
    gates = []
    artifacts = []
    ref = "refs/heads/main" if event == "push" else "refs/pull/1/merge"
    for index, definition in enumerate(INVENTORY["gates"], start=1):
        applicable = ci_contract._event_applies(definition, {"event": event, "ref": ref})
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
                    "commit": SHA_C,
                    "run_id": 35532316123,
                    "run_attempt": 1,
                }
            )
        gates.append(
            {
                "id": definition["id"],
                "name": definition["name"],
                "producer": definition["producer"],
                "provider_id": f"run-3553-job-{index}",
                "commit": SHA_C,
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
        "schema_version": 2,
        "repository": INVENTORY["repository"],
        "base_commit": SHA_A,
        "head_commit": SHA_B,
        "candidate_commit": SHA_C,
        "candidate_tree": SHA_C,
        "event": event,
        "ref": ref,
        "revision_binding": {
            "base_commit": SHA_A,
            "head_commit": SHA_B,
            "candidate_commit": SHA_C,
            "candidate_tree": SHA_C,
            "event": event,
            "ref": ref,
        },
        "platform": "github-actions",
        "run_id": 35532316123,
        "run_attempt": 1,
        "producer": "github-actions/CI",
        "toolchain": "lean-toolchain@fixture",
        "artifacts": artifacts,
        "gates": gates,
    }


class ContractTests(unittest.TestCase):
    def assert_invalid(self, candidate: dict, fragment: str) -> None:
        result = ci_contract.validate_evidence(INVENTORY, candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any(fragment in error for error in result["errors"]), result)

    def test_inventory_is_complete_and_well_formed(self) -> None:
        self.assertEqual(ci_contract.validate_inventory(INVENTORY), [])

    def test_revision_bound_evidence_passes(self) -> None:
        result = ci_contract.validate_evidence(INVENTORY, evidence())
        self.assertTrue(result["valid"], result)
        self.assertEqual(result["warnings"], [])

    def test_missing_candidate_identity_is_rejected(self) -> None:
        candidate = evidence()
        del candidate["candidate_tree"]
        self.assert_invalid(candidate, "evidence.candidate_tree is required")

    def test_push_ref_must_be_provider_canonical(self) -> None:
        candidate = evidence(event="push")
        candidate["ref"] = "main"
        self.assert_invalid(candidate, "valid event-bound ref")

    def test_revision_binding_mismatch_is_rejected(self) -> None:
        candidate = evidence()
        candidate["revision_binding"]["candidate_commit"] = SHA_B
        self.assert_invalid(candidate, "revision_binding.candidate_commit")

    def test_applicable_gate_requires_bound_artifact(self) -> None:
        candidate = evidence()
        candidate["gates"][0]["artifact_refs"] = []
        self.assert_invalid(candidate, "artifact_refs must be non-empty")

    def test_gate_from_stale_revision_is_rejected(self) -> None:
        candidate = evidence()
        candidate["gates"][0]["commit"] = SHA_B
        self.assert_invalid(candidate, "not bound to evidence.candidate_commit")

    def test_duplicate_provider_name_is_rejected(self) -> None:
        candidate = evidence()
        duplicate = copy.deepcopy(candidate["gates"][1])
        duplicate["id"] = "roadmap"
        candidate["gates"].append(duplicate)
        self.assert_invalid(candidate, "duplicates")

    def test_pending_required_gate_is_rejected(self) -> None:
        candidate = evidence()
        candidate["gates"][2]["status"] = "pending"
        candidate["gates"][2]["conclusion"] = "in_progress"
        self.assert_invalid(candidate, "required gate is 'pending'")

    def test_optional_failure_is_visible_but_not_merge_failure(self) -> None:
        candidate = evidence(event="push")
        cache_gate = next(item for item in candidate["gates"] if item["id"] == "cache-warm")
        cache_gate["status"] = "failed"
        cache_gate["conclusion"] = "failure"
        result = ci_contract.validate_evidence(INVENTORY, candidate)
        self.assertTrue(result["valid"], result)
        self.assertTrue(any("cache-warm" in warning for warning in result["warnings"]))

    def test_skipped_required_gate_is_rejected(self) -> None:
        candidate = evidence()
        gate = candidate["gates"][0]
        gate["status"] = "skipped"
        gate["conclusion"] = "skipped"
        gate["applicable"] = True
        self.assert_invalid(candidate, "required gate is 'skipped'")

    def test_unknown_schema_is_rejected(self) -> None:
        candidate = evidence()
        candidate["schema_version"] = 99
        self.assert_invalid(candidate, "evidence.schema_version must be 2")

    def test_passed_gate_requires_passed_prerequisites(self) -> None:
        candidate = evidence()
        build = candidate["gates"][0]
        build["status"] = "failed"
        build["conclusion"] = "failure"
        self.assert_invalid(candidate, "required gate is 'failed'")


if __name__ == "__main__":
    unittest.main()
