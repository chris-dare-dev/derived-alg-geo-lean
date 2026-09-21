#!/usr/bin/env python3
from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts import security_evidence


FIXTURE = json.loads(
    (Path(__file__).parent / "fixtures/github-advanced-security/provider-failure.json").read_text()
)


class SecurityEvidenceTests(unittest.TestCase):
    def test_provider_failure_is_not_a_clean_scan(self) -> None:
        result = security_evidence.validate(FIXTURE)
        self.assertTrue(result["valid"], result)
        self.assertFalse(result["verified_scan"])

    def test_failed_provider_cannot_claim_verified_scan(self) -> None:
        candidate = copy.deepcopy(FIXTURE)
        candidate["disposition"] = "verified_scan"
        result = security_evidence.validate(candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any("non-success" in item for item in result["errors"]))

    def test_verified_scan_requires_complete_bound_proof(self) -> None:
        candidate = copy.deepcopy(FIXTURE)
        candidate.update(
            {
                "conclusion": "success",
                "candidate_commit": "a" * 40,
                "disposition": "verified_scan",
                "scanner_findings": [],
                "coverage_proof": {
                    "workflow": candidate["workflow"],
                    "run_id": candidate["run_id"],
                    "job_id": candidate["job_id"],
                    "candidate_commit": "a" * 40,
                    "scope": ["pull_request", "push:main"],
                    "scanner": "github-advanced-security",
                    "finding_count": 0,
                    "result_artifact": {
                        "sha256": "b" * 64,
                        "size_bytes": 512,
                        "media_type": "application/json",
                        "producer": candidate["provider"],
                    },
                    "negative_fixture": {
                        "id": "known-vulnerable-fixture",
                        "executed": True,
                        "expected_finding": True,
                        "observed_finding": True,
                    },
                },
            }
        )
        result = security_evidence.validate(candidate)
        self.assertTrue(result["valid"], result)
        self.assertTrue(result["verified_scan"])

    def test_empty_coverage_proof_is_rejected(self) -> None:
        candidate = copy.deepcopy(FIXTURE)
        candidate["conclusion"] = "success"
        candidate["disposition"] = "verified_scan"
        candidate["coverage_proof"] = {}
        result = security_evidence.validate(candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any("candidate_commit" in item for item in result["errors"]))

    def test_retirement_requires_owner_decision(self) -> None:
        candidate = copy.deepcopy(FIXTURE)
        candidate["disposition"] = "retired_with_owner_approval"
        result = security_evidence.validate(candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any("owner_decision" in item for item in result["errors"]))

    def test_owner_decision_is_revision_bound(self) -> None:
        candidate = copy.deepcopy(FIXTURE)
        candidate["disposition"] = "retired_with_owner_approval"
        candidate["owner_decision"] = {
            "owner": "repository-owner",
            "decision": "retire",
            "reason": "provider is unavailable",
            "decided_at": "2026-09-21T12:00:00Z",
            "follow_up": "#1440",
            "reviewed_revision": "c" * 40,
        }
        result = security_evidence.validate(candidate)
        self.assertTrue(result["valid"], result)


if __name__ == "__main__":
    unittest.main()
