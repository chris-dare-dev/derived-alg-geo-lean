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

    def test_retirement_requires_owner_decision(self) -> None:
        candidate = copy.deepcopy(FIXTURE)
        candidate["disposition"] = "retired_with_owner_approval"
        result = security_evidence.validate(candidate)
        self.assertFalse(result["valid"])
        self.assertTrue(any("owner_decision" in item for item in result["errors"]))


if __name__ == "__main__":
    unittest.main()
