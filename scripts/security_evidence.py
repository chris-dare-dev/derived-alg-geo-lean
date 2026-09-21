#!/usr/bin/env python3
"""Keep provider/security failures distinct from a verified clean scan."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ALLOWED_DISPOSITIONS = {
    "verified_scan",
    "provider_failure",
    "replacement_required",
    "retired_with_owner_approval",
}
FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
SHA256 = re.compile(r"^[0-9a-fA-F]{64}$")


def load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load security observation {path}: {exc}") from exc


def _positive_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and bool(FULL_SHA.fullmatch(value))


def _is_sha256(value: Any) -> bool:
    return isinstance(value, str) and bool(SHA256.fullmatch(value))


def _required_strings(value: dict[str, Any], fields: tuple[str, ...], prefix: str) -> list[str]:
    return [f"{prefix}.{field} is required" for field in fields if not isinstance(value.get(field), str) or not value[field].strip()]


def _validate_coverage_proof(observation: dict[str, Any], proof: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(proof, dict):
        return ["verified_scan requires coverage_proof"]
    errors.extend(
        _required_strings(
            proof,
            ("workflow", "scanner"),
            "coverage_proof",
        )
    )
    if proof.get("workflow") != observation.get("workflow"):
        errors.append("coverage_proof.workflow must match workflow")
    if proof.get("run_id") != observation.get("run_id"):
        errors.append("coverage_proof.run_id must match run_id")
    if proof.get("job_id") != observation.get("job_id"):
        errors.append("coverage_proof.job_id must match job_id")
    if not _is_sha(observation.get("candidate_commit")):
        errors.append("candidate_commit must be a full SHA for a verified scan")
    elif proof.get("candidate_commit") != observation.get("candidate_commit"):
        errors.append("coverage_proof.candidate_commit must match candidate_commit")
    if not _positive_int(proof.get("run_id")):
        errors.append("coverage_proof.run_id must be a positive integer")
    if not _positive_int(proof.get("job_id")):
        errors.append("coverage_proof.job_id must be a positive integer")
    if not _is_sha(proof.get("candidate_commit")):
        errors.append("coverage_proof.candidate_commit must be a full SHA")
    scope = proof.get("scope")
    if not isinstance(scope, list) or not scope or any(
        not isinstance(item, str) or not item.strip() for item in scope
    ):
        errors.append("coverage_proof.scope must be a non-empty string array")
    result_artifact = proof.get("result_artifact")
    if not isinstance(result_artifact, dict):
        errors.append("coverage_proof.result_artifact must be an object")
    else:
        errors.extend(_required_strings(result_artifact, ("media_type", "producer"), "coverage_proof.result_artifact"))
        if not _is_sha256(result_artifact.get("sha256")):
            errors.append("coverage_proof.result_artifact.sha256 must be a SHA-256")
        if not _positive_int(result_artifact.get("size_bytes")):
            errors.append("coverage_proof.result_artifact.size_bytes must be positive")
    negative_fixture = proof.get("negative_fixture")
    if not isinstance(negative_fixture, dict):
        errors.append("coverage_proof.negative_fixture must be an object")
    else:
        errors.extend(_required_strings(negative_fixture, ("id",), "coverage_proof.negative_fixture"))
        for field in ("executed", "expected_finding", "observed_finding"):
            if negative_fixture.get(field) is not True:
                errors.append(f"coverage_proof.negative_fixture.{field} must be true")
    findings = observation.get("scanner_findings")
    if not isinstance(findings, list):
        errors.append("verified_scan requires scanner_findings to be an array")
    elif findings:
        errors.append("verified_scan cannot claim a clean result with scanner findings")
    if proof.get("finding_count") != 0:
        errors.append("coverage_proof.finding_count must be zero for verified_scan")
    return errors


def _validate_owner_decision(observation: dict[str, Any], decision: Any) -> list[str]:
    if not isinstance(decision, dict):
        return ["retirement/replacement requires an explicit owner_decision"]
    errors = _required_strings(
        decision,
        ("owner", "decision", "reason", "decided_at", "follow_up"),
        "owner_decision",
    )
    expected = "retire" if observation.get("disposition") == "retired_with_owner_approval" else "replace"
    if decision.get("decision") != expected:
        errors.append(f"owner_decision.decision must be {expected!r}")
    if not _is_sha(decision.get("reviewed_revision")):
        errors.append("owner_decision.reviewed_revision must be a full SHA")
    return errors


def validate(observation: Any) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(observation, dict):
        return {"valid": False, "errors": ["observation must be an object"]}
    for field in ("workflow", "run_id", "job_id", "provider", "phase", "conclusion", "disposition"):
        if field not in observation or observation[field] in (None, ""):
            errors.append(f"{field} is required")
    for field in ("run_id", "job_id"):
        if not _positive_int(observation.get(field)):
            errors.append(f"{field} must be a positive integer")
    disposition = observation.get("disposition")
    if disposition not in ALLOWED_DISPOSITIONS:
        errors.append(f"disposition must be one of {sorted(ALLOWED_DISPOSITIONS)}")
    conclusion = observation.get("conclusion")
    if conclusion != "success" and disposition == "verified_scan":
        errors.append("a non-success provider result cannot be a verified scan")
    if disposition == "verified_scan":
        errors.extend(_validate_coverage_proof(observation, observation.get("coverage_proof")))
    if disposition in {"retired_with_owner_approval", "replacement_required"}:
        errors.extend(_validate_owner_decision(observation, observation.get("owner_decision")))
    if disposition == "provider_failure" and not observation.get("error"):
        errors.append("provider_failure requires the observed provider error")
    findings = observation.get("scanner_findings")
    if findings is not None and not isinstance(findings, list):
        errors.append("scanner_findings must be an array when present")
    return {"valid": not errors, "errors": errors, "verified_scan": disposition == "verified_scan" and not errors}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("observation", type=Path)
    args = parser.parse_args(argv)
    try:
        result = validate(load(args.observation))
    except ValueError as exc:
        print(json.dumps({"valid": False, "errors": [str(exc)]}, indent=2))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
