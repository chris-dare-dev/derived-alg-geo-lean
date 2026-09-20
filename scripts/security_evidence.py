#!/usr/bin/env python3
"""Keep provider/security failures distinct from a verified clean scan."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


ALLOWED_DISPOSITIONS = {
    "verified_scan",
    "provider_failure",
    "replacement_required",
    "retired_with_owner_approval",
}


def load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load security observation {path}: {exc}") from exc


def validate(observation: Any) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(observation, dict):
        return {"valid": False, "errors": ["observation must be an object"]}
    for field in ("workflow", "run_id", "job_id", "provider", "phase", "conclusion", "disposition"):
        if field not in observation or observation[field] in (None, ""):
            errors.append(f"{field} is required")
    disposition = observation.get("disposition")
    if disposition not in ALLOWED_DISPOSITIONS:
        errors.append(f"disposition must be one of {sorted(ALLOWED_DISPOSITIONS)}")
    conclusion = observation.get("conclusion")
    if conclusion != "success" and disposition == "verified_scan":
        errors.append("a non-success provider result cannot be a verified scan")
    if disposition == "verified_scan" and not isinstance(observation.get("coverage_proof"), dict):
        errors.append("verified_scan requires coverage_proof")
    if disposition in {"retired_with_owner_approval", "replacement_required"}:
        if not isinstance(observation.get("owner_decision"), dict):
            errors.append("retirement/replacement requires an explicit owner_decision")
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
