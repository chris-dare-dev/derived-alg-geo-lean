#!/usr/bin/env python3
"""Validate the revision-bound evidence contract for CI gates.

The validator is deliberately provider-neutral.  GitHub adapters may collect
check runs, commit statuses, or workflow metadata, but the merge decision is
made only from this normalized, candidate-bound record.  This module is a
contract surface for the later loop-controller work; it does not call GitHub
and it does not change branch protection.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 2
FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
SHA256 = re.compile(r"^[0-9a-fA-F]{64}$")
BRANCH_REF = re.compile(r"^refs/heads/[A-Za-z0-9._/-]+$")
PULL_REF = re.compile(r"^refs/pull/[1-9][0-9]*/(?:head|merge)$")
GENERIC_REF = re.compile(r"^refs/[A-Za-z0-9._/-]+$")
EVENTS = {"pull_request", "push", "merge_group", "workflow_dispatch"}
PLATFORMS = {"github-actions", "github-checks", "github-status"}
GATE_CLASSES = {
    "required_ci",
    "auxiliary",
    "review_validity",
    "merge_readiness",
    "post_merge_health",
}
STATUSES = {
    "passed",
    "failed",
    "pending",
    "cancelled",
    "timed_out",
    "skipped",
    "unknown",
}
SUCCESS_CONCLUSIONS = {"success", "neutral"}


def _load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ValueError(f"file does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path}: invalid JSON at line {exc.lineno}: {exc.msg}") from exc


def _is_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and bool(FULL_SHA.fullmatch(value))


def _is_sha256(value: Any) -> bool:
    return isinstance(value, str) and bool(SHA256.fullmatch(value))


def _is_positive_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def _as_list(value: Any) -> list[Any]:
    return value if isinstance(value, list) else []


def _valid_ref(event: Any, ref: Any) -> bool:
    if not _is_string(ref) or not GENERIC_REF.fullmatch(ref):
        return False
    if ".." in ref or "//" in ref or "\\" in ref:
        return False
    if event in {"push", "workflow_dispatch", "merge_group"}:
        return bool(BRANCH_REF.fullmatch(ref))
    if event == "pull_request":
        return bool(PULL_REF.fullmatch(ref))
    return False


def _event_applies(definition: dict[str, Any], evidence: dict[str, Any]) -> bool:
    event = evidence.get("event")
    ref = evidence.get("ref")
    for selector in definition.get("applies_to", []):
        if selector == event:
            return True
        if (
            selector.startswith("push:")
            and event == "push"
            and ref == f"refs/heads/{selector[5:]}"
        ):
            return True
        if selector == "workflow_dispatch" and event == "workflow_dispatch":
            return True
    return False


def validate_inventory(inventory: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(inventory, dict):
        return ["inventory must be an object"]
    if inventory.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"inventory.schema_version must be {SCHEMA_VERSION}")
    if not _is_string(inventory.get("repository")):
        errors.append("inventory.repository is required")
    gates = inventory.get("gates")
    if not isinstance(gates, list) or not gates:
        return errors + ["inventory.gates must be a non-empty array"]

    by_id: dict[str, dict[str, Any]] = {}
    names: set[str] = set()
    for index, gate in enumerate(gates):
        prefix = f"inventory.gates[{index}]"
        if not isinstance(gate, dict):
            errors.append(f"{prefix} must be an object")
            continue
        gate_id = gate.get("id")
        name = gate.get("name")
        for field in ("id", "name", "producer", "artifact"):
            if not _is_string(gate.get(field)):
                errors.append(f"{prefix}.{field} is required")
        if gate_id in by_id:
            errors.append(f"{prefix}.id duplicates {gate_id!r}")
        elif _is_string(gate_id):
            by_id[gate_id] = gate
        if _is_string(name) and name in names:
            errors.append(f"{prefix}.name duplicates {name!r}")
        elif _is_string(name):
            names.add(name)
        gate_class = gate.get("class")
        if gate_class not in GATE_CLASSES:
            errors.append(f"{prefix}.class is not a recognized gate class")
        if not isinstance(gate.get("required"), bool):
            errors.append(f"{prefix}.required must be boolean")
        prerequisites = gate.get("prerequisites", [])
        if not isinstance(prerequisites, list) or any(
            not _is_string(item) for item in prerequisites
        ):
            errors.append(f"{prefix}.prerequisites must be an array of names")
        applies_to = gate.get("applies_to")
        if not isinstance(applies_to, list) or not applies_to or any(
            not _is_string(item) for item in applies_to
        ):
            errors.append(f"{prefix}.applies_to must be a non-empty string array")
        platforms = gate.get("platforms")
        if not isinstance(platforms, list) or not platforms or any(
            not _is_string(item) for item in platforms
        ):
            errors.append(f"{prefix}.platforms must be a non-empty string array")
        if gate.get("required") and gate_class not in {
            "required_ci",
            "review_validity",
            "merge_readiness",
        }:
            errors.append(f"{prefix}.required is incompatible with class {gate_class!r}")

    for gate_id, gate in by_id.items():
        for prerequisite in gate.get("prerequisites", []):
            if prerequisite not in by_id:
                errors.append(f"inventory.gates[{gate_id}]: unknown prerequisite {prerequisite!r}")
        if gate.get("required") and not gate.get("prerequisites", []) and gate.get("class") == "merge_readiness":
            errors.append(f"inventory.gates[{gate_id}]: merge_readiness requires prerequisites")
    return errors


def validate_evidence(inventory: Any, evidence: Any) -> dict[str, Any]:
    errors = validate_inventory(inventory)
    warnings: list[str] = []
    if not isinstance(evidence, dict):
        return {"valid": False, "errors": errors + ["evidence must be an object"], "warnings": warnings}

    required_fields = (
        "schema_version",
        "repository",
        "base_commit",
        "head_commit",
        "candidate_commit",
        "candidate_tree",
        "event",
        "ref",
        "revision_binding",
        "platform",
        "run_id",
        "run_attempt",
        "producer",
        "toolchain",
        "artifacts",
        "gates",
    )
    for field in required_fields:
        if field not in evidence:
            errors.append(f"evidence.{field} is required")
    if evidence.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"evidence.schema_version must be {SCHEMA_VERSION}")
    if not _is_string(evidence.get("repository")):
        errors.append("evidence.repository is required")
    if isinstance(inventory, dict) and evidence.get("repository") != inventory.get("repository"):
        errors.append("evidence.repository does not match inventory.repository")
    for field in ("base_commit", "head_commit", "candidate_commit", "candidate_tree"):
        if not _is_sha(evidence.get(field)):
            errors.append(f"evidence.{field} must be a full 40-character commit/tree SHA")
    if evidence.get("event") not in EVENTS:
        errors.append("evidence.event is not recognized")
    if not _valid_ref(evidence.get("event"), evidence.get("ref")):
        errors.append("evidence.ref is not a valid event-bound ref")
    revision_binding = evidence.get("revision_binding")
    if not isinstance(revision_binding, dict):
        errors.append("evidence.revision_binding must be an object")
    else:
        for field in (
            "base_commit",
            "head_commit",
            "candidate_commit",
            "candidate_tree",
            "event",
            "ref",
        ):
            if revision_binding.get(field) != evidence.get(field):
                errors.append(f"evidence.revision_binding.{field} does not match evidence")
    if evidence.get("platform") not in PLATFORMS:
        errors.append("evidence.platform is not recognized")
    if not _is_positive_int(evidence.get("run_id")):
        errors.append("evidence.run_id must be a positive integer")
    if not _is_positive_int(evidence.get("run_attempt")):
        errors.append("evidence.run_attempt must be a positive integer")
    if not _is_string(evidence.get("producer")):
        errors.append("evidence.producer is required")
    if not _is_string(evidence.get("toolchain")):
        errors.append("evidence.toolchain is required")

    artifacts = evidence.get("artifacts")
    artifact_ids: set[str] = set()
    artifact_paths: set[str] = set()
    if not isinstance(artifacts, list):
        errors.append("evidence.artifacts must be an array")
        artifacts = []
    if not artifacts:
        errors.append("evidence.artifacts must be non-empty")
    for index, artifact in enumerate(artifacts):
        prefix = f"evidence.artifacts[{index}]"
        if not isinstance(artifact, dict):
            errors.append(f"{prefix} must be an object")
            continue
        for field in ("id", "path", "sha256", "media_type", "producer", "kind", "commit"):
            if not _is_string(artifact.get(field)):
                errors.append(f"{prefix}.{field} is required")
        for field in ("run_id", "run_attempt", "size_bytes"):
            if not _is_positive_int(artifact.get(field)):
                errors.append(f"{prefix}.{field} must be a positive integer")
        artifact_id = artifact.get("id")
        artifact_path = artifact.get("path")
        if _is_string(artifact_id):
            if artifact_id in artifact_ids:
                errors.append(f"{prefix}.id duplicates {artifact_id!r}")
            else:
                artifact_ids.add(artifact_id)
        if _is_string(artifact_path):
            if artifact_path in artifact_paths:
                errors.append(f"{prefix}.path duplicates {artifact_path!r}")
            else:
                artifact_paths.add(artifact_path)
        if artifact.get("sha256") is not None and not _is_sha256(artifact.get("sha256")):
            errors.append(f"{prefix}.sha256 must be a 64-character SHA-256")
        if artifact.get("commit") is not None and not _is_sha(artifact.get("commit")):
            errors.append(f"{prefix}.commit must be a full SHA")
        elif _is_sha(artifact.get("commit")) and artifact.get("commit", "").lower() != str(
            evidence.get("candidate_commit", "")
        ).lower():
            errors.append(f"{prefix}.commit is not bound to evidence.candidate_commit")

    definitions = {
        gate.get("id"): gate
        for gate in _as_list(inventory.get("gates") if isinstance(inventory, dict) else None)
        if isinstance(gate, dict) and _is_string(gate.get("id"))
    }
    gates = evidence.get("gates")
    if not isinstance(gates, list):
        errors.append("evidence.gates must be an array")
        gates = []
    seen_ids: set[str] = set()
    seen_names: set[str] = set()
    seen_provider_names: set[tuple[str, str]] = set()
    seen_provider_ids: set[str] = set()
    gate_by_id: dict[str, dict[str, Any]] = {}
    for index, gate in enumerate(gates):
        prefix = f"evidence.gates[{index}]"
        if not isinstance(gate, dict):
            errors.append(f"{prefix} must be an object")
            continue
        gate_id = gate.get("id")
        if not _is_string(gate_id):
            errors.append(f"{prefix}.id is required")
            continue
        if gate_id in seen_ids:
            errors.append(f"{prefix}.id duplicates {gate_id!r}")
        seen_ids.add(gate_id)
        gate_by_id[gate_id] = gate
        definition = definitions.get(gate_id)
        if definition is None:
            errors.append(f"{prefix}.id {gate_id!r} is not in the inventory")
            continue
        for field in ("name", "producer", "provider_id", "commit", "status", "conclusion", "applicable"):
            if field not in gate:
                errors.append(f"{prefix}.{field} is required")
        if gate.get("name") != definition.get("name"):
            errors.append(f"{prefix}.name does not match inventory")
        if gate.get("producer") != definition.get("producer"):
            errors.append(f"{prefix}.producer does not match inventory")
        if gate.get("name") in seen_names:
            errors.append(f"{prefix} duplicates provider/check name {gate.get('name')!r}")
        elif _is_string(gate.get("name")):
            seen_names.add(gate.get("name"))
        provider_key = (str(gate.get("producer")), str(gate.get("name")))
        if provider_key in seen_provider_names:
            errors.append(f"{prefix} duplicates provider/name {provider_key!r}")
        seen_provider_names.add(provider_key)
        if not _is_string(gate.get("provider_id")):
            errors.append(f"{prefix}.provider_id is required and must not be inferred")
        elif gate.get("provider_id") in seen_provider_ids:
            errors.append(f"{prefix}.provider_id duplicates {gate.get('provider_id')!r}")
        else:
            seen_provider_ids.add(gate.get("provider_id"))
        if not _is_sha(gate.get("commit")):
            errors.append(f"{prefix}.commit must be a full SHA")
        elif gate.get("commit", "").lower() != str(evidence.get("candidate_commit", "")).lower():
            errors.append(f"{prefix}.commit is not bound to evidence.candidate_commit")
        if gate.get("status") not in STATUSES:
            errors.append(f"{prefix}.status is not recognized")
        if not _is_string(gate.get("conclusion")):
            errors.append(f"{prefix}.conclusion is required")
        if not isinstance(gate.get("applicable"), bool):
            errors.append(f"{prefix}.applicable must be boolean")
        if gate.get("run_id") != evidence.get("run_id"):
            errors.append(f"{prefix}.run_id must equal evidence.run_id")
        if gate.get("run_attempt") != evidence.get("run_attempt"):
            errors.append(f"{prefix}.run_attempt must equal evidence.run_attempt")
        expected_prerequisites = sorted(definition.get("prerequisites", []))
        actual_prerequisites = sorted(gate.get("prerequisites", []))
        if expected_prerequisites != actual_prerequisites:
            errors.append(f"{prefix}.prerequisites do not match inventory")
        if not _event_applies(definition, evidence) and gate.get("applicable"):
            errors.append(f"{prefix} is marked applicable for an event outside inventory applicability")
        if gate.get("applicable") and evidence.get("platform") not in definition.get("platforms", []):
            errors.append(f"{prefix} is marked applicable for an unsupported platform")
        if gate.get("applicable") is False:
            if gate.get("status") != "skipped":
                errors.append(f"{prefix}: non-applicable gate must have status skipped")
            if not _is_string(gate.get("skip_reason")):
                errors.append(f"{prefix}.skip_reason is required for a non-applicable gate")
        elif gate.get("status") == "skipped":
            errors.append(f"{prefix}: applicable gate cannot be skipped")
        if gate.get("status") == "passed" and gate.get("conclusion") not in SUCCESS_CONCLUSIONS:
            errors.append(f"{prefix}: passed status requires a successful conclusion")
        if gate.get("applicable") and gate.get("status") != "passed" and definition.get("required"):
            errors.append(f"{prefix}: required gate is {gate.get('status')!r}, not passed")
        if gate.get("status") == "failed" and not definition.get("required"):
            warnings.append(f"optional gate {gate_id} failed; merge readiness is unaffected")
        refs = gate.get("artifact_refs", [])
        if not isinstance(refs, list) or any(ref not in artifact_ids for ref in refs):
            errors.append(f"{prefix}.artifact_refs contain an unknown artifact")
            refs = []
        if gate.get("applicable") and not refs:
            errors.append(f"{prefix}.artifact_refs must be non-empty for an applicable gate")
        if not gate.get("applicable") and refs:
            errors.append(f"{prefix}.artifact_refs must be empty for a non-applicable gate")
        for artifact_id in refs:
            artifact = next(
                (
                    item
                    for item in artifacts
                    if isinstance(item, dict) and item.get("id") == artifact_id
                ),
                None,
            )
            if not isinstance(artifact, dict):
                continue
            if artifact.get("producer") != definition.get("producer"):
                errors.append(f"{prefix}: artifact producer does not match inventory")
            if artifact.get("kind") != definition.get("artifact"):
                errors.append(f"{prefix}: artifact kind does not match inventory")
            if artifact.get("run_id") != evidence.get("run_id"):
                errors.append(f"{prefix}: artifact run_id must equal evidence.run_id")
            if artifact.get("run_attempt") != evidence.get("run_attempt"):
                errors.append(f"{prefix}: artifact run_attempt must equal evidence.run_attempt")

    for gate_id, definition in definitions.items():
        if gate_id not in seen_ids:
            errors.append(f"evidence is missing inventory gate {gate_id!r}")
        if _event_applies(definition, evidence) and gate_id in gate_by_id:
            if not gate_by_id[gate_id].get("applicable"):
                errors.append(f"inventory gate {gate_id!r} applies to this event but evidence marked it non-applicable")

    for gate_id, gate in gate_by_id.items():
        if gate.get("status") != "passed":
            continue
        for prerequisite in gate.get("prerequisites", []):
            prerequisite_gate = gate_by_id.get(prerequisite)
            if prerequisite_gate is None or prerequisite_gate.get("status") != "passed":
                errors.append(f"evidence gate {gate_id!r} passed without passed prerequisite {prerequisite!r}")

    return {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "required_gates": sorted(
            gate_id for gate_id, definition in definitions.items() if definition.get("required")
        ),
        "observed_gates": sorted(seen_ids),
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        inventory = _load(args.inventory)
        evidence = _load(args.evidence)
        result = validate_evidence(inventory, evidence)
    except ValueError as exc:
        print(json.dumps({"valid": False, "errors": [str(exc)], "warnings": []}, indent=2))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
