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
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 4
FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
SHA256 = re.compile(r"^[0-9a-fA-F]{64}$")
BRANCH_REF = re.compile(r"^refs/heads/[A-Za-z0-9._/-]+$")
PULL_REF = re.compile(r"^refs/pull/[1-9][0-9]*/(?:head|merge)$")
GENERIC_REF = re.compile(r"^refs/[A-Za-z0-9._/-]+$")
EVENTS = {"pull_request", "push", "merge_group", "workflow_dispatch", "schedule"}
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
SUCCESS_CONCLUSIONS = {"success"}
REQUIRED_PINS = {"lean-toolchain", "lake-manifest.json", "pins.json"}


def _load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ValueError(f"file does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path}: invalid JSON at line {exc.lineno}: {exc.msg}") from exc


def _load_trusted_inventory(repo_root: Path, commit: str) -> Any:
    """Read policy bytes from an immutable Git object selected by the adapter."""
    if not _is_sha(commit):
        raise ValueError("trusted base commit must be a full Git SHA")
    result = subprocess.run(
        ["git", "-C", str(repo_root), "show", f"{commit}:scripts/ci_gate_inventory.json"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode:
        raise ValueError("trusted base commit has no readable gate inventory")
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError(f"trusted gate inventory is invalid JSON at line {exc.lineno}") from exc


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


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _valid_ref(event: Any, ref: Any) -> bool:
    if not _is_string(event) or not _is_string(ref) or not GENERIC_REF.fullmatch(ref):
        return False
    if ".." in ref or "//" in ref or "\\" in ref:
        return False
    if event in {"push", "schedule"}:
        return ref == "refs/heads/main"
    if event in {"workflow_dispatch", "merge_group"}:
        return bool(BRANCH_REF.fullmatch(ref))
    if event == "pull_request":
        return bool(PULL_REF.fullmatch(ref))
    return False


def _event_applies(definition: dict[str, Any], evidence: dict[str, Any]) -> bool:
    event = evidence.get("event")
    ref = evidence.get("ref")
    for selector in _as_list(definition.get("applies_to")):
        if not _is_string(selector):
            continue
        if selector == event:
            return True
        if (
            selector.startswith("push:")
            and event == "push"
            and ref == f"refs/heads/{selector[5:]}"
        ):
            return True
        if (
            selector.startswith("workflow_dispatch:")
            and event == "workflow_dispatch"
            and evidence.get("producer") == f"github-actions/{selector.split(':', 1)[1]}"
        ):
            return True
    return False


def _validate_provider_binding(evidence: dict[str, Any], errors: list[str]) -> None:
    proof = evidence.get("provider_binding")
    if not isinstance(proof, dict):
        errors.append("evidence.provider_binding must be an object")
        return
    required = (
        "source",
        "repository",
        "producer",
        "run_id",
        "run_attempt",
        "event",
        "ref",
        "commit",
        "tree",
        "parents",
        "proof_sha256",
    )
    for field in required:
        if field not in proof:
            errors.append(f"evidence.provider_binding.{field} is required")
    if not _is_string(proof.get("source")) or proof.get("source") not in {
        "github-api", "provider-adapter"
    }:
        errors.append("evidence.provider_binding.source is not a trusted adapter source")
    if proof.get("repository") != evidence.get("repository"):
        errors.append("evidence.provider_binding.repository does not match evidence.repository")
    if proof.get("producer") != evidence.get("producer"):
        errors.append("evidence.provider_binding.producer does not match evidence.producer")
    for field in ("run_id", "run_attempt"):
        if proof.get(field) != evidence.get(field):
            errors.append(f"evidence.provider_binding.{field} does not match evidence")
    for field in ("event", "ref"):
        if proof.get(field) != evidence.get(field):
            errors.append(f"evidence.provider_binding.{field} does not match evidence")
    if proof.get("commit") != evidence.get("candidate_commit"):
        errors.append("evidence.provider_binding.commit does not match candidate_commit")
    if proof.get("tree") != evidence.get("candidate_tree"):
        errors.append("evidence.provider_binding.tree does not match candidate_tree")
    if not _is_sha(proof.get("commit")):
        errors.append("evidence.provider_binding.commit must be a full SHA")
    if not _is_sha(proof.get("tree")):
        errors.append("evidence.provider_binding.tree must be a full SHA")
    parents = proof.get("parents")
    if not isinstance(parents, list) or any(not _is_sha(parent) for parent in parents):
        errors.append("evidence.provider_binding.parents must be a SHA array")
        parents = []
    elif len(set(parents)) != len(parents):
        errors.append("evidence.provider_binding.parents must not contain duplicates")
    proof_body = {key: value for key, value in proof.items() if key != "proof_sha256"}
    if proof.get("proof_sha256") != _canonical_sha256(proof_body):
        errors.append("evidence.provider_binding.proof_sha256 does not bind the provider proof")

    event = evidence.get("event")
    ref = evidence.get("ref", "")
    head = evidence.get("head_commit")
    base = evidence.get("base_commit")
    candidate = evidence.get("candidate_commit")
    if _is_string(event) and event in {"push", "workflow_dispatch", "schedule"}:
        if candidate != head:
            errors.append("candidate_commit must equal head_commit for a direct ref event")
    elif event == "pull_request":
        if ref.endswith("/head"):
            if candidate != head:
                errors.append("candidate_commit must equal head_commit for a pull request head ref")
        elif ref.endswith("/merge"):
            if candidate == base or candidate == head or base not in parents or head not in parents:
                errors.append(
                    "pull request merge candidate must be a provider-proven merge commit "
                    "with both base_commit and head_commit as parents"
                )
    elif event == "merge_group":
        if candidate == head or head not in parents:
            errors.append("merge_group candidate must prove head_commit as a merge parent")


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
    producer_names: set[tuple[str, str]] = set()
    workflows = {
        producer.removeprefix("github-actions/")
        for gate in gates
        if isinstance(gate, dict)
        for producer in [gate.get("producer")]
        if _is_string(producer) and producer.startswith("github-actions/")
    }
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
        if not _is_string(gate_id):
            errors.append(f"{prefix}.id must be a non-empty string")
        elif gate_id in by_id:
            errors.append(f"{prefix}.id duplicates {gate_id!r}")
        else:
            by_id[gate_id] = gate
        producer_name = (gate.get("producer"), name)
        if all(_is_string(part) for part in producer_name):
            if producer_name in producer_names:
                errors.append(f"{prefix} duplicates producer/name {producer_name!r}")
            producer_names.add(producer_name)
        gate_class = gate.get("class")
        if not _is_string(gate_class) or gate_class not in GATE_CLASSES:
            errors.append(f"{prefix}.class is not a recognized gate class")
        if not isinstance(gate.get("required"), bool):
            errors.append(f"{prefix}.required must be boolean")
        if not _is_string(gate.get("run_binding")) or gate.get("run_binding") not in {
            "primary", "independent", "status", "check"
        }:
            errors.append(f"{prefix}.run_binding must be primary, independent, status or check")
        artifact_kind = gate.get("artifact")
        if gate.get("run_binding") == "status" and not (
            _is_string(artifact_kind) and artifact_kind.startswith("commit-status:")
        ):
            errors.append(f"{prefix}.artifact must identify a commit status")
        if gate.get("run_binding") == "check" and not (
            _is_string(artifact_kind) and artifact_kind.startswith("check-run:")
        ):
            errors.append(f"{prefix}.artifact must identify a check run")
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
        else:
            for selector in applies_to:
                if selector in {"pull_request", "merge_group", "schedule", "push:main"}:
                    continue
                if (
                    selector.startswith("workflow_dispatch:")
                    and selector.removeprefix("workflow_dispatch:") in workflows
                ):
                    continue
                errors.append(f"{prefix}.applies_to has unsupported selector {selector!r}")
        platforms = gate.get("platforms")
        if not isinstance(platforms, list) or not platforms or any(
            not _is_string(item) or item not in PLATFORMS for item in platforms
        ):
            errors.append(f"{prefix}.platforms must be a non-empty recognized platform array")
        if gate.get("required") and (
            not _is_string(gate_class)
            or gate_class not in {"required_ci", "review_validity", "merge_readiness"}
        ):
            errors.append(f"{prefix}.required is incompatible with class {gate_class!r}")

    for gate_id, gate in by_id.items():
        for prerequisite in _as_list(gate.get("prerequisites")):
            if not _is_string(prerequisite):
                continue
            if prerequisite not in by_id:
                errors.append(f"inventory.gates[{gate_id}]: unknown prerequisite {prerequisite!r}")
        if gate.get("required") and not gate.get("prerequisites", []) and gate.get("class") == "merge_readiness":
            errors.append(f"inventory.gates[{gate_id}]: merge_readiness requires prerequisites")
    return errors


def validate_evidence(
    inventory: Any,
    evidence: Any,
    *,
    trusted_base_commit: str | None = None,
    trusted_head_commit: str | None = None,
    trusted_inventory_sha256: str | None = None,
) -> dict[str, Any]:
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
        "policy_binding",
        "provider_binding",
        "platform",
        "run_id",
        "run_attempt",
        "producer",
        "toolchain",
        "pins",
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
    # These two values must come from a trusted provider adapter, not from the
    # PR checkout or from the evidence being validated. A missing anchor denies
    # admission even when the record is internally self-consistent.
    if not _is_sha(trusted_base_commit):
        errors.append("trusted_base_commit must be supplied by the protected-base adapter")
    elif evidence.get("base_commit") != trusted_base_commit:
        errors.append("evidence.base_commit is stale relative to trusted_base_commit")
    if not _is_sha(trusted_head_commit):
        errors.append("trusted_head_commit must be supplied by the provider adapter")
    elif evidence.get("head_commit") != trusted_head_commit:
        errors.append("evidence.head_commit is stale relative to trusted_head_commit")
    if not _is_sha256(trusted_inventory_sha256):
        errors.append("trusted_inventory_sha256 must be supplied by the protected-base adapter")
    elif _canonical_sha256(inventory) != trusted_inventory_sha256:
        errors.append("inventory does not match trusted_inventory_sha256")
    policy_binding = evidence.get("policy_binding")
    if not isinstance(policy_binding, dict):
        errors.append("evidence.policy_binding must be an object")
    else:
        if policy_binding.get("source") != "protected-base":
            errors.append("evidence.policy_binding.source must be protected-base")
        if policy_binding.get("commit") != trusted_base_commit:
            errors.append("evidence.policy_binding.commit does not match trusted_base_commit")
        if policy_binding.get("inventory_sha256") != trusted_inventory_sha256:
            errors.append("evidence.policy_binding.inventory_sha256 does not match trusted_inventory_sha256")
    for field in ("base_commit", "head_commit", "candidate_commit", "candidate_tree"):
        if not _is_sha(evidence.get(field)):
            errors.append(f"evidence.{field} must be a full 40-character commit/tree SHA")
    if not _is_string(evidence.get("event")) or evidence.get("event") not in EVENTS:
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
    _validate_provider_binding(evidence, errors)
    if not _is_string(evidence.get("platform")) or evidence.get("platform") not in PLATFORMS:
        errors.append("evidence.platform is not recognized")
    if not _is_positive_int(evidence.get("run_id")):
        errors.append("evidence.run_id must be a positive integer")
    if not _is_positive_int(evidence.get("run_attempt")):
        errors.append("evidence.run_attempt must be a positive integer")
    if not _is_string(evidence.get("producer")):
        errors.append("evidence.producer is required")
    if not _is_string(evidence.get("toolchain")):
        errors.append("evidence.toolchain is required")
    pins = evidence.get("pins")
    if not isinstance(pins, dict) or set(pins) != REQUIRED_PINS or any(
        not _is_sha256(value) for value in pins.values()
    ):
        errors.append("evidence.pins must contain SHA-256 digests for lean-toolchain, lake-manifest.json and pins.json")

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
        for field in ("id", "path", "sha256", "media_type", "producer", "kind", "commit", "subject"):
            if not _is_string(artifact.get(field)):
                errors.append(f"{prefix}.{field} is required")
        if not _is_positive_int(artifact.get("size_bytes")):
            errors.append(f"{prefix}.size_bytes must be a positive integer")
        for field in ("run_id", "run_attempt"):
            if field in artifact and not _is_positive_int(artifact.get(field)):
                errors.append(f"{prefix}.{field} must be a positive integer when present")
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
        elif _is_sha(artifact.get("commit")) and artifact.get("commit", "").lower() not in {
            str(evidence.get("candidate_commit", "")).lower(),
            str(evidence.get("head_commit", "")).lower(),
        }:
            errors.append(f"{prefix}.commit is not bound to evidence candidate or head")

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
    seen_provider_names: set[tuple[str, str]] = set()
    seen_provider_ids: set[tuple[str, str]] = set()
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
        for field in ("name", "producer", "platform", "provider_id", "commit", "status", "conclusion", "applicable"):
            if field not in gate:
                errors.append(f"{prefix}.{field} is required")
        if gate.get("name") != definition.get("name"):
            errors.append(f"{prefix}.name does not match inventory")
        if gate.get("producer") != definition.get("producer"):
            errors.append(f"{prefix}.producer does not match inventory")
        provider_key = (str(gate.get("producer")), str(gate.get("name")))
        if provider_key in seen_provider_names:
            errors.append(f"{prefix} duplicates provider/name {provider_key!r}")
        seen_provider_names.add(provider_key)
        if not _is_string(gate.get("provider_id")):
            errors.append(f"{prefix}.provider_id is required and must not be inferred")
        elif (str(gate.get("producer")), gate.get("provider_id")) in seen_provider_ids:
            errors.append(f"{prefix}.provider_id duplicates within producer {gate.get('provider_id')!r}")
        else:
            seen_provider_ids.add((str(gate.get("producer")), gate.get("provider_id")))
        expected_commit = (
            evidence.get("head_commit") if definition.get("run_binding") == "check"
            else evidence.get("candidate_commit")
        )
        if not _is_sha(gate.get("commit")):
            errors.append(f"{prefix}.commit must be a full SHA")
        elif gate.get("commit", "").lower() != str(expected_commit).lower():
            subject_name = "head_commit" if definition.get("run_binding") == "check" else "candidate_commit"
            errors.append(f"{prefix}.commit is not bound to evidence.{subject_name}")
        if not _is_string(gate.get("status")) or gate.get("status") not in STATUSES:
            errors.append(f"{prefix}.status is not recognized")
        if not _is_string(gate.get("conclusion")):
            errors.append(f"{prefix}.conclusion is required")
        if not isinstance(gate.get("applicable"), bool):
            errors.append(f"{prefix}.applicable must be boolean")
        if definition.get("run_binding") in {"status", "check"}:
            if "run_id" in gate or "run_attempt" in gate:
                errors.append(f"{prefix}: runless observation must not claim a workflow run")
        else:
            if not _is_positive_int(gate.get("run_id")):
                errors.append(f"{prefix}.run_id must be a positive integer")
            if not _is_positive_int(gate.get("run_attempt")):
                errors.append(f"{prefix}.run_attempt must be a positive integer")
        if definition.get("run_binding") == "primary":
            if gate.get("applicable") and gate.get("producer") != evidence.get("producer"):
                errors.append(f"{prefix}.producer must equal evidence.producer for a primary run")
            if gate.get("run_id") != evidence.get("run_id"):
                errors.append(f"{prefix}.run_id must equal evidence.run_id")
            if gate.get("run_attempt") != evidence.get("run_attempt"):
                errors.append(f"{prefix}.run_attempt must equal evidence.run_attempt")
        expected_prerequisites = sorted(
            item for item in _as_list(definition.get("prerequisites")) if _is_string(item)
        )
        actual_prerequisites = sorted(
            item for item in _as_list(gate.get("prerequisites")) if _is_string(item)
        )
        if not isinstance(gate.get("prerequisites"), list) or len(actual_prerequisites) != len(
            gate.get("prerequisites", [])
        ):
            errors.append(f"{prefix}.prerequisites must be a string array")
        if expected_prerequisites != actual_prerequisites:
            errors.append(f"{prefix}.prerequisites do not match inventory")
        if not _event_applies(definition, evidence) and gate.get("applicable"):
            errors.append(f"{prefix} is marked applicable for an event outside inventory applicability")
        if not _is_string(gate.get("platform")) or gate.get("platform") not in PLATFORMS:
            errors.append(f"{prefix}.platform is not recognized")
        if gate.get("applicable") and gate.get("platform") not in _as_list(definition.get("platforms")):
            errors.append(f"{prefix} is marked applicable for an unsupported platform")
        if gate.get("applicable") is False:
            if gate.get("status") != "skipped":
                errors.append(f"{prefix}: non-applicable gate must have status skipped")
            if not _is_string(gate.get("skip_reason")):
                errors.append(f"{prefix}.skip_reason is required for a non-applicable gate")
        elif gate.get("status") == "skipped":
            if definition.get("required"):
                errors.append(f"{prefix}: applicable required gate cannot be skipped")
            elif not _is_string(gate.get("skip_reason")):
                errors.append(f"{prefix}.skip_reason is required for a skipped auxiliary gate")
            else:
                warnings.append(f"optional gate {gate_id} skipped: {gate.get('skip_reason')}")
        if gate.get("status") == "passed" and (
            not _is_string(gate.get("conclusion"))
            or gate.get("conclusion") not in SUCCESS_CONCLUSIONS
        ):
            errors.append(f"{prefix}: passed status requires a successful conclusion")
        if gate.get("applicable") and gate.get("status") != "passed" and definition.get("required"):
            errors.append(f"{prefix}: required gate is {gate.get('status')!r}, not passed")
        if gate.get("status") == "failed" and not definition.get("required"):
            warnings.append(f"optional gate {gate_id} failed; merge readiness is unaffected")
        elif (
            gate.get("applicable")
            and not definition.get("required")
            and _is_string(gate.get("status"))
            and gate.get("status") in {"pending", "cancelled", "timed_out", "unknown"}
        ):
            warnings.append(f"optional gate {gate_id} is {gate.get('status')}")
        refs = gate.get("artifact_refs", [])
        if not isinstance(refs, list) or any(
            not _is_string(ref) or ref not in artifact_ids for ref in refs
        ):
            errors.append(f"{prefix}.artifact_refs contain an unknown artifact")
            refs = []
        if gate.get("applicable") and gate.get("status") != "skipped" and not refs:
            errors.append(f"{prefix}.artifact_refs must be non-empty for an observed applicable gate")
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
            if artifact.get("subject") != gate_id:
                errors.append(f"{prefix}: artifact subject does not match gate id")
            if artifact.get("commit") != expected_commit:
                errors.append(f"{prefix}: artifact commit does not match gate revision")
            if definition.get("run_binding") in {"status", "check"}:
                if "run_id" in artifact or "run_attempt" in artifact:
                    errors.append(f"{prefix}: runless artifact must not claim a workflow run")
            else:
                if artifact.get("run_id") != gate.get("run_id"):
                    errors.append(f"{prefix}: artifact run_id must equal gate.run_id")
                if artifact.get("run_attempt") != gate.get("run_attempt"):
                    errors.append(f"{prefix}: artifact run_attempt must equal gate.run_attempt")

    for gate_id, definition in definitions.items():
        if gate_id not in seen_ids and _event_applies(definition, evidence):
            if definition.get("required"):
                errors.append(f"evidence is missing required inventory gate {gate_id!r}")
            else:
                warnings.append(f"optional gate {gate_id} is missing")
        if _event_applies(definition, evidence) and gate_id in gate_by_id:
            if not gate_by_id[gate_id].get("applicable"):
                errors.append(f"inventory gate {gate_id!r} applies to this event but evidence marked it non-applicable")

    for gate_id, gate in gate_by_id.items():
        if gate.get("status") != "passed":
            continue
        for prerequisite in _as_list(gate.get("prerequisites")):
            prerequisite_gate = gate_by_id.get(prerequisite)
            if prerequisite_gate is None or prerequisite_gate.get("status") != "passed":
                errors.append(f"evidence gate {gate_id!r} passed without passed prerequisite {prerequisite!r}")

    auxiliary_healthy = not any(
        definition.get("class") == "auxiliary"
        and _event_applies(definition, evidence)
        and (gate_by_id.get(gate_id, {}).get("status") != "passed")
        for gate_id, definition in definitions.items()
    )
    required_ci_applicable = any(
        definition.get("required") and _event_applies(definition, evidence)
        for definition in definitions.values()
    )
    return {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "claims": {
            "required_ci_verified": not errors and required_ci_applicable,
            "auxiliary_checks_healthy": auxiliary_healthy,
            "all_pipelines_green": not errors and required_ci_applicable and auxiliary_healthy,
            "merge_readiness": "not_evaluated",
            "post_merge_health": "not_evaluated",
        },
        "required_gates": sorted(
            gate_id for gate_id, definition in definitions.items() if definition.get("required")
        ),
        "observed_gates": sorted(seen_ids),
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--trusted-base-commit", required=True)
    parser.add_argument("--trusted-head-commit", required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        inventory = _load_trusted_inventory(args.repo_root, args.trusted_base_commit)
        evidence = _load(args.evidence)
        result = validate_evidence(
            inventory,
            evidence,
            trusted_base_commit=args.trusted_base_commit,
            trusted_head_commit=args.trusted_head_commit,
            trusted_inventory_sha256=_canonical_sha256(inventory),
        )
    except ValueError as exc:
        print(json.dumps({"valid": False, "errors": [str(exc)], "warnings": []}, indent=2))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
