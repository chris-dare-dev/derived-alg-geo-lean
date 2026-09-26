#!/usr/bin/env python3
"""Exact-revision publication receipts for the loop delivery adapters."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any

if __package__:
    from . import ci_contract
else:
    import ci_contract


FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
RECEIPT_SCHEMA = "derived-alg-geo-lean.publication-receipt/v1"
MERGE_READINESS = {"ready", "blocked", "stale", "not_evaluated"}
POST_MERGE_HEALTH = {"passed", "failed", "pending", "unknown", "not_evaluated"}


class PublicationError(ValueError):
    """A publication cannot be bound to the reviewed revision and provider."""


def _sha(value: Any, label: str) -> str:
    if not isinstance(value, str) or not FULL_SHA.fullmatch(value):
        raise PublicationError(f"{label} must be a full Git SHA")
    return value.lower()


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def _provider_check_summary(check: dict[str, Any]) -> dict[str, Any]:
    app = check.get("app") if isinstance(check.get("app"), dict) else {}
    return {
        "id": check.get("id"),
        "name": check.get("name"),
        "head_sha": check.get("head_sha"),
        "status": check.get("status"),
        "conclusion": check.get("conclusion"),
        "url": check.get("html_url"),
        "app_id": app.get("id"),
        "app_slug": app.get("slug"),
    }


def receipt_digest(receipt: dict[str, Any]) -> str:
    payload = {key: value for key, value in receipt.items() if key != "receipt_sha256"}
    return hashlib.sha256(_canonical(payload)).hexdigest()


def evaluate_merge_readiness(
    pr: dict[str, Any],
    *,
    checked_base: str,
    checked_head: str,
    reviewed_tree: str,
    head_tree: str,
    required_ci_verified: bool,
) -> dict[str, Any]:
    """Classify merge readiness against the revisions and review actually checked.

    `UNSTABLE` can still be mergeable when required CI is verified and optional
    checks are red. The separate auxiliary claim remains visible in the receipt.
    """

    checked_base = _sha(checked_base, "checked base")
    checked_head = _sha(checked_head, "checked head")
    reviewed_tree = _sha(reviewed_tree, "reviewed tree")
    head_tree = _sha(head_tree, "PR head tree")
    reasons: list[str] = []
    status = "blocked"

    if pr.get("state") != "OPEN":
        reasons.append("pull request is not open")
    if pr.get("isDraft") is True:
        reasons.append("pull request is a draft")
    if pr.get("baseRefOid") != checked_base:
        reasons.append("base moved after CI evidence was collected")
        status = "stale"
    if pr.get("headRefOid") != checked_head:
        reasons.append("head moved after CI evidence was collected")
        status = "stale"
    if head_tree != reviewed_tree:
        reasons.append("PR head tree differs from the reviewed tree; renew review")
        status = "stale"
    if not required_ci_verified:
        reasons.append("required CI evidence is not verified")
    if pr.get("reviewDecision") in {"CHANGES_REQUESTED", "REVIEW_REQUIRED"}:
        reasons.append(f"review decision is {pr['reviewDecision']}")

    merge_state = pr.get("mergeStateStatus")
    if merge_state == "BEHIND":
        reasons.append("PR branch is behind the protected base")
        status = "stale"
    elif merge_state in {"BLOCKED", "DIRTY"}:
        reasons.append(f"provider merge state is {merge_state}")
    elif merge_state not in {"CLEAN", "UNSTABLE"}:
        reasons.append("provider merge state is missing or inconclusive")
        status = "not_evaluated"

    if not reasons:
        status = "ready"
    return {
        "status": status,
        "reasons": reasons,
        "merge_state": merge_state,
        "checked_base": checked_base,
        "checked_head": checked_head,
        "reviewed_tree": reviewed_tree,
        "head_tree": head_tree,
    }


def build_receipt(
    *,
    repository: str,
    pr_number: int,
    pr_url: str,
    reviewed_commit: str,
    reviewed_tree: str,
    premerge_evidence: dict[str, Any],
    premerge_validation: dict[str, Any],
    premerge_observations: dict[str, Any],
    premerge_inventory: dict[str, Any],
    published_commit: str,
    published_tree: str,
    published_parents: list[str],
    published_base_is_ancestor: bool,
    merge_readiness: dict[str, Any],
    post_merge_health: dict[str, Any],
) -> dict[str, Any]:
    """Bind provider publication to the final reviewed tree and premerge CI."""

    reviewed_commit = _sha(reviewed_commit, "reviewed commit")
    reviewed_tree = _sha(reviewed_tree, "reviewed tree")
    published_commit = _sha(published_commit, "published commit")
    published_tree = _sha(published_tree, "published tree")
    base = _sha(premerge_evidence.get("base_commit"), "premerge base")
    head = _sha(premerge_evidence.get("head_commit"), "premerge head")
    candidate = _sha(premerge_evidence.get("candidate_commit"), "CI candidate")
    candidate_tree = _sha(premerge_evidence.get("candidate_tree"), "CI candidate tree")
    parents = [_sha(parent, "published parent") for parent in published_parents]
    claims = premerge_validation.get("claims")
    if premerge_validation.get("valid") is not True or not isinstance(claims, dict):
        raise PublicationError("premerge CI evidence is not valid")
    if claims.get("required_ci_verified") is not True:
        raise PublicationError("required premerge CI is not verified")
    if merge_readiness.get("status") != "ready":
        if merge_readiness.get("status") != "not_evaluated":
            raise PublicationError("publication receipt has blocked or stale merge readiness")
    health = post_merge_health.get("status")
    if health not in POST_MERGE_HEALTH:
        raise PublicationError("post-merge health status is malformed")
    if not parents or published_base_is_ancestor is not True:
        raise PublicationError("published commit does not bind the checked base as an ancestor")
    if reviewed_tree != candidate_tree or published_tree != reviewed_tree:
        raise PublicationError(
            "published tree differs from the final reviewed tree; renewed review is required"
        )
    if merge_readiness.get("checked_head") != head or merge_readiness.get("checked_base") != base:
        raise PublicationError("merge readiness is bound to different revisions")
    if merge_readiness.get("reviewed_tree") != reviewed_tree:
        raise PublicationError("merge readiness is bound to a different reviewed tree")

    auxiliary_healthy = claims.get("auxiliary_checks_healthy") is True
    all_pipelines_green = claims.get("all_pipelines_green") is True
    definitions = {
        gate.get("id"): gate
        for gate in premerge_inventory.get("gates", [])
        if isinstance(gate, dict) and isinstance(gate.get("id"), str)
    }
    gate_records = []
    for gate in premerge_evidence.get("gates", []):
        if not isinstance(gate, dict):
            raise PublicationError("premerge evidence contains a malformed gate")
        definition = definitions.get(gate.get("id"), {})
        gate_records.append(
            {
                "id": gate.get("id"),
                "name": gate.get("name"),
                "provider_id": gate.get("provider_id"),
                "commit": gate.get("commit"),
                "status": gate.get("status"),
                "conclusion": gate.get("conclusion"),
                "class": definition.get("class"),
                "required": definition.get("required"),
            }
        )
    applicable_auxiliary_gate_ids = sorted(
        gate_id
        for gate_id, definition in definitions.items()
        if definition.get("class") == "auxiliary"
        and ci_contract._event_applies(
            definition,
            {
                "event": premerge_evidence.get("event"),
                "ref": premerge_evidence.get("ref"),
                "producer": premerge_evidence.get("producer"),
            },
        )
    )
    observed_provider_ids = {
        str(gate.get("provider_id"))
        for gate in premerge_evidence.get("gates", [])
        if isinstance(gate, dict)
    }
    workflow_run = premerge_observations.get("workflow_run")
    if not isinstance(workflow_run, dict):
        raise PublicationError("premerge provider workflow run is missing")
    check_suites = premerge_observations.get("suites")
    check_runs = premerge_observations.get("check_runs")
    statuses = premerge_observations.get("statuses")
    if not all(isinstance(value, list) for value in (check_suites, check_runs, statuses)):
        raise PublicationError("premerge check-run or status observations are malformed")
    unclassified_check_ids = sorted(
        str(check.get("id"))
        for check in check_runs
        if str(check.get("id")) not in observed_provider_ids
    )
    unclassified_status_ids = sorted(str(item.get("id")) for item in statuses)
    all_pipelines_green = (
        claims.get("all_pipelines_green") is True
        and not unclassified_check_ids
        and not unclassified_status_ids
    )
    run_identity_fields = (
        "id", "run_attempt", "check_suite_id", "head_sha", "event", "path",
        "status", "conclusion", "html_url",
    )
    associations = workflow_run.get("pull_requests")
    matching_associations = [
        {
            "number": item.get("number"),
            "base_sha": (item.get("base") or {}).get("sha") if isinstance(item.get("base"), dict) else None,
            "head_sha": (item.get("head") or {}).get("sha") if isinstance(item.get("head"), dict) else None,
        }
        for item in associations or []
        if isinstance(item, dict)
        and item.get("number") == pr_number
        and isinstance(item.get("base"), dict)
        and item["base"].get("sha") == base
        and isinstance(item.get("head"), dict)
        and item["head"].get("sha") == head
    ]
    if not matching_associations:
        raise PublicationError("premerge workflow observation lacks the PR/base/head association")
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "repository": repository,
        "pull_request": {"number": pr_number, "url": pr_url},
        "review": {"commit": reviewed_commit, "tree": reviewed_tree},
        "premerge": {
            "base_commit": base,
            "head_commit": head,
            "candidate_commit": candidate,
            "candidate_tree": candidate_tree,
            # Preserve the CI1.01 contract record so an independent verifier
            # can re-run the canonical inventory/evidence validation instead
            # of treating this receipt's flattened gate list as its authority.
            "contract_evidence": premerge_evidence,
            "run_id": premerge_evidence.get("run_id"),
            "run_attempt": premerge_evidence.get("run_attempt"),
            "producer": premerge_evidence.get("producer"),
            "provider_proof_sha256": premerge_evidence.get("provider_binding", {}).get(
                "proof_sha256"
            ),
            "provider_binding": premerge_evidence.get("provider_binding"),
            "event": premerge_evidence.get("event"),
            "ref": premerge_evidence.get("ref"),
            "required_gate_ids": premerge_validation.get("required_gates", []),
            "applicable_auxiliary_gate_ids": applicable_auxiliary_gate_ids,
            "gates": gate_records,
            "workflow_run": {
                **{field: workflow_run.get(field) for field in run_identity_fields},
                "pull_requests": matching_associations,
            },
            "check_suites": [
                {
                    "id": suite.get("id"),
                    "head_sha": suite.get("head_sha"),
                    "app_id": (suite.get("app") or {}).get("id") if isinstance(suite.get("app"), dict) else None,
                    "app_slug": (suite.get("app") or {}).get("slug") if isinstance(suite.get("app"), dict) else None,
                }
                for suite in check_suites
            ],
            "check_runs": sorted(
                (_provider_check_summary(check) for check in check_runs),
                key=lambda item: str(item.get("id")),
            ),
            "statuses": sorted(
                (
                    {
                        "id": item.get("id"),
                        "sha": item.get("sha"),
                        "context": item.get("context"),
                        "state": item.get("state"),
                        "updated_at": item.get("updated_at"),
                        "target_url": item.get("target_url"),
                    }
                    for item in statuses
                ),
                key=lambda item: str(item.get("id")),
            ),
            "unclassified_check_ids": unclassified_check_ids,
            "unclassified_status_ids": unclassified_status_ids,
            "claims": {
                "required_ci_verified": True,
                "auxiliary_checks_healthy": auxiliary_healthy,
                "all_pipelines_green": all_pipelines_green,
            },
        },
        "publication": {
            "commit": published_commit,
            "tree": published_tree,
            "parents": parents,
            "checked_base_is_ancestor": True,
            "provider_merge_commit": published_commit,
        },
        "merge_readiness": merge_readiness,
        "post_merge_health": post_merge_health,
        "claims": {
            "code_complete": True,
            "published": True,
            "required_ci_verified": True,
            "auxiliary_checks_healthy": auxiliary_healthy,
            "all_pipelines_green": all_pipelines_green,
            "merge_readiness": merge_readiness.get("status"),
            "post_merge_health": health,
            "operationally_verified": health == "passed",
        },
    }
    receipt["receipt_sha256"] = receipt_digest(receipt)
    return receipt


def verify_receipt(receipt: dict[str, Any]) -> None:
    """Check receipt integrity and its revision/claim relationships."""

    if receipt.get("schema") != RECEIPT_SCHEMA:
        raise PublicationError("unsupported publication receipt schema")
    if receipt.get("receipt_sha256") != receipt_digest(receipt):
        raise PublicationError("publication receipt digest mismatch")
    review = receipt.get("review")
    publication = receipt.get("publication")
    premerge = receipt.get("premerge")
    claims = receipt.get("claims")
    if not all(isinstance(value, dict) for value in (review, publication, premerge, claims)):
        raise PublicationError("publication receipt is missing a required object")
    reviewed_tree = _sha(review.get("tree"), "reviewed tree")
    published_tree = _sha(publication.get("tree"), "published tree")
    published_commit = _sha(publication.get("commit"), "published commit")
    candidate_tree = _sha(premerge.get("candidate_tree"), "CI candidate tree")
    _sha(review.get("commit"), "reviewed commit")
    base = _sha(premerge.get("base_commit"), "premerge base")
    _sha(premerge.get("head_commit"), "premerge head")
    candidate = _sha(premerge.get("candidate_commit"), "premerge candidate")
    parents = publication.get("parents")
    if not isinstance(parents, list) or not parents:
        raise PublicationError("publication receipt has no published parent")
    normalized_parents = [_sha(parent, "published parent") for parent in parents]
    if publication.get("checked_base_is_ancestor") is not True:
        raise PublicationError("receipt does not prove the checked base is a published ancestor")
    if published_tree != reviewed_tree or candidate_tree != reviewed_tree:
        raise PublicationError("receipt does not preserve the reviewed tree")
    if publication.get("provider_merge_commit") != published_commit:
        raise PublicationError("provider merge commit does not match publication commit")
    provider_binding = premerge.get("provider_binding")
    if not isinstance(provider_binding, dict):
        raise PublicationError("receipt is missing the premerge provider binding")
    proof = {key: value for key, value in provider_binding.items() if key != "proof_sha256"}
    if (
        premerge.get("provider_proof_sha256") != provider_binding.get("proof_sha256")
        or hashlib.sha256(_canonical(proof)).hexdigest() != provider_binding.get("proof_sha256")
        or provider_binding.get("source") != "github-api"
        or provider_binding.get("repository") != receipt.get("repository")
        or provider_binding.get("producer") != premerge.get("producer")
        or provider_binding.get("run_id") != premerge.get("run_id")
        or provider_binding.get("run_attempt") != premerge.get("run_attempt")
        or provider_binding.get("event") != premerge.get("event")
        or provider_binding.get("ref") != premerge.get("ref")
        or provider_binding.get("commit") != candidate
        or provider_binding.get("tree") != candidate_tree
        or provider_binding.get("parents") != [base, premerge.get("head_commit")]
    ):
        raise PublicationError("premerge provider proof does not bind the receipt revisions")
    if claims.get("required_ci_verified") is not True or premerge.get("claims", {}).get(
        "required_ci_verified"
    ) is not True:
        raise PublicationError("receipt overstates or omits required CI evidence")
    if claims.get("auxiliary_checks_healthy") != premerge.get("claims", {}).get(
        "auxiliary_checks_healthy"
    ):
        raise PublicationError("receipt changed the auxiliary-check claim")
    if claims.get("all_pipelines_green") != premerge.get("claims", {}).get(
        "all_pipelines_green"
    ):
        raise PublicationError("receipt changed the all-pipelines claim")
    contract_evidence = premerge.get("contract_evidence")
    if not isinstance(contract_evidence, dict):
        raise PublicationError("receipt is missing its CI1.01 contract evidence")
    if any(
        contract_evidence.get(field) != premerge.get(receipt_field)
        for field, receipt_field in (
            ("base_commit", "base_commit"),
            ("head_commit", "head_commit"),
            ("candidate_commit", "candidate_commit"),
            ("candidate_tree", "candidate_tree"),
            ("run_id", "run_id"),
            ("run_attempt", "run_attempt"),
            ("event", "event"),
            ("ref", "ref"),
            ("producer", "producer"),
        )
    ):
        raise PublicationError("receipt CI1.01 revisions or producer are inconsistent")
    if contract_evidence.get("provider_binding") != provider_binding:
        raise PublicationError("receipt CI1.01 provider binding is inconsistent")
    health = receipt.get("post_merge_health", {}).get("status")
    if health not in POST_MERGE_HEALTH or claims.get("post_merge_health") != health:
        raise PublicationError("receipt post-merge health claim is inconsistent")
    if claims.get("operationally_verified") is not (health == "passed"):
        raise PublicationError("receipt overstates operational verification")
    readiness = receipt.get("merge_readiness", {}).get("status")
    if readiness not in {"ready", "not_evaluated"} or claims.get("merge_readiness") != readiness:
        raise PublicationError("receipt overstates or misbinds merge readiness")
    gate_records = premerge.get("gates")
    if not isinstance(gate_records, list):
        raise PublicationError("receipt has no premerge gate records")
    gate_by_id = {gate.get("id"): gate for gate in gate_records if isinstance(gate, dict)}
    workflow_run = premerge.get("workflow_run")
    if not isinstance(workflow_run, dict) or (
        workflow_run.get("id") != premerge.get("run_id")
        or workflow_run.get("run_attempt") != premerge.get("run_attempt")
        or workflow_run.get("head_sha") != premerge.get("head_commit")
        or workflow_run.get("event") != premerge.get("event")
        or workflow_run.get("path") != ".github/workflows/ci.yml"
        or workflow_run.get("status") != "completed"
        or workflow_run.get("conclusion") != "success"
    ):
        raise PublicationError("premerge workflow run identity is inconsistent")
    pull_requests = workflow_run.get("pull_requests")
    pr_number = receipt.get("pull_request", {}).get("number")
    if not isinstance(pull_requests, list) or not any(
        isinstance(item, dict)
        and item.get("number") == pr_number
        and item.get("base_sha") == base
        and item.get("head_sha") == premerge.get("head_commit")
        for item in pull_requests
    ):
        raise PublicationError("premerge workflow run is not bound to the receipt PR")
    required_gate_ids = premerge.get("required_gate_ids")
    if not isinstance(required_gate_ids, list) or any(
        gate_by_id.get(gate_id, {}).get("status") != "passed" for gate_id in required_gate_ids
    ):
        raise PublicationError("receipt required gate records are incomplete or not green")
    optional_auxiliary_green = all(
        gate.get("status") == "passed"
        for gate in gate_records
        if gate.get("class") == "auxiliary" and gate.get("required") is False
    )
    applicable_auxiliary_ids = premerge.get("applicable_auxiliary_gate_ids")
    if not isinstance(applicable_auxiliary_ids, list) or any(
        gate_by_id.get(gate_id, {}).get("status") != "passed"
        for gate_id in applicable_auxiliary_ids
    ):
        optional_auxiliary_green = False
    if claims.get("auxiliary_checks_healthy") is True and not optional_auxiliary_green:
        raise PublicationError("receipt overstates auxiliary-check health")
    if claims.get("all_pipelines_green") is True and (
        claims.get("auxiliary_checks_healthy") is not True
        or premerge.get("unclassified_check_ids")
        or premerge.get("unclassified_status_ids")
    ):
        raise PublicationError("receipt overstates the all-pipelines-green claim")
