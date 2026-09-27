#!/usr/bin/env python3
"""Validate revision-bound technical review receipts against a trusted live snapshot.

This is a pure validator. The caller must obtain the policy from the protected
base and a complete, read-only provider/runtime snapshot outside the PR checkout.
It does not grant GitHub approval or establish a human reviewer's independence.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any


SCHEMA_VERSION = 1
POLICY_ID = "ci1-single-collaborator-v1"
REQUIRED_ROLES = (
    "mathematics-adversary",
    "repository-boundary-adversary",
    "abstraction-adversary",
    "mathlib-reviewer",
)
PASSING_VERDICTS = {"PASS", "PASS_WITH_LIFT"}
FULL_SHA = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
FILE_STATUSES = {"added", "modified", "removed", "renamed"}


def digest(value: Any) -> str:
    """Hash a JSON value with stable key order and Unicode encoding."""
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def _sha(value: Any) -> bool:
    return isinstance(value, str) and bool(FULL_SHA.fullmatch(value))


def _digest(value: Any) -> bool:
    return isinstance(value, str) and bool(SHA256.fullmatch(value))


def _positive_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def _nonempty(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _complete_page(snapshot: dict[str, Any], name: str, errors: list[str]) -> list[Any]:
    page = snapshot.get(name)
    if not isinstance(page, dict):
        errors.append(f"snapshot.{name} must be a complete collection")
        return []
    items = page.get("items")
    if not isinstance(items, list):
        errors.append(f"snapshot.{name}.items must be an array")
        return []
    if page.get("complete") is not True or page.get("truncated") is not False:
        errors.append(f"snapshot.{name} is incomplete or truncated")
    if not isinstance(page.get("fetched_count"), int) or isinstance(page.get("fetched_count"), bool) or page["fetched_count"] != len(items):
        errors.append(f"snapshot.{name}.fetched_count does not match items")
    return items


def _changed_files(items: list[Any], errors: list[str]) -> str:
    normalized = []
    paths = set()
    for index, item in enumerate(items):
        if not isinstance(item, dict):
            errors.append(f"snapshot.files[{index}] must be an object")
            continue
        path, status, previous = item.get("path"), item.get("status"), item.get("previous_path")
        if not _nonempty(path) or path.startswith("/") or ".." in path.split("/") or "\\" in path:
            errors.append(f"snapshot.files[{index}].path is invalid")
            continue
        if path in paths:
            errors.append(f"snapshot.files[{index}].path is duplicated")
        paths.add(path)
        if not isinstance(status, str) or status not in FILE_STATUSES:
            errors.append(f"snapshot.files[{index}].status is invalid")
            continue
        if status == "renamed":
            if not _nonempty(previous) or previous == path or previous.startswith("/") or ".." in previous.split("/") or "\\" in previous:
                errors.append(f"snapshot.files[{index}].previous_path is invalid")
                continue
        elif previous is not None:
            errors.append(f"snapshot.files[{index}].previous_path is only valid for a rename")
            continue
        normalized.append({"path": path, "status": status, "previous_path": previous})
    return digest(sorted(normalized, key=lambda item: (item["path"], item["status"])))


def validate_receipt(policy: Any, receipt: Any, snapshot: Any) -> dict[str, Any]:
    """Check a receipt against live identities and all current review records.

    ``policy`` and ``snapshot`` are trusted inputs supplied by an external
    adapter; accepting either from PR content would defeat this contract.
    """
    errors: list[str] = []
    claims = {"technical_reviews_recorded": False, "github_approval_observed": False,
              "independent_human_approval": False, "merge_group_verified": False}
    if not all(isinstance(value, dict) for value in (policy, receipt, snapshot)):
        return {"valid": False, "errors": ["policy, receipt and snapshot must be objects"], "claims": claims}

    if (type(policy.get("schema_version")) is not int
            or policy.get("schema_version") != SCHEMA_VERSION
            or policy.get("policy_id") != POLICY_ID):
        errors.append("trusted policy version is unsupported")
    if policy.get("required_roles") != list(REQUIRED_ROLES):
        errors.append("trusted policy must retain all four review roles")
    required_approvals = policy.get("required_provider_approvals")
    if not isinstance(required_approvals, int) or isinstance(required_approvals, bool) or required_approvals < 0:
        errors.append("trusted policy.required_provider_approvals is invalid")
        required_approvals = 0
    shared_actor_ids = policy.get("shared_credential_actor_ids")
    if not isinstance(shared_actor_ids, list) or any(not _positive_int(actor) for actor in shared_actor_ids):
        errors.append("trusted policy.shared_credential_actor_ids is invalid")
        shared_actor_ids = []
    policy_sha256 = digest(policy)

    if snapshot.get("source") != "trusted-read-only-adapter":
        errors.append("snapshot must come from a trusted read-only adapter")
    if not isinstance(snapshot.get("from_fork"), bool):
        errors.append("snapshot.from_fork must be a provider-observed boolean")
    if snapshot.get("event") != "pull_request":
        errors.append("merge-group and non-PR review admission is unsupported")
    for field in ("repository", "pull_number", "head_commit", "base_commit"):
        value = snapshot.get(field)
        if (field == "pull_number" and not _positive_int(value)) or (
            field in {"head_commit", "base_commit"} and not _sha(value)
        ) or (field == "repository" and not _nonempty(value)):
            errors.append(f"snapshot.{field} is invalid")
        if receipt.get(field) != value:
            errors.append(f"receipt.{field} is stale or mismatched")
    if type(receipt.get("schema_version")) is not int or receipt.get("schema_version") != SCHEMA_VERSION:
        errors.append("receipt.schema_version is unsupported")
    if receipt.get("policy_id") != policy.get("policy_id") or receipt.get("policy_sha256") != policy_sha256:
        errors.append("receipt policy binding is stale or mismatched")
    if snapshot.get("policy_sha256") != policy_sha256:
        errors.append("live trusted policy binding is stale or mismatched")
    files = _complete_page(snapshot, "files", errors)
    records = _complete_page(snapshot, "technical_reviews", errors)
    provider_reviews = _complete_page(snapshot, "provider_reviews", errors)
    files_sha256 = _changed_files(files, errors)
    if receipt.get("files_sha256") != files_sha256:
        errors.append("receipt file-set binding is stale or mismatched")

    selected = receipt.get("technical_review_ids")
    if not isinstance(selected, list) or any(not _nonempty(item) for item in selected) or len(selected) != len(set(selected)):
        errors.append("receipt.technical_review_ids must be distinct review IDs")
        selected = []
    by_id: dict[str, dict[str, Any]] = {}
    for index, record in enumerate(records):
        if not isinstance(record, dict) or not _nonempty(record.get("id")):
            errors.append(f"snapshot.technical_reviews[{index}] has no review ID")
            continue
        if record["id"] in by_id:
            errors.append(f"snapshot.technical_reviews[{index}] duplicates a review ID")
        by_id[record["id"]] = record
    latest_role: dict[str, dict[str, Any]] = {}
    latest_identity: dict[str, dict[str, Any]] = {}
    for record in records:
        if isinstance(record, dict):
            if isinstance(record.get("role"), str):
                latest_role[record["role"]] = record
            if isinstance(record.get("reviewer_identity"), str):
                latest_identity[record["reviewer_identity"]] = record
    roles: dict[str, str] = {}
    for review_id in selected:
        record = by_id.get(review_id)
        if record is None:
            errors.append(f"review {review_id} is absent from the complete live snapshot")
            continue
        role = record.get("role")
        identity = record.get("reviewer_identity")
        if role not in REQUIRED_ROLES or not _nonempty(identity):
            errors.append(f"review {review_id} has no recognized role and identity")
            continue
        if role in roles or identity in roles.values():
            errors.append(f"review {review_id} repeats a role or reviewer identity")
        roles[role] = identity
        verdict = record.get("verdict")
        if record.get("state") != "active" or not isinstance(verdict, str) or verdict not in PASSING_VERDICTS:
            errors.append(f"review {review_id} is revoked or does not pass")
        if latest_role.get(role) is not record or latest_identity.get(identity) is not record:
            errors.append(f"review {review_id} is superseded by a later technical review")
        for field, expected in (("head_commit", snapshot.get("head_commit")),
                                ("base_commit", snapshot.get("base_commit")),
                                ("policy_sha256", policy_sha256),
                                ("files_sha256", files_sha256)):
            if record.get(field) != expected:
                errors.append(f"review {review_id} has stale {field}")
        if not _digest(record.get("artifact_sha256")):
            errors.append(f"review {review_id} has no verified artifact digest")
    missing = set(REQUIRED_ROLES) - set(roles)
    if missing:
        errors.append("missing technical review roles: " + ", ".join(sorted(missing)))

    provider_ids = receipt.get("provider_review_ids", [])
    if not isinstance(provider_ids, list) or any(not _positive_int(item) for item in provider_ids) or len(provider_ids) != len(set(provider_ids)):
        errors.append("receipt.provider_review_ids must be distinct provider IDs")
        provider_ids = []
    latest: dict[int, dict[str, Any]] = {}
    seen_ids = set()
    for index, review in enumerate(provider_reviews):
        if not isinstance(review, dict) or not _positive_int(review.get("id")) or not _positive_int(review.get("actor_id")):
            errors.append(f"snapshot.provider_reviews[{index}] has invalid identity")
            continue
        if review["id"] in seen_ids:
            errors.append(f"snapshot.provider_reviews[{index}] duplicates an ID")
        seen_ids.add(review["id"])
        latest[review["actor_id"]] = review
    approvals = set()
    for review_id in provider_ids:
        match = next((review for review in provider_reviews if isinstance(review, dict) and review.get("id") == review_id), None)
        if match is None:
            errors.append(f"provider review {review_id} is absent from the complete live snapshot")
            continue
        actor = match.get("actor_id")
        if not _positive_int(actor):
            errors.append(f"provider review {review_id} has invalid actor identity")
            continue
        if latest.get(actor) is not match or match.get("state") != "APPROVED" or match.get("commit_id") != snapshot.get("head_commit"):
            errors.append(f"provider review {review_id} is revoked, superseded or stale")
            continue
        if actor == snapshot.get("author_actor_id") or actor in shared_actor_ids:
            errors.append(f"provider review {review_id} uses author or shared credential")
            continue
        approvals.add(actor)
    if len(approvals) < required_approvals:
        errors.append("trusted policy requires additional current provider approvals")
    if receipt.get("independent_human_approval") is True:
        errors.append("shared-credential evidence cannot assert independent human approval")

    valid = not errors
    claims["technical_reviews_recorded"] = valid and not missing
    claims["github_approval_observed"] = valid and bool(approvals)
    return {"valid": valid, "errors": errors, "claims": claims}
