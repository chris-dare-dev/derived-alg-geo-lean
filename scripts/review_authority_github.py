#!/usr/bin/env python3
"""Collect provider-only, read-only PR review metadata for CI1.03.

This is not a trusted review snapshot. CI1.05 must load its policy from the
protected base, join authenticated runtime review records, and revalidate at
admission. In particular, this module never sets the validator's trusted
snapshot source marker.
"""

from __future__ import annotations

from datetime import datetime
from typing import Any

if __package__:
    from . import ci_github_evidence, review_authority
else:
    import ci_github_evidence
    import review_authority


EvidenceError = ci_github_evidence.EvidenceError
GitHubClient = ci_github_evidence.GitHubClient
REVIEW_STATES = {"APPROVED", "CHANGES_REQUESTED", "COMMENTED", "DISMISSED", "PENDING"}


def _object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise EvidenceError(f"{label} is missing or malformed")
    return value


def _positive(value: Any, label: str) -> int:
    if type(value) is not int or value <= 0:
        raise EvidenceError(f"{label} is not a positive integer")
    return value


def _sha(value: Any, label: str) -> str:
    if not isinstance(value, str) or not review_authority.FULL_SHA.fullmatch(value):
        raise EvidenceError(f"{label} is not a full Git SHA")
    return value


def _timestamp(value: Any, label: str) -> str:
    if not isinstance(value, str):
        raise EvidenceError(f"{label} is missing")
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as exc:
        raise EvidenceError(f"{label} is invalid") from exc
    if parsed.tzinfo is None:
        raise EvidenceError(f"{label} has no timezone")
    return value


def _identity(client: GitHubClient, pull_number: int) -> dict[str, Any]:
    branch = client.get_object("/branches/main")
    if branch.get("name") != "main" or branch.get("protected") is not True:
        raise EvidenceError("main is not the reported protected base")
    base_sha = _sha(_object(branch.get("commit"), "main commit").get("sha"), "main commit")
    pull = client.get_object(f"/pulls/{pull_number}")
    if pull.get("number") != pull_number or pull.get("state") != "open":
        raise EvidenceError("pull request is not the requested open PR")
    base = _object(pull.get("base"), "PR base")
    head = _object(pull.get("head"), "PR head")
    base_repo = _object(base.get("repo"), "PR base repository")
    head_repo = _object(head.get("repo"), "PR head repository")
    base_repo_id = _positive(base_repo.get("id"), "PR base repository ID")
    head_repo_id = _positive(head_repo.get("id"), "PR head repository ID")
    if base_repo.get("full_name") != client.repository:
        raise EvidenceError("PR base repository differs from requested repository")
    if base.get("ref") != "main" or _sha(base.get("sha"), "PR base") != base_sha:
        raise EvidenceError("PR base differs from current protected main")
    if head_repo_id == base_repo_id and head_repo.get("full_name") != client.repository:
        raise EvidenceError("same-repository PR head identity is inconsistent")
    changed_files = pull.get("changed_files")
    if type(changed_files) is not int or not 0 <= changed_files < 3000:
        raise EvidenceError("PR changed-file count is invalid or reached GitHub's 3000-file cap")
    author_id = _positive(_object(pull.get("user"), "PR author").get("id"), "PR author ID")
    return {
        "repository": client.repository,
        "pull_number": pull_number,
        "base_commit": base_sha,
        "head_commit": _sha(head.get("sha"), "PR head"),
        "author_actor_id": author_id,
        "from_fork": head_repo_id != base_repo_id,
        "changed_files": changed_files,
    }


def _files(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    files: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in rows:
        path, status = row.get("filename"), row.get("status")
        previous = row.get("previous_filename")
        if (not isinstance(path, str) or not path or path.startswith("/")
                or ".." in path.split("/") or "\\" in path or path in seen):
            raise EvidenceError("PR file path is invalid or duplicated")
        seen.add(path)
        if status not in review_authority.FILE_STATUSES:
            raise EvidenceError(f"PR file {path!r} has an unsupported status")
        if status == "renamed":
            if (not isinstance(previous, str) or not previous or previous == path
                    or previous.startswith("/") or ".." in previous.split("/")
                    or "\\" in previous):
                raise EvidenceError(f"PR file {path!r} has an invalid rename source")
        elif previous is not None:
            raise EvidenceError(f"PR file {path!r} has an unexpected previous name")
        files.append({"path": path, "status": status, "previous_path": previous})
    return files


def _reviews(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    reviews: list[dict[str, Any]] = []
    seen: set[int] = set()
    for row in rows:
        review_id = _positive(row.get("id"), "provider review ID")
        if review_id in seen:
            raise EvidenceError("provider review ID is duplicated")
        seen.add(review_id)
        state = row.get("state")
        if state not in REVIEW_STATES:
            raise EvidenceError(f"provider review {review_id} has an unsupported state")
        submitted = row.get("submitted_at")
        if submitted is not None:
            submitted = _timestamp(submitted, f"provider review {review_id} submitted_at")
        elif state != "PENDING":
            raise EvidenceError(f"provider review {review_id} has no submission time")
        commit = row.get("commit_id")
        if commit is not None:
            commit = _sha(commit, f"provider review {review_id} commit")
        elif state != "PENDING":
            raise EvidenceError(f"provider review {review_id} has no commit")
        reviews.append({
            "id": review_id,
            "actor_id": _positive(_object(row.get("user"), "provider reviewer").get("id"),
                                  "provider reviewer ID"),
            "state": state,
            "submitted_at": submitted,
            "commit_id": commit,
        })
    return sorted(reviews, key=lambda row: row["id"])


def _complete(items: list[dict[str, Any]]) -> dict[str, Any]:
    return {"items": items, "fetched_count": len(items), "complete": True,
            "truncated": False, "next_page": False}


def collect_provider_observation(client: GitHubClient, pull_number: int) -> dict[str, Any]:
    """Read stable GitHub metadata; never assert trusted review authority.

    A 31-page budget allows a complete file enumeration below GitHub's
    3000-file cap. The client's scoped GET pagination fails closed on missing
    or ambiguous final pages. Provider reviews are fetched on both sides of
    the file fetch to catch concurrent submission or dismissal.
    """
    _positive(pull_number, "pull number")
    if client.max_pages < 31:
        raise EvidenceError("review metadata collector needs at least 31 API pages")
    before = _identity(client, pull_number)
    review_path = f"/pulls/{pull_number}/reviews"
    reviews_before = _reviews(client.get_all(review_path))
    files = _files(client.get_all(f"/pulls/{pull_number}/files"))
    reviews_after = _reviews(client.get_all(review_path))
    after = _identity(client, pull_number)
    if before != after:
        raise EvidenceError("protected base or PR identity changed during collection")
    if reviews_before != reviews_after:
        raise EvidenceError("provider reviews changed during collection")
    if len(files) != before["changed_files"]:
        raise EvidenceError("PR file enumeration differs from reported changed-file count")
    return {
        "source": "github-read-only-metadata",
        "event": "pull_request",
        "repository": before["repository"],
        "pull_number": pull_number,
        "base_commit": before["base_commit"],
        "head_commit": before["head_commit"],
        "author_actor_id": before["author_actor_id"],
        "from_fork": before["from_fork"],
        "files": _complete(files),
        "provider_reviews": _complete(reviews_after),
    }
