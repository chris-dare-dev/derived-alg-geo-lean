#!/usr/bin/env python3
"""Adversarial fixtures for the CI1 reviewer-authority receipt contract."""

from __future__ import annotations

import hashlib
import unittest

from scripts import review_authority


HEAD = "a" * 40
BASE = "b" * 40
NEXT = "c" * 40


def fixture() -> tuple[dict, dict, dict]:
    policy = {
        "schema_version": 1,
        "policy_id": review_authority.POLICY_ID,
        "required_roles": list(review_authority.REQUIRED_ROLES),
        "required_provider_approvals": 0,
        "shared_credential_actor_ids": [234062931],
    }
    files = [{"path": "scripts/review_authority.py", "status": "added"}]
    files_sha256 = review_authority.digest([
        {"path": files[0]["path"], "status": files[0]["status"], "previous_path": None}
    ])
    records = [
        {
            "id": f"review-{index}",
            "role": role,
            "reviewer_identity": f"agent-{index}",
            "sequence": index,
            "state": "active",
            "verdict": "PASS",
            "head_commit": HEAD,
            "base_commit": BASE,
            "policy_sha256": review_authority.digest(policy),
            "files_sha256": files_sha256,
            "artifact_text": f"Reviewed by agent-{index}.\nReviewed commit: {HEAD}\nClose: PASS\n",
        }
        for index, role in enumerate(review_authority.REQUIRED_ROLES, start=1)
    ]
    for record in records:
        record["artifact_sha256"] = hashlib.sha256(
            record["artifact_text"].encode("utf-8")
        ).hexdigest()
    receipt = {
        "schema_version": 1,
        "repository": "chris-dare-dev/derived-alg-geo-lean",
        "pull_number": 1,
        "head_commit": HEAD,
        "base_commit": BASE,
        "policy_id": policy["policy_id"],
        "policy_sha256": review_authority.digest(policy),
        "files_sha256": files_sha256,
        "technical_review_ids": [item["id"] for item in records],
        "provider_review_ids": [],
        "independent_human_approval": False,
    }
    snapshot = {
        "source": "trusted-read-only-adapter",
        "event": "pull_request",
        "repository": receipt["repository"],
        "pull_number": receipt["pull_number"],
        "head_commit": HEAD,
        "base_commit": BASE,
        "policy_sha256": review_authority.digest(policy),
        "author_actor_id": 234062931,
        "from_fork": False,
        "files": {"items": files, "fetched_count": 1, "complete": True, "truncated": False, "next_page": False},
        "technical_reviews": {"items": records, "fetched_count": 4, "complete": True, "truncated": False, "next_page": False},
        "provider_reviews": {"items": [], "fetched_count": 0, "complete": True, "truncated": False, "next_page": False},
    }
    return policy, receipt, snapshot


class ReviewAuthorityTests(unittest.TestCase):
    def assert_rejected(self, policy: dict, receipt: dict, snapshot: dict, fragment: str) -> None:
        result = review_authority.validate_receipt(policy, receipt, snapshot)
        self.assertFalse(result["valid"], result)
        self.assertFalse(result["claims"]["technical_reviews_recorded"], result)
        self.assertTrue(any(fragment in error for error in result["errors"]), result)

    def test_exact_receipt_records_four_technical_reviews_without_human_approval(self) -> None:
        result = review_authority.validate_receipt(*fixture())
        self.assertTrue(result["valid"], result)
        self.assertTrue(result["claims"]["technical_reviews_recorded"])
        self.assertFalse(result["claims"]["independent_human_approval"])
        self.assertFalse(result["claims"]["github_approval_observed"])

    def test_replay_on_new_head_or_base_fails(self) -> None:
        for field in ("head_commit", "base_commit"):
            with self.subTest(field=field):
                policy, receipt, snapshot = fixture()
                snapshot[field] = NEXT
                self.assert_rejected(policy, receipt, snapshot, f"receipt.{field}")

    def test_changed_trust_file_invalidates_existing_receipt(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["files"]["items"].append({"path": ".github/workflows/ci.yml", "status": "modified"})
        snapshot["files"]["fetched_count"] = 2
        self.assert_rejected(policy, receipt, snapshot, "file-set binding")

    def test_rename_and_delete_are_bound_by_exact_path_and_status(self) -> None:
        for changed in (
            {"path": "docs/ci/new.md", "status": "renamed", "previous_path": "docs/ci/old.md"},
            {"path": "docs/ci/old.md", "status": "removed"},
        ):
            with self.subTest(changed=changed):
                policy, receipt, snapshot = fixture()
                snapshot["files"]["items"] = [changed]
                self.assert_rejected(policy, receipt, snapshot, "file-set binding")

    def test_rename_without_previous_path_is_rejected(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["files"]["items"] = [{"path": "docs/new.md", "status": "renamed"}]
        self.assert_rejected(policy, receipt, snapshot, "previous_path")

    def test_truncated_or_incomplete_provider_results_fail(self) -> None:
        for collection in ("files", "technical_reviews", "provider_reviews"):
            for defect in ({"complete": False}, {"truncated": True}, {"next_page": True},
                           {"fetched_count": 99}):
                with self.subTest(collection=collection, defect=defect):
                    policy, receipt, snapshot = fixture()
                    snapshot[collection].update(defect)
                    self.assert_rejected(policy, receipt, snapshot, f"snapshot.{collection}")

    def test_provider_file_cap_fails_closed(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["files"]["items"] = [
            {"path": f"file-{index}.txt", "status": "added"} for index in range(3000)
        ]
        snapshot["files"]["fetched_count"] = 3000
        self.assert_rejected(policy, receipt, snapshot, "3000-file cap")

    def test_revoked_technical_review_fails(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["technical_reviews"]["items"][0]["state"] = "revoked"
        self.assert_rejected(policy, receipt, snapshot, "revoked or does not pass")

    def test_later_failed_technical_review_supersedes_an_earlier_pass(self) -> None:
        policy, receipt, snapshot = fixture()
        later = dict(snapshot["technical_reviews"]["items"][0])
        later.update(id="review-5", sequence=5, verdict="NEEDS_CHANGES")
        snapshot["technical_reviews"]["items"].insert(0, later)
        snapshot["technical_reviews"]["fetched_count"] = 5
        self.assert_rejected(policy, receipt, snapshot, "superseded by a later technical review")

    def test_review_artifact_bytes_and_trailer_are_verified(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["technical_reviews"]["items"][0]["artifact_sha256"] = "d" * 64
        self.assert_rejected(policy, receipt, snapshot, "digest does not match")
        policy, receipt, snapshot = fixture()
        record = snapshot["technical_reviews"]["items"][0]
        record["artifact_text"] = record["artifact_text"].replace(f"Reviewed commit: {HEAD}", f"Reviewed commit: {BASE}")
        record["artifact_sha256"] = hashlib.sha256(record["artifact_text"].encode()).hexdigest()
        self.assert_rejected(policy, receipt, snapshot, "trailer does not bind")

    def test_duplicate_or_missing_technical_sequence_fails(self) -> None:
        for bad in (None, 2):
            with self.subTest(sequence=bad):
                policy, receipt, snapshot = fixture()
                snapshot["technical_reviews"]["items"][0]["sequence"] = bad
                self.assert_rejected(policy, receipt, snapshot, "technical review sequence")

    def test_label_only_claim_has_no_review_evidence(self) -> None:
        policy, receipt, snapshot = fixture()
        receipt["technical_review_ids"] = []
        receipt["label"] = "reviewed"
        self.assert_rejected(policy, receipt, snapshot, "missing technical review roles")

    def test_duplicate_role_or_identity_fails(self) -> None:
        for field in ("role", "reviewer_identity"):
            with self.subTest(field=field):
                policy, receipt, snapshot = fixture()
                snapshot["technical_reviews"]["items"][1][field] = snapshot["technical_reviews"]["items"][0][field]
                self.assert_rejected(policy, receipt, snapshot, "repeats a role or reviewer identity")

    def test_policy_replay_and_untrusted_weakening_fail(self) -> None:
        policy, receipt, snapshot = fixture()
        policy["required_roles"] = []
        self.assert_rejected(policy, receipt, snapshot, "retain all four review roles")
        policy, receipt, snapshot = fixture()
        policy["policy_id"] = "ci1-review-v2"
        self.assert_rejected(policy, receipt, snapshot, "trusted policy version")

    def test_current_provider_approval_can_be_observed_but_not_called_human_independence(self) -> None:
        policy, receipt, snapshot = fixture()
        policy["required_provider_approvals"] = 1
        current_policy_digest = review_authority.digest(policy)
        receipt["policy_sha256"] = snapshot["policy_sha256"] = current_policy_digest
        for record in snapshot["technical_reviews"]["items"]:
            record["policy_sha256"] = current_policy_digest
        snapshot["provider_reviews"] = {
            "items": [{"id": 17, "actor_id": 900, "state": "APPROVED", "commit_id": HEAD,
                       "submitted_at": "2026-09-27T01:00:00Z"}],
            "fetched_count": 1, "complete": True, "truncated": False, "next_page": False,
        }
        receipt["provider_review_ids"] = [17]
        result = review_authority.validate_receipt(policy, receipt, snapshot)
        self.assertTrue(result["valid"], result)
        self.assertTrue(result["claims"]["github_approval_observed"])
        self.assertFalse(result["claims"]["independent_human_approval"])

        snapshot["provider_reviews"]["items"].insert(
            0, {"id": 18, "actor_id": 900, "state": "DISMISSED", "commit_id": HEAD,
                "submitted_at": "2026-09-27T02:00:00Z"}
        )
        snapshot["provider_reviews"]["fetched_count"] = 2
        self.assert_rejected(policy, receipt, snapshot, "revoked, superseded or stale")

    def test_pending_provider_review_without_submission_time_does_not_veto_technical_receipt(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["provider_reviews"] = {
            "items": [{"id": 22, "actor_id": 900, "state": "PENDING", "commit_id": HEAD,
                       "submitted_at": None}],
            "fetched_count": 1, "complete": True, "truncated": False, "next_page": False,
        }
        result = review_authority.validate_receipt(policy, receipt, snapshot)
        self.assertTrue(result["valid"], result)
        self.assertTrue(result["claims"]["technical_reviews_recorded"])
        self.assertFalse(result["claims"]["github_approval_observed"])

    def test_shared_credential_cannot_satisfy_provider_requirement(self) -> None:
        policy, receipt, snapshot = fixture()
        policy["required_provider_approvals"] = 1
        current_policy_digest = review_authority.digest(policy)
        receipt["policy_sha256"] = snapshot["policy_sha256"] = current_policy_digest
        for record in snapshot["technical_reviews"]["items"]:
            record["policy_sha256"] = current_policy_digest
        snapshot["provider_reviews"] = {
            "items": [{"id": 17, "actor_id": 234062931, "state": "APPROVED", "commit_id": HEAD,
                       "submitted_at": "2026-09-27T01:00:00Z"}],
            "fetched_count": 1, "complete": True, "truncated": False, "next_page": False,
        }
        receipt["provider_review_ids"] = [17]
        self.assert_rejected(policy, receipt, snapshot, "shared credential")

    def test_merge_group_cannot_reuse_pr_receipt(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["event"] = "merge_group"
        self.assert_rejected(policy, receipt, snapshot, "merge-group")

    def test_missing_author_actor_identity_fails_closed(self) -> None:
        policy, receipt, snapshot = fixture()
        del snapshot["author_actor_id"]
        self.assert_rejected(policy, receipt, snapshot, "author_actor_id")

    def test_human_approval_claim_must_be_explicitly_false(self) -> None:
        for bad in (None, "yes", 1, True):
            with self.subTest(value=bad):
                policy, receipt, snapshot = fixture()
                receipt["independent_human_approval"] = bad
                self.assert_rejected(policy, receipt, snapshot, "explicitly deny")
        policy, receipt, snapshot = fixture()
        del receipt["independent_human_approval"]
        self.assert_rejected(policy, receipt, snapshot, "explicitly deny")

    def test_untrusted_snapshot_source_fails(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["source"] = "pull-request-file"
        self.assert_rejected(policy, receipt, snapshot, "trusted read-only adapter")

    def test_fork_metadata_can_be_reviewed_read_only(self) -> None:
        policy, receipt, snapshot = fixture()
        snapshot["from_fork"] = True
        self.assertTrue(review_authority.validate_receipt(policy, receipt, snapshot)["valid"])


if __name__ == "__main__":
    unittest.main()
