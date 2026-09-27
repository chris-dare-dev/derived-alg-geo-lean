"""Provider-only review metadata collection fixtures for CI1.03."""

from __future__ import annotations

import copy
import unittest
from urllib.parse import urlsplit

from scripts import ci_github_evidence, review_authority, review_authority_github


REPO = "chris-dare-dev/derived-alg-geo-lean"
BASE = "a" * 40
HEAD = "b" * 40
OTHER = "c" * 40


def pull(*, head: str = HEAD, base: str = BASE, count: int = 3,
         head_repo_id: int = 1) -> dict:
    return {
        "number": 42, "state": "open", "changed_files": count,
        "user": {"id": 7},
        "base": {"ref": "main", "sha": base,
                 "repo": {"id": 1, "full_name": REPO}},
        "head": {"sha": head, "repo": {"id": head_repo_id,
                "full_name": REPO if head_repo_id == 1 else "other/fork"}},
    }


FILES = [
    {"filename": "new.txt", "status": "modified"},
    {"filename": "renamed.txt", "status": "renamed", "previous_filename": "old.txt"},
    {"filename": "gone.txt", "status": "removed"},
]


def review(review_id: int, *, state: str = "APPROVED", commit: str = HEAD) -> dict:
    return {"id": review_id, "user": {"id": 11}, "state": state,
            "commit_id": commit, "submitted_at": "2026-09-27T20:00:00Z"}


class FakeClient:
    repository = REPO
    max_pages = 31

    def __init__(self) -> None:
        self.pulls = [pull(), pull()]
        self.branches = [{"name": "main", "protected": True,
                          "commit": {"sha": BASE}}] * 2
        self.files = copy.deepcopy(FILES)
        self.review_pages = [[review(1)], [review(1)]]
        self.pull_calls = 0
        self.branch_calls = 0
        self.review_calls = 0

    def get_object(self, path: str) -> dict:
        if path == "/branches/main":
            index = min(self.branch_calls, len(self.branches) - 1)
            self.branch_calls += 1
            return copy.deepcopy(self.branches[index])
        if path == "/pulls/42":
            index = min(self.pull_calls, len(self.pulls) - 1)
            self.pull_calls += 1
            return copy.deepcopy(self.pulls[index])
        raise AssertionError(path)

    def get_all(self, path: str) -> list[dict]:
        if path == "/pulls/42/files":
            return copy.deepcopy(self.files)
        if path == "/pulls/42/reviews":
            index = min(self.review_calls, len(self.review_pages) - 1)
            self.review_calls += 1
            return copy.deepcopy(self.review_pages[index])
        raise AssertionError(path)


class CollectorTests(unittest.TestCase):
    def test_collects_provider_metadata_without_claiming_trusted_review(self) -> None:
        client = FakeClient()
        observation = review_authority_github.collect_provider_observation(client, 42)
        self.assertEqual(observation["source"], "github-read-only-metadata")
        self.assertEqual(observation["head_commit"], HEAD)
        self.assertEqual(observation["base_commit"], BASE)
        self.assertEqual(observation["author_actor_id"], 7)
        self.assertFalse(observation["from_fork"])
        self.assertEqual(observation["files"]["fetched_count"], 3)
        self.assertEqual(observation["files"]["items"][1], {
            "path": "renamed.txt", "status": "renamed", "previous_path": "old.txt"})
        self.assertEqual(observation["provider_reviews"]["fetched_count"], 1)
        self.assertNotIn("technical_reviews", observation)
        self.assertNotIn("policy_sha256", observation)
        verdict = review_authority.validate_receipt({}, {}, observation)
        self.assertFalse(verdict["valid"])
        self.assertIn("snapshot must come from a trusted read-only adapter", verdict["errors"])
        self.assertEqual(client.review_calls, 2)

    def test_records_fork_from_provider_repository_ids(self) -> None:
        client = FakeClient()
        client.pulls = [pull(head_repo_id=2), pull(head_repo_id=2)]
        self.assertTrue(review_authority_github.collect_provider_observation(client, 42)["from_fork"])

    def test_rejects_moved_head_or_base(self) -> None:
        for changed in (pull(head=OTHER), pull(base=OTHER)):
            with self.subTest(changed=changed):
                client = FakeClient()
                client.pulls[1] = changed
                with self.assertRaises(ci_github_evidence.EvidenceError):
                    review_authority_github.collect_provider_observation(client, 42)

    def test_rejects_review_revocation_or_new_review_during_collection(self) -> None:
        for later in ([review(1, state="DISMISSED")], [review(1), review(2)]):
            with self.subTest(later=later):
                client = FakeClient()
                client.review_pages[1] = later
                with self.assertRaisesRegex(ci_github_evidence.EvidenceError,
                                            "provider reviews changed"):
                    review_authority_github.collect_provider_observation(client, 42)

    def test_rejects_truncated_file_set_and_cap(self) -> None:
        client = FakeClient()
        client.files = FILES[:-1]
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError,
                                    "differs from reported changed-file count"):
            review_authority_github.collect_provider_observation(client, 42)
        client = FakeClient()
        client.pulls = [pull(count=3000)] * 2
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError, "3000-file cap"):
            review_authority_github.collect_provider_observation(client, 42)

    def test_rejects_malformed_file_and_review_rows(self) -> None:
        client = FakeClient()
        client.files[1]["previous_filename"] = None
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError, "rename source"):
            review_authority_github.collect_provider_observation(client, 42)
        client = FakeClient()
        client.files[1]["filename"] = "new.txt"
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError, "duplicated"):
            review_authority_github.collect_provider_observation(client, 42)
        client = FakeClient()
        client.review_pages = [[review(1), review(1)]] * 2
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError, "duplicated"):
            review_authority_github.collect_provider_observation(client, 42)

    def test_pending_review_has_no_submission_time_or_approval_claim(self) -> None:
        client = FakeClient()
        pending = {"id": 2, "user": {"id": 11}, "state": "PENDING",
                   "commit_id": None, "submitted_at": None}
        client.review_pages = [[pending], [pending]]
        observation = review_authority_github.collect_provider_observation(client, 42)
        self.assertEqual(observation["provider_reviews"]["items"][0]["state"], "PENDING")
        self.assertNotIn("github_approval_observed", observation)

    def test_client_follows_pages_and_requires_complete_final_page(self) -> None:
        root = f"https://api.github.com/repos/{REPO}"
        first_reviews = f"{root}/pulls/42/reviews?per_page=100"
        second_reviews = first_reviews + "&page=2"
        first_files = f"{root}/pulls/42/files?per_page=100"
        second_files = first_files + "&page=2"
        responses = {
            f"{root}/branches/main": ({"name": "main", "protected": True,
                                        "commit": {"sha": BASE}}, {}),
            f"{root}/pulls/42": (pull(count=2), {}),
            first_reviews: ([review(1)], {"Link": f'<{second_reviews}>; rel="next"'}),
            second_reviews: ([review(2)], {}),
            first_files: ([FILES[0]], {"Link": f'<{second_files}>; rel="next"'}),
            second_files: ([FILES[1]], {}),
        }
        calls: list[str] = []

        def transport(url: str):
            self.assertEqual(urlsplit(url).hostname, "api.github.com")
            calls.append(url)
            return copy.deepcopy(responses[url])

        client = ci_github_evidence.GitHubClient(REPO, transport=transport,
                                                  max_pages=31)
        observation = review_authority_github.collect_provider_observation(client, 42)
        self.assertEqual(observation["files"]["fetched_count"], 2)
        self.assertEqual(observation["provider_reviews"]["fetched_count"], 2)
        self.assertEqual(calls.count(second_reviews), 2)
        responses[first_files] = ([FILES[0]] * 100, {})
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError,
                                    "full page has no completeness proof"):
            review_authority_github.collect_provider_observation(client, 42)

    def test_page_budget_must_cover_file_cap(self) -> None:
        client = FakeClient()
        client.max_pages = 20
        with self.assertRaisesRegex(ci_github_evidence.EvidenceError, "31 API pages"):
            review_authority_github.collect_provider_observation(client, 42)


if __name__ == "__main__":
    unittest.main()
