from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from scripts.ci_performance.collect_actions import collect_attempt, write_snapshot


SHA = "a" * 40
RUN = {
    "id": 17, "run_attempt": 2, "head_sha": SHA, "event": "pull_request",
    "path": ".github/workflows/ci.yml", "status": "completed", "conclusion": "success",
}
JOB = {"id": 42, "run_id": 17, "run_attempt": 2, "head_sha": SHA, "name": "build"}


class FakeClient:
    repository = "example/repo"

    def __init__(self, before=None, attempt=None, jobs=None, after=None):
        self.before = copy.deepcopy(before or RUN)
        self.attempt = copy.deepcopy(attempt or RUN)
        self.jobs = copy.deepcopy(jobs if jobs is not None else [JOB])
        self.after = copy.deepcopy(after or self.before)
        self.calls = []

    def get_object(self, path):
        self.calls.append(path)
        if "/attempts/" in path:
            return self.attempt
        return self.before if self.calls.count(path) == 1 else self.after

    def get_pages(self, path, *, key):
        self.calls.append((path, key))
        return [{
            "request_url": f"https://api.github.com/repos/{self.repository}{path}?per_page=100",
            "response_headers": {}, "pagination_links": {},
            "response": {"total_count": len(self.jobs), key: self.jobs},
        }]


class CollectActionsTests(unittest.TestCase):
    def test_collects_exact_attempt_and_rechecks_run(self):
        client = FakeClient()
        bundle = collect_attempt(client, 17)
        self.assertEqual(bundle["schema_version"], 2)
        self.assertEqual(bundle["jobs"], [JOB])
        self.assertEqual(bundle["jobs_pages"][0]["response"]["total_count"], 1)
        self.assertIn("request_url", bundle["jobs_pages"][0])
        self.assertEqual(bundle["attempt"]["run_attempt"], 2)
        self.assertIn(("/actions/runs/17/attempts/2/jobs", "jobs"), client.calls)
        self.assertEqual(client.calls.count("/actions/runs/17"), 2)

    def test_rejects_changed_run_and_foreign_or_duplicate_job(self):
        changed = copy.deepcopy(RUN)
        changed["head_sha"] = "b" * 40
        with self.assertRaisesRegex(ValueError, "changed during collection"):
            collect_attempt(FakeClient(after=changed), 17)
        foreign = copy.deepcopy(JOB)
        foreign["run_attempt"] = 1
        with self.assertRaisesRegex(ValueError, "another run"):
            collect_attempt(FakeClient(jobs=[foreign]), 17)
        with self.assertRaisesRegex(ValueError, "duplicate job ID"):
            collect_attempt(FakeClient(jobs=[JOB, JOB]), 17)
        pending = copy.deepcopy(RUN)
        pending["status"] = "in_progress"
        with self.assertRaisesRegex(ValueError, "not completed"):
            collect_attempt(FakeClient(before=pending), 17)

    def test_selected_previous_attempt_and_immutable_output(self):
        previous = copy.deepcopy(RUN)
        previous["run_attempt"] = 1
        prior_job = copy.deepcopy(JOB)
        prior_job["run_attempt"] = 1
        bundle = collect_attempt(FakeClient(attempt=previous, jobs=[prior_job]), 17, 1)
        self.assertEqual(bundle["attempt"]["run_attempt"], 1)
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "captured.json"
            manifest = write_snapshot(bundle, path)
            self.assertEqual(manifest["bundle_file"], path.name)
            self.assertTrue(path.with_suffix(".json.sha256.json").exists())
            with self.assertRaisesRegex(ValueError, "already exists"):
                write_snapshot(bundle, path)


if __name__ == "__main__":
    unittest.main()
