from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts.ci_performance import profile_actions


ROOT = Path(__file__).resolve().parents[2]
SAMPLE = json.loads((ROOT / "scripts/ci_performance/fixtures/sample-run.json").read_text())
REPLAY = json.loads((ROOT / "scripts/ci_performance/fixtures/replay-cases.json").read_text())


class ProfileActionTests(unittest.TestCase):
    def test_profile_requires_terminal_job_and_preserves_pending(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["jobs"].append(
            {
                "id": 2,
                "name": "pending-job",
                "conclusion": "in_progress",
                "steps": [],
            }
        )
        result = profile_actions.profile_run(payload)
        self.assertEqual(result["terminal_job_count"], 1)
        self.assertEqual(result["pending_jobs"][0]["job"], "pending-job")
        self.assertEqual(result["failures"], [])
        self.assertEqual(result["phase_durations_seconds"]["queue"], 120.0)
        self.assertGreater(result["wall_clock_seconds"], 0)

    def test_profile_rejects_run_with_only_pending_jobs(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["jobs"][0]["conclusion"] = "in_progress"
        payload["jobs"][0].pop("completed_at")
        with self.assertRaisesRegex(ValueError, "no terminal job"):
            profile_actions.profile_run(payload)

    def test_replay_requires_exact_partition(self) -> None:
        case = copy.deepcopy(REPLAY[0])
        case["identity"]["transitive_changes"] = ["DerivedAlgGeo/Other.lean"]
        result = profile_actions.replay_decision(case)
        self.assertEqual(result["decision"], "full_rebuild")
        self.assertIn("exact partition", result["reasons"][0])

    def test_replay_accepts_explicit_empty_transitive_partition(self) -> None:
        result = profile_actions.replay_decision(REPLAY[0])
        self.assertEqual(result["decision"], "targeted_replay")


if __name__ == "__main__":
    unittest.main()
