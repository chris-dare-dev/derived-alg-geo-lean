"""Boundary matrix for selected, carried, and uncertain Actions jobs."""

from __future__ import annotations

import copy
import itertools
import unittest

from scripts.ci_performance.profile_actions import PHASES, profile_run


SHA = "a" * 40


def fixture(*, attempt_created="2026-09-27T18:00:00Z",
            attempt_started="2026-09-27T18:00:00Z"):
    return {
        "id": 17, "run_attempt": 2, "head_sha": SHA,
        "event": "pull_request", "status": "completed", "conclusion": "success",
        "created_at": attempt_created, "attempt_created_at": attempt_created,
        "run_started_at": attempt_started,
        "job_needs": {"current": [], "edge": []},
        "jobs": [{
            "id": 1, "name": "current", "conclusion": "success",
            "created_at": "2026-09-27T18:00:00Z",
            "started_at": "2026-09-27T18:01:00Z",
            "completed_at": "2026-09-27T18:02:00Z",
            "steps": [{
                "name": "Audit", "started_at": "2026-09-27T18:01:10Z",
                "completed_at": "2026-09-27T18:01:20Z",
            }],
        }],
    }


def edge_job(start, end, conclusion="success", steps=None):
    return {
        "id": 2, "name": "edge", "conclusion": conclusion,
        "created_at": "2026-09-27T18:00:00Z",
        "started_at": start, "completed_at": end,
        "steps": [] if steps is None else steps,
    }


class AttemptAttributionMatrix(unittest.TestCase):
    def test_boundary_interval_and_conclusion_matrix(self):
        boundaries = (
            ("2026-09-27T18:00:00Z", "2026-09-27T18:00:00Z"),
            ("2026-09-27T18:00:00Z", "2026-09-27T17:59:59Z"),
            ("2026-09-27T18:00:00Z", "2026-09-27T17:40:00Z"),
        )
        intervals = (
            ("2026-09-27T17:30:00Z", "2026-09-27T17:39:59Z", "carried"),
            ("2026-09-27T17:50:00Z", "2026-09-27T17:59:59Z", None),
            ("2026-09-27T17:59:59Z", "2026-09-27T18:00:01Z", "uncertain"),
            ("2026-09-27T18:00:00Z", "2026-09-27T18:00:01Z", "selected"),
            ("2026-09-27T18:00:01Z", "2026-09-27T17:59:59Z", "uncertain"),
            (None, "2026-09-27T18:02:00Z", "uncertain"),
            ("2026-09-27T18:00:01Z", None, "uncertain"),
        )
        for boundary, interval, conclusion in itertools.product(
            boundaries, intervals, ("success", "failure", "cancelled", "skipped")
        ):
            created, started = boundary
            job_start, job_end, fixed = interval
            low = min(created, started)
            high = max(created, started)
            if fixed == "uncertain" or job_start is None or job_end is None:
                expected = "uncertain"
            elif job_end < low:
                expected = "carried"
            elif job_start >= high:
                expected = "selected"
            else:
                expected = "uncertain"
            with self.subTest(boundary=boundary, interval=interval, conclusion=conclusion):
                payload = fixture(attempt_created=created, attempt_started=started)
                payload["jobs"].append(edge_job(job_start, job_end, conclusion))
                result = profile_run(payload)
                row = result["jobs"][1]
                self.assertEqual(row["attribution"], expected)
                if expected == "uncertain":
                    self.assertIsNone(row["duration_seconds"])
                    if conclusion in {"failure", "cancelled"}:
                        self.assertEqual(result["failures"], [])
                        self.assertEqual(len(result["attribution_uncertain_failures"]), 1)
                    if conclusion != "skipped":
                        self.assertIsNone(result["wall_clock_seconds"])
                        self.assertIsNone(result["phase_durations_seconds"]["audit"])
                elif expected == "carried":
                    self.assertIsNone(row["duration_seconds"])
                    self.assertEqual(result["wall_clock_seconds"], 60.0)
                    self.assertEqual(result["failures"], [])

    def test_steps_and_missing_execution_edges(self):
        valid = [{"name": "Run leanprover/lean-action@v1",
                  "started_at": "2026-09-27T18:00:12Z",
                  "completed_at": "2026-09-27T18:00:18Z"}]
        prior = [{"name": "Run leanprover/lean-action@v1",
                  "started_at": "2026-09-27T17:58:30Z",
                  "completed_at": "2026-09-27T17:59:59Z"}]
        inverted = [{"name": "Run leanprover/lean-action@v1",
                     "started_at": "2026-09-27T18:00:18Z",
                     "completed_at": "2026-09-27T18:00:12Z"}]
        for steps, expected in ((valid, "selected"), (prior, "uncertain"),
                                (inverted, "uncertain")):
            with self.subTest(steps=steps):
                payload = fixture()
                payload["jobs"].append(edge_job(
                    "2026-09-27T18:00:10Z", "2026-09-27T18:00:20Z",
                    "failure", copy.deepcopy(steps),
                ))
                result = profile_run(payload)
                self.assertEqual(result["jobs"][1]["attribution"], expected)
                if expected == "uncertain":
                    self.assertEqual(result["failures"], [])
                    self.assertIsNone(result["phase_durations_seconds"]["lake_build"])
                else:
                    self.assertEqual(len(result["failures"]), 1)
                    self.assertEqual(result["phase_durations_seconds"]["lake_build"], 6.0)

        payload = fixture()
        payload["jobs"].append(edge_job(
            None, "2026-09-27T18:02:00Z", "failure", prior,
        ))
        result = profile_run(payload)
        self.assertEqual(result["jobs"][1]["attribution"], "uncertain")
        self.assertEqual(result["failures"], [])
        self.assertIsNone(result["phase_durations_seconds"]["lake_build"])

        for step in (
            {"name": "Run leanprover/lean-action@v1",
             "started_at": "2026-09-27T18:00:12Z"},
            {"name": "Run leanprover/lean-action@v1",
             "started_at": "2026-09-27T18:00:12Z",
             "completed_at": "2026-09-27T18:00:12Z"},
        ):
            with self.subTest(partial_or_zero_step=step):
                payload = fixture()
                payload["jobs"].append(edge_job(
                    "2026-09-27T18:00:10Z", "2026-09-27T18:00:20Z",
                    "success", [step],
                ))
                result = profile_run(payload)
                self.assertEqual(result["jobs"][1]["attribution"], "selected")
                self.assertIsNone(result["phase_durations_seconds"]["lake_build"])

        for start, end, partial in (
            ("2026-09-27T17:58:00Z", "2026-09-27T17:59:00Z",
             {"name": "Run leanprover/lean-action@v1", "started_at": "2026-09-27T18:01:00Z"}),
            ("2026-09-27T18:00:10Z", "2026-09-27T18:00:20Z",
             {"name": "Run leanprover/lean-action@v1", "started_at": "2026-09-27T17:59:50Z"}),
            ("2026-09-27T18:00:10Z", "2026-09-27T18:00:20Z",
             {"name": "Run leanprover/lean-action@v1", "completed_at": "2026-09-27T18:01:00Z"}),
        ):
            with self.subTest(contradictory_partial_step=partial):
                payload = fixture()
                payload["jobs"].append(edge_job(start, end, "failure", [partial]))
                result = profile_run(payload)
                self.assertEqual(result["jobs"][1]["attribution"], "uncertain")
                self.assertEqual(result["failures"], [])
                self.assertEqual(len(result["attribution_uncertain_failures"]), 1)
                self.assertIsNone(result["wall_clock_seconds"])

    def test_missing_attempt_start_makes_attribution_uncertain(self):
        payload = fixture(attempt_started=None)
        payload["platform"] = "self-hosted"
        result = profile_run(payload)
        self.assertEqual(result["measurement_status"], "attribution_uncertain")
        self.assertEqual(result["run"]["platform"], "unknown")
        self.assertEqual(result["terminal_job_count"], 0)
        self.assertEqual(result["attribution_uncertain_terminal_job_count"], 1)
        self.assertIsNone(result["workflow_start_delay_seconds"])
        self.assertIsNone(result["wall_clock_seconds"])

        payload = fixture()
        payload["created_at"] = None
        payload["attempt_created_at"] = None
        result = profile_run(payload)
        self.assertEqual(result["measurement_status"], "attribution_uncertain")
        self.assertEqual(result["terminal_job_count"], 0)
        self.assertIsNone(result["phase_durations_seconds"]["queue"])
        self.assertIsNone(result["phase_durations_seconds"]["dependency_wait"])
        self.assertIsNone(result["wall_clock_seconds"])

    def test_zero_duration_no_steps_and_no_selected_terminal(self):
        payload = fixture()
        payload["jobs"].append(edge_job(
            "2026-09-27T18:00:00Z", "2026-09-27T18:00:00Z", "success",
        ))
        result = profile_run(payload)
        self.assertEqual(result["jobs"][1]["attribution"], "selected")
        for phase in PHASES[2:]:
            self.assertIsNone(result["phase_durations_seconds"][phase])

        payload = fixture()
        payload["jobs"] = [edge_job(
            "2026-09-27T18:00:01Z", "2026-09-27T17:59:59Z", "cancelled",
        )]
        result = profile_run(payload)
        self.assertEqual(result["terminal_job_count"], 0)
        self.assertEqual(result["attribution_uncertain_terminal_job_count"], 1)
        self.assertEqual(result["measurement_status"], "attribution_uncertain")
        self.assertEqual(result["attribution_uncertain_failures"][0]["class"], "cancelled")
        self.assertIsNone(result["wall_clock_seconds"])

        payload = fixture()
        payload["jobs"] = [edge_job(
            "2026-09-27T17:58:00Z", "2026-09-27T17:59:00Z", "success",
        )]
        result = profile_run(payload)
        self.assertEqual(result["measurement_status"], "no_selected_terminal")
        self.assertEqual(result["run"]["platform"], "unknown")
        self.assertEqual(result["terminal_job_count"], 0)
        self.assertEqual(result["carried_terminal_job_count"], 1)
        self.assertIsNone(result["wall_clock_seconds"])
        self.assertTrue(all(value is None for value in result["phase_durations_seconds"].values()))

        payload = fixture()
        payload["jobs"].append(edge_job(
            "2026-09-27T17:59:59Z", "2026-09-27T18:00:10Z", "skipped",
            [{"name": "Run leanprover/lean-action@v1",
              "started_at": "2026-09-27T18:00:00Z",
              "completed_at": "2026-09-27T18:00:05Z"}],
        ))
        result = profile_run(payload)
        self.assertEqual(result["jobs"][1]["attribution"], "uncertain")
        self.assertIsNone(result["wall_clock_seconds"])
        self.assertIsNone(result["phase_durations_seconds"]["lake_build"])
        self.assertIsNone(result["phase_durations_seconds"]["queue"])


if __name__ == "__main__":
    unittest.main()
