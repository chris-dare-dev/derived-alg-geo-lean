from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path

from scripts.ci_performance import profile_actions
from scripts.ci_performance.collect_actions import write_snapshot


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
        self.assertIsNone(result["phase_durations_seconds"]["queue"])
        self.assertEqual(result["workflow_start_delay_seconds"], 120.0)
        self.assertGreater(result["wall_clock_seconds"], 0)

    def test_profile_rejects_run_with_only_pending_jobs(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["jobs"][0]["conclusion"] = "in_progress"
        payload["jobs"][0].pop("completed_at")
        with self.assertRaisesRegex(ValueError, "no terminal job"):
            profile_actions.profile_run(payload)

    def test_replay_requires_exact_partition(self) -> None:
        case = copy.deepcopy(REPLAY[0])
        case["transitive_changes"] = ["DerivedAlgGeo/Other.lean"]
        result = profile_actions.replay_decision(case)
        self.assertEqual(result["decision"], "full_rebuild")
        self.assertIn("exact partition", result["reasons"][0])

    def test_replay_accepts_explicit_empty_transitive_partition(self) -> None:
        result = profile_actions.replay_decision(REPLAY[0])
        self.assertEqual(result["decision"], "targeted_replay")

    def test_replay_identity_changes_and_missing_fields_force_full_rebuild(self) -> None:
        for field in (
            "toolchain", "manifest", "target", "options", "pins", "emitter",
            "instances", "exported_axioms",
        ):
            with self.subTest(field=field):
                changed = copy.deepcopy(REPLAY[0])
                changed["candidate_identity"][field] += "-changed"
                result = profile_actions.replay_decision(changed)
                self.assertEqual(result["decision"], "full_rebuild")
                self.assertIn(f"changed identity: {field}", result["reasons"])

                missing = copy.deepcopy(REPLAY[0])
                del missing["candidate_identity"][field]
                result = profile_actions.replay_decision(missing)
                self.assertEqual(result["decision"], "full_rebuild")
                self.assertIn(f"missing candidate identity: {field}", result["reasons"])

    def test_replay_legacy_single_identity_and_unsafe_inputs_fail_closed(self) -> None:
        legacy = {"identity": copy.deepcopy(REPLAY[0]["candidate_identity"])}
        self.assertEqual(profile_actions.replay_decision(legacy)["decision"], "full_rebuild")
        for field, value in (
            ("renames", ["A.lean -> B.lean"]),
            ("deletions", ["A.lean"]),
            ("unknown_inputs", ["unresolved import"]),
        ):
            with self.subTest(field=field):
                case = copy.deepcopy(REPLAY[0])
                case[field] = value
                self.assertEqual(profile_actions.replay_decision(case)["decision"], "full_rebuild")
        self.assertEqual(profile_actions.replay_decision(REPLAY[1])["decision"], "full_rebuild")

    def test_replay_needs_complete_diff_and_handles_transitive_changes(self) -> None:
        incomplete = copy.deepcopy(REPLAY[0])
        incomplete.pop("change_inventory_complete")
        self.assertEqual(profile_actions.replay_decision(incomplete)["decision"], "full_rebuild")

        transitive = copy.deepcopy(REPLAY[0])
        transitive["changed_files"].append("DerivedAlgGeo/Consumer.lean")
        transitive["transitive_changes"] = ["DerivedAlgGeo/Consumer.lean"]
        self.assertEqual(profile_actions.replay_decision(transitive)["decision"], "targeted_replay")

        empty_diff = copy.deepcopy(REPLAY[0])
        empty_diff["changed_files"] = []
        empty_diff["direct_changes"] = []
        self.assertEqual(profile_actions.replay_decision(empty_diff)["decision"], "full_rebuild")
        empty_diff["candidate_commit"] = empty_diff["base_commit"]
        self.assertEqual(profile_actions.replay_decision(empty_diff)["decision"], "cache_reuse")
        contradictory = copy.deepcopy(REPLAY[0])
        contradictory["candidate_commit"] = contradictory["base_commit"]
        self.assertEqual(profile_actions.replay_decision(contradictory)["decision"], "full_rebuild")

    def test_profile_maps_lean_action_and_separates_dependency_wait(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["jobs"][0]["steps"].append({
            "name": "Run leanprover/lean-action@v1",
            "started_at": "2026-09-20T18:38:00Z",
            "completed_at": "2026-09-20T18:40:00Z",
        })
        payload["job_needs"] = {"build": [], "roadmap": [], "ci": ["build", "roadmap"]}
        payload["jobs"].extend([
            {
                "id": 2, "name": "roadmap", "created_at": "2026-09-20T18:00:00Z",
                "started_at": "2026-09-20T18:00:00Z",
                "completed_at": "2026-09-20T18:05:00Z", "conclusion": "success",
                "steps": [{"name": "Roadmap", "started_at": "2026-09-20T18:00:00Z",
                           "completed_at": "2026-09-20T18:05:00Z"}],
            },
            {
                "id": 3, "name": "ci", "created_at": "2026-09-20T18:00:00Z",
                "started_at": "2026-09-20T18:48:00Z",
                "completed_at": "2026-09-20T18:50:00Z", "conclusion": "success",
                "steps": [{"name": "Aggregate", "started_at": "2026-09-20T18:48:00Z",
                           "completed_at": "2026-09-20T18:50:00Z"}],
            },
        ])
        result = profile_actions.profile_run(payload)
        ci = next(job for job in result["jobs"] if job["name"] == "ci")
        self.assertEqual(result["phase_durations_seconds"]["lake_build"], 120.0)
        self.assertEqual(ci["dependency_wait_seconds"], 2820.0)
        self.assertEqual(ci["runner_queue_seconds"], 60.0)
        self.assertEqual(result["phase_durations_seconds"]["queue"], 180.0)

    def test_profile_keeps_cancelled_timestamp_inversion_as_unknown(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["job_needs"]["cancelled"] = []
        payload["jobs"].append({
            "id": 2, "name": "cancelled", "created_at": "2026-09-20T18:03:00Z",
            "started_at": "2026-09-20T18:04:01Z",
            "completed_at": "2026-09-20T18:04:00Z", "conclusion": "cancelled",
            "steps": [],
        })
        result = profile_actions.profile_run(payload)
        cancelled = next(job for job in result["jobs"] if job["name"] == "cancelled")
        self.assertIsNone(cancelled["duration_seconds"])
        self.assertEqual(cancelled["runner_queue_seconds"], 61.0)
        self.assertTrue(any("precedes start" in item for item in result["timestamp_anomalies"]))

    def test_inverted_step_marks_affected_phase_unknown(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        audit = payload["jobs"][0]["steps"][1]
        audit["completed_at"] = "2026-09-20T18:09:47Z"
        result = profile_actions.profile_run(payload)
        self.assertIsNone(result["phase_durations_seconds"]["audit"])
        self.assertEqual(result["phase_durations_seconds"]["reset"], 468.0)

    def test_executed_job_without_steps_does_not_claim_zero_phase_time(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["jobs"][0]["steps"] = []
        result = profile_actions.profile_run(payload)
        for phase in profile_actions.PHASES[2:]:
            self.assertIsNone(result["phase_durations_seconds"][phase])
        self.assertTrue(any("no step data" in note for note in result["timestamp_anomalies"]))

    def test_replay_rejects_outside_and_noncanonical_paths(self) -> None:
        for path in (
            "../outside.lean", "/tmp/outside.lean",
            "DerivedAlgGeo/../scripts/ci.yml", "DerivedAlgGeo//Foo.lean",
            "DerivedAlgGeo/./Foo.lean", "C:/outside.lean",
            "DerivedAlgGeo\\Foo.lean",
        ):
            with self.subTest(path=path):
                case = copy.deepcopy(REPLAY[0])
                case["changed_files"] = [path]
                case["direct_changes"] = [path]
                self.assertEqual(profile_actions.replay_decision(case)["decision"], "full_rebuild")

    def test_single_instantiation_is_audit_work(self) -> None:
        self.assertEqual(profile_actions._phase("Single instantiation"), "audit")

    def test_rerun_carries_forward_job_without_counting_its_work(self) -> None:
        run = {
            "id": 36334136413, "run_attempt": 2, "head_sha": SAMPLE["head_sha"],
            "event": "pull_request", "status": "completed", "conclusion": "success",
            "created_at": "2026-09-27T17:27:02Z", "run_started_at": "2026-09-27T17:27:02Z",
        }
        old = {
            "id": 1, "name": "build", "run_id": run["id"], "run_attempt": 2,
            "head_sha": run["head_sha"], "labels": ["self-hosted"],
            "created_at": "2026-09-27T16:49:15Z", "started_at": "2026-09-27T16:49:16Z",
            "completed_at": "2026-09-27T17:08:55Z", "conclusion": "success",
            "steps": [{"name": "Run leanprover/lean-action@v1",
                       "started_at": "2026-09-27T16:50:00Z",
                       "completed_at": "2026-09-27T16:55:05Z"}],
        }
        current = {
            "id": 2, "name": "roadmap", "run_id": run["id"], "run_attempt": 2,
            "head_sha": run["head_sha"], "labels": ["ubuntu-latest"],
            "created_at": "2026-09-27T17:27:03Z", "started_at": "2026-09-27T17:27:06Z",
            "completed_at": "2026-09-27T17:28:38Z", "conclusion": "success",
            "steps": [{"name": "Roadmap", "started_at": "2026-09-27T17:27:06Z",
                       "completed_at": "2026-09-27T17:28:38Z"}],
        }
        bundle = {
            "schema_version": 1, "repository": "example/repo",
            "captured_at_utc": "2026-09-27T18:00:00Z", "provider_paths": {},
            "run": run, "attempt": run, "jobs": [old, current],
        }
        result = profile_actions.profile_bundle(bundle, {"build": [], "roadmap": []})
        self.assertEqual(result["carried_forward_jobs"][0]["name"], "build")
        self.assertIsNone(result["jobs"][0]["duration_seconds"])
        self.assertEqual(result["phase_durations_seconds"]["lake_build"], 0.0)
        self.assertEqual(result["wall_clock_seconds"], 92.0)
        self.assertEqual(result["run"]["platform"], "github-hosted-ubuntu")

        # GitHub may report the attempt start one second before created_at.
        run["run_started_at"] = "2026-09-27T17:27:01Z"
        current["started_at"] = run["run_started_at"]
        current["steps"][0]["started_at"] = run["run_started_at"]
        result = profile_actions.profile_bundle(bundle, {"build": [], "roadmap": []})
        self.assertFalse(result["jobs"][1]["carried_forward"])
        self.assertFalse(result["jobs"][1]["attribution_uncertain"])
        self.assertEqual(result["wall_clock_seconds"], 97.0)

    def test_overlap_before_attempt_start_is_uncertain(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["attempt_created_at"] = "2026-09-20T18:00:00Z"
        payload["run_started_at"] = "2026-09-20T17:59:59Z"
        payload["jobs"].append({
            "id": 2, "name": "overlap", "conclusion": "success",
            "started_at": "2026-09-20T17:50:00Z",
            "completed_at": "2026-09-20T18:01:00Z", "steps": [],
        })
        result = profile_actions.profile_run(payload)
        self.assertTrue(result["jobs"][1]["attribution_uncertain"])
        self.assertFalse(result["jobs"][1]["carried_forward"])
        self.assertIsNone(result["wall_clock_seconds"])
        self.assertIsNone(result["phase_durations_seconds"]["audit"])

    def test_dependent_job_created_after_prerequisites_is_dependency_wait(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        payload["job_needs"] = {"build": [], "ci": ["build"]}
        payload["jobs"].append({
            "id": 2, "name": "ci", "created_at": "2026-09-20T18:47:01Z",
            "started_at": "2026-09-20T18:47:03Z",
            "completed_at": "2026-09-20T18:47:04Z", "conclusion": "success",
            "steps": [{"name": "Aggregate", "started_at": "2026-09-20T18:47:03Z",
                       "completed_at": "2026-09-20T18:47:04Z"}],
        })
        result = profile_actions.profile_run(payload)
        ci = next(job for job in result["jobs"] if job["name"] == "ci")
        self.assertEqual(ci["dependency_wait_seconds"], 2820.0)
        self.assertEqual(ci["scheduler_gap_seconds"], 1.0)
        self.assertEqual(ci["runner_queue_seconds"], 2.0)

    def test_duplicate_job_name_rejected_when_graph_is_ambiguous(self) -> None:
        payload = copy.deepcopy(SAMPLE)
        duplicate = copy.deepcopy(payload["jobs"][0])
        duplicate["id"] = 2
        payload["jobs"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "job name is duplicated"):
            profile_actions.profile_run(payload)

    def test_verified_raw_bundle_profiles_and_rejects_tampering(self) -> None:
        run = {
            "id": SAMPLE["id"], "run_attempt": 1,
            "head_sha": SAMPLE["head_sha"], "event": SAMPLE["event"],
            "status": "completed", "conclusion": "success",
            "created_at": SAMPLE["created_at"],
            "run_started_at": SAMPLE["run_started_at"],
        }
        job = copy.deepcopy(SAMPLE["jobs"][0])
        job.update({"run_id": run["id"], "run_attempt": 1,
                    "head_sha": run["head_sha"], "labels": ["ubuntu-latest"]})
        bundle = {
            "schema_version": 1, "repository": "example/repo",
            "captured_at_utc": "2026-09-20T19:00:00Z",
            "provider_paths": {"run": "/actions/runs/1", "attempt": "/actions/runs/1/attempts/1"},
            "run": run, "attempt": run, "jobs": [job],
        }
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "run.json"
            write_snapshot(bundle, path)
            normalized = profile_actions.profile_bundle(
                profile_actions._load_verified_bundle(path), {"build": []}
            )
            self.assertEqual(normalized["run"]["platform"], "github-hosted-ubuntu")
            self.assertEqual(normalized["provider_bundle"]["job_count"], 1)
            path.write_text(path.read_text() + " ")
            with self.assertRaisesRegex(ValueError, "digest sidecar"):
                profile_actions._load_verified_bundle(path)

    def test_page_envelopes_must_agree_with_flattened_jobs(self) -> None:
        run = {
            "id": SAMPLE["id"], "run_attempt": 1,
            "head_sha": SAMPLE["head_sha"], "event": SAMPLE["event"],
            "status": "completed", "conclusion": "success",
            "created_at": SAMPLE["created_at"],
            "run_started_at": SAMPLE["run_started_at"],
        }
        job = copy.deepcopy(SAMPLE["jobs"][0])
        job.update({"run_id": run["id"], "run_attempt": 1,
                    "head_sha": run["head_sha"], "labels": ["ubuntu-latest"]})
        page_url = "https://api.github.com/repos/example/repo/actions/runs/1/attempts/1/jobs?per_page=100"
        bundle = {
            "schema_version": 2, "repository": "example/repo",
            "captured_at_utc": "2026-09-20T19:00:00Z", "provider_paths": {},
            "run": run, "attempt": run, "jobs": [job],
            "jobs_pages": [{
                "request_url": page_url, "response_headers": {},
                "pagination_links": {},
                "response": {"total_count": 1, "jobs": [job]},
            }],
        }
        profile = profile_actions.profile_bundle(bundle)
        self.assertEqual(profile["provider_bundle"]["job_page_count"], 1)
        altered = copy.deepcopy(bundle)
        altered["jobs_pages"][0]["response"]["jobs"] = []
        with self.assertRaisesRegex(ValueError, "differ from flattened"):
            profile_actions.profile_bundle(altered)


if __name__ == "__main__":
    unittest.main()
