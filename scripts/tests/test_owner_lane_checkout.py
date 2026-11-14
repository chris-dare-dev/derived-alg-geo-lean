#!/usr/bin/env python3
"""Jobs on the owner's runners leave `build`'s `.lake` in place."""

from __future__ import annotations

import unittest
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github/workflows/ci.yml"


class OwnerLaneCheckoutTests(unittest.TestCase):
    def test_owner_lane_checkouts_keep_lake(self) -> None:
        # Every job routed by OWNER_CI_RUNS_ON checks out into the same
        # directory on an owner runner. actions/checkout's default,
        # clean: true, runs `git clean -ffdx`, which deletes the ignored
        # `.lake` that `build` keeps there, and the runner's next build
        # starts cold.
        jobs = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))["jobs"]
        routed = {
            name: job
            for name, job in jobs.items()
            if "vars.OWNER_CI_RUNS_ON" in str(job.get("runs-on", ""))
        }
        self.assertIn("build", routed)
        checkouts = 0
        for name, job in routed.items():
            for step in job.get("steps", []):
                if not str(step.get("uses", "")).startswith("actions/checkout@"):
                    continue
                checkouts += 1
                with self.subTest(job=name):
                    self.assertIs((step.get("with") or {}).get("clean"), False)
        self.assertGreater(checkouts, 0)


if __name__ == "__main__":
    unittest.main()
