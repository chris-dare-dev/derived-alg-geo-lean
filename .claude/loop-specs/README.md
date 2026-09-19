# Loop manifests

OpenSpec owns the planning artifacts under `openspec/`. Files in this
directory are execution manifests: they select a small issue batch, reference
the OpenSpec change that defines the work, freeze review roles and chunk
boundaries, and explicitly authorize provider actions.

The distinction is intentional:

- `openspec/changes/<name>/` contains the proposal, requirements/scenarios,
  design, and tasks that describe what should be built.
- `.claude/loop-specs/*.yaml` contains the authority and scheduling policy for
  one unattended run.
- `.loop-runs/` contains local, ignored review ledgers for frozen commits.

Validate a manifest before inspecting or enabling a run:

```text
python scripts/loop_engine.py validate --spec .claude/loop-specs/sf8-sf9-pilot.yaml
python scripts/loop_engine.py preflight --spec .claude/loop-specs/sf8-sf9-pilot.yaml
```

The pilot is intentionally checked in with `enabled: false`. Enabling it is a
separate repository-owner decision after its live issue/dependency state and
the merge policy have been reviewed. `merge_pr` remains false by default, and
code issues may only be closed after a confirmed merged pull request.
