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

## Lift targets and the lift chunk

A reviewer regularly finds that a statement belongs at a higher altitude, in a
file the frozen chunk may not touch. Two manifest keys give that finding a legal
route without a mid-run manifest edit — which would move `digest(spec)` and
invalidate every passed dependency ledger in the run.

```yaml
chunks:
  - id: <chunk-id>
    files:
      - DerivedAlgGeo/<the leaf this chunk implements>
      - docs/architecture/generalization-backlog.md
    lift_targets:
      # ancestor prefixes this chunk's concepts might actually belong to.
      # Declaring one is standing permission, not an open door: the controller
      # refuses a diff here until a reviewer records pass_with_lift naming a
      # path under it.
      - DerivedAlgGeo/<plausible ancestor>
```

Then, last in each issue's chunk list, a chunk that implements what the reviewers
asked for:

```yaml
  - id: <issue-slug>-lift
    scope: implement the lift findings recorded against this issue
    closure: progress          # a lift chunk does not close the tracked issue
    files:
      - <the union of this issue's lift_targets>
      - docs/architecture/abstraction-tree.md
      - docs/architecture/generalization-backlog.md
    acceptance:
      - Every lift finding recorded against this issue's chunks is either
        implemented here, or recorded FALSIFIED with a counterexample.
```

Because ledgers are keyed on chunk id, the lift chunk gets its own ledger, its
own frozen list, and a fresh full panel. Nothing about it moves a digest, because
the manifest declared it before anything armed.

**Choosing `lift_targets` is a mathematical judgement, not a mechanical one.**
Derive them from `docs/architecture/abstraction-tree.md` when you plan the run,
and leave the key absent rather than guessing: an ancestor named wrongly is
standing authorization to edit a file nobody meant to open.

Validate a manifest before inspecting or enabling a run:

```text
python scripts/loop_engine.py validate --spec .claude/loop-specs/sf8-sf9-pilot.yaml
python scripts/loop_engine.py preflight --spec .claude/loop-specs/sf8-sf9-pilot.yaml
```

The pilot is checked in with `enabled: true` because the repository owner has
authorized this first run. The controller still requires a clean `main`-based
checkout and a passing live preflight before it performs any mutation. The
schema keeps `merge_pr` false by default; this pilot explicitly enables it.
Method, auto-merge, administrator merge, and branch deletion are separate
explicit merge-policy settings. Code issues may only be closed after a
confirmed merged pull request.
