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

### What happens when a reviewer opens one

Authorization keys off the **recorded review**, not the adjudication. The moment
a reviewer records `pass_with_lift --lift-target <path under a declared prefix>`,
that prefix is writable for this ledger. So at adjudication the orchestrator has
a real choice, and both options are legal:

- **`needs_changes`** — implement the lift now. The ancestor is open, the next
  round reviews the widened diff, and it costs one round like any other fix.
  Choose this when the lift is small and the chunk is young.
- **`pass_with_lift`** — ship the chunk as reviewed and carry the lift to
  `docs/architecture/generalization-backlog.md` for a later run. Costs no round.
  Choose this when the lift is large, cascading, or would outgrow the issue.

Note the asymmetry: only the second requires the backlog row, because only the
second defers. Adjudication refuses `pass_with_lift` while the target is missing
from the backlog, so a deferred lift cannot be lost.

**Do not pre-declare a separate `<issue>-lift` chunk.** It deadlocks a run that
finds no lifts: `verify_local_chunk_files` refuses a chunk whose diff is empty
("frozen chunk has no committed file changes relative to the protected base"), so
a lift chunk with nothing to implement fails the run rather than being skipped. A
lift too large for the current issue belongs in the backlog and then in the next
manifest, where it is ordinary planned work.

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
