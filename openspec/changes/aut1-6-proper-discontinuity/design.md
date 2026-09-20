# Design

## Context

The combined symmetry layer already owns `AutPairQuot`, its action on
`StabilityCondition.WithClassMap`, the orbit quotient, and the continuous
constant scalar-action instance.  The metric/topology layer already supplies
Hausdorffness from a surjective class map, while Mathlib supplies the proper
discontinuity lemmas and the free-locus covering theorem.  The source module
added for #927 is therefore an interface-and-consequences layer, not a place to
construct the geometric input.

The repository's architecture rules require theorems to live with the
definition or property they consume, require explicit hypotheses, and forbid
whole-library local builds.  The acceptance pass must also account for the
fact that PR #1175 merged into a stacked non-default branch, leaving the GitHub
issue and a cutover note stale even though its code is now on `main`.

## Goals / Non-Goals

**Goals:**

- Keep the three-field `ProperDiscontinuityData` boundary as the single owner
  of the supplied geometric input.
- Make each consequence consume precisely the Mathlib hypotheses it needs:
  proper discontinuity alone for finite point stabilizers, and the remaining
  topological/action hypotheses for local and quotient consequences.
- Audit the public declarations in `PhaseTopology.lean` and keep the negative
  boundary visible in source documentation.
- Leave a stable repository note describing stale tracker information and
  proven build/loop friction.

**Non-Goals:**

- Constructing an inhabitant of `ProperDiscontinuityData`.
- Proving arithmetic lattice-image control, wall local finiteness,
  finite-dimensionality, or any algebraicity/preservation/descent statement.
- Claiming a covering map away from the trivial-stabilizer locus.
- Adding convenience abstractions or duplicate orbit-space roots.

## Decisions

### 1. Keep the external data boundary in the combined symmetry owner

`ProperDiscontinuityData` remains in
`Symmetry/Combined/ProperDiscontinuity.lean`, beside the `AutPairQuot` action
and orbit space it describes.  The lower metric layer is consumed through its
Hausdorff theorem and does not import the combined action.  Moving the data to a
generic topology module would reverse dependency direction and invite a second
canonical root.

Alternative considered: add a generic wrapper around Mathlib's action classes.
Rejected because it would hide the distinction between supplied geometric
input and consequences specific to this stability action.

### 2. Use Mathlib's theorem boundary rather than duplicating proofs

The finite-stabilizer theorem uses the proper-discontinuity field only.  The two
neighborhood results and orbit-space `T2Space` result install the explicit
surjectivity-derived Hausdorff, local-compactness, and proper-discontinuity
instances locally, while consuming the canonical continuous-constant-action
instance from the combined-topology layer before invoking Mathlib.  The
covering theorem uses Mathlib's `IsCoveringMapOn` free-locus result.

Alternative considered: provide a stronger unrestricted quotient-covering
theorem.  Rejected because nontrivial stabilizers are allowed and the stronger
claim would be mathematically false without a freeness hypothesis.

### 3. Keep comparison and audit surfaces explicit

The orbit projection used by the covering theorem is the existing
`autPairOrbitMap`; no parallel quotient map or adapter is introduced.  The
audit appends the structure, its projections, and each consequence's axiom
prints in the existing proper-discontinuity section.  This keeps the
diamond-instance agreement visible: the local instances are exactly the
canonical topology/action instances already owned by the preceding modules.

The finite point-stabilizer consequence is exposed as a specialization taking
only the `ProperlyDiscontinuousSMul` class.  A compatibility wrapper remains
under `ProperDiscontinuityData` for clients that already hold the bundle, while
the remaining consequences take `ProperDiscontinuityData` because they
genuinely consume its other fields.

Alternative considered: expose only a `ProperDiscontinuityData` receiver for
the finite-stabilizer theorem.  Rejected because that would make new callers
construct unused surjectivity and local-compactness proofs just to obtain finite
point stabilizers and would hide the exact Mathlib hypothesis boundary.

### 4. Treat tracker/documentation repair as part of acceptance, not new math

The cutover ledger will describe #927 as a separately implemented interface
whose issue closure is handled by this PR, rather than claiming that the
unrelated cutover row discharges it.  A run note records the non-default-base
merge behavior, the stale `blocked` label, the Windows cache-seeding issue, and
the invalid `openspec list --all`/old precheck command patterns.  These notes do
not become mathematical APIs.

### 5. Bounded review and verification

The frozen chunk is reviewed on one commit by the mathematics,
repository-boundary, abstraction, and mathlib reviewers independently.  A
needs-changes result may produce at most two correction commits; a third
needs-changes adjudication records `blocked` and stops.  Local verification is
limited to OpenSpec validation, the targeted proper-discontinuity module build,
the audit/precheck commands, and the configured CI checks; no `lake build` of
the repository is run.

## Risks / Trade-offs

- **Risk:** The existing Lean code is already on `main`, so the acceptance PR
  could drift into a no-op or duplicate API. → **Mitigation:** Freeze the
  existing owner files, require a small source-documentation/audit clarification
  plus the stale-ledger repair, and reject any new geometric construction.
- **Risk:** A future reader may mistake point-stabilizer finiteness for chamber
  stabilizer finiteness. → **Mitigation:** Keep the negative section in the
  module docstring and the explicit negative OpenSpec scenarios.
- **Risk:** Seeded Windows caches can make a named build appear to be a full
  build. → **Mitigation:** retain `LEAN_NUM_THREADS=2`, run one named target at
  a time, and report the target and CI verdict separately.

## Migration Plan

1. Validate this OpenSpec change and the enabled loop manifest against the
   current `origin/main` digest.
2. Apply the documentation/audit clarification, run the targeted checks, and
   commit the frozen chunk.
3. Run the four independent adversarial reviews and any bounded corrections.
4. Push, create, approve, and merge the issue-closing PR only through the loop
   controller after the ledger and required checks pass.
5. Re-read the merged issue state and archive the OpenSpec change only after the
   controller confirms closure.

Rollback is a normal revert of the small merged PR; the external geometric
data contract remains unconstructed either way.

## Open Questions

None.  The user-authorized loop policy, review cap, merge authority, and
targeted-build restriction are fixed inputs for this run.
