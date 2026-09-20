# Proposal

## Why

Issue #927 asks for the proper-discontinuity consequences of the compatible
autoequivalence action without pretending that the geometric input has already
been constructed.  The public Lean interface and most consequences are already
on `main` through stacked PR #1175, but the issue stayed open because that PR
merged into a non-default branch; this change makes the acceptance boundary,
audit coverage, and repository documentation explicit so the issue can be
closed safely.

## What Changes

- Record the externally supplied proper-discontinuity data and its three
  required hypotheses as an OpenSpec acceptance contract; the corresponding
  Lean API is already present on `main`.
- Preserve and audit the finite point-stabilizer, local-neighborhood, Hausdorff
  orbit-space, and free-locus covering consequences already implemented in the
  combined symmetry layer.
- Keep the covering statement restricted to `IsCoveringMapOn` over the image of
  the free locus; do not introduce an unrestricted quotient-covering claim.
- Keep the missing geometric inhabitant and chamber-stabilizer finiteness as
  explicit non-goals, with their arithmetic, wall-local-finiteness, and
  finite-dimensionality prerequisites documented.
- Repair the cutover ledger's stale statement about #927 and record verified
  loop-engineering friction and repository inconsistencies for future agents.

## Capabilities

### New Capabilities

- `proper-discontinuity`: External proper-discontinuity data for the compatible
  autoequivalence action and the exact topological consequences derivable from
  it. This is new in the OpenSpec contract inventory only; this acceptance
  change does not add another Lean API root.

### Modified Capabilities

## Impact

The affected surface is the combined stability-condition symmetry layer,
`scripts/StabilityConditionAudit/PhaseTopology.lean`, and the architecture
cutover notes.  No new dependency or geometric construction is introduced;
verification uses a named Lean target, the repository precheck, OpenSpec
validation, and the configured self-hosted CI checks rather than a whole-
repository build.
