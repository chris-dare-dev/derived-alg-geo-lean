# Tasks

## Chunk: `rou1-919-rouquier-dimension` — issue #919

**Depends on:** #917 is closed. Run as a separate enabled loop manifest after
this OpenSpec plan and manifest are committed on the planned issue branch.

**Frozen file list:**

- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Rouquier.lean`
- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension.lean`
- `scripts/StabilityConditionAudit/Dimension.lean`
- `openspec/changes/rou1-rouquier-dimension/`
- `.claude/loop-specs/rou1-919-rouquier-dimension.yaml`

### Work

- [ ] 1.1 Define `CategoryTheory.Triangulated.rouquierDim` as the infimum of
  existing generation times over singleton object properties.
- [ ] 1.2 Prove the `≤ n` witness characterization, the finite/strong-generator
  equivalence, the classical-generator consequence, and the zero-stage
  characterization.
- [ ] 1.3 Document why `triangEnvelopeIter n` corresponds to Rouquier's
  `⟨G⟩_{n+1}` and why the dimension has no offset.
- [ ] 1.4 Append every new public declaration to the dimension audit slice and add
  the new module to the nearest umbrella.

**Acceptance:** The four #919 mathematical characterisations compile under the
existing pretriangulated hypotheses; public names remain in the canonical
triangulated namespace; no geometry or stability import, new closure carrier,
or proof hole is introduced; and the audit includes all public declarations.

**Verification:** Run
`LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.CategoryTheory.Triangulated.Dimension`
and `scripts/precheck.sh`. Inspect `#print axioms` output for the new public
declarations and confirm no `sorryAx`. The source PR must pass the required
hosted `ci` check before it is offered for review.

## Successor chunk: `rou1-921-triangulated-functor-transport` — issue #921

**Depends on:** #919's PR is merged and its exact controller attestation is
present; the stale `blocked` label is removed; the issue and dependency state
are re-read; and the successor manifest passes a fresh live preflight. Do not
start this chunk from an open predecessor PR.

**Frozen file list:**

- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Functor.lean`
- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension.lean`
- `scripts/StabilityConditionAudit/Dimension.lean`
- `openspec/changes/rou1-rouquier-dimension/`
- The successor `.claude/loop-specs/` manifest bound to the merged #919 PR

### Work

- [ ] 2.1 Prove pointwise forward transport of each iterated envelope stage and
  its object-property map corollary.
- [ ] 2.2 Prove generation-time monotonicity for image properties, dimension
  monotonicity for essentially surjective triangulated functors, and equality
  under a triangulated equivalence.
- [ ] 2.3 Prove generation-time invariance and transfer of strong generation under
  a triangulated equivalence; state the proof that the quasi-inverse is
  triangulated when required.
- [ ] 2.4 Append declarations to the audit and import the functor module from the
  nearest umbrella.

**Acceptance:** The source-to-target envelope implication has the stated
direction; all target-wide claims include essential surjectivity or an
equivalence; hypotheses match the pinned Mathlib APIs; no reverse inclusion
for a general functor, geometry, stability, compact-generation dependency,
or proof hole is introduced; and the new declarations are audited.

**Verification:** Run
`LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.CategoryTheory.Triangulated.Dimension`
and `scripts/precheck.sh`. Inspect `#print axioms` output for the new public
declarations and confirm no `sorryAx`. The successor PR must pass a fresh
preflight, the predecessor attestation check, and the required hosted `ci`
check before it is offered for review.
