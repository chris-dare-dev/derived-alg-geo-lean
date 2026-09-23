# Tasks

## Chunk: `rou1-919-rouquier-dimension` — issue #919

**Depends on:** #917 is closed. First publish this OpenSpec plan and enabled
manifest through the explicitly user-authorized, planning-only bootstrap PR
path: only planning artifacts and the manifest, no Lean changes, and no issue
closing syntax or provider closing references. This one-time PR uses direct
push/create because no issue ledger can exist before the manifest is merged.
Then create a fresh clean checkout on the exact `origin/main` base and use the
manifest's planned issue branch. Run validation and live preflight before both
altitude advisors, then initialize the ledger; implementation-phase provider
actions use the loop controller.

**Frozen file list:**

- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Rouquier.lean`
- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension.lean`
- `scripts/StabilityConditionAudit/Dimension.lean`
- `docs/architecture/generalization-backlog.md` (append-only, only for a
  recorded advisor/reviewer lift that cannot be implemented within this chunk)

### Work

- [ ] 1.1 Define `CategoryTheory.Triangulated.rouquierDim` as the infimum of
  existing generation times over singleton object properties.
- [ ] 1.2 Prove the `≤ n` witness characterization, the finite/strong-generator
  equivalence, the classical-generator consequence, and the zero-stage
  characterization.
- [ ] 1.3 Document in the module docstring that the infimum ranges over single
  objects rather than arbitrary properties and does not designate a chosen
  object attaining it; state finite witnesses as separate existentials.
- [ ] 1.4 Document why `triangEnvelopeIter n` corresponds to Rouquier's
  `⟨G⟩_{n+1}` and why the dimension has no offset, citing the zeroth and
  successor equations. Also identify `triangEnvelopeIter_add` as the matching
  extension-composition equation under its additional `[IsTriangulated C]`
  hypothesis, without adding that class to the dimension API.
- [ ] 1.5 Append every new public declaration to the dimension audit slice and add
  the new module to the nearest umbrella.

**Acceptance:** The four #919 mathematical characterisations compile under the
existing pretriangulated hypotheses; public names remain in the canonical
triangulated namespace; no geometry or stability import, new closure carrier,
or proof hole is introduced; `Nonempty C` is derived locally from the zero
object only where `ENat.exists_eq_iInf` needs it; the module docstring records
both scope caveats and the no-offset convention; and the audit includes all
public declarations. Any unimplemented advisor/reviewer lift is preserved as
an append-only backlog row in the exact frozen commit.

**Verification:** Run
`LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.CategoryTheory.Triangulated.Dimension`
and `scripts/precheck.sh`. Inspect `#print axioms` output for the new public
declarations and confirm no `sorryAx`. The source PR must pass the required
hosted `ci` check before it is offered for review.

## Successor chunk: `rou1-921-triangulated-functor-transport` — issue #921

**Depends on:** #919's PR is merged and the issue is closed; the stale
`blocked` label is removed; the issue and dependency state are re-read; and a
successor manifest passes a fresh live preflight. Do not start this chunk from
an open predecessor PR. The successor manifest is execution configuration,
not a file in the frozen #921 source diff.

**Frozen file list:**

- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Functor.lean`
- `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension.lean`
- `scripts/StabilityConditionAudit/Dimension.lean`
- `docs/architecture/generalization-backlog.md` (append-only, only for a
  recorded advisor/reviewer lift that cannot be implemented within this chunk)

### Work

- [ ] 2.1 Prove pointwise forward transport of each iterated envelope stage and
  its object-property map corollary.
- [ ] 2.2 Prove generation-time monotonicity for image properties, dimension
  monotonicity for essentially surjective triangulated functors, and equality
  under a triangulated equivalence.
- [ ] 2.3 Prove generation-time invariance and transfer of strong generation under
  a triangulated equivalence, using Mathlib's existing triangulated-equivalence
  interface for the inverse functor.
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
preflight, the live dependency check, and the required hosted `ci` check before
it is offered for review.
