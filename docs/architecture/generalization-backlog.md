# Generalization backlog

Append-only. One row per altitude finding that could not be acted on inside the
chunk that found it.

This file exists because a reviewer who notices that a theorem holds in greater
generality usually notices it while reviewing a frozen chunk that may not touch
the ancestor module. Before this file existed, that observation had nowhere to
go: the reviewer could either suppress it or make it a blocking `needs_changes`
the chunk could not legally satisfy. Both outcomes lost the finding.

**Deliberately outside `openspec/changes/`.** `openspec_digest` in
`scripts/loop_engine.py` hashes only the required artifacts under a change
directory. A backlog living there would be digest-frozen, and appending to it
mid-run would invalidate every passed ledger in the run. Here it is free to grow.

## Rules

- Append only. Never delete a row; change its state in place.
- A row is cheap. Record a lift you are unsure of rather than not recording it.
- A falsified lift is a **result**, not a retraction. `abstraction-tree.md` is
  explicit that a failed unification recorded with its counterexample is a
  successful architecture outcome. Keep the row and mark it `FALSIFIED`.
- Read this file in Phase 0, before choosing an implementation approach. A row
  here may already answer where the work belongs.

## States

| State | Meaning |
|---|---|
| `UNVERIFIED` | Proposed. The general statement has not been compiled. |
| `CONFIRMED <PR>` | The lift was implemented and merged. |
| `FALSIFIED <counterexample>` | The general statement is false. Leaves stay separate. |

## Row schema

```
### <date> — <leaf declaration>
- chunk:              <chunk id>
- reviewing commit:   <sha>
- found by:           <reviewer or advisor name>
- proposed ancestor:  <module or namespace>
- weaker hypotheses:  <the binder/typeclass set the proof actually needs>
- state:              UNVERIFIED | CONFIRMED <PR> | FALSIFIED <counterexample>
```

## Rows

### 2026-09-22 — compare the explicit affine `H^{-1}` witness with `CategoryTheory.Tor` (planned)
- chunk:              sf8-5-tor-witness-comparison
- reviewing commit:   b8306d6b
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Tor`, with a later comparison from the
  abstract left-derived tensor calculation to the displayed affine cochain
  representative
- weaker hypotheses:  an abelian monoidal preadditive category with projective
  resolutions and a chosen projective resolution; no distinguished `ℤ → ZMod 2`,
  no particular mapping-cone presentation, and no scheme-level pullback claim
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Tor.lean:44`
- source note:        The explicit nonzero `H^{-1}` witness is now proved in
  merged PR #1457. Mathlib's `Tor` derives the second tensor factor; the
  concrete `ModuleCat` specialization, selected projective-resolution
  comparison, chain/cochain indexing bridge, and restriction-of-scalars
  comparison remain unverified. Do not duplicate this row for the same lift.
- state:              UNVERIFIED
- progress note (2026-09-22, after PR #1464): The concrete `ℤ → ZMod 2`
  specialization, selected projective-resolution comparison, chain/cochain
  bridge, and restriction-of-scalars Tor comparison are merged. Only the
  proposed abstract left-derived tensor comparison under the weaker hypotheses
  above remains `UNVERIFIED`.
- clarification (2026-09-22): The source note above records the status at the
  original #1457 review; its statement that the
  concrete comparison remained unverified is superseded by the post-#1464
  progress note. The row's `UNVERIFIED` state applies only to the abstract lift.

### 2026-09-21 — `ZModTwoNonflatDerived.baseChangedConeIso` (planned)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           altitude-scout
- proposed ancestor:  `CochainComplex.mappingCone.mapHomologicalComplexIso`
- weaker hypotheses:  an additive functor between preadditive categories and
  an arbitrary cochain morphism; no scalar-extension ring map, `ℤ`, or
  `ZMod 2` is needed for the cone-transport comparison
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean:636`
- source note:        This is the generic mapped-cone transport already suited
  to the representative-level comparison; whether a repository-facing wrapper
  is useful beyond the witness is unverified.
- state:              UNVERIFIED
- progress note (2026-09-22, after PR #1457): The private witness comparison
  uses Mathlib's generic mapped-cone transport directly; no repository-facing
  wrapper was added, and whether it has independent consumers remains
  unverified. This is not an unimplemented prerequisite for the concrete
  witness.

### 2026-09-21 — `ZModTwoNonflatDerived.affineKProjectivePullbackObject_homology_negOne_not_isZero` (planned)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           altitude-scout
- proposed ancestor:  `ProjectiveResolution.isoLeftDerivedObj`, potentially
  followed by a comparison with the repository's bounded-above-projective
  affine pullback lane
- weaker hypotheses:  an additive functor out of an abelian category with
  projective resolutions and a selected projective resolution; this omits the
  specific affine ring map and does not assert a general scheme-level derived
  pullback theorem
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/LeftDerived.lean:112`
- source note:        The pinned theorem computes a left-derived functor from a
  projective resolution, but its chain indexing and its relation to the
  repository's K-projective representative have not been compared here.
- state:              UNVERIFIED
- progress note (2026-09-22, after PR #1464): The concrete `ℤ → ZMod 2`
  specialization and its chain/cochain degree bridge are proved; the proposed
  abstract comparison to `ProjectiveResolution.isoLeftDerivedObj` under the
  weaker hypotheses above remains unverified.

### 2026-09-21 — planned K-projective representative bridge (drop `K.IsStrictlyLE d`)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `KProjectiveHomotopyCategory.ofBoundedAboveProjectives`
  and `AlgebraicGeometry.DerivedCategory.Dqc.affineKProjectivePullbackObjIso`
- weaker hypotheses:  keep `[∀ n : ℤ, Projective (K.X n)]`, deliberately omit
  `[K.IsStrictlyLE d]` from the generic representative bridge
- pin status:         PIN-CONFIRMED
  `DerivedAlgGeo/Algebra/Homology/DerivedCategory/KProjective.lean:89-94` and
  `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Dqc/AffineKProjectivePullback.lean:65-73`
- source note:        A 3.2-second bounded `~/.elan/bin/lake env lean /dev/stdin`
  probe instantiated both the object expression and
  `affineKProjectivePullbackObjIso f K d` without this binder. Both sites
  failed with `failed to synthesize instance of type class K.IsStrictlyLE d`.
- state:              FALSIFIED compiler witness: the current generic bridge
  cannot admit a complex without a strict upper bound.

### 2026-09-21 — planned K-projective representative bridge (drop degreewise projectivity)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `KProjectiveHomotopyCategory.ofBoundedAboveProjectives`
  and `AlgebraicGeometry.DerivedCategory.Dqc.affineKProjectivePullbackObjIso`
- weaker hypotheses:  keep `[K.IsStrictlyLE d]`, deliberately omit
  `[∀ n : ℤ, Projective (K.X n)]` from the generic representative bridge
- pin status:         PIN-CONFIRMED
  `DerivedAlgGeo/Algebra/Homology/DerivedCategory/KProjective.lean:89-94` and
  `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Dqc/AffineKProjectivePullback.lean:65-73`
- source note:        A 6.8-second bounded `~/.elan/bin/lake env lean /dev/stdin`
  probe instantiated both the object expression and
  `affineKProjectivePullbackObjIso f K d` without this binder. Both sites
  failed with `failed to synthesize ∀ (n : ℤ), Projective (K.X n)` (after the
  pinned typeclass-heartbeat diagnostic).
- state:              FALSIFIED compiler witness: the current generic bridge
  cannot admit a merely bounded-above complex without degreewise projectivity.
