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

### 2026-09-21 — `ZModTwoNonflatDerived.baseChangedResolution_homology_negOne_not_isZero` (planned)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Tor`, with a later comparison from the
  abstract left-derived tensor calculation to the displayed affine cochain
  representative
- weaker hypotheses:  an abelian monoidal preadditive category with projective
  resolutions and a chosen projective resolution; no distinguished `ℤ → ZMod 2`,
  no particular mapping-cone presentation, and no scheme-level pullback claim
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Tor.lean:44`
- source note:        Mathlib's `Tor` is defined by a left-derived tensor
  functor; Stacks Project, Tag 064F, identifies the corresponding negative
  derived-tensor cohomology with Tor.  The ModuleCat specialization and the
  comparison to this cochain convention remain unverified.
- state:              UNVERIFIED

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
