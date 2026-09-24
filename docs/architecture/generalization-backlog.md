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

### 2026-09-22 — existence of a minimizing object for `rouquierDim` (planned)
- chunk:              rou1-919-rouquier-dimension
- reviewing commit:   e18e20f9c3768269eedb622da04b9ab9f26ce127
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Triangulated.rouquierDim`, via
  `ENat.exists_eq_iInf`
- weaker hypotheses:  a nonempty index type and any function into `ℕ∞`; for
  `rouquierDim`, `HasZeroObject` supplies a local `Nonempty C` witness. No
  finite-dimension assumption or `[IsTriangulated C]` is needed.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/Data/ENat/Lattice.lean:115-116`
- source note:        The pinned lemma gives an index attaining the infimum
  even when its value is `⊤`. The definition still returns only a scalar and
  does not package that object. “Non-attainment” therefore describes the lack
  of a selected witness in the definition, not the absence of an existential
  minimizer. Whether to expose the stronger existence theorem is a separate
  API decision.
- state:              UNVERIFIED

### 2026-09-22 — classical generators are strong when one strong generator exists (planned)
- chunk:              rou1-919-rouquier-dimension
- reviewing commit:   e18e20f9c3768269eedb622da04b9ab9f26ce127
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Triangulated.Generators`, with the
  iterated-envelope composition theorem as the reusable result
- weaker hypotheses:  a triangulated category with some strong generator and
  a chosen classical generator; no scheme, stability, or geometric
  hypotheses.
- pin status:         UPSTREAM-ONLY (absent at the pinned revision)
- source note:        [Stacks Project tag 0FXA](https://stacks.math.columbia.edu/tag/0FXA)
  proves that every classical generator is strong when the category has a
  strong generator. Pinned Mathlib records this as a TODO at
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Generators.lean:40-41`;
  its current strong-to-classical theorem is at lines 196-200. This sharpens
  the planned “finite dimension gives a classical generator” consequence, but
  requires the composition-of-envelopes work and is outside this chunk.
- state:              UNVERIFIED

### 2026-09-22 — finite Rouquier witnesses avoid nonempty-index minimization
- chunk:              rou1-919-rouquier-dimension
- reviewing commit:   e18e20f9c3768269eedb622da04b9ab9f26ce127
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Triangulated.rouquierDim` finite-bound
  and finite/strong-generator characterizations
- weaker hypotheses:  for any `ι : Sort*` and `f : ι → ℕ∞`,
  `(⨅ i, f i) ≤ n ↔ ∃ i, f i ≤ n` and
  `(⨅ i, f i) ≠ ⊤ ↔ ∃ i, f i ≠ ⊤` compile without `[Nonempty ι]`;
  specializing to Rouquier dimension requires no local `[Nonempty C]` or
  `[IsTriangulated C]` proof assumption.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/Order/CompleteLattice/Defs.lean:313-315`,
  `.lake/packages/mathlib/Mathlib/Data/ENat/Basic.lean:325-326`, and
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Generators.lean:86-90`
- source note:        `/tmp/rou1-919-no-nonempty-probe.lean` compiled the
  arbitrary-index lemmas and the finite-bound, finite/strong-generator,
  classical-generator, and zero-stage statements for the proposed `rouquierDim`
  infimum formula (named `candidateDim` in the probe) against this exact commit.
  Finite witnesses follow from `iInf_lt_iff` at `n + 1` and `⊤`,
  followed by `ENat.lt_coe_add_one_iff`; the proof need not use
  `ENat.exists_eq_iInf`. The issue body suggests `iInf_le_iff`, but its pinned
  signature is a universal lower-bound condition, not an existential witness.
  `triangEnvelopeIter_succ` has only the existing
  pretriangulated context, whereas `triangEnvelopeIter_add` requires
  `[IsTriangulated C]`. This lift does not remove `HasZeroObject` from the
  public API, which the reused generation-time/envelope API requires.
- state:              L (proof-witness verified)

### 2026-09-22 — zero Rouquier dimension needs no inhabited infimum index
- chunk:              rou1-919-rouquier-dimension
- reviewing commit:   e18e20f9c3768269eedb622da04b9ab9f26ce127
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Triangulated.rouquierDim` zero-stage
  characterization through `ENat.iInf_eq_zero`
- weaker hypotheses:  for any `ι : Sort*` and `f : ι → ℕ∞`,
  `(⨅ i, f i) = 0 ↔ ∃ i, f i = 0` compiles without `[Nonempty ι]`;
  the Rouquier specialization needs no local `[Nonempty C]` or
  `[IsTriangulated C]` proof assumption.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/Data/ENat/Lattice.lean:71` and
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Generators.lean:66-68`
- source note:        `/tmp/rou1-919-no-nonempty-probe.lean` compiled the
  arbitrary-index lemma and the zero-stage Rouquier equivalence using
  `ENat.iInf_eq_zero` and `generationTime_eq_zero_iff'`; this proof route does
  not need an inhabited-index instance.
- state:              L (proof-witness verified)

### 2026-09-23 — `affineKProjectiveSchemeModulePullbackComparison`
- chunk:              sf8-5-affine-kprojective-scheme-comparison
- reviewing commit:   b3d0ad4aeb971972e47e7b4be28a06e801cdc4e1
- found by:           abstraction-adversary
- proposed ancestor:  `DerivedAlgGeo/Algebra/Homology/DerivedCategory/KProjective.lean`,
  beside `CategoryTheory.kProjectiveLocusDerivedFunctor`
- weaker hypotheses:  abelian `C`, `D`, `E`; additive `F : C ⥤ E` and
  `G : C ⥤ D`; exact `T : D ⥤ E`; and `e : F ≅ G ⋙ T`. The comparison
  needs no ring map, scheme, or tilde functor beyond data supplying `e`.
- source note:        The reviewer searched this repository's `KProjective.lean`,
  `BoundedAboveProjective.lean`, and `ExactFunctor.lean`, plus pinned Mathlib's
  homotopy-category, exact-derived-functor, K-projective, and localization
  APIs. Existing composition/comparison results do not provide this general
  K-projective-locus localization transport. In the reviewed affine proof,
  homotopy-category composition and exact-functor factorization through
  localization use only the hypotheses above (implementation lines 95–130).
  The generic API is outside this frozen chunk and is deferred; do not move or
  duplicate the geometric declaration to implement it.
- state:              UNVERIFIED

### 2026-09-23 — `SerreFunctorData.fullyFaithful` without Hom-finiteness
- chunk:              srf1-897-full-faithfulness
- reviewing commit:   74a05e716502cd3034958530c8134021fd2688c1
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Linear.SerreFunctor.Equivalence`
- weaker hypotheses:  retain `[Field k] [Category C] [Preadditive C] [Linear k C]`
  and the Serre duality data, but omit `[HomFinite k C]` and all replacement
  reflexivity hypotheses.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Defs.lean:229` and
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean:288-306`
- source note:        `/tmp/srf1-hypothesis-probes.lean` attempted the double-dual
  Hom equivalence without `HomFinite`; Mathlib failed to synthesize
  `Module.IsReflexive k (A ⟶ B)` for `Module.evalEquiv`. The full-faithfulness
  chain needs reflexivity of each Hom module. A probe replacing Hom-finiteness
  by `[∀ A B, Module.IsReflexive k (A ⟶ B)]` compiled, but over the existing
  `[Field k]` root Mathlib infers `FiniteDimensional` from reflexivity, so that
  is not a genuine weakening. The adjunction from both duality structures does
  not itself use Hom-finiteness; this row concerns the double-dual step.
- state:              FALSIFIED compiler witness: without Hom-finiteness or
  reflexivity, `Module.evalEquiv k (A ⟶ B)` has no `Module.IsReflexive` instance.

### 2026-09-23 — `SerreFunctorData.fullyFaithful` over a commutative ring
- chunk:              srf1-897-full-faithfulness
- reviewing commit:   74a05e716502cd3034958530c8134021fd2688c1
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Linear.SerreFunctor`, if its existing
  scalar binder is ever generalized
- weaker hypotheses:  replace `[Field k]` by `[CommRing k]` while retaining
  finite generation `[Module.Finite k (A ⟶ B)]` for each Hom module.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Defs.lean:229` and
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean:258-288`
- source note:        `/tmp/srf1-hypothesis-probes.lean` attempted
  `Module.evalEquiv R M` with `[CommRing R] [Module.Finite R M]`; pinned Mathlib
  could not synthesize `Module.IsReflexive R M`. Finite generation over a
  commutative ring does not supply the finite-projective/free reflexivity
  hypotheses used by the available instances. This falsifies the weakening
  with finite generation alone; an explicit reflexivity or finite-projective
  condition is a different hypothesis set. The existing Serre root is
  field-based, and this finding is outside the frozen #897 chunk.
- state:              FALSIFIED compiler witness: `Module.evalEquiv R M` fails
  with `failed to synthesize Module.IsReflexive R M`.
