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
| `UNVERIFIED` | The lift is not yet confirmed in merged canonical code. A proof may have been compiled in a scratch probe or an unmerged candidate; record that evidence in the source note. |
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

### 2026-09-27 — generic Fourier--Mukai `ShiftCompatibility` (issue #1369)
- chunk:              1369-shiftcompat-unification
- reviewing commit:   00196ff8
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.NatTrans.CommShift`, defined in module
  `Mathlib.CategoryTheory.Shift.CommShift`; the Fourier--Mukai record packages
  a selected `CategoryTheory.Functor.CommShift` structure and compatibility
  evidence for the supplied comparison isomorphism
- weaker hypotheses:  any natural transformation between functors carrying
  selected shift structures for an additive monoid; no isomorphism, Fourier--Mukai
  transform, triangulatedness, dg presentation, or cotwist shift is required
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/CommShift.lean:360`
  [pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/520045ab14e26149ee970e2e617ca04b09bde5d6/Mathlib/CategoryTheory/Shift/CommShift.lean#L35-L362)
- source note:        The pinned `CategoryTheory.NatTrans.CommShift` class asserts
  generic compatibility of a natural transformation with its source and target
  shift structures, leaving both structures as inputs. The `CategoryTheory.NatTrans`
  namespace is nested directly under `CategoryTheory`; `Shift` belongs to the
  defining module path, not the declaration namespace. The issue's record packages
  the independently selected Fourier--Mukai target structure alongside this proof.
  `CategoryTheory.Functor.CommShift.ofIso` can instead transport the source
  structure across the comparison, but that produces the transported choice
  rather than proving compatibility with an independently selected target.
  `CategoryTheory.Functor.isTriangulated_of_iso` consumes the selected structures
  and this compatibility evidence to transfer exactness. Stacks Project §13.3
  (tag 05QK) describes the analogous compatibility for 2-morphisms between
  triangulated functors, in the additional setting where the functors are exact:
  [Stacks Project §13.3, tag 05QK](https://stacks.math.columbia.edu/tag/05QK).
- state:              UNVERIFIED

### 2026-09-23 — K-flat resolutions and derived pullback for ringed topoi (planned)
- chunk:              sf8-5-task12-kflat-pullback
- reviewing commit:   e2332372922d884eea345f3ad79c536e66c22d84
- found by:           altitude-scout
- proposed ancestor:  ringed-site/topos module complexes and their derived
  pullback interface
- weaker hypotheses:  a morphism of ringed topoi and an arbitrary unbounded
  complex of modules; no scheme, affine, flatness, boundedness,
  quasicoherence, or Noetherian hypothesis
- pin status:         UPSTREAM-ONLY (absent from pinned Mathlib)
- source note:        Stacks Project §21.17, Lemma 21.17.11, gives an
  objectwise K-flat replacement with flat terms; §21.18, Lemmas 21.18.2–.3,
  constructs derived pullback and its composition law for ringed-topoi
  morphisms. The cited lemmas do not supply a functorial replacement object
  with natural comparison, and the derived-functor existence argument is not
  a Lean producer. This is a broader
  mathematical analogue, not a dependency or theorem of the scheme chunk.
  Sources: [flat resolutions](https://stacks.math.columbia.edu/tag/06YL),
  [derived pullback](https://stacks.math.columbia.edu/tag/06YV).
- state:              UNVERIFIED

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
### 2026-09-24 — stabilization of a lifted localization-heart filtration (planned)
- chunk:              sf11-4a-1496-noetherian-cover
- reviewing commit:   ce58cc9e44340c07c89836ba2a81fdd07aaee6b4
- found by:           altitude-scout
- proposed ancestor:  `Mathlib.CategoryTheory.Subobject.NoetherianObject`
- weaker hypotheses:  any category `C`, object `E : C`, and a filtration
  `F : ℕ ⥤ MonoOver E`; no scheme or t-structure hypotheses.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Subobject/NoetherianObject.lean:88`
- source note:        `isNoetherianObject_iff_isEventuallyConstant` supplies ACC
  once a localization filtration is lifted into subobjects of a fixed global
  heart object. The current `Lemma416Part3Data` lifts to a chain of objects
  but records no common ambient object or embeddings, so this application
  remains unverified.
- state:              UNVERIFIED
- progress note (2026-09-24): The categorical transfer from an explicit
  fixed-ambient subobject-chain lift is proved in this SF11.4 continuation.
  The geometric lift for a section-open or affine localization, the bounded
  `D_T` heart restriction, and their comparison remain `UNVERIFIED`.
- progress note (2026-09-24): Successive binary joins now turn pointwise
  subobject lifts into a fixed-ambient monotone chain. A triangulated t-exact
  restriction induces an exact heart functor and therefore preserves those
  joins, so the heart-level transfer needs only chainwise pointwise lifts.
  The bounded-component geometric pointwise lift is still not supplied by
  the existing `SLocal` owner-data fields.
- progress note (2026-09-24): A mono/epi-preserving functor between the
  abelian hearts maps image subobjects to image subobjects. Fixed-target
  *mono* extension therefore implies pointwise subobject lifting, provided
  the relevant target-heart object and its chosen source ambient lift are
  paired. All-arrow extension
  at every source-heart target is a stronger criterion: applying it to a zero
  arrow supplies the target-object lift as well. Constructing even the
  required mono extensions for the bounded coherent base-change component
  remains `UNVERIFIED`.

### 2026-09-24 — `anchored_chain_of_pointwise_lifts` with local join structure
- chunk:              sf11-4d-pointwise-anchored
- reviewing commit:   46d220ce422f8ea2aa1c712de1c08634522e7b56
- found by:           abstraction-adversary
- proposed ancestor:  `DerivedAlgGeo/CategoryTheory/Subobject/NoetherianObject.lean`
- weaker hypotheses:  binary joins only in `Subobject X` and in the target
  ambient subobject poset, rather than category-wide images and binary
  coproducts
- pin status:         UNCOMPILED
- source note:        The current proof uses Mathlib's category-wide instances
  to synthesize the two joins. A locally quantified semilattice formulation
  may suffice mathematically, but its Lean instance binding and theorem type
  have not been tested; do not present it as an available API.
- state:              UNVERIFIED

### 2026-09-24 — `SLocalSlicingData.restriction_eq_of_phase_iff`
- chunk:              sf11-4a-1496-noetherian-cover
- reviewing commit:   ce58cc9e44340c07c89836ba2a81fdd07aaee6b4
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Stability/SLocal.lean`
- weaker hypotheses:  drop `_L : SLocalSlicingData R s`; retain the open,
  compactness, both restrictions, and the phase comparison.
- pin status:         Focused copy of the existing proof compiled from
  `/dev/stdin` at this base.
- state:              UNVERIFIED

### 2026-09-24 — `Coh.restrict_jointlyReflectsIsomorphisms`
- chunk:              sf11-4a-1496-noetherian-cover
- reviewing commit:   ce58cc9e44340c07c89836ba2a81fdd07aaee6b4
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `DerivedAlgGeo/AlgebraicGeometry/Modules/Coherent/Noetherian.lean`
- weaker hypotheses:  drop `[IsLocallyNoetherian X]`; retain the open cover
  and the premise that every restricted map is an isomorphism.
- pin status:         Focused copy of the existing proof compiled from
  `/dev/stdin` at this base.
- state:              UNVERIFIED

### 2026-09-24 — `isNoetherianObject_of_finite_jointlyReflectsIsomorphisms`
- chunk:              sf11-4a-1496-noetherian-cover
- reviewing commit:   1187331a9df2c7be6907d2385eb3329675facd6b
- found by:           abstraction-adversary
- proposed ancestor:  `DerivedAlgGeo/CategoryTheory/Subobject/NoetherianObject.lean`
- weaker hypotheses:  jointly reflect isomorphisms only for monomorphisms,
  rather than all morphisms; no scheme or t-structure hypothesis
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Subobject/Basic.lean:298`
- source note:        The generic detector applies joint reflection to
  `Subobject.ofLE`, which is monic at the pinned Mathlib API. A theorem with
  reflection restricted to monomorphisms may therefore suffice, but the
  weaker statement has not been compiled. This generic API change is outside
  the SF11.4a geometry chunk.
- state:              UNVERIFIED

### 2026-09-24 — compare the open free-Yoneda sheaf with extension by zero
- chunk:              sf8-flat-generators
- reviewing commit:   300a828ce99b9b7b02e7f77320bd1aacde3fc84
- found by:           altitude-scout
- proposed ancestor:  the extension-by-zero functor `j_!` for an open immersion
- weaker hypotheses:  an open immersion of ringed spaces and a module sheaf on
  its source; no scheme-specific free-Yoneda construction is needed for the
  upstream stalk formula
- pin status:         UPSTREAM-ONLY (Stacks Project Lemma 6.31.8, tag 00A7;
  no pinned Lean comparison established)
- source note:        Stacks gives zero stalks off the open and the original
  stalk on it for `j_!`. This does not prove that the repository's canonical
  `SheafOfModules.freeYonedaSheaf` is `j_!` of the restricted structure sheaf.
  The current scheme-level result proves the stalk formula directly and makes
  no such identification.
- state:              UNVERIFIED

### 2026-09-21 — `CommShift₂Int` output transport of `ObjectProperty.lift₂`
- chunk:              dt1-928-exact-bifunctor-restriction
- reviewing commit:   858ca700829706455ddc7ea3f4ca9fff4ffa951b
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Functor.CommShift₂` via a general fully faithful output-composition transport
- weaker hypotheses:  coherence-only statement for arbitrary `C₁`, `C₂`, `D`, `D'`, additive-commutative shift monoid `M`, shifts, explicitly compatible `CommShift₂Setup` data, a fully faithful shift-compatible `H : D ⥤ D'`, a bifunctor postcomposition isomorphism, and a `CommShift₂` witness after postcomposition; no object property, closure witness, `Pretriangulated`, or `ExactBifunctor` fields
- state:              UNVERIFIED

### 2026-09-23 — `liftNatTrans_commShift`
- chunk:              dt1-928-exact-bifunctor-restriction
- reviewing commit:   8a61f0e94cd9c414f172d97535f62c1684a91c21
- found by:           abstraction-adversary
- proposed ancestor:  `DerivedAlgGeo/CategoryTheory/Shift/CommShift.lean`, as a general faithful-postcomposition reflection lemma for `NatTrans.CommShift`
- weaker hypotheses:  arbitrary categories with shifts by an additive monoid; `F, G : E ⥤ D` and `H : D ⥤ E'` commute with shifts; `H` is faithful; and `τ : F ⟶ G` commutes with shifts after whiskering by `H`. No object property, closure, or triangulated hypotheses.
- evidence:           the private `commShift_of_whiskerRight` proof uses only `H.map_injective`, `H`'s shift naturality, and the assumed shift compatibility of the whiskered transformation; `liftNatTrans_commShift` applies it to the restricted natural transformation.
- state:              UNVERIFIED

### 2026-09-23 — `ExactBifunctor.lift₂` with distinct full subcategories
- chunk:              dt1-928-exact-bifunctor-restriction
- reviewing commit:   ffb17b7b8cac3feecda2288845167f9470f79dd1
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Functor.ExactBifunctor.lift₂`, generalized to distinct domain, second-input, and output `ObjectProperty` full subcategories
- weaker hypotheses:  an ambient bifunctor on three (possibly distinct) triangulated categories with a supplied `ExactBifunctor`, three object properties whose full subcategories inherit triangulated structures, and an explicit closure witness from the first two properties into the output property; no single-category or same-property identification among the three positions
- source note:        This is a plausible API generalization inferred from the current restriction's use of one category and property for all three positions. The distinct-category coherence transport was not proved or compiled during this review.
- state:              UNVERIFIED

### 2026-09-26 — generation-time `+1` submultiplicativity without `P.Nonempty`
- chunk:              rou1-920-envelope-composition
- reviewing commit:   b674a436dd002da2487d744531f804ddbb795628
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.ObjectProperty.generationTime` and the
  planned envelope-composition API
- weaker hypotheses:  the scalar inequality
  `P.generationTime R + 1 ≤ (P.generationTime Q + 1) *
  (Q.generationTime R + 1)` needs no separate `[P.Nonempty]` binder. The
  iterated-envelope composition law and zero-stage fixed-point statement also
  hold without `[P.Nonempty]`; the fixed-point statement additionally needs no
  `[IsTriangulated C]`.
- pin status:         PIN-CONFIRMED for the corollary proof route
- source note:        `CategoryTheory.ObjectProperty.generationTime_add_one_submultiplicative`
  proves the scalar inequality by splitting the empty-generator case from
  finite generation-time witnesses. `triangEnvelopeIter_compose` handles an
  empty property by showing all its iterates are bottom; the nonempty branch
  uses the fixed-point lemma. The fixed-point proof uses
  `triangEnvelopeIter_succ`, which needs only the shared pretriangulated
  context, while the composition proof uses the triangulated stage-addition
  API.
- state:              L (proof-witness verified)

### 2026-09-26 — products of retract-closed object properties
- chunk:              rou1-920-envelope-composition
- reviewing commit:   12b1f252d33ca17406fc85197fa060c33794fc78
- found by:           abstraction-adversary
- proposed ancestor:  `Mathlib.CategoryTheory.ObjectProperty.Retract`
- weaker hypotheses:  a category with binary products and an object property
  `Q` closed under binary products; no additive, shift, or triangulated
  structure
- pin status:         UPSTREAM-ONLY (the pinned
  `ObjectProperty/Retract.lean` and `ObjectProperty/FiniteProducts.lean`
  provide no such closure instance)
- source note:        The private `retractClosure_isClosedUnderBinaryProducts`
  proof constructs products of two retracts componentwise and transfers the
  product property across an isomorphism. Whether this belongs as a general
  closure API in Mathlib's retract module remains to be confirmed.
- state:              UNVERIFIED

### 2026-09-26 — products of extension-closed object properties
- chunk:              rou1-920-envelope-composition
- reviewing commit:   12b1f252d33ca17406fc85197fa060c33794fc78
- found by:           abstraction-adversary
- proposed ancestor:  `Mathlib.CategoryTheory.Triangulated.Subcategory`
- weaker hypotheses:  the existing pretriangulated context, binary products,
  and binary-product closure of both input properties; no `IsTriangulated`
  or nonemptiness assumption
- pin status:         UPSTREAM-ONLY (the pinned `Subcategory.lean` has only
  the more restrictive closure instance requiring a triangulated object
  property)
- source note:        The private `extensionProduct_prop_prod` and
  `extensionProduct_isClosedUnderBinaryProducts` proofs form products of the
  input distinguished triangles using Mathlib's
  `productTriangle_distinguished`. Whether to expose this weaker closure
  result as general Subcategory API remains to be confirmed.
- state:              UNVERIFIED

### 2026-09-26 — exact-functor transport of finite triangulated-generation stages
- chunk:              rou1-921-generation-functor-transport
- reviewing commit:   e83b614078d491b7f1d8dab085bf494fddb32ebc
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Triangulated.Generators`, for pointwise
  transport of `ObjectProperty.triangEnvelopeIter`; the generation-time and
  Rouquier-dimension consequences remain downstream
- weaker hypotheses:  an exact functor between triangulated categories and an
  object property with a finite generation-stage bound; essential
  surjectivity is needed only for the category-level Rouquier-dimension
  inequality, and full faithfulness is not needed
- pin status:         UPSTREAM-ONLY (the transport and dimension statements
  are absent at the pinned revision)
- source note:        Olander, *Ample line bundles and generation time*, §4,
  uses that finite-stage generated subcategories are preserved by exact
  functors (published PDF p. 304, lines 324-328). Its Lemma 7 proves that an
  essentially-surjective exact functor does not increase countable Rouquier
  dimension (PDF p. 303, lines 224-230); specializing its stage argument to a
  singleton gives the planned ordinary Rouquier-dimension inequality. This
  is a literature precedent, not a pinned Lean API. At the pin,
  `triangEnvelopeIter` and its stage recurrence are defined at
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Generators.lean:62-80`,
  while `Functor.IsTriangulated` and its additive/product-preservation
  instances are at
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Functor.lean:181-235`;
  the searched Mathlib tree has no functor transport of these stages or
  Rouquier-dimension API. The quasi-inverse triangulated structure is already
  supplied for `Equivalence.IsTriangulated` at
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Adjunction.lean:186-198`.
  Source: [Olander, published PDF](https://pure.uva.nl/ws/files/174469947/Ample_line_bundles_and_generation_time.pdf).
  Merged implementation in PR #1590: `triangEnvelopeIter_map_obj` and
  `triangEnvelopeIter_map_le` are in
  `DerivedAlgGeo/CategoryTheory/Triangulated/Generators/Functor.lean`;
  generation-time and Rouquier-dimension consequences are in
  `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Functor.lean`.
- state:              CONFIRMED #1590

### 2026-09-26 — generation transport needs only pretriangulated categories (planned)
- chunk:              rou1-921-generation-functor-transport
- reviewing commit:   e83b614078d491b7f1d8dab085bf494fddb32ebc
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.ObjectProperty` envelope transport and
  `CategoryTheory.Triangulated.Dimension.Functor` numerical consequences
- weaker hypotheses:  independently universe-polymorphic `C` and `D`, each
  with `Category`, `HasZeroObject`, `HasShift _ ℤ`, `Preadditive`, additive
  shifts, and `Pretriangulated`; `F : C ⥤ D` with `F.CommShift ℤ` and
  `F.IsTriangulated`. Neither category needs `IsTriangulated` (octahedral).
  Pointwise transport additionally binds `P : ObjectProperty C`, `n : ℕ`,
  `X : C`, and the source stage-membership proof; the `map` inequality binds
  only `P,n`; generation-time monotonicity binds arbitrary `P,Q`. None needs
  property nonemptiness, `ContainsZero`, closure under isomorphisms,
  `F.Full`, `F.Faithful`, or `F.EssSurj`. Additivity and binary-product
  preservation of `F` are inferred, not additional assumptions. Dimension
  monotonicity adds `F.EssSurj`; strong-generator transport adds `G : C`
  and `(singleton G).IsStrongTriangulatedGenerator`.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Functor.lean:181-235`
  and `Triangulated/Generators.lean:62-74`
- source note:        `/tmp/rou1-921-hypothesis-probes.lean` compiled complete
  proofs of pointwise tower transport, the `ObjectProperty.map` inequality,
  generation-time monotonicity, Rouquier-dimension monotonicity and equivalence
  invariance, generation-time equivalence invariance, and strong-generator
  transport with the above category hypotheses. The tower proof follows the
  left-associated `triangEnvelopeIter_succ`, so never uses the octahedral
  recurrence or the composition law. Verified using
  `LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean`; only unused-section-variable
  warnings in three scratch helper lemmas remain. No implementation module
  was changed by this scout.
  Merged implementation in PR #1590 uses the recorded `Pretriangulated C`
  and `Pretriangulated D` context, without an `IsTriangulated` (octahedral)
  assumption; see the stage and generation-time results in
  `DerivedAlgGeo/CategoryTheory/Triangulated/Generators/Functor.lean` and
  `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Functor.lean`.
- state:              CONFIRMED #1590

### 2026-09-26 — equivalence transport can construct the inverse's exact data (planned)
- chunk:              rou1-921-generation-functor-transport
- reviewing commit:   e83b614078d491b7f1d8dab085bf494fddb32ebc
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Triangulated.Dimension.Functor`
- weaker hypotheses:  the pretriangulated category context recorded above,
  `E : C ≌ D`, `[E.functor.CommShift ℤ]`, and
  `[E.functor.IsTriangulated]`; omit separate inverse-shift, inverse-exactness,
  and `E.CommShift` assumptions. Generation-time invariance additionally binds
  arbitrary `P,Q : ObjectProperty C`, without either being replete.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/Adjunction.lean:617-624`
  and `Triangulated/Adjunction.lean:61`
- source note:        `/tmp/rou1-921-hypothesis-probes.lean` compiled
  `dim_equivalence` and `time_equivalence` using
  `letI := E.commShiftInverse ℤ`, `letI := E.commShift_of_functor ℤ`, and
  `letI := E.toAdjunction.isTriangulated_rightAdjoint`. The proof constructs
  the compatible inverse shift, rather than claiming an independently chosen
  inverse shift is automatically compatible. The generation-time proof also
  compiled `P.isoClosure.triangEnvelopeIter n = P.triangEnvelopeIter n`,
  accounting for the isomorphism closure of `ObjectProperty.map`.
  Merged implementation in PR #1590 constructs the inverse compatibility
  locally in `generationTime_map_eq_of_equiv` and
  `rouquierDim_eq_of_equiv`; the strong-generator equivalence result is
  `exists_isStrongTriangulatedGenerator_iff_of_equiv`.
- state:              CONFIRMED #1590

### 2026-09-26 — Rouquier dimension and strong generators under retract-dense functors (planned)
- chunk:              rou1-921-generation-functor-transport
- reviewing commit:   e83b614078d491b7f1d8dab085bf494fddb32ebc
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Triangulated.Dimension.Functor`
- weaker hypotheses:  the pretriangulated category and exact-functor context
  recorded above, replacing `[F.EssSurj]` by
  `∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))`; strong-generator
  transport also binds `G : C` and its singleton strong-generation proof.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/ObjectProperty/Retract.lean:34`
- source note:        `/tmp/rou1-921-hypothesis-probes.lean` compiled
  `dim_retract_dense` and `strong_retract_dense` with complete proofs.
  Apply pointwise singleton-stage transport and then `prop_of_retract` to
  the target envelope stage. Essential surjectivity supplies this premise
  using `(F.objObjPreimageIso Y).symm.retract`; that specialization also
  compiled. This proposes an explicit hypothesis, not a new carrier or
  typeclass; whether to expose the stronger API in #921 remains an
  implementation scope decision.
  Merged implementation in PR #1590 proves
  `rouquierDim_le_of_retract_coverage` in
  `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Functor.lean` and
  `isStrongTriangulatedGenerator_map_of_retract_coverage` in
  `DerivedAlgGeo/CategoryTheory/Triangulated/Generators/Functor.lean`.
- state:              CONFIRMED #1590

### 2026-09-26 — replace exactness by additivity and shift compatibility (planned)
- chunk:              rou1-921-generation-functor-transport
- reviewing commit:   e83b614078d491b7f1d8dab085bf494fddb32ebc
- found by:           hypothesis-elimination-scout
- proposed ancestor:  distinguished-triangle step of finite-stage transport
- weaker hypotheses:  retain the pretriangulated category context,
  `[F.CommShift ℤ]`, and `[F.Additive]`; omit `[F.IsTriangulated]`.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Functor.lean:185`
- source note:        `/tmp/rou1-921-failed-hypothesis-probes.lean` attempted
  `F.map_distinguished T hT` with exactly these assumptions. The compiler
  reports `failed to synthesize instance of type class F.IsTriangulated`.
  This falsifies deleting exactness from this proof route; it is not a
  compiler-produced mathematical counterexample to every alternate statement.
- state:              UNVERIFIED

### 2026-09-26 — omit compatibility for a separately chosen inverse shift (planned)
- chunk:              rou1-921-generation-functor-transport
- reviewing commit:   e83b614078d491b7f1d8dab085bf494fddb32ebc
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `Equivalence` inverse triangulated-functor derivation
- weaker hypotheses:  retain `[E.functor.CommShift ℤ]`,
  `[E.functor.IsTriangulated]`, and an independently supplied
  `[E.inverse.CommShift ℤ]`; omit `[E.CommShift ℤ]`.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Adjunction.lean:53-61`
- source note:        `/tmp/rou1-921-failed-hypothesis-probes.lean` attempted
  `E.toAdjunction.isTriangulated_rightAdjoint` for that inverse shift. The
  compiler reports `failed to synthesize instance of type class
  E.toAdjunction.CommShift ℤ`. The verified construction above avoids this
  failure by choosing the compatible inverse shift locally; it does not
  erase compatibility from the adjunction theorem.
- state:              UNVERIFIED

### 2026-09-26 — transport of shift-closed properties for arbitrary additive shifts (planned)
- chunk:              rou1-921-triangulated-functor-transport
- reviewing commit:   65b2dff1ef8aaa5a986c8695f9e59dcc3b236c56
- found by:           abstraction-adversary (review round 1)
- proposed ancestor:  `DerivedAlgGeo/CategoryTheory/ObjectProperty/Shift.lean`
- weaker hypotheses:  categories with shifts by an additive monoid `A`,
  `[F.CommShift A]`, and pointwise transport of the generating property; no
  preadditivity, zero object, or triangulated structure
- pin status:         PIN-CONFIRMED
- source note:        Replacing `ℤ` by `A` in the complete shift-closure
  transport proof compiles unchanged; only `F.mapIso` and
  `F.commShiftIso` are used. The proposed owner is outside the frozen #921
  file list, so this lift is deferred.
- state:              UNVERIFIED

### 2026-09-26 — transport of arbitrary-shape limit closures (planned)
- chunk:              rou1-921-triangulated-functor-transport
- reviewing commit:   65b2dff1ef8aaa5a986c8695f9e59dcc3b236c56
- found by:           abstraction-adversary (review round 1)
- proposed ancestor:  `DerivedAlgGeo/CategoryTheory/ObjectProperty/LimitsClosure.lean`
- weaker hypotheses:  an arbitrary family `J : α → Type`, categories on each
  `J a`, preservation of each `J a`-shaped limit by `F`, and pointwise
  transport of the generating property; no `WalkingPair` specialization
- pin status:         PIN-CONFIRMED
- source note:        The complete `limitsClosure_le` proof compiles for
  `P.limitsClosure J`; no proof step uses the binary-product shape. The
  proposed owner is outside the frozen #921 file list, so this lift is
  deferred.
- state:              UNVERIFIED

### 2026-09-26 — shift closure commutes with isomorphism closure for arbitrary additive shifts (planned)
- chunk:              rou1-921-triangulated-functor-transport
- reviewing commit:   65b2dff1ef8aaa5a986c8695f9e59dcc3b236c56
- found by:           abstraction-adversary (review round 1)
- proposed ancestor:  `DerivedAlgGeo/CategoryTheory/ObjectProperty/Shift.lean`
- weaker hypotheses:  one category with shifts by any additive monoid `A` and
  an arbitrary object property `P`; no preadditivity, zero object, or
  triangulation
- pin status:         PIN-CONFIRMED
- source note:        The existing three-line argument for
  `P.isoClosure.shiftClosure A = P.shiftClosure A` compiles with only the
  additive-shift assumptions. The proposed owner is outside the frozen #921
  file list, so this lift is deferred.
- state:              UNVERIFIED


### 2026-09-27 — extension of the resolution-degree-zero augmentation target (planned)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           altitude-scout
- proposed ancestor:  `HomologicalComplex.extendSingleIso` in
  `Mathlib.Algebra.Homology.Embedding.Extend`
- weaker hypotheses:  an arbitrary category with zero morphisms and a zero
  object, decidable equality on both complex index types, an embedding of
  arbitrary complex shapes, and an equality identifying the image of the
  single supported degree; no schemes, abelianness, or flatness
- pin status:         PIN-CONFIRMED .lake/packages/mathlib/Mathlib/Algebra/Homology/Embedding/Extend.lean:293
- source note:        At Mathlib pin `520045ab14e26149ee970e2e617ca04b09bde5d6`,
  `extendSingleIso e X i i' h` identifies the extension of the single complex
  at `i` with the single complex at `i'`. Specializing to
  `embeddingDownNat`, `i = 0`, and `i' = 0` supplies the objectwise
  identification of the inner complexes in the target of
  `freeYonedaSheafCoproductTotalAugmentationToSingleZero`. It does not
  identify a total complex with the input, and its declaration is an
  objectwise isomorphism rather than the required natural isomorphism of
  totalization functors. The functorial assembly and total comparison are
  still obligations; no proof was compiled by this research scout.
- state:              UNVERIFIED

### 2026-09-27 — exchanging the supported axis before a single-zero total comparison (planned)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           altitude-scout
- proposed ancestor:  `HomologicalComplex₂.totalFlipIso` in
  `Mathlib.Algebra.Homology.TotalComplexSymmetry`
- weaker hypotheses:  a preadditive category, arbitrary input and output
  complex shapes with total-shape structures in both orders and compatible
  symmetry signs, existence of the chosen bicomplex total, and decidable
  equality on the output indices; no schemes, flatness, or abelianness
- pin status:         PIN-CONFIRMED .lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplexSymmetry.lean:114
- source note:        This is the canonical isomorphism
  `K.flip.total c ≅ K.total c`. The repository already proves its generic
  naturality in `Algebra/Homology/SpectralSequence/TotalFlipNaturality.lean:47`.
  It permits a second-axis support comparison to reuse a first-axis
  comparison, but does not itself collapse a single supported axis.
  The existing `singleZeroTotalIso` in
  `Algebra/Homology/SpectralSequence/FilteredTotalComplexAdjacent.lean:410`
  and its naturality in `TotalQuasiIso.lean:248` are explicitly restricted
  to `AddCommGrpCat`, so they do not instantiate directly for `X.Modules`.
  `CategoryTheory/Sites/SheafCohomology/Cech/TotalComparison.lean:154`
  demonstrates composition through this flip and the existing single-zero
  comparison for abelian groups. A generic extraction and the required
  bicomplex adapter remain to be checked; none was compiled by this scout.
- state:              UNVERIFIED

### 2026-09-27 — natural recovery of the supported term of a single complex (planned)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           altitude-scout
- proposed ancestor:  `HomologicalComplex.singleCompEvalIsoSelf` in
  `Mathlib.Algebra.Homology.Single`
- weaker hypotheses:  an arbitrary category with zero morphisms and a zero
  object, an arbitrary complex shape, decidable equality on its indices,
  and a chosen supported degree; no preadditivity or geometric assumptions
- pin status:         PIN-CONFIRMED .lake/packages/mathlib/Mathlib/Algebra/Homology/Single.lean:103
- source note:        The natural isomorphism
  `single V c j ⋙ eval V c j ≅ 𝟭 V` recovers the surviving degree,
  while the adjacent `isZero_single_comp_eval` treats all other degrees.
  This supplies canonical component data for the single-axis comparison;
  it is an evaluation theorem and does not subsume the direct-sum total
  comparison or its differential compatibility. The related pinned
  `singleMapHomologicalComplex` in `Algebra/Homology/Additive.lean:266`
  already makes single-complex formation commute with any functor
  preserving zero morphisms, but likewise contains no totalization result.
  Source inspection did not find a general single-complex total theorem
  at the pin. The three-candidate cap was reached on disk, so no external
  sources were fetched. No proof was compiled by this scout.
- state:              UNVERIFIED


### 2026-09-27 — single-zero total comparison outside abelian groups (planned)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the canonical `HomologicalComplex₂.singleZeroTotalIso`
  and `singleZeroTotalIso_naturality` beside Mathlib's total-complex API,
  extracted from the current spectral-sequence consumers
- weaker hypotheses:  `{C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C]`, an arbitrary `A : CochainComplex C ℤ`, and only
  `[(singleZeroBicomplex A).HasTotal (ComplexShape.up ℤ)]`; naturality also
  takes an arbitrary `B`, its selected-total instance, and `f : A ⟶ B`.
  No `Abelian C`, all-coproducts, boundedness, flatness, or scheme assumption.
- pin status:         PIN-CONFIRMED Mathlib
  `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        `.lake/sf8_hypothesis_minimal.lean` copied the existing
  comparison and naturality proof into a scratch namespace, replacing
  `AddCommGrpCat` with `C`. The only proof adjustment was to expose generic
  componentwise cancellation for an isomorphism of complexes, proved by
  `HomologicalComplex.comp_f` and the iso identities. The complete proof,
  naturality, and the composite `totalFlipIso ≪≫ singleZeroTotalIso` compiled
  with `LEAN_NUM_THREADS=2 /home/chris-dare/.elan/bin/lake env lean
  .lake/sf8_hypothesis_minimal.lean`. The printed axiom sets for the comparison
  and naturality contain only `propext`, `Classical.choice`, and `Quot.sound`.
  The subsequent support witness below removes even the selected-total
  assumptions. These are scratch witnesses, not merged public declarations.
- state:              L (proof-witness verified)

### 2026-09-27 — single support supplies the required total coproducts (planned)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the same canonical single-zero bicomplex comparison
  beside Mathlib's total-complex API
- weaker hypotheses:  `{C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C]` and an arbitrary `A : CochainComplex C ℤ`; no supplied
  `HasTotal`, countable coproducts, finite biproducts, or arbitrary coproducts.
  Naturality adds only `B : CochainComplex C ℤ` and `f : A ⟶ B`.
- pin status:         PIN-CONFIRMED Mathlib
  `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        `.lake/sf8_hypothesis_support.lean` reorganizes the
  existing surviving-summand/inverse calculation into a cofan with point
  `A.X n`. Its universal property selects the `(0,n)` summand; every other
  summand is zero. `GradedObject.CofanMapObjFun.hasMap` then supplies
  `singleZeroHasTotal`. The comparison, its naturality, and the second-axis
  comparison through `totalFlipIso` compile without any colimit assumption.
  `.lake/sf8_hypothesis_narrow.lean` additionally compiles the same witness
  with only `Mathlib.Algebra.Homology.Single` and
  `Mathlib.Algebra.Homology.TotalComplexSymmetry` imports, using the underlying
  `HomologicalComplex.single` instead of the definitionally equal
  `CochainComplex.singleFunctor` spelling. Command:
  `LEAN_NUM_THREADS=2 /home/chris-dare/.elan/bin/lake env lean
  .lake/sf8_hypothesis_narrow.lean`. Exit code 0; comparison and naturality
  depend only on `propext`, `Classical.choice`, and `Quot.sound`. No stable
  Lean source was edited. This records the support argument for the planned
  extraction, not a general coproduct-existence theorem for arbitrary totals.
- state:              L (proof-witness verified)

### 2026-09-27 — drop the zero object from the single-zero comparison (attempted)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the canonical single-zero bicomplex constructor
- weaker hypotheses:  `{C : Type u} [Category.{v} C] [Preadditive C]` and
  `A : CochainComplex C ℤ`, deliberately omitting `HasZeroObject C`
- pin status:         PIN-CONFIRMED Mathlib
  `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        `.lake/sf8_hypothesis_nozero.lean`, compiled with
  `LEAN_NUM_THREADS=1 /home/chris-dare/.elan/bin/lake env lean`, fails at
  `(CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj A` with the exact
  diagnostic `failed to synthesize instance of type class
  HasZeroObject (CochainComplex C ℤ)`. The canonical single complex needs an
  actual zero object to populate every unsupported degree. This is a boundary
  of the current construction, not a claim about all possible alternate APIs.
- state:              FALSIFIED compiler witness: the current single-complex
  constructor does not accept this hypothesis deletion.

### 2026-09-27 — replace preadditivity by zero morphisms for totalization (attempted)
- chunk:              sf8-554-total-zero-comparison
- reviewing commit:   1d29d6696bb048fc2a3e648fab4b39931d836488
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `HomologicalComplex₂.total`
- weaker hypotheses:  `{C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]`, deliberately omitting `Preadditive C`
- pin status:         PIN-CONFIRMED Mathlib
  `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        `.lake/sf8_hypothesis_nopreadditive.lean`, compiled with
  `LEAN_NUM_THREADS=1 /home/chris-dare/.elan/bin/lake env lean`, fails at
  `HomologicalComplex₂.total (C := C)` with the exact diagnostic
  `failed to synthesize instance of type class Preadditive C`. The existing
  proof also explicitly uses `Preadditive.comp_add`, `Preadditive.add_comp`,
  and the integer-unit signs in the total differential. Single support does
  not remove the preadditive parameter from this canonical total API. A
  different construction would be outside this proof-based scout's scope.
- state:              FALSIFIED compiler witness: zero morphisms alone do not
  support Mathlib's existing total-complex construction.

### 2026-09-27 — natural extension of a single complex for the free-Yoneda augmentation target (planned)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           altitude-scout
- proposed ancestor:  `HomologicalComplex.singleCompExtendIso`, as a direct
  extension of Mathlib's `Algebra/Homology/Embedding/Extend.lean` API
- weaker hypotheses:  any category with zero morphisms and a zero object,
  arbitrary complex shapes with decidable index equality, an embedding `e`,
  degrees `i` and `i'`, and `e.f i = i'`; no schemes, sheaves, abelian structure,
  coproducts, preadditivity, or fixed natural/integer grading are needed for
  the natural isomorphism before totalization
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/Algebra/Homology/Embedding/Extend.lean:293`
- source note:        At Mathlib revision
  `520045ab14e26149ee970e2e617ca04b09bde5d6`, the cited
  `HomologicalComplex.extendSingleIso` supplies the objectwise canonical
  comparison. The proposed lift packages those same components as
  `single C c i ⋙ e.extendFunctor C ≅ single C c' i'`; it is not a claim that
  this natural wrapper is already declared in the pin. A unique scratch
  probe, `.lake/sf8_554_target_altitude_single_extend_20260927.lean`, compiled
  this naturalization, its `ChainComplex.single₀` / `embeddingDownNat`
  specialization, and its cochain lift using pinned
  `CategoryTheory.NatIso.mapHomologicalComplex`
  (`Mathlib/Algebra/Homology/Additive.lean:196`). The only printed axioms were
  `propext`, `Classical.choice`, and `Quot.sound`. This finding is distinct from
  the objectwise ancestor noted in pending PR #1600: it checks arbitrary-shape
  naturality and the reusable outer-complex transport. The mapped single
  presentation still needs an explicit comparison with the flipped
  `singleZeroBicomplex` presentation before composing with that PR's
  `singleZeroFlipTotalIso`; an `Iso.refl` probe did not elaborate, which is
  evidence only against that attempted definitional identification. Whiskering
  with pinned `HomologicalComplex₂.totalFunctor`
  (`Mathlib/Algebra/Homology/TotalComplex.lean:467`) requires that functor's
  ambient total-existence assumptions. No total augmentation quasi-isomorphism
  or K-flatness claim follows from these comparisons.
- state:              UNVERIFIED

### 2026-09-27 — omit explicit decidable index equality from natural single extension (planned)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `HomologicalComplex.singleCompExtendIso`, extending
  `Algebra/Homology/Embedding/Extend.lean`
- weaker hypotheses:  `[Category C] [HasZeroObject C] [HasZeroMorphisms C]`,
  arbitrary index types and shapes, `e : c.Embedding c'`, `i`, `i'`, and
  `h : e.f i = i'`; neither `[DecidableEq ι]` nor `[DecidableEq ι']`
  is an explicit parameter
- level:              L (proof-witness verified)
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        `.lake/sf8_554_target_hypothesis_verified_20260927.lean`
  compiled with Lean v4.32.1, exit 0. Its
  `SF8554TargetHypothesisScout20260927.singleCompExtendIso` uses the altitude
  scout's complete naturality proof unchanged under `open scoped Classical`.
  `#print` confirms both decidability parameters are absent; `#print axioms`
  reports only `propext`, `Classical.choice`, and `Quot.sound`. This supplies
  classical decisions inside the signature; it does not make `single`
  independent of its chosen decisions. Preserving ambient instances in the
  generic public wrapper remains useful for definitional interoperability.
- state:              UNVERIFIED

### 2026-09-27 — construct the zero morphisms needed by natural single extension (planned)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `HomologicalComplex.singleCompExtendIso`, with the
  existing `CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject`
- weaker hypotheses:  `[Category C] [HasZeroObject C]`, arbitrary index types
  and shapes, embedding, degrees and `e.f i = i'`; zero morphisms are chosen
  locally and index equality is supplied classically
- level:              L (proof-witness verified)
- pin status:         PIN-CONFIRMED
  `Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean:258`
- source note:        In
  `.lake/sf8_554_target_hypothesis_verified_20260927.lean`,
  `SF8554TargetHypothesisDerivedZeros20260927.singleCompExtendIso` compiles
  using `letI : HasZeroMorphisms C :=
  HasZeroObject.zeroMorphismsOfZeroObject (C := C)` in both its result type and
  proof. `SF8554TargetHypothesisNativeDerivedZeros20260927.mappedSingleZeroExtendDownNatIso`
  separately verifies the same deletion for the native `ChainComplex.single₀`
  / `embeddingDownNat` specialization and its outer cochain lift. Both print
  only the standard three axioms. A further compiled example proves agreement
  with any ambient `HasZeroMorphisms C` by `Subsingleton.elim`. This agreement
  is propositional: Mathlib's comment immediately preceding the constructor
  explicitly warns that the constructed instance need not be definitionally
  equal to an additive category's existing instance. This is a verified logical
  redundancy, not a recommendation to replace the ambient-instance API.
- state:              UNVERIFIED

### 2026-09-27 — eliminate the output-degree equality by fixing its value (planned)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `HomologicalComplex.singleCompExtendIso`
- weaker hypotheses:  category, zero object, zero morphisms, arbitrary shapes,
  embedding `e` and source degree `i`; the target is `single C c' (e.f i)`
- level:              L (proof-witness verified)
- pin status:         PIN-CONFIRMED
- source note:        `singleCompExtendAtImageIso` in
  `.lake/sf8_554_target_hypothesis_verified_20260927.lean` compiles by applying
  the generic comparison with `i' := e.f i` and `rfl`. This removes a redundant
  parameter and its equality proof together; it does not justify deleting
  the equality while keeping an independently selected `i'`.
- state:              UNVERIFIED

### 2026-09-27 — natural single extension lifts along any outer complex shape (planned)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `HomologicalComplex.singleCompExtendIso`, consumed by
  pinned `CategoryTheory.NatIso.mapHomologicalComplex`
- weaker hypotheses:  the category, zero object, zero morphisms and embedding
  comparison above, plus an arbitrary `κ : Type*` and `d : ComplexShape κ`;
  no outer `[DecidableEq κ]`, fixed `ℤ`, preadditivity, abelian structure,
  boundedness, or total-existence assumption
- level:              L (proof-witness verified)
- pin status:         PIN-CONFIRMED `Mathlib/Algebra/Homology/Additive.lean:196`
- source note:        `SF8554TargetHypothesisScout20260927.mappedSingleCompExtendIso`
  in `.lake/sf8_554_target_hypothesis_verified_20260927.lean` compiles directly
  as `NatIso.mapHomologicalComplex (singleCompExtendIso e i i' h) d`. The two
  required zero-preservation instances are inferred from the single and
  extension functors. Its printed signature contains none of the omitted
  assumptions and its axioms are the standard three. The scratch file imports
  only `Mathlib.Algebra.Homology.Embedding.Extend`; the altitude witness's
  `TotalComplex` import is unnecessary for these comparisons. This is an outer
  complex comparison and asserts no totalization quasi-isomorphism.
- state:              UNVERIFIED

### 2026-09-27 — native zero-degree extension needs no caller index data (planned)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  natural single extension specialized to
  `ChainComplex.single₀` and `ComplexShape.embeddingDownNat`
- weaker hypotheses:  only `{C : Type u} [Category.{v} C] [HasZeroObject C]
  [HasZeroMorphisms C]`; no index types, decidability instances, embedding,
  degrees, or equality supplied by the caller
- level:              L (proof-witness verified)
- pin status:         PIN-CONFIRMED
- source note:        In
  `.lake/sf8_554_target_hypothesis_verified_20260927.lean`, the namespace
  `SF8554TargetHypothesisNative20260927` rechecks the altitude witness with
  the ambient decidability parameters preserved in its generic helper.
  `#print singleZeroExtendDownNatIso` and
  `#print mappedSingleZeroExtendDownNatIso` show exactly the four parameters
  above. The equality is discharged by `simp`, the two concrete index
  instances are synthesized, and the lift uses `NatIso.mapHomologicalComplex`.
  Both the specialization and its lift compile with no additional assumptions.
- state:              UNVERIFIED

### 2026-09-27 — weaken the category of natural single extension to CategoryStruct (failed)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the same pinned single/extension API with only
  `[CategoryStruct C]`
- weaker hypotheses:  remove category laws while retaining objects, morphisms,
  identities and composition
- source note:        `.lake/sf8_554_target_hypothesis_failures_20260927.lean`
  attempts both `HasZeroObject C` and
  `HomologicalComplex C (ComplexShape.up ℤ)` under `[CategoryStruct C]`.
  Lean reports `failed to synthesize instance of type class Category ... C`
  at lines 10 and 11. This falsifies literal deletion in the existing API;
  it is not a counterexample about a different encoding. Functors, complex
  categories, and the naturality proof all use the category structure.
- state:              FALSIFIED (the proposed signature does not elaborate)

### 2026-09-27 — omit zero morphisms without installing their construction (failed)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  native single/extension API with automatic zero-morphism
  synthesis from a zero object
- weaker hypotheses:  `[Category C] [HasZeroObject C]`, with no local choice
  of `HasZeroMorphisms C`
- source note:        `.lake/sf8_554_target_hypothesis_failures_20260927.lean:17`
  and line 18 check `ChainComplex.single₀ C` and
  `ComplexShape.embeddingDownNat.extendFunctor C`. Both report
  `failed to synthesize instance of type class HasZeroMorphisms C`.
  The successful explicit local construction is recorded above; the failure
  is about automatic instance search, not mathematical existence.
- state:              FALSIFIED (the unmodified signature does not elaborate)

### 2026-09-27 — omit the zero object or replace it by a distinguished object (failed)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the same pinned single/extension API without
  `[HasZeroObject C]`
- weaker hypotheses:  `[Category C] [HasZeroMorphisms C]`, first alone and
  then additionally `[Zero C]`
- source note:        `.lake/sf8_554_target_hypothesis_failures_20260927.lean`
  checks generic `single` and `extendFunctor`, the native `single₀` and
  `embeddingDownNat.extendFunctor`, and `single`/`single₀` again with `[Zero C]`.
  All report `failed to synthesize instance of type class HasZeroObject C`.
  The proof uses zero-object uniqueness off the support, and extension uses
  the zero object outside the embedding's image. A chosen object with a
  supplied `IsZero` proof would reintroduce equivalent evidence; a bare
  distinguished object does not. This records the existing API's requirement,
  not an impossibility result for every special shape or alternative proof.
- state:              FALSIFIED (the proposed signatures do not elaborate)

### 2026-09-27 — omit decidable indices without supplying classical decisions (failed)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the same pinned `HomologicalComplex.single` API
- weaker hypotheses:  remove `[DecidableEq ι]` and `[DecidableEq ι']`
  independently, without enabling a classical instance
- source note:        The `NoSourceDecidableEq` and `NoTargetDecidableEq`
  sections of `.lake/sf8_554_target_hypothesis_failures_20260927.lean` each
  check the corresponding `single`. Lean reports respectively
  `failed to synthesize instance of type class DecidableEq ι` and
  `failed to synthesize instance of type class DecidableEq ι'`.
  The successful classical wrapper above resolves exactly these failures;
  this row does not claim that decidability is an essential mathematical
  hypothesis of a noncomputable comparison.
- state:              FALSIFIED (literal binder deletion without replacement)

### 2026-09-27 — independently choose a different degree for extended single complexes (failed)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `HomologicalComplex.extendSingleIso` or its natural
  wrapper without `e.f i = i'`
- weaker hypotheses:  retain independent `i : ι` and `i' : ι'`, removing
  their equality constraint
- source note:        The direct reuse attempt in
  `.lake/sf8_554_target_hypothesis_failures_20260927.lean` fails with the
  remaining goal `⊢ e.f i = i'`. More decisively,
  `SF8554TargetHypothesisScout20260927.noExtendSingleIsoOffImage` in the
  verified probe proves that `e.f i ≠ i'` and `¬ IsZero X` imply
  `¬ Nonempty ((((single C c i).obj X).extend e) ≅ (single C c' i').obj X)`.
  Evaluation at `e.f i` would identify `X` with the target's zero object.
  The compiler accepts that obstruction with only the standard three axioms.
  No different proof can supply the unconstrained comparison in this case;
  fixing `i' := e.f i`, or imposing a zero-object degeneracy, changes the claim.
- state:              FALSIFIED (proved obstruction for unequal degrees and nonzero input)

### 2026-09-27 — treat a classical single wrapper as definitionally the native single₀ (failed)
- chunk:              sf8-554-target-comparison
- reviewing commit:   f18bf326077601e1502702b6e6dc154a0a34f057
- found by:           hypothesis-elimination-scout
- proposed ancestor:  direct native specialization of a generic wrapper
  whose signature fixes classical decidability
- weaker hypotheses:  omit the generic decidability parameters and expect
  the resulting concrete specialization to identify definitionally with
  `ChainComplex.single₀`
- source note:        The retained
  `.lake/sf8_554_target_hypothesis_classical_native_attempt_20260927.lean`
  and its log show the attempted direct specialization failing at line 40:
  the source uses `@HomologicalComplex.single ... ℕ
  (fun a b => Classical.propDecidable (a = b)) ...`, whereas the expected
  `single₀` uses `instDecidableEqNat`. The attempted `simpa only` transport
  did not close this mismatch. This falsifies that attempted definitional
  reuse, not the existence of a comparison; a different proof could transport
  between the decisions using their propositional equality. The verified
  native specialization instead retains the generic helper's ambient
  decidability parameters and needs no explicit decisions from callers.
- state:              FALSIFIED (attempted definitional identification fails)

### 2026-09-27 — one-step compatibility suffices for triangulatedness transfer (planned)
- chunk:              1369-shiftcompat-unification
- reviewing commit:   00196ff8fa17f1904a68e0bdccd633ae2fe86d64
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Functor.isTriangulated_of_iso` and
  `Functor.mapTriangleIso`
- weaker hypotheses:  keep the chosen `[F₁.CommShift ℤ]` and
  `[F₂.CommShift ℤ]`, but require only
  `NatTrans.CommShiftCore e.hom (1 : ℤ)` rather than the full
  `[NatTrans.CommShift e.hom ℤ]`; retain `[F₁.IsTriangulated]` and the usual
  pretriangulated-category context
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/CommShift.lean:296-318`
  and `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Functor.lean:258`
- source note:        `/tmp/issue1369_single_shift_probe.lean` copies the
  triangle-isomorphism proof using only the core compatibility at `+1`, then
  transfers distinguishedness by `isomorphic_distinguished`. The theorem
  `isTriangulated_of_iso_of_core` compiled with exit code 0 under
  `~/.elan/bin/lake env lean /tmp/issue1369_single_shift_probe.lean`. The
  selected target `CommShift` remains an independent input; this does not
  manufacture it via `Functor.CommShift.ofIso`.
- state:              L (proof-witness verified)

### 2026-09-27 — derive inverse shift compatibility for equivalence transfer (planned)
- chunk:              1369-shiftcompat-unification
- reviewing commit:   00196ff8fa17f1904a68e0bdccd633ae2fe86d64
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Equivalence.IsTriangulated`, using
  `Equivalence.commShiftInverse` and `Equivalence.commShift_of_functor`
- weaker hypotheses:  an equivalence `E`, its selected forward
  `[E.functor.CommShift ℤ]`, and `[E.functor.IsTriangulated]`; no independently
  supplied `[E.inverse.CommShift ℤ]` or `E.CommShift ℤ` is needed. The inverse
  shift and adjunction compatibility are derived from the chosen forward shift.
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/Adjunction.lean:617-624`
  and `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Adjunction.lean:197-221`
- source note:        `equivalenceIsTriangulated` in
  `/tmp/issue1369_hypothesis_probe.lean` builds a selected forward shift from
  the packaged comparison, derives the inverse and equivalence compatibility
  with Mathlib, and applies `Equivalence.IsTriangulated.mk'`. The generic
  wrapper compiled with exit code 0 under `~/.elan/bin/lake env lean
  /tmp/issue1369_hypothesis_probe.lean`.
- state:              L (proof-witness verified)

### 2026-09-27 — drop all shift compatibility evidence for exactness transfer (attempted)
- chunk:              1369-shiftcompat-unification
- reviewing commit:   00196ff8fa17f1904a68e0bdccd633ae2fe86d64
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.Functor.isTriangulated_of_iso`
- weaker hypotheses:  retain both selected functor `CommShift ℤ` structures
  and source triangulatedness, but omit compatibility of `e.hom` with the
  selected shifts
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Functor.lean:258`
- source note:        `/tmp/issue1369_drop_comparison_compat.lean` attempts
  `Functor.isTriangulated_of_iso α` after deleting only
  `[NatTrans.CommShift α.hom ℤ]`. Lean reports `failed to synthesize instance
  of type class NatTrans.CommShift α.hom ℤ`. The one-step witness above shows
  that compatibility specifically at `+1` is sufficient for a weaker custom
  wrapper, but some compatibility evidence cannot be dropped from the
  transported-triangulation proof.
- state:              FALSIFIED (literal compatibility-evidence deletion fails)

### 2026-09-30 — `discretePseudofunctorMap` (issue #1635)
- chunk:              1635-representable-stacks
- reviewing commit:   a30793798c7faecef2a83895df639b53934eb3f8
- found by:           altitude-scout
- proposed ancestor:  a natural-transformation adapter for
  `Functor.toPseudofunctor'`, owned by
  `CategoryTheory/Bicategory/Functor/LocallyDiscrete.lean`; a discrete map
  specializes it using `Functor.whiskerRight φ typeToCat`
- weaker hypotheses:  `{I B : Type*} [Category* I] [Bicategory B] [Strict B]
  and `{F G : I ⥤ B} (φ : F ⟶ G)`; no presheaf variance, discrete fibers,
  sheaf condition, Grothendieck topology, groupoid condition, or scheme
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/LocallyDiscrete.lean:146`
- source note:        At the pin `Functor.toPseudofunctor'` already promotes an
  ordinary functor into any strict bicategory. The precise NatTrans adapter
  is not declared there; it is a new adapter on that existing root, with
  `app T := φ.app T.as` and `naturality f := eqToIso (φ.naturality f.as)`.
  The three coherence proofs reduce using `LocallyDiscrete.eq_of_hom`,
  `Strict.leftUnitor_eqToIso`, `Strict.rightUnitor_eqToIso`, and
  `Strict.associator_eqToIso`. Its proposed implementation is typechecked
  in `scratch/altitude-probe-1635.lean:29`.
  `Functor.whiskerRight` is at
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Whiskering.lean:61`, with
  component `typeToCat.map (φ.app T)`. `typeToCat` is at
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Cat.lean:408`,
  and its map is literally `Discrete.functor (Discrete.mk ∘ f)` (:410).
  Scratch examples at :42 and :47 confirm by `rfl` both
  `Discrete.mk (φ.app T x)` and `Discrete.mk (g ≫ f)` for `yoneda.map f`.
  This is a possible foundation for later consolidation, not a request to
  introduce another pseudofunctor or stack carrier.
- state:              UNVERIFIED

### 2026-09-30 — `StackInGroupoids.representable` (issue #1635)
- chunk:              1635-representable-stacks
- reviewing commit:   a30793798c7faecef2a83895df639b53934eb3f8
- found by:           altitude-scout
- proposed ancestor:  the existing `stackInGroupoidsOfSheaf` constructor,
  specialized with `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`;
  the upstream represented-sheaf API is `CategoryTheory/Sites/Canonical.lean`
- weaker hypotheses:  arbitrary `C`, arbitrary subcanonical `J`, and any
  `{P : Cᵒᵖ ⥤ Type w} [P.IsRepresentable]`; the underlying discrete-stack
  constructor already works for any `P` supplied with a `J`-sheaf proof
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Canonical.lean:151`
- source note:        The pinned theorem is universe-general in `P` and is
  stronger than a theorem restricted to literal `yoneda.obj X`. The same
  file packages the entire sheaf-valued Yoneda functor as
  `GrothendieckTopology.yoneda` (:168) and its raised-universe variant
  `uliftYoneda` (:176). For relative sites the existing instance
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/SubcanonicalOver.lean:25`
  proves `(J.over X).Subcanonical` without geometry. The repository root
  `DerivedAlgGeo/CategoryTheory/Sites/Descent/StackInGroupoids/Discrete.lean:131`
  already supplies the stack constructor and :28 supplies its pseudofunctor;
  a new representable carrier, independently assumed descent, or a relative
  representable carrier is unnecessary. The issue's `yoneda.obj X`
  specialization can keep the existing `StackInGroupoids` owner.
- state:              UNVERIFIED

### 2026-09-30 — `fppfTopology_eq_propQCTopology` and `etaleTopology_eq_propQCTopology` (issue #1635)
- chunk:              1635-representable-stacks
- reviewing commit:   a30793798c7faecef2a83895df639b53934eb3f8
- found by:           altitude-scout
- proposed ancestor:  `AlgebraicGeometry/Sites/QuasiCompact.lean`, with
  `precoverage P = propQCPrecoverage P` and
  `grothendieckTopology P = propQCTopology P` for every open-map property `P`
- weaker hypotheses:  `{P : MorphismProperty Scheme.{u}}`
  `(hP : P ≤ fun _ _ f ↦ IsOpenMap f.base)` only; no multiplicativity,
  base-change stability, flatness, local finite presentation, or étaleness
  is needed for the generic equality
- pin status:         PIN-CONFIRMED
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/QuasiCompact.lean:87`
- source note:        The pinned source already proves
  `precoverage P ≤ qcPrecoverage` from exactly `hP`.
  `propQCPrecoverage P` is `qcPrecoverage ⊓ precoverage P` (:112), so
  `le_antisymm (le_inf (precoverage_le_qcPrecoverage_of_isOpenMap hP) le_rfl)
  inf_le_right` proves the equality. `congrArg Precoverage.toGrothendieck`
  proves the corresponding topology equality. Both typechecked as scratch
  examples (:10 and :18) without extra hypotheses. Exact equality names are
  absent at the pin; this is a pin-supported generic derivation, not a claim
  that the requested fppf/étale equalities are already named. The fppf
  specialization repeats Mathlib's own use of the open-map inequality in
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:66`.
  The generic equality is an extension of scheme-site machinery, not neutral
  category theory: quasi-compact covers and underlying open maps keep its
  owner under `AlgebraicGeometry/Sites/`.
- state:              UNVERIFIED


### 2026-09-30 — individual representables need only objectwise sheafhood

- chunk: `stk2-1-1635-representable-stacks`
- reviewing commit: a30793798c7faecef2a83895df639b53934eb3f8
- found by: `hypothesis-elimination-scout`
- proposed ancestor: existing `stackInGroupoidsOfSheaf` and planned
  `StackInGroupoids.discreteMap`, in `CategoryTheory/Sites/Descent/StackInGroupoids/`
- weaker hypotheses: arbitrary category `C`; `Presieve.IsSheaf J (yoneda.obj X)`
  for one constructor, and the two objectwise sheaf proofs for a map;
  omit `[J.Subcanonical]` from this proof-witness formulation.
- pin status: `PIN-CONFIRMED`
- source note: private scratch file compiled with the exact bounded command
  above. `PUnit` at the top topology verifies that this is strictly weaker than
  requiring all representables to be sheaves. No new public root is required.
- state: UNVERIFIED
- proof classification: L (proof-witness verified; compiled candidate, not merged)

### 2026-09-30 — restriction needs no explicit lower subcanonical class

- chunk: `stk2-1-1635-representable-stacks`
- reviewing commit: a30793798c7faecef2a83895df639b53934eb3f8
- found by: `hypothesis-elimination-scout`
- proposed ancestor: planned `StackInGroupoids.representable_ofLE`, with the
  arbitrary-sheaf restriction equality in `Discrete.lean`
- weaker hypotheses: retain `[J₂.Subcanonical]`, `h : J₁ ≤ J₂`, and `X : C`;
  omit `[J₁.Subcanonical]` and derive it with Mathlib's
  `GrothendieckTopology.Subcanonical.of_le h`. More generally retain only a
  sheaf proof for arbitrary `P` at `J₂`, and transport it by
  `Presieve.isSheaf_of_le _ h hP`.
- pin status: `PIN-CONFIRMED`
- source note: both resulting equalities compile by `rfl` in the private
  scratch file with the exact bounded command above.
- state: UNVERIFIED
- proof classification: L (proof-witness verified; compiled candidate, not merged)

### 2026-09-30 — QC comparison consumes ordinary openness only

- chunk: `stk2-1-1635-representable-stacks`
- reviewing commit: a30793798c7faecef2a83895df639b53934eb3f8
- found by: `hypothesis-elimination-scout`
- proposed ancestor: `AlgebraicGeometry.Scheme.precoverage_eq_propQCPrecoverage_of_isOpenMap`
  and induced topology equality, beside Mathlib's `Sites/QuasiCompact.lean`
- weaker hypotheses: any `P : MorphismProperty Scheme.{u}` and
  `P ≤ fun _ _ f ↦ IsOpenMap f.base`; omit flatness, local finite presentation,
  étaleness, stability, multiplicativity, locality, or finiteness assumptions.
- pin status: `PIN-CONFIRMED`
- source note: `le_antisymm (le_inf
  (precoverage_le_qcPrecoverage_of_isOpenMap hP) le_rfl) inf_le_right`
  compiles, and `congrArg Precoverage.toGrothendieck` gives the topology
  equality. The parent plans these generic results in
  `DerivedAlgGeo/AlgebraicGeometry/Sites/QuasiCompact.lean`.
- state: UNVERIFIED
- proof classification: L (proof-witness verified; compiled candidate, not merged)

### 2026-09-30 — delete subcanonicity without an objectwise sheaf replacement

- chunk: `stk2-1-1635-representable-stacks`
- reviewing commit: a30793798c7faecef2a83895df639b53934eb3f8
- found by: `hypothesis-elimination-scout`
- attempted weaker hypotheses: arbitrary category `C`, topology `J`, object `X`,
  with no `[J.Subcanonical]` and no `IsSheaf J (yoneda.obj X)` proof.
- pin status: `PIN-CONFIRMED`
- source note: compiled `bool_yoneda_not_sheaf_top` and
  `bool_discrete_not_stack_top` for `C = Type`, `J = ⊤`, `X = Bool`.
  The empty cover of `PUnit` makes the false and true maps have indistinguishable
  descent data. Full faithfulness would produce a morphism between their
  discrete fibre objects, forcing `false = true`.
- state: `FALSIFIED (compiled counterexample)`

### 2026-09-30 — a morphism and one sheaf endpoint imply the other endpoint is a sheaf

- chunk: `stk2-1-1635-representable-stacks`
- reviewing commit: a30793798c7faecef2a83895df639b53934eb3f8
- found by: `hypothesis-elimination-scout`
- attempted weaker hypotheses: only the source sheaf proof or only the target
  sheaf proof in `discreteMap`, retaining the natural transformation.
- pin status: `PIN-CONFIRMED`
- source note: compiled examples give arrows `PUnit ⟶ Bool` and `Bool ⟶ PUnit`,
  while `yoneda.obj PUnit` is a sheaf at `⊤` and `yoneda.obj Bool` is not.
  Thus neither endpoint's proof can generally be reconstructed from the other.
- state: `FALSIFIED (compiled counterexample)`

### 2026-09-30 — reverse topology restriction

- chunk: `stk2-1-1635-representable-stacks`
- reviewing commit: a30793798c7faecef2a83895df639b53934eb3f8
- found by: `hypothesis-elimination-scout`
- attempted weaker hypotheses: use descent for a coarser topology to obtain
  descent for a finer topology without further proof.
- pin status: `PIN-CONFIRMED`
- source note: compiled conjunction proves `yoneda.obj Bool` is a sheaf for
  `⊥` by `Presieve.isSheaf_bot` and is not a sheaf for `⊤` by the empty-cover
  counterexample. The associated discrete pseudofunctor fails the `⊤` stack
  condition by the compiled direct descent proof.
- state: `FALSIFIED (compiled counterexample)`

### 2026-09-30 — dropping the open-map premise from QC comparison (issue #1635)
- chunk: 1635-representable-stacks
- reviewing commit: 068871899ba704007712939699dbbe7dc5c00d8f
- found by: mathematics-adversary
- proposed ancestor: `AlgebraicGeometry/Sites/QuasiCompact.lean`
- weaker hypotheses: arbitrary scheme morphism property, without the open-map premise
- source note: The review's compiled point-family counterexample takes an infinite affine
  scheme and its residue-field points. The family is jointly surjective, hence a cover for
  the unrestricted property, but cannot satisfy the quasi-compact covering condition:
  finitely many source point opens cover only finitely many target points. The empty-cover
  and point-family proof witnesses are kept in the private transcript supplement for #1635.
- state: FALSIFIED (infinite affine residue-field point family)

### 2026-09-30 — `Lattice.pairCharge` over a nonsymmetric form (issue #1230, withdrawn)
- chunk:              none (owner decision on #1230)
- reviewing commit:   3f6453a3
- found by:           second-consumer research agent, spot-checked by hand
- proposed ancestor:  a `LinearAlgebra/BilinearForm/` root `pairCharge b x y v`
  with `b` not assumed symmetric, above `PeriodDomain.centralCharge`
  (`QuadraticForm/ComplexPairing.lean:79`) and `Mukai.expCharge`
  (`CentralCharge/Mukai/Charge.lean:50`)
- weaker hypotheses:  a real bilinear form with no symmetry. Neither leaf's API
  uses symmetry except `expCharge_apply`, which needs it through
  `polar_realForm`.
- pin status:         not applicable; no Mathlib declaration is involved
- source note:        `expCharge` is `centralCharge (realForm b)` by definition,
  so the two were already one root. For nonsymmetric `b`, `polar (realForm b)` is
  the symmetrization of `realPairing b`, so `expCharge = pairCharge (realPairing
  b)` fails. The surviving Lift is add/smul/zero/kernel lemmas of about one line
  each with no consumer. The one hand-rolled copy of the form is `cPair`
  (`Exponential/Divisorial.lean:101`), which is symmetric (follow-up #1810). `Mukai.Graded.pairing`
  has no consumer: n = 2 is `realPairing (LinearMap.mul ℝ ℝ)` and the odd form is
  a recorded negative result.
- state:              FALSIFIED (as motivated: nonsymmetry admits no leaf, and `expCharge ≠ pairCharge (realPairing b)` for nonsymmetric `b`)
