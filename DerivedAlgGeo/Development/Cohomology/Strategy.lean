/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional

/-!
# Layer B stage 3 — which cohomology finiteness theorem this library will prove

**This file proves nothing.** It is a compile-only API map recording the decision taken in
issue #26, and it exists so that the next session can start the finiteness proof without
repeating the reconnaissance. Every declaration below is an `example` naming an upstream
declaration, so the file fails to build the day one of them moves — which is the only
reason to keep it. Delete it once the decision is encoded in real theorem statements.

## The question

The project milestones target smooth projective varieties over a field, while this strategy was written
promising cohomology finiteness for all **proper** schemes over a field. Those are not the
same theorem and they do not cost the same. This file decides which one is supportable on
`leanprover/lean4:v4.29.0` with the pinned Mathlib, and fixes the hypotheses that appear in
each downstream statement.

## What is upstream, precisely

*Sheaf cohomology exists, with almost no API.* `CategoryTheory.Sheaf.H F n` is defined as
`Ext` from the constant sheaf `ULift ℤ` in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`. It occurs in exactly two Mathlib
files — that one and `MayerVietoris.lean`. There is no vanishing theorem, no finiteness
theorem, and no comparison with Čech cohomology; `Cech.lean` supplies
`cechComplexFunctor` and stops there. DerivedAlgGeo now supplies the explicit affine Čech
calculation
in #13 and the single-cover Čech-to-derived comparison in #27.

*Coherent cohomology does not exist upstream at all.* There is no proper-pushforward
finiteness theorem, no Serre finiteness, and no coherent-cohomology anything.
`AlgebraicGeometry.IsProper` is available as a class with the expected stability lemmas,
and `Proj 𝒜 ⟶ Spec 𝒜₀` is known to be proper — but properness of the morphism is the only
part of the classical argument that is in place.

*The projective route now has an explicit construction boundary.*
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` contains the structure sheaf, the proof
that `Proj` is a scheme, functoriality, and properness, but still no modules. DerivedAlgGeo now
supplies
degree-zero localized modules, the locally fractional associated sheaf, integer twists and
`O(d)`. The structure module is canonically identified with Mathlib's structure sheaf, and every
nonnegative twist is explicitly trivialized on a degree-one chart, including bijectivity of the
canonical basic-open section map. `Proj.Modules.Finiteness` derives quasi-coherence and coherence
from visible affine comparison data and exposes a degree-bounded global-section interface.
`Proj.Modules.ProjectiveSpace` now proves the concrete polynomial comparison
`R[Xᵢ]_d ≃ Γ(Proj R[Xᵢ], O(d))` over a field (for at least two variables), proves that the
variable charts cover, and exposes every degreewise Čech term as a homogeneous localization.
What remains for #29 is the cohomological Serre-finiteness argument; it must not try to prove the
affine Čech terms finite-dimensional over the field.

*The affine-cover route is complete.* `IsAffineOpen.inf` and
`IsAffineOpen.iInf` give affineness of intersections under an affine diagonal — the
separatedness hypothesis in the Čech argument, in the exact form Mathlib states it — and
`IsNoetherian X` already packages locally noetherian with quasi-compactness. #103 constructs the
non-circular compact-basis comparison of Stacks Tag 01EW, and #28 combines it with affine Čech
exactness to prove unconditional positive-degree derived vanishing for affine quasi-coherent
sheaves.

## The decision

**B3 proves vanishing, not finite-dimensionality.** Concretely, stage B3 splits along a
line that was not visible when it was written:

* **Affine vanishing is complete.** #13 proves affine Čech exactness, #27 proves the
  single-cover comparison, #103 constructs the compact-basis witness, and #28 transports the
  result across the affine module/sheaf equivalence. Properness and a base field do not enter
  this vanishing layer.
* **Still not proved.** #29, finite-dimensionality of `H^i(X, F)` over a field. Its Proj object,
  polynomial global-section comparison, variable-cover algebra, finiteness interfaces, and
  canonical functorial `k`-linear lift of derived cohomology now exist; the cohomological Serre
  resolution argument remains. The affine terms of a projective standard-cover Čech complex are
  generally infinite-dimensional over the field, so finiteness must be proved for its homology
  using grading rather than termwise. The exact output type is `FiniteDimensionalCohomology`; it
  deliberately contains no eventual-vanishing claim. #31 and #32 are downstream of it.

So the milestone target moves from "proper over a field" to **separated noetherian**, for
vanishing only. The projective-to-proper question (#26 question 3, Chow's lemma plus
dévissage) does not arise: this library does not reach the projective case either.

**Consequence for #31 and #32.** The Euler characteristic cannot be *defined* by a theorem
this stage will prove, so it must take finiteness as an input rather than derive it. #31 is now
implemented by `DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Basic`: `χ` is
relative to a
`FiniteCohomology` package extending the #29 `FiniteDimensionalCohomology` interface with the
separate #30 eventual-vanishing bound. #32 proves
additivity from the `Ext` long exact sequence (`Ext.covariantSequence_exact`) plus that bound,
with the hypotheses carried. It is implemented by
`DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Additivity`; the only additional
input is the
base-field-linearity of the connecting maps, since Mathlib currently exposes them only as
additive homomorphisms. Both results become unconditional when Serre finiteness and that
linear compatibility land, without restating them. This keeps the trust boundary where
`CONTRIBUTING.md` puts it: a hypothesis in a statement, never an axiom and never a `sorry`.

## Two shape facts that fix every B3 statement

Both were established by elaboration, not by reading, and both are load-bearing:

1. **`Sheaf.H` needs an explicit `HasExt` and raises the universe.** For `X : Scheme.{u}`
   there is no `HasExt` instance in scope for the Zariski sheaf category; one has to be
   supplied as `HasExt.standard`, and because `Sheaf J AddCommGrpCat.{u}` lives in
   `Type (u + 1)`, the only instance available is `HasExt.{u + 1}`. Cohomology of a sheaf on
   a `Scheme.{u}` therefore lands in `Type (u + 1)`. Every B3 statement inherits that bump;
   deciding it once here is cheaper than each file discovering it.
2. **The bridge from `X.Modules` to abelian sheaves is
   `(SheafOfModules.toSheaf X.ringCatSheaf).obj`.** It is `Additive` and
   `PreservesFiniteLimits`. DerivedAlgGeo's `Scheme.Modules.toSheaf` wrapper also preserves finite
   colimits, so a short exact sequence in `X.Modules` remains short exact in
   `Sheaf J AddCommGrpCat` before `Ext.covariantSequence_exact` applies. The central action of
   global functions now supplies the canonical scalar-linear cohomology functor. Linearity of the
   separately constructed `Ext` connecting morphisms remains an explicit #32 input.

## Dependency graph for #29–#32

```text
  #13 + #27 ──> #103 ──> #28 ──> #30 ──┐
                                         ├──> #31 ──> #32
  toSheaf preserves epis ──────────────┘

  #57/#94–#96 ──> #97 polynomial global/Čech algebra ──> #29
```

## Not done here

No Serre-finiteness theorem is proved here. The completed affine boundary and the Proj module,
global-section, and variable-Čech machinery live in real implementation modules; this file pins
the declarations that #29 will consume.

## References

* [Stacks, Tag 01X8](https://stacks.math.columbia.edu/tag/01X8) — cohomology of quasi-coherent
  sheaves on affines vanishes
* [Stacks, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB) — Čech cohomology on a
  separated scheme computes sheaf cohomology
* [Stacks, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW) — the basis/cofinal-cover
  criterion needed for the non-circular affine proof
* [Stacks, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1) — finiteness for proper
  morphisms, the theorem this stage does **not** prove
* Hartshorne, *Algebraic Geometry*, III.4 (Čech) and III.5 (Serre finiteness)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Cohomology.Strategy

/-! ### The cohomology of a sheaf of modules on a scheme is formable

This is the fact that decides the shape of every statement in B3: the `HasExt` instance
has to be supplied by hand, and the result lands one universe up. -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Cohomology of a sheaf of modules on `X : Scheme.{u}` exists and lands in
`Type (u + 1)`. The `HasExt.{u + 1}` instance is not found by synthesis and is not
`HasExt.{u}`; see the module docstring. -/
noncomputable example (X : Scheme.{u}) (M : X.Modules) (n : ℕ) : Type (u + 1) :=
  letI : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

/-! ### The bridge to abelian sheaves, and exactly how exact it is -/

/-- `toSheaf` is additive. -/
example {C : Type*} [Category C] {J : GrothendieckTopology C} (R : Sheaf J RingCat) :
    (SheafOfModules.toSheaf R).Additive := inferInstance

/-- `toSheaf` preserves finite limits, hence kernels and monomorphisms. Preservation of
epimorphisms is *not* upstream, and #32 needs it. -/
noncomputable example {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) :=
  inferInstance

/-! ### The long exact sequence engine for #32 -/

/-- The covariant `Ext` long exact sequence attached to a short exact sequence. With
`Sheaf.H` defined as `Ext` from the constant sheaf, this *is* the cohomology long exact
sequence, once the short exact sequence is known to survive `toSheaf`. -/
example := @Abelian.Ext.covariantSequence_exact

/-! ### The Čech side and completed affine comparison -/

/-- Mathlib's Čech complex of a presheaf. There is no comparison with `Sheaf.H` upstream;
the completed #27 comparison lives in DerivedAlgGeo. -/
noncomputable example := @CategoryTheory.cechComplexFunctor

/-- The stable affine boundary used by the completed #28 theorem. -/
example := @AlgebraicGeometry.Cohomology.tilde_H_subsingleton_of_comparisonAt

/-! ### The separatedness hypothesis, in the form Mathlib states it

The Čech route needs a finite affine cover whose finite intersections are affine. Mathlib
supplies the second half from an affine diagonal rather than from `IsSeparated` directly,
so that is the hypothesis B3 statements should carry. -/

/-- Intersections of affine opens are affine when the diagonal is affine. -/
example := @IsAffineOpen.inf

/-- The same for finite non-empty families — the shape a Čech complex actually consumes. -/
example := @IsAffineOpen.iInf

/-- `IsNoetherian X` already packages locally noetherian with quasi-compactness, which is
where the *finite* affine cover comes from. -/
example (X : Scheme.{u}) [IsNoetherian X] : CompactSpace X := inferInstance

/-! ### The current projective boundary

`Proj 𝒜 ⟶ Spec 𝒜₀` is proper upstream. DerivedAlgGeo supplies the missing module and twist objects;
the following compile-only references pin the explicit comparison and finiteness interfaces
that separate completed Proj infrastructure from the remaining #29 proof. -/

/-- Quasi-coherence is a theorem once the standard affine `tilde` comparisons are supplied. -/
example := @AlgebraicGeometry.Proj.AffineComparisonData.associatedSheaf_isQuasicoherent

/-- Coherence exposes every chart-level noetherianity and finite-generation assumption. -/
example := @AlgebraicGeometry.Proj.associatedSheaf_isCoherent_of_noetherian_finite

/-- The global-section theorem is degree-bounded and therefore no stronger than its algebraic
comparison data. -/
example := @AlgebraicGeometry.Proj.TwistingSectionRange.globalSections_finite

/-- Finite-variable homogeneous polynomials supply the finite algebraic source for projective
space in each certified degree. -/
example := @AlgebraicGeometry.Proj.projectiveSpace_globalSections_finite

/-- On each variable chart of polynomial projective space, the canonical section map for a
nonnegative twist is now constructed and bijective. -/
example := @AlgebraicGeometry.Proj.projectiveSpace_variableSection_bijective

/-- Degree-`d` homogeneous polynomials are concretely the global sections of `O(d)`, including
the transported `k`-module structure needed by the #29 finiteness statement. -/
noncomputable example := @AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsModuleIso

/-- Variable-cover Čech terms are explicit homogeneous localizations, without an incorrect
termwise finite-dimensionality assertion. -/
noncomputable example := MvPolynomial.polynomialVariableCechTerm

/-- The exact output boundary for #29: a functorial linear lift of derived cohomology together
with degreewise finite-dimensionality, but no #30 vanishing bound. -/
example {k : Type u} [Field k] (X : Variety k) := FiniteDimensionalCohomology X

/-- The functorial linear lift itself is now canonical; #29 only still owes the geometric
degreewise finite-dimensionality proof. -/
noncomputable example {k : Type u} [Field k] (X : Variety k) :=
  canonicalLinearCohomology X

/-- Properness of `Proj` over its degree-zero part — the one piece of the classical
projective argument that is already available. -/
example {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] : IsProper (Proj.toSpecZero 𝒜) :=
  inferInstance

end Cohomology.Strategy

end AlgebraicGeometry
