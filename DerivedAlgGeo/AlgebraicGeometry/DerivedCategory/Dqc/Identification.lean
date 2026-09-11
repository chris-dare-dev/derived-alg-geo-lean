/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Bounded

/-!
# The bounded-coherent identification from the coherent `Ext` comparison

`Dqc.lean` states the identification `Dᵇ(Coh X) ≌ Dᵇ_coh(Dqc X)` as the explicit
proposition `BoundedCoherentDqcIdentification X`, whose `comparison` field pins
the equivalence to the concrete derived inclusion `boundedCoherentDerivedToDqc X`.
This file reduces that proposition to a single statement about the abelian
categories themselves:

`CoherentExtComparison X`: for coherent sheaves `F G` on `X` and every `n`, the
map `Ext^n_{Coh X}(F, G) → Ext^n_{X.Modules}(F, G)` induced by `Coh.ι X` is a
bijection.

Everything else is formal and is proved here, on any locally noetherian scheme:

* `boundedCoherentDerivedToDqc_full_of_coherentExtComparison`, `boundedCoherentDerivedToDqc_faithful_of_coherentExtComparison`:
  full faithfulness of the derived inclusion on `Dᵇ(Coh X)`, by the amplitude
  dévissage `Functor.mapDerivedCategory_map_bijective_of_bounded`;
* `boundedCoherentDerivedToDqc_essSurj_of_coherentExtComparison`: essential surjectivity onto the
  intrinsic bounded-coherent locus, by the cone argument
  `Functor.exists_bounded_iso_mapDerivedCategory_obj` — the coherent
  approximation of quasi-coherent sheaves is **not** needed for this step;
* `boundedCoherentDqcIdentificationOfCoherentExtComparison`: the inhabitant of
  `BoundedCoherentDqcIdentification X`, with `comparison := Iso.refl _`.

## What remains open

`CoherentExtComparison X` itself. Its target is `Ext` in *all* `𝒪_X`-modules,
not in quasi-coherent ones, and that is what makes it the genuine geometric
content of the identification: the surjection-lifting criterion of Stacks 0FCL
does not apply to `Coh X ⊆ X.Modules` (a coherent sheaf need not map onto a
coherent quotient of an arbitrary module sheaf), so the classical route runs
through `D(QCoh X) ≌ D_qc(X)` (Stacks 08DB) or the injectivity of quasi-coherent
injectives in `X.Modules` (Hartshorne, *Residues and Duality* II.7.18). Neither
is available at this Mathlib pin, and the affine case is not a shortcut: see the
2026-09-10 entry of `docs/architecture/cutover-ledger.md`.

Nothing here inhabits `CoherentExtComparison`; affine noetherian schemes satisfy it by
`Dqc/AffineIdentification.lean`, through the `Ext` comparison from acyclic generators.
-/

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DerivedCategory

noncomputable section

universe u

attribute [local instance] Coh.ι_additive Coh.ι_preservesFiniteLimits
  Coh.ι_preservesFiniteColimits

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- **The coherent `Ext` comparison.** The inclusion `Coh.ι X : Coh X ⥤ X.Modules`
induces bijections `Ext^n_{Coh X}(F, G) → Ext^n_{X.Modules}(F, G)` for all coherent
`F`, `G` and all `n`. This is the exact geometric content of the bounded-coherent
identification; nothing in this file inhabits it. -/
def CoherentExtComparison : Prop :=
  ∀ (F G : Coh X) (n : ℕ), Function.Bijective ((Coh.ι X).mapExtAddHom F G n)

variable {X}

/-- Under the `Ext` comparison, the derived inclusion `Dᵇ(Coh X) ⥤ D(X.Modules)` is
bijective on every hom-set. -/
theorem boundedCoherentDerivedInclusion_map_bijective (h : CoherentExtComparison X)
    (E E' : SchemeBoundedCoherentDerivedCategory X) :
    Function.Bijective
      ((DerivedCategory.Bounded.ι ⋙ coherentDerivedInclusion X).map : (E ⟶ E') → _) := by
  have hι : Function.Bijective ((DerivedCategory.Bounded.ι (C := Coh X)).map : (E ⟶ E') → _) :=
    ⟨DerivedCategory.Bounded.ι.map_injective, DerivedCategory.Bounded.ι.map_surjective⟩
  exact ((Coh.ι X).mapDerivedCategory_map_bijective_of_bounded h E.property E'.property).comp hι

/-- Under the `Ext` comparison, `Dᵇ(Coh X) ⥤ Dqc(X)` restricted to bounded objects is
full. -/
theorem boundedToDqc_full (h : CoherentExtComparison X) :
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedToDqc X).Full := by
  haveI : (DerivedCategory.Bounded.ι ⋙ coherentDerivedInclusion X).Full :=
    ⟨fun g ↦ (boundedCoherentDerivedInclusion_map_bijective h _ _).2 g⟩
  exact Functor.Full.of_comp_faithful_iso (G := SchemeQuasicoherentDerivedCategory.ι X)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (coherentDerivedToDqcCompInclusion X))

/-- Under the `Ext` comparison, `Dᵇ(Coh X) ⥤ Dqc(X)` restricted to bounded objects is
faithful. -/
theorem boundedToDqc_faithful (h : CoherentExtComparison X) :
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedToDqc X).Faithful := by
  haveI : (DerivedCategory.Bounded.ι ⋙ coherentDerivedInclusion X).Faithful :=
    ⟨fun hfg ↦ (boundedCoherentDerivedInclusion_map_bijective h _ _).1 hfg⟩
  exact Functor.Faithful.of_comp_iso (G := SchemeQuasicoherentDerivedCategory.ι X)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (coherentDerivedToDqcCompInclusion X))

/-- **Full faithfulness (#1070).** Under the `Ext` comparison, the concrete functor
`Dᵇ(Coh X) ⥤ Dᵇ_coh(Dqc X)` is full. -/
theorem boundedCoherentDerivedToDqc_full_of_coherentExtComparison (h : CoherentExtComparison X) :
    (boundedCoherentDerivedToDqc X).Full := by
  haveI := boundedToDqc_full h
  change ((schemeBoundedCoherentCohomology X).lift
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedToDqc X) _).Full
  infer_instance

/-- **Full faithfulness (#1070).** Under the `Ext` comparison, the concrete functor
`Dᵇ(Coh X) ⥤ Dᵇ_coh(Dqc X)` is faithful. -/
theorem boundedCoherentDerivedToDqc_faithful_of_coherentExtComparison (h : CoherentExtComparison X) :
    (boundedCoherentDerivedToDqc X).Faithful := by
  haveI := boundedToDqc_faithful h
  change ((schemeBoundedCoherentCohomology X).lift
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedToDqc X) _).Faithful
  infer_instance

/-- **Essential surjectivity (#1071).** Under the `Ext` comparison, every object of the
intrinsic bounded-coherent locus in `Dqc(X)` is isomorphic to the image of a bounded
complex of coherent sheaves. The cohomology sheaves of such an object are coherent, so
they lie in the essential image of `Coh.ι X`, and the generic cone argument applies. -/
theorem boundedCoherentDerivedToDqc_essSurj_of_coherentExtComparison (h : CoherentExtComparison X) :
    (boundedCoherentDerivedToDqc X).EssSurj where
  mem_essImage E := by
    obtain ⟨K, hK, ⟨e⟩⟩ := (Coh.ι X).exists_bounded_iso_mapDerivedCategory_obj h E.property.1
      (fun n ↦ ⟨⟨_, E.property.2 n⟩, ⟨Iso.refl _⟩⟩)
    exact ⟨⟨K, hK⟩, ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)⟩⟩

/-- **The bounded-coherent identification (#722), from the `Ext` comparison.** The
equivalence is `boundedCoherentDerivedToDqc X` itself, so the `comparison` field is the
identity isomorphism: nothing but the concrete derived inclusion is used. -/
def boundedCoherentDqcIdentificationOfCoherentExtComparison (h : CoherentExtComparison X) :
    BoundedCoherentDqcIdentification X :=
  haveI := boundedCoherentDerivedToDqc_full_of_coherentExtComparison h
  haveI := boundedCoherentDerivedToDqc_faithful_of_coherentExtComparison h
  haveI := boundedCoherentDerivedToDqc_essSurj_of_coherentExtComparison h
  haveI : (boundedCoherentDerivedToDqc X).IsEquivalence := {}
  { equivalence := (boundedCoherentDerivedToDqc X).asEquivalence
    comparison := Iso.refl _ }

/-- The `Ext` comparison implies the explicit existence proposition consumed by
`Dqc/Comparison.lean`. -/
theorem hasBoundedCoherentDqcIdentification_of_coherentExtComparison
    (h : CoherentExtComparison X) : HasBoundedCoherentDqcIdentification X :=
  ⟨boundedCoherentDqcIdentificationOfCoherentExtComparison h⟩

end

end AlgebraicGeometry.DerivedCategory.Dqc
