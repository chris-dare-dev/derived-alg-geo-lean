/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import DerivedAlgGeo.CategoryTheory.MorphismProperty.Limits

/-!
# Coproducts in a localization

Let `L : C ⥤ D` be a localization functor for a class `W` of morphisms with a right calculus
of fractions.  If `C` has coproducts of shape `ι` and `W` is stable under them, then `D` has
coproducts of shape `ι`, they are computed in `C`, and `L` preserves them.  This is the
argument that the derived category of an abelian category with exact coproducts has
coproducts, run at the level of the localization: a morphism out of `L (∐ X)` is a right
fraction, its restrictions to the summands are right fractions with a common denominator
`Sigma.map` of denominators, and two fractions agreeing on every summand are identified by
the Ore condition summand by summand and one more `Sigma.map`.

## Main definitions

* `Localization.isColimitCofan`: `L (∐ X)` is a coproduct of the `L (X i)`.

## Main results

* `Localization.sigma_hom_ext`: two morphisms out of `L (∐ X)` agreeing on every summand
  are equal.
* `Localization.preservesCoproductsOfShape`: `L` preserves coproducts of shape `ι`.
* `Localization.hasCoproductsOfShape`: `D` has coproducts of shape `ι`.

## Implementation notes

The hypotheses are exactly those of the derived category `Qh : K(A) ⥤ D(A)`: the
homotopy category has coproducts computed degreewise, quasi-isomorphisms have a right
calculus of fractions there, and they are stable under coproducts when `A` has exact
coproducts.  Nothing here is about complexes; the instances for `D(A)` are a later consumer.

Mathlib's `Localization.preservesProductsOfShape` and `hasProductsOfShape`
(`Mathlib/CategoryTheory/Localization/FiniteProducts.lean`) need no calculus of fractions but
only apply to `Finite J`: they descend `lim` along the localization of `Discrete J ⥤ C`, and
`Functor.IsLocalization.pi` is proved by induction on a finite index type.  This file trades a
right calculus of fractions for an arbitrary `ι`.  Right fractions, not left: a morphism out of
`L (∐ X)` written as a right fraction has its denominator on the coproduct side, so the
`ι`-many denominators of the legs are absorbed by a single `Sigma.map`; with left fractions the
denominators sit at the target, and a common one for infinitely many legs would need an
infinitary Ore condition that a calculus of fractions does not provide.

The two main results are theorems producing instances rather than instances, since `W` is not
determined by `L` nor `L` by `D`; for the universal localization `W.Q` they are instances, as
in Mathlib's finite-products file.  The construction internals live in
`Localization.HasCoproductsOfShapeAux`, following `Localization.HasProductsOfShapeAux`.

## References

* Neeman, *Triangulated categories*, Lemma 3.2.10, the Verdier-quotient form: for a
  β-localizing subcategory `N` of `T`, `T/N` has the coproducts of fewer than β objects that
  `T` has, and the quotient functor preserves them.
* [Stacks, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L), Lemma 13.33.5, the
  derived-category form for countable direct sums under exact countable direct sums; this file
  removes the countability.
-/

open CategoryTheory Category Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Localization

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasRightCalculusOfFractions]
  {ι : Type w} [HasCoproductsOfShape ι C] [W.IsStableUnderCoproductsOfShape ι]

include W in
/-- Two morphisms out of `L (∐ X)` that agree on every summand are equal: written as right
fractions with a common denominator `t`, the Ore condition against each `Sigma.ι X i` and
`map_eq_iff_precomp` give, summand by summand, morphisms in `W` equalizing the two
numerators, and `Sigma.map` of those is a morphism in `W` through which both fractions
factor. -/
theorem sigma_hom_ext {X : ι → C} {Y : C} {ψ ψ' : L.obj (∐ X) ⟶ L.obj Y}
    (h : ∀ i, L.map (Sigma.ι X i) ≫ ψ = L.map (Sigma.ι X i) ≫ ψ') : ψ = ψ' := by
  obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction L W ψ
  obtain ⟨φ', rfl⟩ := Localization.exists_rightFraction L W ψ'
  obtain ⟨ρ, hρ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
    (W := W) (MorphismProperty.LeftFraction.mk φ.s φ'.s φ'.hs)
  have hρ' : ρ.s ≫ φ.s = ρ.f ≫ φ'.s := hρ
  have ht : W (ρ.s ≫ φ.s) := W.comp_mem _ _ ρ.hs φ.hs
  haveI := Localization.inverts L W _ ht
  haveI := Localization.inverts L W _ φ.hs
  haveI := Localization.inverts L W _ φ'.hs
  haveI := Localization.inverts L W _ ρ.hs
  haveI : IsIso (L.map ρ.f) := by
    have : IsIso (L.map ρ.f ≫ L.map φ'.s) := by rw [← L.map_comp, ← hρ']; infer_instance
    exact IsIso.of_isIso_comp_right (L.map ρ.f) (L.map φ'.s)
  have hψ : φ.map L (Localization.inverts L W) =
      inv (L.map (ρ.s ≫ φ.s)) ≫ L.map (ρ.s ≫ φ.f) := by
    simp [MorphismProperty.RightFraction.map, L.map_comp]
  have hψ' : φ'.map L (Localization.inverts L W) =
      inv (L.map (ρ.s ≫ φ.s)) ≫ L.map (ρ.f ≫ φ'.f) := by
    rw [IsIso.eq_inv_comp]
    have e : L.map (ρ.s ≫ φ.s) = L.map (ρ.f ≫ φ'.s) := by rw [hρ']
    rw [e, L.map_comp, L.map_comp, assoc]
    simp [MorphismProperty.RightFraction.map]
  rw [hψ, hψ'] at h ⊢
  set g₁ := ρ.s ≫ φ.f with hg₁
  set g₂ := ρ.f ≫ φ'.f with hg₂
  clear_value g₁ g₂
  choose ρi hρi using fun i => MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
    (W := W) (MorphismProperty.LeftFraction.mk (Sigma.ι X i) (ρ.s ≫ φ.s) ht)
  have hρi' : ∀ i, (ρi i).s ≫ Sigma.ι X i = (ρi i).f ≫ (ρ.s ≫ φ.s) := fun i => hρi i
  have key : ∀ i, L.map ((ρi i).f ≫ g₁) = L.map ((ρi i).f ≫ g₂) := by
    intro i
    have e : L.map (ρi i).s ≫ L.map (Sigma.ι X i) ≫ inv (L.map (ρ.s ≫ φ.s)) =
        L.map (ρi i).f := by
      rw [← L.map_comp_assoc, hρi' i, L.map_comp, assoc, IsIso.hom_inv_id, comp_id]
    have := congrArg (fun z => L.map (ρi i).s ≫ z) (h i)
    simp only [reassoc_of% e] at this
    rw [L.map_comp, L.map_comp]
    exact this
  choose Z w hw hw' using fun i => (MorphismProperty.map_eq_iff_precomp L W _ _).1 (key i)
  let u : (∐ fun i => Z i) ⟶ ρ.X' := Sigma.desc fun i => w i ≫ (ρi i).f
  let v : (∐ fun i => Z i) ⟶ ∐ X := Limits.Sigma.map fun i => w i ≫ (ρi i).s
  have hv : W v := W.sigma_map _ fun i => W.comp_mem _ _ (hw i) (ρi i).hs
  have huv : u ≫ (ρ.s ≫ φ.s) = v := by
    apply Sigma.hom_ext
    intro i
    simp only [u, v, Sigma.ι_desc_assoc, Sigma.ι_map, assoc, hρi' i]
  have hg : u ≫ g₁ = u ≫ g₂ := by
    apply Sigma.hom_ext
    intro i
    simp only [u, Sigma.ι_desc_assoc, assoc, hw' i]
  haveI : IsIso (L.map v) := Localization.inverts L W _ hv
  haveI : IsIso (L.map u ≫ L.map (ρ.s ≫ φ.s)) := by rw [← L.map_comp, huv]; infer_instance
  haveI : IsIso (L.map u) := IsIso.of_isIso_comp_right (L.map u) (L.map (ρ.s ≫ φ.s))
  have : (L.map u ≫ L.map (ρ.s ≫ φ.s)) ≫ inv (L.map (ρ.s ≫ φ.s)) ≫ L.map g₁ =
      (L.map u ≫ L.map (ρ.s ≫ φ.s)) ≫ inv (L.map (ρ.s ≫ φ.s)) ≫ L.map g₂ := by
    rw [assoc, assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc, ← L.map_comp,
      ← L.map_comp, hg]
  exact (cancel_epi (L.map u ≫ L.map (ρ.s ≫ φ.s))).1 this

namespace HasCoproductsOfShapeAux

variable (X : ι → C) (t : Cofan fun i => L.obj (X i)) (Y : C) (e : L.obj Y ≅ t.pt)

/-- The right fraction representing a leg of a cofan under `L`, against a chosen preimage
`Y` of its vertex. -/
noncomputable def cofanFraction (i : ι) : W.RightFraction (X i) Y :=
  (Localization.exists_rightFraction L W (t.inj i ≫ e.inv)).choose

omit [HasCoproductsOfShape ι C] [W.IsStableUnderCoproductsOfShape ι] in
/-- The defining equation of `cofanFraction`, the `choose_spec` of
`Localization.exists_rightFraction`. -/
theorem cofanFraction_map (i : ι) :
    (cofanFraction L W X t Y e i).map L (Localization.inverts L W) = t.inj i ≫ e.inv :=
  (Localization.exists_rightFraction L W (t.inj i ≫ e.inv)).choose_spec.symm

/-- The common denominator of the legs' fractions is inverted by `L`. -/
instance isIso_map_sigma_map_cofanFraction_s :
    IsIso (L.map (Limits.Sigma.map fun i => (cofanFraction L W X t Y e i).s)) :=
  Localization.inverts L W _ (W.sigma_map _ fun i => (cofanFraction L W X t Y e i).hs)

/-- The morphism out of `L (∐ X)` induced by a cofan under `L`: the common denominator of
the legs' fractions, then the numerators assembled by `Sigma.desc`, then the identification of
the vertex. -/
noncomputable def cofanDesc : L.obj (∐ X) ⟶ t.pt :=
  inv (L.map (Limits.Sigma.map fun i => (cofanFraction L W X t Y e i).s)) ≫
    L.map (Sigma.desc fun i => (cofanFraction L W X t Y e i).f) ≫ e.hom

/-- `cofanDesc` restricts on each summand to the given leg. -/
theorem cofanDesc_fac (i : ι) : L.map (Sigma.ι X i) ≫ cofanDesc L W X t Y e = t.inj i := by
  haveI := Localization.inverts L W _ (cofanFraction L W X t Y e i).hs
  have h1 : L.map (Sigma.ι X i) ≫
      inv (L.map (Limits.Sigma.map fun i => (cofanFraction L W X t Y e i).s)) =
      inv (L.map (cofanFraction L W X t Y e i).s) ≫
        L.map (Sigma.ι (fun i => (cofanFraction L W X t Y e i).X') i) := by
    rw [IsIso.comp_inv_eq, assoc, ← L.map_comp, Sigma.ι_map, L.map_comp, IsIso.inv_hom_id_assoc]
  unfold cofanDesc
  rw [← assoc, h1, assoc, ← L.map_comp_assoc, Sigma.ι_desc]
  have := cofanFraction_map L W X t Y e i
  simp only [MorphismProperty.RightFraction.map] at this
  rw [← assoc, this, assoc, Iso.inv_hom_id, comp_id]

end HasCoproductsOfShapeAux

open HasCoproductsOfShapeAux in
include W in
/-- `L (∐ X)` is a coproduct of the `L (X i)`, with legs `L (Sigma.ι X i)`: the description
is `cofanDesc` against a preimage of the vertex, which exists because `L` is essentially
surjective, and uniqueness is `sigma_hom_ext`. -/
noncomputable def isColimitCofan (X : ι → C) :
    IsColimit (Cofan.mk (L.obj (∐ X)) fun i => L.map (Sigma.ι X i)) := by
  haveI := Localization.essSurj L W
  exact Cofan.IsColimit.mk _
    (fun t => cofanDesc L W X t _ (L.objObjPreimageIso t.pt))
    (fun t i => cofanDesc_fac L W X t _ (L.objObjPreimageIso t.pt) i)
    (fun t m hm => by
      change L.obj (∐ X) ⟶ t.pt at m
      have hm' : ∀ i, L.map (Sigma.ι X i) ≫ m = t.inj i := hm
      have : m ≫ (L.objObjPreimageIso t.pt).inv =
          cofanDesc L W X t _ (L.objObjPreimageIso t.pt) ≫ (L.objObjPreimageIso t.pt).inv := by
        apply sigma_hom_ext L W
        intro i
        rw [← assoc, ← assoc, hm' i, cofanDesc_fac]
      exact (cancel_mono (L.objObjPreimageIso t.pt).inv).1 this)

variable (ι)

include W in
/-- `L` preserves coproducts of shape `ι`: `isColimitCofan` transported along
`Discrete.natIsoFunctor`.  Unlike Mathlib's `Localization.preservesProductsOfShape`, which
needs `Finite J` and no calculus of fractions, this holds for every `ι` given a right
calculus. -/
theorem preservesCoproductsOfShape : PreservesColimitsOfShape (Discrete ι) L := by
  haveI : ∀ X : ι → C, PreservesColimit (Discrete.functor X) L := fun X => by
    refine preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct _) ?_
    refine IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ L) _ ?_
    refine IsColimit.ofIsoColimit (isColimitCofan L W X) ?_
    exact Cocone.ext (Iso.refl _) (by
      rintro ⟨i⟩
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_discrete L

include L W in
/-- `D` has coproducts of shape `ι`: every family is isomorphic to the image of a family in
`C`, whose coproduct `L` preserves. -/
theorem hasCoproductsOfShape : HasCoproductsOfShape ι D := by
  haveI := Localization.essSurj L W
  constructor
  intro F
  let X : ι → C := fun i => L.objPreimage (F.obj ⟨i⟩)
  have e : F ≅ Discrete.functor fun i => L.obj (X i) :=
    Discrete.natIso fun ⟨i⟩ => (L.objObjPreimageIso (F.obj ⟨i⟩)).symm
  haveI : HasColimit (Discrete.functor fun i => L.obj (X i)) :=
    ⟨⟨_, isColimitCofan L W X⟩⟩
  exact hasColimit_of_iso e

/-- The universal localization has coproducts of shape `ι`. -/
instance hasCoproductsOfShapeLocalization : HasCoproductsOfShape ι W.Localization :=
  hasCoproductsOfShape W.Q W ι

/-- The universal localization functor preserves coproducts of shape `ι`. -/
noncomputable instance preservesCoproductsOfShapeQ : PreservesColimitsOfShape (Discrete ι) W.Q :=
  preservesCoproductsOfShape W.Q W ι

end CategoryTheory.Localization
