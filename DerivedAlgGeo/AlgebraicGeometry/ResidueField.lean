/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.LocalRing.LocalSubring
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.LocalRing.LocalSubring

/-!
# The image of a stalk in a residue field

Let `y ⤳ y'` be a specialization in a scheme `Y`. The stalk `𝒪_{Y,y'}` maps to `𝒪_{Y,y}` and
then to the residue field `κ(y)`. The image of this map is a local subring of `κ(y)` with fraction
field `κ(y)`, which is the starting point for dominating it by a valuation ring: a valuation ring
of an extension of `κ(y)` that dominates it yields a point of `Spec R` over `y'` and a point over
`y`.

## Main definitions

* `AlgebraicGeometry.Scheme.specializesResidueFieldHom`: the map `𝒪_{Y,y'} ⟶ κ(y)`.
* `AlgebraicGeometry.Scheme.residueFieldSubring`: its range, a subring of `κ(y)`.

## Main results

* `AlgebraicGeometry.Scheme.isFractionRing_residueFieldSubring`: the fraction field of the range is
  `κ(y)`.
* `AlgebraicGeometry.Scheme.not_isField_residueFieldSubring`: the range is not a field if
  `y ≠ y'`.
* `AlgebraicGeometry.Scheme.isNoetherianRing_residueFieldSubring`: the range is Noetherian if `Y`
  is locally Noetherian.
* `AlgebraicGeometry.Scheme.exists_hom_of_le_residueFieldSubring`: a local subring of a field `K`
  dominating the image of the range gives a morphism `Spec R ⟶ Y` sending the closed point to `y'`
  and compatible with `Spec K ⟶ Spec κ(y) ⟶ Y`.
-/

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {y y' : Y}

/-- The ring map `𝒪_{Y,y'} ⟶ κ(y)` attached to a specialization `y ⤳ y'`: the specialization map
of stalks followed by the residue map. -/
noncomputable def specializesResidueFieldHom (h : y ⤳ y') :
    Y.presheaf.stalk y' ⟶ Y.residueField y :=
  Y.presheaf.stalkSpecializes h ≫ Y.residue y

/-- The image of `𝒪_{Y,y'}` in `κ(y)`, for a specialization `y ⤳ y'`. -/
noncomputable def residueFieldSubring (h : y ⤳ y') : Subring (Y.residueField y) :=
  (specializesResidueFieldHom h).hom.range

/-- The surjection `𝒪_{Y,y'} ⟶ residueFieldSubring h`. -/
noncomputable def toResidueFieldSubring (h : y ⤳ y') :
    Y.presheaf.stalk y' →+* residueFieldSubring h :=
  (specializesResidueFieldHom h).hom.rangeRestrict

theorem toResidueFieldSubring_surjective (h : y ⤳ y') :
    Function.Surjective (toResidueFieldSubring h) :=
  RingHom.rangeRestrict_surjective _

instance (h : y ⤳ y') : IsLocalRing (residueFieldSubring h) :=
  .of_surjective' (toResidueFieldSubring h) (toResidueFieldSubring_surjective h)

instance (h : y ⤳ y') : IsLocalHom (toResidueFieldSubring h) :=
  .of_surjective _ (toResidueFieldSubring_surjective h)

@[simp]
theorem coe_toResidueFieldSubring (h : y ⤳ y') (a : Y.presheaf.stalk y') :
    (toResidueFieldSubring h a : Y.residueField y) = (specializesResidueFieldHom h).hom a :=
  rfl

theorem isNoetherianRing_residueFieldSubring [IsLocallyNoetherian Y] (h : y ⤳ y') :
    IsNoetherianRing (residueFieldSubring h) :=
  isNoetherianRing_of_surjective _ _ _ (toResidueFieldSubring_surjective h)

/-- The morphism `Spec (residueFieldSubring h) ⟶ Spec 𝒪_{Y,y'}` is compatible with the structure
morphisms to `Y`. -/
theorem SpecMap_specializesResidueFieldHom_fromSpecStalk (h : y ⤳ y') :
    Spec.map (specializesResidueFieldHom h) ≫ Y.fromSpecStalk y' = Y.fromSpecResidueField y := by
  rw [specializesResidueFieldHom, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rfl

theorem not_isField_residueFieldSubring (h : y ⤳ y') (hne : y ≠ y') :
    ¬ IsField (residueFieldSubring h) := by
  intro hF
  let := hF.toField
  have hsurj := toResidueFieldSubring_surjective h
  have hker : RingHom.ker (specializesResidueFieldHom h).hom =
      maximalIdeal (Y.presheaf.stalk y') := by
    rw [← IsLocalRing.ker_eq_maximalIdeal (toResidueFieldSubring h) hsurj]
    exact (RingHom.ker_rangeRestrict _).symm
  have hpt : Spec.map (specializesResidueFieldHom h) (closedPoint (Y.residueField y)) =
      closedPoint (Y.presheaf.stalk y') := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (specializesResidueFieldHom h).hom (maximalIdeal (Y.residueField y)) = _
    rw [maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    rfl
  have h1 : (Spec.map (specializesResidueFieldHom h) ≫ Y.fromSpecStalk y')
      (closedPoint (Y.residueField y)) = y := by
    rw [SpecMap_specializesResidueFieldHom_fromSpecStalk]
    exact Scheme.fromSpecResidueField_apply _ _
  have h2 : (Spec.map (specializesResidueFieldHom h) ≫ Y.fromSpecStalk y')
      (closedPoint (Y.residueField y)) = y' := by
    change Y.fromSpecStalk y' (Spec.map (specializesResidueFieldHom h) _) = y'
    rw [hpt]
    exact Scheme.fromSpecStalk_closedPoint
  exact hne (h1.symm.trans h2)

/-- The image of `𝒪_{Y,y'}` in `κ(y)` has fraction field `κ(y)`. -/
instance isFractionRing_residueFieldSubring (h : y ⤳ y') :
    IsFractionRing (residueFieldSubring h) (Y.residueField y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy'U, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y') isOpen_univ
  have hyU : y ∈ U := h.mem_open U.isOpen hy'U
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hyU).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have hgg : ∀ r : Γ(Y, U), (specializesResidueFieldHom h).hom ((Y.presheaf.germ U y' hy'U).hom r) =
      (Y.residue y).hom ((Y.presheaf.germ U y hyU).hom r) := fun r ↦ by
    have := congr($(TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hy'U h).hom r)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    simp only [specializesResidueFieldHom, CommRingCat.hom_comp, RingHom.comp_apply, this]
  exact
    { map_units := fun b ↦ IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
      surj := fun z ↦ by
        obtain ⟨t, rfl⟩ := Y.residue_surjective y z
        obtain ⟨⟨r, s⟩, rfl⟩ :=
          IsLocalization.mk'_surjective (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl t
        have hs : (Y.residue y).hom ((Y.presheaf.germ U y hyU).hom s) ≠ 0 :=
          ((IsLocalization.map_units (Y.presheaf.stalk y) s).map (Y.residue y).hom).ne_zero
        refine ⟨⟨⟨_, (Y.presheaf.germ U y' hy'U).hom r, rfl⟩,
          ⟨⟨_, (Y.presheaf.germ U y' hy'U).hom s, rfl⟩,
            mem_nonZeroDivisors_of_ne_zero ?_⟩⟩, ?_⟩
        · intro h0
          apply hs
          rw [← hgg]
          exact congr_arg Subtype.val h0
        · change (Y.residue y).hom (IsLocalization.mk' (Y.presheaf.stalk y) r s) *
            (specializesResidueFieldHom h).hom ((Y.presheaf.germ U y' hy'U).hom s) =
              (specializesResidueFieldHom h).hom ((Y.presheaf.germ U y' hy'U).hom r)
          rw [hgg, hgg, ← map_mul]
          congr 1
          exact IsLocalization.mk'_spec (Y.presheaf.stalk y) r s
      exists_of_eq := fun h ↦ ⟨1, by simpa using Subtype.ext h⟩ }

/-- The map from the sections over an affine open `U ∋ y'` to the image of `𝒪_{Y,y'}` in `κ(y)`
is essentially of finite type. -/
theorem essFiniteType_toResidueFieldSubring_comp_germ (h : y ⤳ y') {U : Y.Opens}
    (hU : IsAffineOpen U) (hy' : y' ∈ U) :
    ((toResidueFieldSubring h).comp (Y.presheaf.germ U y' hy').hom).EssFiniteType := by
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y') := (Y.presheaf.germ U y' hy').hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y') (hU.primeIdealOf ⟨y', hy'⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y', hy'⟩
  have hgerm : (Y.presheaf.germ U y' hy').hom.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr
      (.of_isLocalization _ (hU.primeIdealOf ⟨y', hy'⟩).asIdeal.primeCompl)
  exact hgerm.comp (RingHom.FiniteType.of_surjective _
    (toResidueFieldSubring_surjective h)).essFiniteType

/-- A local subring `R` of a field `K` that dominates the image of `κ(y)`'s subring
`residueFieldSubring h` gives a morphism `Spec R ⟶ Y` sending the closed point to `y'`, and the
square with `Spec K ⟶ Spec κ(y) ⟶ Y` commutes. The morphism is
`Spec.map ψ ≫ Y.fromSpecStalk y'`, where `ψ : 𝒪_{Y,y'} ⟶ R` agrees with the map to `κ(y)`. -/
theorem exists_hom_of_le_residueFieldSubring (h : y ⤳ y') {K : Type u} [Field K]
    (ι : Y.residueField y ⟶ .of K) (R : LocalSubring K)
    (hR : LocalSubring.range (ι.hom.comp (residueFieldSubring h).subtype) ≤ R) :
    ∃ ψ : Y.presheaf.stalk y' →+* R.toSubring, IsLocalHom ψ ∧
      (∀ a, (ψ a : K) = ι.hom ((specializesResidueFieldHom h).hom a)) ∧
      (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y') (closedPoint R.toSubring) = y' ∧
      Spec.map (CommRingCat.ofHom (algebraMap R.toSubring K)) ≫
          Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y' =
        Spec.map ι ≫ Y.fromSpecResidueField y := by
  obtain ⟨hR₁, hRloc⟩ := id hR
  let c : residueFieldSubring h →+* R.toSubring :=
    (ι.hom.comp (residueFieldSubring h).subtype).codRestrict R.toSubring
      fun a ↦ LocalSubring.toSubring_mono hR ⟨a, rfl⟩
  let e : residueFieldSubring h →+*
      (LocalSubring.range (ι.hom.comp (residueFieldSubring h).subtype)).toSubring :=
    (ι.hom.comp (residueFieldSubring h).subtype).codRestrict _ fun a ↦ ⟨a, rfl⟩
  have : IsLocalHom e := .of_surjective e fun ⟨_, a, rfl⟩ ↦ ⟨a, rfl⟩
  let ψ : Y.presheaf.stalk y' →+* R.toSubring := c.comp (toResidueFieldSubring h)
  have hψ : IsLocalHom ψ :=
    inferInstanceAs (IsLocalHom (((Subring.inclusion hR₁).comp e).comp (toResidueFieldSubring h)))
  have hψK : ∀ a, (ψ a : K) = ι.hom ((specializesResidueFieldHom h).hom a) := fun a ↦ rfl
  refine ⟨ψ, hψ, hψK, ?_, ?_⟩
  · change Y.fromSpecStalk y' (Spec.map (CommRingCat.ofHom ψ) (closedPoint R.toSubring)) = y'
    rw [show Spec.map (CommRingCat.ofHom ψ) (closedPoint R.toSubring) = closedPoint _ from
      IsLocalRing.comap_closedPoint ψ]
    exact Scheme.fromSpecStalk_closedPoint
  · rw [← Spec.map_comp_assoc,
      show CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap R.toSubring K) =
        specializesResidueFieldHom h ≫ ι from by ext a; exact hψK a,
      Spec.map_comp, Category.assoc, SpecMap_specializesResidueFieldHom_fromSpecStalk]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- For a morphism `f : X ⟶ Y` locally of finite type, the map `κ(f x) ⟶ κ(x)` on residue fields
is essentially of finite type. -/
theorem essFiniteType_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) : (f.residueFieldMap x).hom.EssFiniteType := by
  have h1 : ((X.residue x).hom.comp (f.stalkMap x).hom).EssFiniteType :=
    (LocallyOfFiniteType.stalkMap f x).comp
      (RingHom.FiniteType.of_surjective _ (X.residue_surjective x)).essFiniteType
  rw [← CommRingCat.hom_comp, ← Scheme.residue_residueFieldMap, CommRingCat.hom_comp] at h1
  exact RingHom.EssFiniteType.of_comp _ h1

end AlgebraicGeometry.LocallyOfFiniteType
