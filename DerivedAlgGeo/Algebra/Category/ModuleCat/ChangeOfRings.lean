/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Extension of scalars: additivity and composites given by an equation

Extension of scalars along a ring map is an additive functor. Mathlib's `ModuleCat.extendScalarsComp` identifies extension of scalars along `f₂₃.comp f₁₂`
with extension along `f₁₂` followed by extension along `f₂₃`. This file adds the variant
`ModuleCat.extendScalarsComp'`, which takes a ring morphism `f₁₃` together with a proof of
`f₁₃ = f₂₃.comp f₁₂`, as Mathlib's `ModuleCat.restrictScalarsComp'` does for restriction of
scalars. It is the form needed when the composite is only propositionally equal to `f₁₃`, as for
the legs `R.map f ≫ c.ι.app j' = c.ι.app j` of a cocone.

## Main definitions

* `ModuleCat.extendScalars_additive`: extension of scalars along any ring map is additive.
* `ModuleCat.extendScalarsComp'`: the isomorphism
  `extendScalars f₁₃ ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃` for `f₁₃ = f₂₃.comp f₁₂`.

## Main results

* `ModuleCat.extendScalarsComp'_hom_app_tmul` and `ModuleCat.extendScalarsComp'_inv_app_tmul`:
  the isomorphism sends `s ⊗ m` to `s ⊗ (1 ⊗ m)`, and its inverse sends `s ⊗ (r ⊗ m)` to
  `(s * f₂₃ r) ⊗ m`.

## Tags

module, extension of scalars, base change
-/

universe v u u₁ u₂

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₁₃ : R₁ →+* R₃) (h : f₁₃ = f₂₃.comp f₁₂)

/-- Extension of scalars along `f₁₃` identifies with extension along `f₁₂` followed by extension
along `f₂₃`, given `f₁₃ = f₂₃.comp f₁₂`. For `h = rfl` this is `ModuleCat.extendScalarsComp`. -/
noncomputable def extendScalarsComp' :
    extendScalars f₁₃ ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃ :=
  (conjugateIsoEquiv ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
    (extendRestrictScalarsAdj f₁₃)).symm (restrictScalarsComp' f₁₂ f₂₃ f₁₃ h).symm

lemma extendScalarsComp'_eq_extendScalarsComp :
    extendScalarsComp' f₁₂ f₂₃ _ rfl = extendScalarsComp f₁₂ f₂₃ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In an extension of scalars, `s ⊗ m = s • (1 ⊗ m)`. -/
private lemma tmul_eq_smul_one_tmul {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R →+* S) {M : ModuleCat.{v} R} (s : S) (m : M) :
    (s ⊗ₜ[R, f] m : (extendScalars f).obj M) =
      s • ((1 : S) ⊗ₜ[R, f] m : (extendScalars f).obj M) := by
  rw [ExtendScalars.smul_tmul, mul_one]

set_option backward.isDefEq.respectTransparency false in
lemma extendScalarsComp'_hom_app_tmul (M : ModuleCat.{max v u} R₁) (s : R₃) (m : M) :
    (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom.app M (s ⊗ₜ[R₁, f₁₃] m) =
      s ⊗ₜ[R₂, f₂₃] ((1 : R₂) ⊗ₜ[R₁, f₁₂] m) := by
  subst h
  rw [tmul_eq_smul_one_tmul, map_smul, extendScalarsComp'_eq_extendScalarsComp,
    extendScalarsComp_hom_app_one_tmul]
  exact (tmul_eq_smul_one_tmul f₂₃ s _).symm

set_option backward.isDefEq.respectTransparency false in
lemma extendScalarsComp'_inv_app_tmul (M : ModuleCat.{max v u} R₁) (s : R₃) (r : R₂) (m : M) :
    (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).inv.app M (s ⊗ₜ[R₂, f₂₃] (r ⊗ₜ[R₁, f₁₂] m)) =
      (s * f₂₃ r) ⊗ₜ[R₁, f₁₃] m := by
  have : (s ⊗ₜ[R₂, f₂₃] (r ⊗ₜ[R₁, f₁₂] m) : (extendScalars f₂₃).obj ((extendScalars f₁₂).obj M)) =
      (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom.app M ((s * f₂₃ r) ⊗ₜ[R₁, f₁₃] m) := by
    rw [extendScalarsComp'_hom_app_tmul, tmul_eq_smul_one_tmul f₁₂ r,
      ← TensorProduct.smul_tmul]
    congr 1
    exact mul_comm (f₂₃ r) s
  rw [this]
  exact Iso.hom_inv_id_apply ((extendScalarsComp' f₁₂ f₂₃ f₁₃ h).app M) _

section Additive

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]

/-- Extension of scalars along a ring map is additive: `1 ⊗ (g + h) = 1 ⊗ g + 1 ⊗ h`. -/
instance extendScalars_additive (f : R →+* S) : (extendScalars.{u₁, u₂, v} f).Additive where
  map_add {M N} g h := by
    apply ExtendScalars.hom_ext
    intro m
    letI : Module R S := Module.compHom S f
    change (1 : S) ⊗ₜ[R, f] (g m + h m) = (1 : S) ⊗ₜ[R, f] g m + (1 : S) ⊗ₜ[R, f] h m
    rw [TensorProduct.tmul_add]

end Additive

end ModuleCat
