/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexPostcomp
import DerivedAlgGeo.CategoryTheory.Localization.SmallShiftedHom
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Functoriality of the injective-resolution presentation of `Ext`

Mathlib identifies `Ext X Y n` with cohomology classes of degree `n` from `X` to a chosen
injective resolution of `Y`, through `InjectiveResolution.extEquivCohomologyClass`, but records
no compatibility of that identification with a morphism in the second variable.

That compatibility is what a comparison theorem needs when the target sheaf varies — and in
particular it is what makes a scalar action visible on `Ext`: multiplication by a scalar is an
endomorphism of the sheaf, and the resolution presentation must carry it to the corresponding
endomorphism of the resolution.

The identification is post-composition with the augmentation `R.ι'`, so the proof is the
associativity of composition in `SmallShiftedHom`, once cohomology classes are equipped with
their own post-composition.
-/


universe w v u

open CategoryTheory Category Localization

namespace CategoryTheory.InjectiveResolution

open CochainComplex CochainComplex.HomComplex Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y Y' : C} {n : ℕ}

/-- The canonical lift of a morphism to chosen injective resolutions.

`InjectiveResolution.desc` produces the map of `ℕ`-indexed resolutions; this packages it with
its degree-zero commutation, so that `Hom.hom'` and `Hom.ι'_comp_hom'` supply the lifted chain
map and the square it satisfies. -/
noncomputable def descHom {Y Y' : C} (φ : Y ⟶ Y')
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') :
    R.Hom R' φ :=
  ⟨InjectiveResolution.desc φ R' R, by
    simpa using InjectiveResolution.desc_commutes_zero φ R' R⟩

omit [HasExt.{w} C] in
/-- The underlying map of resolutions is Mathlib's `desc`; this is stated so that later rewrites
never need to unfold `descHom`. -/
@[simp]
lemma descHom_hom {Y Y' : C} (φ : Y ⟶ Y')
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') :
    (descHom φ R R').hom = InjectiveResolution.desc φ R' R :=
  rfl

/-- The injective-resolution presentation of `Ext` is compatible with a morphism in the second
variable, once that morphism is lifted to the resolutions.

The lift is an explicit hypothesis rather than a chosen descent: the Proj lane passes its
comparison data positionally, and a chosen lift would reintroduce exactly the ambiguity that
convention exists to remove. `InjectiveResolution.Hom.hom'` supplies `hΦ` for the canonical
lift of `φ`. -/
lemma extEquivCohomologyClass_naturality
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') (φ : Y ⟶ Y')
    (Φ : R.cochainComplex ⟶ R'.cochainComplex)
    (hΦ : R.ι' ≫ Φ = (CochainComplex.singleFunctor C 0).map φ ≫ R'.ι')
    (α : Ext.{w} X Y n) :
    R'.extEquivCohomologyClass (α.comp (Ext.mk₀ φ) (add_zero n)) =
      CohomologyClass.postcomp Φ (R.extEquivCohomologyClass α) := by
  have key : ∀ {Z : C} (S : InjectiveResolution Z) (β : Ext.{w} X Z n),
      CohomologyClass.equivOfIsKInjective (S.extEquivCohomologyClass β) =
        SmallShiftedHom.comp β (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl S.ι')
          (zero_add (n : ℤ)) :=
    fun S β ↦ CohomologyClass.equivOfIsKInjective.apply_symm_apply _
  apply CohomologyClass.equivOfIsKInjective.injective
  rw [key]
  show _ = (CohomologyClass.postcomp Φ (R.extEquivCohomologyClass α)).toSmallShiftedHom
  rw [CohomologyClass.toSmallShiftedHom_postcomp]
  show _ = (CohomologyClass.equivOfIsKInjective
    (R.extEquivCohomologyClass α)).comp _ (zero_add (n : ℤ))
  rw [key]
  have hcomp : α.comp (Ext.mk₀ φ) (add_zero n) =
      SmallShiftedHom.comp α (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl
        ((CochainComplex.singleFunctor C 0).map φ)) (zero_add (n : ℤ)) := rfl
  rw [hcomp,
    SmallShiftedHom.comp_assoc (α := α) (h₁₂ := zero_add (n : ℤ))
      (h₂₃ := zero_add (0 : ℤ)) (h := by simp),
    SmallShiftedHom.comp_assoc (α := α) (h₁₂ := zero_add (n : ℤ))
      (h₂₃ := zero_add (0 : ℤ)) (h := by simp),
    SmallShiftedHom.mk₀_comp_mk₀', SmallShiftedHom.mk₀_comp_mk₀', hΦ]

end CategoryTheory.InjectiveResolution
