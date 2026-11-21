/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The cartesian monoidal structure on sheaves, and pushforward

Let `A` carry a cartesian monoidal structure. Mathlib's cartesian monoidal structure on
`Sheaf K A` is computed sectionwise. This file makes its underlying monoidal structure the one
found by instance search, so that monoid and group objects of `Sheaf K A` are those of Mathlib's
cartesian API, and shows that pushforward along a continuous functor `F : C ⥤ D`, which is
precomposition with `F.op`, preserves products on the nose.

## Main definitions

* `Sheaf.monoidalCategoryOfCartesian`: the monoidal structure on `Sheaf J A` underlying
  `CartesianMonoidalCategory.fullSubcategory`, with high priority.
* `Functor.sheafPushforwardContinuousMonoidal`: the monoidal structure on
  `F.sheafPushforwardContinuous A J K` whose comparison morphisms `ε` and `μ` are identities.

## Implementation notes

Mathlib gives `Sheaf J A` two monoidal structures: `ObjectProperty.fullMonoidalSubcategory`,
induced along the inclusion into presheaves, and the one underlying the cartesian monoidal
structure `CartesianMonoidalCategory.fullSubcategory`. They agree only after unfolding. Instance
search finds the first, while `GrpObj` and the cartesian API (`ModObj.leftSMul`, the group
`Hom.group`) use the second, so without `Sheaf.monoidalCategoryOfCartesian` a group object `G`
of `Sheaf J A` is not a monoid object for the structure found by instance search, and
`[GrpObj G] [ModObj G P]` does not elaborate.

A finite-product-preserving functor between cartesian monoidal categories carries a unique
monoidal structure (`Functor.Monoidal` is a subsingleton there), so this instance agrees with
`Functor.Monoidal.ofChosenFiniteProducts` whenever both are available. The instance given here
needs no product-preservation instance, and its comparison morphisms are identities by
definition. Through `Functor.monObjObj` and `Functor.grpObjObj` it makes the pushforward of a
monoid or group object a monoid or group object, for instance the restriction of a sheaf of
groups to a slice `Over X` along `J.overPullback A X`.

## References

No literature source is followed: this is the sectionwise computation of products of sheaves.

## Tags

sheaf, pushforward, monoidal functor, cartesian monoidal category
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

/-- The monoidal structure on `Sheaf J A` underlying Mathlib's cartesian monoidal structure
`CartesianMonoidalCategory.fullSubcategory`. Mathlib also provides
`ObjectProperty.fullMonoidalSubcategory`, which instance search finds first; the two agree only
after unfolding, so without this instance a monoid object for the second is not one for the first,
and `[GrpObj G] [ModObj G P]` does not elaborate for sheaves `G` and `P`, because `GrpObj` uses the
cartesian structure. -/
instance (priority := high) Sheaf.monoidalCategoryOfCartesian {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) (A : Type u₃) [Category.{v₃} A] [CartesianMonoidalCategory A] :
    MonoidalCategory (Sheaf J A) :=
  SemiCartesianMonoidalCategory.toMonoidalCategory

namespace Functor

open MonoidalCategory LaxMonoidal OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (A : Type u₃) [Category.{v₃} A] [CartesianMonoidalCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]

/-- The pushforward of sheaves along a continuous functor is monoidal for the cartesian monoidal
structures, with identity comparison morphisms: products and the terminal sheaf are computed
sectionwise, so they are preserved on the nose. -/
instance sheafPushforwardContinuousMonoidal : (F.sheafPushforwardContinuous A J K).Monoidal :=
  CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _
      μIso_hom_natural_left _ _ := by
        dsimp only [Iso.refl_hom]
        erw [Category.comp_id, Category.id_comp]
        rfl
      μIso_hom_natural_right _ _ := by
        dsimp only [Iso.refl_hom]
        erw [Category.comp_id, Category.id_comp]
        rfl
      associativity _ _ _ := by
        dsimp only [Iso.refl_hom]
        erw [MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp,
          Category.id_comp, Category.comp_id, Category.comp_id]
        rfl
      left_unitality _ := by
        dsimp only [Iso.refl_hom]
        erw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.id_comp]
        rfl
      right_unitality _ := by
        dsimp only [Iso.refl_hom]
        erw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.id_comp]
        rfl }

@[simp]
lemma sheafPushforwardContinuous_ε : ε (F.sheafPushforwardContinuous A J K) = 𝟙 _ := rfl

@[simp]
lemma sheafPushforwardContinuous_η : η (F.sheafPushforwardContinuous A J K) = 𝟙 _ := rfl

@[simp]
lemma sheafPushforwardContinuous_μ (X Y : Sheaf K A) :
    μ (F.sheafPushforwardContinuous A J K) X Y = 𝟙 _ := rfl

@[simp]
lemma sheafPushforwardContinuous_δ (X Y : Sheaf K A) :
    δ (F.sheafPushforwardContinuous A J K) X Y = 𝟙 _ := rfl

end Functor

end CategoryTheory
