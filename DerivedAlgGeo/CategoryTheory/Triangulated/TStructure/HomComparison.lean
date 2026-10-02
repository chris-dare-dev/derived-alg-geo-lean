/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Hom comparison through t-structure truncations

A map from an object in the nonpositive aisle factors uniquely through its
nonpositive truncation. When the two outer Hom groups of the next truncation
triangle vanish, the map into the degree-zero truncation is an additive
equivalence.

## Main definitions

This file introduces no carrier, class, or instance.

## Main results

* `CategoryTheory.Triangulated.TStructure.homTruncLTAddEquiv` identifies maps into a target with maps into
  its upper truncation from a source in the appropriate aisle.
* `CategoryTheory.Triangulated.TStructure.homToDegreeZeroTruncAddEquiv` identifies maps into a target with
  maps into its degree-zero truncation under explicit outer-Hom vanishing.

## Implementation notes

The triangle factorization is private. Its injectivity and surjectivity use
Mathlib's two coyoneda exactness lemmas, respectively. No t-structure
vanishing is inferred from the generic statement's explicit hypotheses.

## References

Mathlib's `CategoryTheory.Triangulated.TStructure.liftTruncLT_ι`, `CategoryTheory.Triangulated.TStructure.to_truncLT_obj_ext`, and
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂` and
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₃` at the pinned revision.

## Tags

t-structure, truncation, additive Hom comparison
-/

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open CategoryTheory.Triangulated.TStructure CategoryTheory.Limits

universe v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

/-- Maps from an object in the aisle `≤ n` into a target factor uniquely and
additively through its truncation `τ_{<n+1}`. -/
noncomputable def homTruncLTAddEquiv {X Y : C} (n : ℤ) [t.IsLE X n] :
    (X ⟶ (t.truncLT (n + 1)).obj Y) ≃+ (X ⟶ Y) where
  toFun g := g ≫ (t.truncLTι (n + 1)).app Y
  invFun f := t.liftTruncLT f n (n + 1) rfl
  left_inv g := by
    haveI : t.IsLE X (n + 1 - 1) := by simpa using (inferInstance : t.IsLE X n)
    apply t.to_truncLT_obj_ext
    exact t.liftTruncLT_ι (g ≫ (t.truncLTι (n + 1)).app Y) n (n + 1) rfl
  right_inv f := t.liftTruncLT_ι f n (n + 1) rfl
  map_add' g h := by simp

end CategoryTheory.Triangulated.TStructure

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An exact triangle induces an additive Hom equivalence when the two outer
Hom groups vanish. This is support for the t-structure comparison below. -/
private noncomputable def homMorTwoAddEquiv (T : Triangle C) (hT : T ∈ distTriang C)
    (X : C) (h₁ : ∀ f : X ⟶ T.obj₁, f = 0)
    (h₄ : ∀ f : X ⟶ T.obj₁⟦(1 : ℤ)⟧, f = 0) :
    (X ⟶ T.obj₂) ≃+ (X ⟶ T.obj₃) := by
  let φ : (X ⟶ T.obj₂) →+ (X ⟶ T.obj₃) :=
    { toFun := fun f => f ≫ T.mor₂
      map_zero' := by simp
      map_add' := by intros; simp }
  apply AddEquiv.ofBijective φ
  constructor
  · intro f g hfg
    change f ≫ T.mor₂ = g ≫ T.mor₂ at hfg
    have hzero : (f - g) ≫ T.mor₂ = 0 := by rw [Preadditive.sub_comp, hfg, sub_self]
    obtain ⟨k, hk⟩ := T.coyoneda_exact₂ hT (f - g) hzero
    have hk0 : k = 0 := h₁ k
    have : f - g = 0 := by rw [hk, hk0, zero_comp]
    exact sub_eq_zero.mp this
  · intro y
    have hz : y ≫ T.mor₃ = 0 := h₄ _
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT y hz
    exact ⟨g, hg.symm⟩

end CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

/-- Under the stated outer-Hom vanishing, maps into `M` identify additively
with maps into its degree-zero t-structure truncation. -/
noncomputable def homToDegreeZeroTruncAddEquiv {X M : C} [t.IsLE X 0]
    (h₁ : ∀ f : X ⟶ (t.truncLT 0).obj ((t.truncLT 1).obj M), f = 0)
    (h₄ : ∀ f : X ⟶ ((t.truncLT 0).obj ((t.truncLT 1).obj M))⟦(1 : ℤ)⟧, f = 0) :
    (X ⟶ M) ≃+ (X ⟶ (t.truncGE 0).obj ((t.truncLT 1).obj M)) := by
  let L := (t.truncLT 1).obj M
  let T := (t.triangleLTGE 0).obj L
  exact (t.homTruncLTAddEquiv (n := 0)).symm.trans
    (homMorTwoAddEquiv T (t.triangleLTGE_distinguished 0 L) X h₁ h₄)

end CategoryTheory.Triangulated.TStructure
