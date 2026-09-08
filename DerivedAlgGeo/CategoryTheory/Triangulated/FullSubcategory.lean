/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Triangles in full triangulated subcategories

An ambient triangle whose three objects satisfy a triangulated object property
has a canonical lift to the corresponding full subcategory. This file owns
that construction, its comparison with the ambient triangle, and the lift of
triangle morphisms.

Concrete bounded-derived-category adapters should provide only the three
objectwise membership proofs. They do not need to repeat the fully faithful
preimage construction or manipulate the inclusion's shift comparison.
-/

universe v u

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated Triangulated

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

/-- The assertion that an object property holds on all three objects of a
triangle. -/
structure OnTriangle (T : Triangle C) : Prop where
  obj₁ : P T.obj₁
  obj₂ : P T.obj₂
  obj₃ : P T.obj₃

/-- Lift an ambient triangle objectwise to a full triangulated subcategory.

The third morphism is transported through the inverse of the inclusion's
shift comparison before fullness is used. -/
noncomputable def liftTriangle (T : Triangle C) (hT : P.OnTriangle T) :
    Triangle P.FullSubcategory := by
  let X₁ : P.FullSubcategory := ⟨T.obj₁, hT.obj₁⟩
  let X₂ : P.FullSubcategory := ⟨T.obj₂, hT.obj₂⟩
  let X₃ : P.FullSubcategory := ⟨T.obj₃, hT.obj₃⟩
  let f : X₁ ⟶ X₂ := P.fullyFaithfulι.preimage T.mor₁
  let g : X₂ ⟶ X₃ := P.fullyFaithfulι.preimage T.mor₂
  let h : X₃ ⟶ X₁⟦(1 : ℤ)⟧ := P.fullyFaithfulι.preimage
    (T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app X₁)
  exact Triangle.mk f g h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from the image of a lifted triangle to its
ambient triangle. -/
noncomputable def liftTriangleIso (T : Triangle C) (hT : P.OnTriangle T) :
    P.ι.mapTriangle.obj (P.liftTriangle T hT) ≅ T :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [liftTriangle]) (by simp [liftTriangle])
    (by simp [liftTriangle, Category.assoc])

/-- A distinguished ambient triangle with objects in `P` lifts to a
distinguished triangle in the full subcategory. -/
theorem liftTriangle_distinguished (T : Triangle C) (hT : P.OnTriangle T)
    (h : T ∈ distTriang C) :
    P.liftTriangle T hT ∈ distTriang P.FullSubcategory := by
  change P.ι.mapTriangle.obj (P.liftTriangle T hT) ∈ distTriang C
  exact isomorphic_distinguished _ h _ (P.liftTriangleIso T hT)

/-- Lift a morphism of ambient triangles to the corresponding objectwise
lifts in a full triangulated subcategory. -/
noncomputable def liftTriangleMap {T₁ T₂ : Triangle C}
    (hT₁ : P.OnTriangle T₁) (hT₂ : P.OnTriangle T₂) (f : T₁ ⟶ T₂) :
    P.liftTriangle T₁ hT₁ ⟶ P.liftTriangle T₂ hT₂ :=
  P.ι.mapTriangle.preimage
    ((P.liftTriangleIso T₁ hT₁).hom ≫ f ≫
      (P.liftTriangleIso T₂ hT₂).inv)

/-- The image of a lifted triangle map is the ambient map conjugated by the
canonical comparison isomorphisms. -/
@[simp]
theorem map_liftTriangleMap {T₁ T₂ : Triangle C}
    (hT₁ : P.OnTriangle T₁) (hT₂ : P.OnTriangle T₂) (f : T₁ ⟶ T₂) :
    P.ι.mapTriangle.map (P.liftTriangleMap hT₁ hT₂ f) =
      (P.liftTriangleIso T₁ hT₁).hom ≫ f ≫
        (P.liftTriangleIso T₂ hT₂).inv :=
  P.ι.mapTriangle.map_preimage _

/-- After identifying both images with their ambient triangles, a lifted map
is exactly the original triangle map. -/
@[simp]
theorem liftTriangleMap_ambient {T₁ T₂ : Triangle C}
    (hT₁ : P.OnTriangle T₁) (hT₂ : P.OnTriangle T₂) (f : T₁ ⟶ T₂) :
    (P.liftTriangleIso T₁ hT₁).inv ≫
        P.ι.mapTriangle.map (P.liftTriangleMap hT₁ hT₂ f) ≫
        (P.liftTriangleIso T₂ hT₂).hom = f := by
  rw [P.map_liftTriangleMap]
  calc
    _ = f ≫ (P.liftTriangleIso T₂ hT₂).inv ≫
        (P.liftTriangleIso T₂ hT₂).hom := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = f := by
      simp only [(P.liftTriangleIso T₂ hT₂).inv_hom_id,
        Category.comp_id]

/-- Lifting preserves identity triangle maps. -/
@[simp]
theorem liftTriangleMap_id (T : Triangle C) (hT : P.OnTriangle T) :
    P.liftTriangleMap hT hT (𝟙 T) = 𝟙 (P.liftTriangle T hT) := by
  apply P.ι.mapTriangle.map_injective
  rw [P.map_liftTriangleMap, Functor.map_id]
  simpa only [Category.id_comp] using (P.liftTriangleIso T hT).hom_inv_id

/-- Lifting preserves composition of triangle maps. -/
@[simp]
theorem liftTriangleMap_comp {T₁ T₂ T₃ : Triangle C}
    (hT₁ : P.OnTriangle T₁) (hT₂ : P.OnTriangle T₂)
    (hT₃ : P.OnTriangle T₃) (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    P.liftTriangleMap hT₁ hT₃ (f ≫ g) =
      P.liftTriangleMap hT₁ hT₂ f ≫ P.liftTriangleMap hT₂ hT₃ g := by
  apply P.ι.mapTriangle.map_injective
  rw [P.map_liftTriangleMap, Functor.map_comp,
    P.map_liftTriangleMap, P.map_liftTriangleMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end ObjectProperty

end CategoryTheory
