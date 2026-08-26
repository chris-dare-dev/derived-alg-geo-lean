/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge

/-!
# From the Grothendieck group of a heart to the ambient one

`K₀Ab.toAmbient` sends the class of a heart object to the class of the
underlying ambient object, `K₀Ab 𝒜 →+ K₀ C` for `𝒜` the heart of a t-structure
on `C`.

## Why only one direction, and why that is enough

`Weak/Basic/Definitions.lean` records that the comparison `K(𝒜) ≅ K(D)` for a
bounded t-structure is not available at this Mathlib pin and is not assumed.
That is the **isomorphism**.  This file constructs only the **map**, which needs
no boundedness and no inverse: a short exact sequence in the heart extends to a
distinguished triangle on the same three objects
(`heartFullSubcategory_shortExact_triangle`), so the abelian relations are
carried into the triangulated ones and `GrothendieckPresentation.map` applies.

Every conversion between a charge on a heart and a charge on `K₀ C` uses the map
in this direction only, so nothing here depends on the unavailable iso.

## What this replaces

Charges written on heart objects and charges written on `K₀ C` were previously
two unrelated families, and the conversion between them existed once, hand-rolled
and inlined, inside a mass-subadditivity file.  With this map the conversion is
`AddMonoidHom.comp`.
-/

universe v u

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] (t : TStructure C)

attribute [local instance] TStructure.hasHeartFullSubcategory
  TStructure.heartFullSubcategoryAbelian

/-- A short exact sequence in the heart, as a distinguished triangle on the same
three ambient objects.  The `delta` is chosen; the map below only needs the
objects, which are determined. -/
noncomputable def shortExactToTriangle
    (r : {S : ShortComplex t.heart.FullSubcategory // S.ShortExact}) :
    {T : Triangle C // T ∈ distTriang C} := by
  have hmono : Mono r.1.f := r.2.mono_f
  have hepi : Epi r.1.g := r.2.epi_g
  have hlift : ∀ {W : t.heart.FullSubcategory} (alpha : W ⟶ r.1.X₂),
      alpha ≫ r.1.g = 0 → ∃ beta : W ⟶ r.1.X₁, beta ≫ r.1.f = alpha :=
    fun alpha halpha ↦ ⟨r.2.exact.lift alpha halpha, r.2.exact.lift_f alpha halpha⟩
  exact ⟨_, (heartFullSubcategory_shortExact_triangle t r.1.f r.1.g r.1.zero hlift).choose_spec⟩

/-- The underlying-object function carries abelian relations of the heart into
triangulated relations of `C`. -/
theorem toAmbient_isAdditive :
    (abelianPresentation t.heart.FullSubcategory).IsAdditive
      ((triangulatedPresentation C).of ∘ (fun X : t.heart.FullSubcategory ↦ X.obj)) :=
  GrothendieckPresentation.IsAdditive.of_relationMap
    (P := abelianPresentation t.heart.FullSubcategory)
    (Q := triangulatedPresentation C)
    (fun X ↦ X.obj) (shortExactToTriangle t) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- **The comparison map `K₀Ab 𝒜 →+ K₀ C`.**

Built from `GrothendieckPresentation.map`: the underlying-object function carries
the abelian relations of the heart into the triangulated relations of `C`, which
is exactly `heartFullSubcategory_shortExact_triangle`. -/
noncomputable def _root_.CategoryTheory.K₀Ab.toAmbient :
    K₀Ab t.heart.FullSubcategory →+ K₀ C :=
  (abelianPresentation t.heart.FullSubcategory).map
    (Q := triangulatedPresentation C) (fun X ↦ X.obj) (toAmbient_isAdditive t)

@[simp]
theorem _root_.CategoryTheory.K₀Ab.toAmbient_of (E : t.heart.FullSubcategory) :
    K₀Ab.toAmbient t (K₀Ab.of E) = K₀.of C E.obj :=
  (abelianPresentation t.heart.FullSubcategory).map_of
    (Q := triangulatedPresentation C) _ _ E

end Triangulated.TStructure

end CategoryTheory
