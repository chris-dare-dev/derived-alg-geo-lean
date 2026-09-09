/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Functoriality laws for short-exact derived triangles

Mathlib constructs a morphism between the distinguished triangles associated
to a morphism of short exact sequences. This file records the identity and
composition laws for that construction, so downstream geometry can use it as
a functorial interface rather than unfold its three components.
-/

universe v u

open CategoryTheory Category

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard

@[simp]
theorem singleTriangle.map_id {S : ShortComplex C} (hS : S.ShortExact) :
    singleTriangle.map hS hS (𝟙 S) = 𝟙 hS.singleTriangle := by
  ext <;> simp [singleTriangle.map] <;> rfl

@[simp, reassoc]
theorem singleTriangle.map_comp {S₁ S₂ S₃ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (h₃ : S₃.ShortExact)
    (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    singleTriangle.map h₁ h₃ (f ≫ g) =
      singleTriangle.map h₁ h₂ f ≫ singleTriangle.map h₂ h₃ g := by
  ext <;> simp [singleTriangle.map] <;> rfl

end CategoryTheory.ShortComplex.ShortExact
