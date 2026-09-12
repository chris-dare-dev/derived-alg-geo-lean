/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linear Hom equivalences from adjunctions

An adjunction between preadditive linear categories gives an additive equivalence between its
Hom groups when the left adjoint is additive. If the left adjoint is also linear, naturality in
the source upgrades that equivalence to a linear equivalence.

Only the left adjoint needs a linearity hypothesis: scalar multiplication on a morphism out of
`F.obj X` is rewritten as precomposition by `F.map (r • 𝟙 X)`.
-/

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Adjunction

variable {R : Type w} [Semiring R]
  {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- The Hom equivalence of an additive adjunction is linear when its left adjoint is linear. -/
noncomputable def homLinearEquiv (adj : F ⊣ G) [F.Additive] [F.Linear R]
    (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homAddEquiv X Y
  map_smul' r f := by
    change adj.homEquiv X Y (r • f) = r • adj.homEquiv X Y f
    calc
      adj.homEquiv X Y (r • f) =
          adj.homEquiv X Y (F.map (r • 𝟙 X) ≫ f) := by
            congr 1
            rw [F.map_smul, F.map_id, Linear.smul_comp, Category.id_comp]
      _ = (r • 𝟙 X) ≫ adj.homEquiv X Y f :=
        adj.homEquiv_naturality_left (r • 𝟙 X) f
      _ = r • adj.homEquiv X Y f := by
        rw [Linear.smul_comp, Category.id_comp]

end CategoryTheory.Adjunction
