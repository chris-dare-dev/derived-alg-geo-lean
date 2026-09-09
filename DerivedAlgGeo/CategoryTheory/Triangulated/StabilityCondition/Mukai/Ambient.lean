/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.Charge
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HeartComparison

/-!
# Ambient Mukai charges and restriction to a heart

This module is the categorical transport layer for the Mukai exponential
charge.  An additive Mukai class map on `K₀ C` determines an additive complex
charge on `K₀ C`; restriction along `K₀Ab.toAmbient` gives the corresponding
heart datum.  Triangle and shift formulas are then inherited from the
Grothendieck group rather than reproved from the charge formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v

namespace CategoryTheory.Triangulated

attribute [local instance] TStructure.heartFullSubcategoryAbelian

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace MukaiChargeData

variable (t : TStructure C)

/-- **The heart datum of an ambient Mukai class map**, by restriction along
`K₀Ab.toAmbient`. -/
def ofAmbient (m : K₀ C →+ Mukai.RealExtension V) :
    MukaiChargeData t.heart.FullSubcategory V where
  mukai := m.comp (K₀Ab.toAmbient t)

@[simp]
theorem ofAmbient_mukai (m : K₀ C →+ Mukai.RealExtension V)
    (E : t.heart.FullSubcategory) :
    (ofAmbient t m).mukai (K₀Ab.of E) = m (K₀.of C E.obj) := by
  simp [ofAmbient]

/-- The exponential Mukai charge as an additive homomorphism on ambient
Grothendieck classes. -/
noncomputable def ambientChargeHom (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) : K₀ C →+ ℂ :=
  (Mukai.expChargeHom b β ω).comp m

omit [IsTriangulated C] in
@[simp]
theorem ambientChargeHom_apply (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (x : K₀ C) :
    ambientChargeHom m b β ω x = Mukai.expCharge b β ω (m x) := rfl

/-- The ambient charge, on any object of `C`. -/
def ambientCharge (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (X : C) : ℂ :=
  ambientChargeHom m b β ω (K₀.of C X)

/-- On a heart object the ambient charge is the restricted heart charge — by
construction. -/
@[simp]
theorem ambientCharge_obj (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (E : t.heart.FullSubcategory) :
    ambientCharge m b β ω E.obj = (ofAmbient t m).charge b β ω E := by
  rw [ambientCharge, ambientChargeHom_apply, MukaiChargeData.charge_apply, ofAmbient_mukai]

omit [IsTriangulated C] in
/-- The ambient charge is additive on distinguished triangles. -/
theorem ambientCharge_triangle (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) {T : Triangle C} (hT : T ∈ distTriang C) :
    ambientCharge m b β ω T.obj₂ =
      ambientCharge m b β ω T.obj₁ + ambientCharge m b β ω T.obj₃ := by
  rw [ambientCharge, ambientCharge, ambientCharge, K₀.of_triangle C T hT, map_add]

omit [IsTriangulated C] in
/-- A shift negates the ambient charge. -/
theorem ambientCharge_shift (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (X : C) :
    ambientCharge m b β ω (X⟦(1 : ℤ)⟧) = -ambientCharge m b β ω X := by
  rw [ambientCharge, ambientCharge, K₀.of_shift_one, map_neg]

end MukaiChargeData

end CategoryTheory.Triangulated
