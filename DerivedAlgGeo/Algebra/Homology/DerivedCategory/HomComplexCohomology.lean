/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Degree-zero Hom-complex classes and derived-category morphisms

For a K-projective source, degree-zero cohomology classes of the Hom complex
identify additively with morphisms in the derived category. This compares
Hom-sets; it does not construct an internal derived-Hom object.
-/

open CategoryTheory

namespace CochainComplex.HomComplex.CohomologyClass

universe u v

/-- Degree-zero Hom-complex classes are derived-category morphisms when the
source complex is K-projective. The equivalence is additive; no scalar-linearity
or base-change compatibility is asserted. -/
noncomputable def derivedCategoryHomAddEquiv
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [K.IsKProjective] :
    CohomologyClass K L 0 ≃+
      ((DerivedCategory.Qh).obj ((HomotopyCategory.quotient C (.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh).obj ((HomotopyCategory.quotient C (.up ℤ)).obj L)) := by
  let Kₕ := (HomotopyCategory.quotient C (.up ℤ)).obj K
  let Lₕ := (HomotopyCategory.quotient C (.up ℤ)).obj L
  let L₀ := (HomotopyCategory.quotient C (.up ℤ)).obj (L⟦(0 : ℤ)⟧)
  let e : L₀ ≅ Lₕ :=
    (HomotopyCategory.quotient C (.up ℤ)).mapIso
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app L)
  let e₁ : (Kₕ ⟶ L₀) ≃+ (Kₕ ⟶ Lₕ) :=
    { toFun := fun f => f ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := by intro f; simp
      right_inv := by intro g; simp
      map_add' := by intro f g; simp [Preadditive.add_comp] }
  let e₂ : (Kₕ ⟶ Lₕ) ≃+
      ((DerivedCategory.Qh).obj Kₕ ⟶ (DerivedCategory.Qh).obj Lₕ) :=
    AddEquiv.ofBijective (Functor.mapAddHom DerivedCategory.Qh)
      (CochainComplex.IsKProjective.Qh_map_bijective K Lₕ)
  exact CohomologyClass.homAddEquiv.trans (e₁.trans e₂)

end CochainComplex.HomComplex.CohomologyClass
