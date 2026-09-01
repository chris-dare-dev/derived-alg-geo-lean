/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Finite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# The zero module sheaf has finite presentation

On an arbitrary ringed site with binary products, the zero sheaf of modules admits the empty
finite presentation. Thus finite presentation contains a zero object independently of any
scheme or coherent-sheaf specialization.

## Main result

* `SheafOfModules.isFinitePresentation_containsZero`.
-/

universe u

open CategoryTheory Limits ZeroObject

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The zero sheaf of modules has finite presentation. -/
noncomputable instance isFinitePresentation_containsZero [HasBinaryProducts C] :
    (isFinitePresentation R).ContainsZero where
  exists_zero := by
    let P := presentationOfIsCokernelFree
      (𝟙 (free (R := R) PEmpty)) (0 : free (R := R) PEmpty ⟶ 0) (by simp)
      (CokernelCofork.IsColimit.ofEpiOfIsZero _ (by infer_instance) (isZero_zero _))
    letI : P.IsFinite := by
      constructor
      · refine ⟨?_⟩
        change Finite PEmpty
        infer_instance
      · refine ⟨?_⟩
        change Finite PEmpty
        infer_instance
    exact ⟨0, isZero_zero _, IsFinitePresentation.of_presentation.{u, u, u} P⟩

end SheafOfModules
