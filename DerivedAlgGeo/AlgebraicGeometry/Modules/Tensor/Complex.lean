/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import Mathlib.Algebra.Homology.Monoidal

/-!
# Total tensor products of complexes of scheme-module sheaves

The sheafified tensor product is additive in both variables and `X.Modules` has all coproducts.
Mathlib's total-complex construction therefore promotes it to a bifunctor on unbounded cochain
complexes. This is the underived complex-level input for K-flat localization.
-/

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The total tensor product of two unbounded cochain complexes of module sheaves. -/
noncomputable def totalTensor (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ ⥤
      CochainComplex X.Modules ℤ :=
  (curriedTensor X.Modules).map₂CochainComplex

@[simp]
lemma totalTensor_obj_obj (X : Scheme.{u}) (K L : CochainComplex X.Modules ℤ) :
    ((totalTensor X).obj K).obj L = HomologicalComplex.tensorObj K L :=
  rfl

end

end AlgebraicGeometry.Scheme.Modules
