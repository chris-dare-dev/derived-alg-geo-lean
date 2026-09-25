/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.FlatGenerators
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Total complex of the free-Yoneda flat-resolution bicomplex

The objectwise left resolution gives a bicomplex of flat module sheaves. We include its
resolution direction into the integers and form Mathlib's direct-sum total complex in
`X.Modules`. The construction is functorial, but this file does not identify its total
complex with the input, prove its terms flat, or prove K-flatness.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Extend the resolution degree of the free-Yoneda bicomplex from nonnegative chain
degrees to nonpositive integer cochain degrees, then include the flat terms into all
module sheaves. -/
noncomputable def freeYonedaSheafCoproductResolutionBicomplexUpInt
    (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤
      HomologicalComplex₂ X.Modules (ComplexShape.up ℤ) (ComplexShape.up ℤ) := by
  let ι := ObjectProperty.ι (fun M : X.Modules => IsFlatOver (𝟙 X) M)
  let E := ι.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor X.Modules
  letI : E.PreservesZeroMorphisms := by infer_instance
  exact freeYonedaSheafCoproductResolutionBicomplex X ⋙
    E.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The direct-sum total complex of the functorial free-Yoneda flat-resolution bicomplex.
Its comparison with the input and K-flatness remain separate obligations. -/
noncomputable def freeYonedaSheafCoproductTotalComplexFunctor (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  freeYonedaSheafCoproductResolutionBicomplexUpInt X ⋙
    HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

end AlgebraicGeometry.Scheme.Modules
