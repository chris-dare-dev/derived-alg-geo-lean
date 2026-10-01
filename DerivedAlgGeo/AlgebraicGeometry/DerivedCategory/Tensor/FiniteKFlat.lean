/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Bifunctor
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KFlatResolution
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Complex

/-!
# Finite flat complexes are K-flat for scheme-module tensor

A complex of scheme-module sheaves with finite term support is K-flat for the
literal total tensor when every term in its support interval is flat over the
identity. The fixed complex may have zero terms outside the interval; no
flatness evidence is needed there.

## Main definitions

This module introduces no new definitions. It specializes the existing
`CategoryTheory.CochainComplex.IsKFlat` predicate to
`AlgebraicGeometry.Scheme.Modules.totalTensor`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.quasiIso_totalTensor_map_left_of_finiteFlatTerms`
  sends a quasi-isomorphism through the second slot of total tensor.
* `AlgebraicGeometry.Scheme.Modules.quasiIso_totalTensor_map_right_of_finiteFlatTerms`
  sends a quasi-isomorphism through the first slot.
* `AlgebraicGeometry.Scheme.Modules.isKFlat_totalTensor_of_finiteFlatTerms`
  packages both directions into the generic K-flat predicate.

## Implementation notes

The generic finite-strip theorem for bifunctor totals reduces both maps to
columnwise quasi-isomorphisms. Flatness of each supported sheaf supplies those
columnwise results through homology preservation of ordinary tensor. The
right-slot proof uses the generic signed-flip comparison; no global braiding
instance on complexes is required. This does not prove K-flatness of an
unbounded complex of flat terms.

## References

The finite-strip criterion is
`HomologicalComplex.quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso`
and its right-slot counterpart. The flat-sheaf inputs are
`AlgebraicGeometry.Scheme.Modules.quasiIso_map_tensorLeftFunctor_of_isFlatOverId`
and `AlgebraicGeometry.Scheme.Modules.quasiIso_map_tensorRight_of_isFlatOverId`.

## Tags

scheme-module sheaf, flatness, total tensor, K-flat complex, quasi-isomorphism
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory ComplexShape

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Flatness gives quasi-isomorphisms columnwise, and finite support lets the
finite-strip criterion pass them to the total. No flatness witness is needed
outside the support interval. -/
theorem quasiIso_totalTensor_map_left_of_finiteFlatTerms
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hFlat : ∀ p, a ≤ p → p ≤ b → IsFlatOver (𝟙 X) (K.X p))
    {L M : CochainComplex X.Modules ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso (((totalTensor X).obj K).map f) := by
  have hcol : ∀ p, a ≤ p → p ≤ b →
      QuasiIso (((((curriedTensor X.Modules).obj (K.X p)).mapHomologicalComplex
        (up ℤ)).map f)) := by
    intro p hpa hpb
    exact quasiIso_map_tensorLeftFunctor_of_isFlatOverId X (K.X p)
      (hFlat p hpa hpb) f
  exact HomologicalComplex.quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso
    (curriedTensor X.Modules) K f a b hLower hUpper hcol

/-- The generic signed-flip comparison applies the finite-strip criterion with
the supported complex fixed on the right, without a braiding instance on
complexes. -/
theorem quasiIso_totalTensor_map_right_of_finiteFlatTerms
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hFlat : ∀ p, a ≤ p → p ≤ b → IsFlatOver (𝟙 X) (K.X p))
    {L M : CochainComplex X.Modules ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso (((totalTensor X).flip.obj K).map f) := by
  have hcol : ∀ p, a ≤ p → p ≤ b →
      QuasiIso (((((curriedTensor X.Modules).flip.obj (K.X p)).mapHomologicalComplex
        (up ℤ)).map f)) := by
    intro p hpa hpb
    exact quasiIso_map_tensorRight_of_isFlatOverId X (K.X p)
      (hFlat p hpa hpb) f
  exact HomologicalComplex.quasiIso_mapBifunctorMap_id_right_of_finite_support_of_column_quasiIso
    (curriedTensor X.Modules) K f a b hLower hUpper hcol

/-- The two total-map results supply the localization clauses of the generic
K-flat predicate. This proves K-flatness of the supplied complex without
constructing a resolution. -/
theorem isKFlat_totalTensor_of_finiteFlatTerms
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hFlat : ∀ p, a ≤ p → p ≤ b → IsFlatOver (𝟙 X) (K.X p)) :
    CochainComplex.IsKFlat (totalTensor X) K := by
  constructor
  · intro L M f hf
    letI : QuasiIso f := hf
    change IsIso (DerivedCategory.Q.map (((totalTensor X).obj K).map f))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_totalTensor_map_left_of_finiteFlatTerms
      X K a b hLower hUpper hFlat f
  · intro L M f hf
    letI : QuasiIso f := hf
    change IsIso (DerivedCategory.Q.map (((totalTensor X).flip.obj K).map f))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_totalTensor_map_right_of_finiteFlatTerms
      X K a b hLower hUpper hFlat f

end

end AlgebraicGeometry.Scheme.Modules
