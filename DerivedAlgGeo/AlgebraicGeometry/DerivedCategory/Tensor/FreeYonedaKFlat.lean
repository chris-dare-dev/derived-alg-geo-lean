/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.FlatResolutionTotalization
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedAboveKFlat
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Unbounded

/-!
# Functorial K-flat resolution from the free-Yoneda total

Resolving each good truncation of an arbitrary input produces a bounded-above
complex with identity-flat terms. The bounded-above K-flat theorem applies to
these resolved stages. Their free-Yoneda totals form a colimiting cocone over
the free-Yoneda total of the original input, so exact sequential colimits and
two-slot total-tensor colimit preservation pass K-flatness to every input.

## Main definitions

* `AlgebraicGeometry.DerivedCategory.freeYonedaSchemeKFlatResolution` inhabits
  the existing `AlgebraicGeometry.DerivedCategory.SchemeKFlatResolution` interface
  with the canonical functorial
  free-Yoneda total and its already-proved quasi-isomorphic augmentation.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isKFlat_freeYonedaSheafCoproductTotalComplexFunctor_obj`
  proves K-flatness of the canonical free-Yoneda total for every input complex.

## Implementation notes

The tower resolves `K.truncLE n` afresh at each stage. A good truncation of a
flat-term complex need not itself have flat terms at its cutoff. The proof uses
the existing mapped-tower colimit, not preservation of every filtered colimit
by the free-Yoneda functor. It transports both slots of K-flatness through the
canonical colimit isomorphism. This construction alone does not establish
acyclicity under arbitrary nonflat scheme pullback.

## References

The support bound comes from `FlatResolutionTotalization.lean`; the stagewise
criterion is
`AlgebraicGeometry.Scheme.Modules.isKFlat_totalTensor_of_boundedAbove_flatTerms`;
colimit closure is `CategoryTheory.CochainComplex.IsKFlat.colimit`.

## Tags

scheme-module sheaf, free-Yoneda resolution, K-flat complex, derived tensor
-/

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical free-Yoneda total of every scheme-module complex is K-flat
for the literal total tensor in both slots. No boundedness or flatness premise
is imposed on the input. -/
theorem isKFlat_freeYonedaSheafCoproductTotalComplexFunctor_obj
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    CochainComplex.IsKFlat (totalTensor X)
      ((freeYonedaSheafCoproductTotalComplexFunctor X).obj K) := by
  let H := freeYonedaSheafCoproductTotalComplexFunctor X
  let T := CochainComplex.truncLETower K ⋙ H
  letI : AB5OfSize.{0,0} X.Modules := AB5OfSize_of_univLE X.Modules
  letI (L : CochainComplex X.Modules ℤ) :
      PreservesColimitsOfShape ℕ ((totalTensor X).obj L) :=
    preservesColimitsOfShape_totalTensor_obj_nat X L
  letI (L : CochainComplex X.Modules ℤ) :
      PreservesColimitsOfShape ℕ ((totalTensor X).flip.obj L) :=
    preservesColimitsOfShape_totalTensor_flip_obj_nat X L
  have hStage : ∀ n, CochainComplex.IsKFlat (totalTensor X) (T.obj n) := by
    intro n
    haveI hBound : (T.obj n).IsStrictlyLE (n : ℤ) := by
      change CochainComplex.IsStrictlyLE (H.obj (K.truncLE (n : ℤ))) (n : ℤ)
      exact isStrictlyLE_freeYonedaSheafCoproductTotalComplexFunctor_obj
        X (K.truncLE (n : ℤ)) (n : ℤ)
    apply isKFlat_totalTensor_of_boundedAbove_flatTerms X (T.obj n) (n : ℤ)
    intro p
    change IsFlatOver (𝟙 X) ((H.obj (K.truncLE (n : ℤ))).X p)
    exact freeYonedaSheafCoproductTotalComplexFunctor_obj_X_isFlatOverId X _ p
  have hCol := CochainComplex.IsKFlat.colimit T hStage
  let e : H.obj K ≅ colimit T := IsColimit.coconePointUniqueUpToIso
    (isColimitFreeYonedaSheafCoproductTotalTruncLETowerCocone X K) (colimit.isColimit T)
  constructor
  · exact (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerRight ((totalTensor X).mapIso e) DerivedCategory.Q)).mpr hCol.1
  · exact (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerRight ((totalTensor X).flip.mapIso e) DerivedCategory.Q)).mpr hCol.2

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.DerivedCategory

/-- The canonical free-Yoneda total and augmentation give a functorial K-flat
resolution of every complex of scheme-module sheaves. -/
def freeYonedaSchemeKFlatResolution (X : Scheme.{u}) : SchemeKFlatResolution X where
  resolution := Scheme.Modules.freeYonedaSheafCoproductTotalComplexFunctor X
  comparison := Scheme.Modules.freeYonedaSheafCoproductTotalAugmentation X
  comparison_quasiIso := Scheme.Modules.quasiIso_freeYonedaSheafCoproductTotalAugmentation X
  isKFlat := Scheme.Modules.isKFlat_freeYonedaSheafCoproductTotalComplexFunctor_obj X

end AlgebraicGeometry.DerivedCategory

end
