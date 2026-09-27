/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Embedding.Extend
import DerivedAlgGeo.Algebra.Homology.HomologicalBicomplex
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.SingleZeroTotal
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.TotalComplex

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]

/-!
# Totalization of a single complex extended along the chain-to-cochain embedding

The chain-degree-zero presentation of an object can be extended to integer
cochain degrees and mapped over an input cochain complex. Its direct-sum total
is naturally isomorphic to the input complex.

## Main definitions and results

* `HomologicalComplex₂.singleExtendToZeroTotalIso` compares the total for any
  single degree whose embedding lands at integer cochain degree zero.
* `HomologicalComplex₂.singleCompExtendTotalIso` specializes it to the standard
  nonnegative-chain embedding.

## Implementation notes

The single/extension and mapped-single/flip comparisons are natural. The
final comparison passes through Mathlib's signed total symmetry; the surviving
single column has sign one.

## References

`HomologicalComplex₂.singleZeroFlipTotalIso` supplies the signed total
comparison used in both results.
-/

namespace HomologicalComplex₂

/-- The signed flip of the single-zero bicomplex fixes the differential of
the input cochain complex. This comparison uses no geometric resolution data
and works for any source degree embedded at cochain degree zero. -/
noncomputable def singleExtendToZeroTotalIso
    {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    (e : c.Embedding (ComplexShape.up ℤ)) (i : ι) (h : e.f i = 0) :
    (((HomologicalComplex.single C c i) ⋙
        e.extendFunctor C).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex C ℤ) :=
  (CategoryTheory.Functor.isoWhiskerRight
    (CategoryTheory.NatIso.mapHomologicalComplex
      (HomologicalComplex.singleCompExtendIso (C := C) e i 0 h)
      (ComplexShape.up ℤ)) _).trans
    ((CategoryTheory.Functor.isoWhiskerRight
      (HomologicalComplex₂.singleMapHomologicalComplexFlipIso
        (C := C) (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0) _).trans
      (CategoryTheory.NatIso.ofComponents
        (fun K => HomologicalComplex₂.singleZeroFlipTotalIso K)
        (by
          intro K L f
          exact HomologicalComplex₂.singleZeroFlipTotalIso_naturality f)))

/-- The comparison passes through the signed flip of the single-zero bicomplex
so its differential agrees with the input cochain differential; it uses no
geometric resolution data. -/
noncomputable def singleCompExtendTotalIso :
    (((ChainComplex.single₀ C) ⋙
        ComplexShape.embeddingDownNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex C ℤ) :=
  singleExtendToZeroTotalIso (C := C) ComplexShape.embeddingDownNat 0 rfl

end HomologicalComplex₂
