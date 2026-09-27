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

* `HomologicalComplex₂.singleCompExtendTotalIso` gives the natural target
  comparison in an arbitrary preadditive category with a zero object and
  totals for the relevant bicomplexes.

## Implementation notes

The proof composes the natural single/extension comparison with the
mapped-single/flip comparison. The final flip comparison uses Mathlib's signed
total symmetry, fixing the total-complex differential sign.
-/

namespace HomologicalComplex₂

private noncomputable def targetSingleIso :
    ChainComplex.single₀ C ⋙
        ComplexShape.embeddingDownNat.extendFunctor C ≅
      CochainComplex.singleFunctor C 0 :=
  HomologicalComplex.singleCompExtendIso
    (C := C) ComplexShape.embeddingDownNat 0 0 rfl

private noncomputable def targetBicomplexIso :
    ((ChainComplex.single₀ C) ⋙
      ComplexShape.embeddingDownNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (CochainComplex.singleFunctor C 0).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  CategoryTheory.NatIso.mapHomologicalComplex
    (targetSingleIso (C := C)) (ComplexShape.up ℤ)

private noncomputable def targetTotalIso :
    (((ChainComplex.single₀ C) ⋙
        ComplexShape.embeddingDownNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
      ((CochainComplex.singleFunctor C 0).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CategoryTheory.Functor.isoWhiskerRight (targetBicomplexIso (C := C)) _

private noncomputable def mappedSingleFlipIso :
    (CochainComplex.singleFunctor C 0).mapHomologicalComplex
      (ComplexShape.up ℤ) ≅
    CochainComplex.singleFunctor (CochainComplex C ℤ) 0 ⋙
      HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.singleMapHomologicalComplexFlipIso
    (C := C) (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0

private noncomputable def mappedSingleTotalFlipIso :
    ((CochainComplex.singleFunctor C 0).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    (CochainComplex.singleFunctor (CochainComplex C ℤ) 0 ⋙
      HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CategoryTheory.Functor.isoWhiskerRight (mappedSingleFlipIso (C := C)) _

private noncomputable def flippedSingleTotalToId :
    (CochainComplex.singleFunctor (CochainComplex C ℤ) 0 ⋙
      HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
      HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex C ℤ) :=
  CategoryTheory.NatIso.ofComponents
    (fun K => HomologicalComplex₂.singleZeroFlipTotalIso K)
    (by
      intro K L f
      exact HomologicalComplex₂.singleZeroFlipTotalIso_naturality f)

/-- The natural isomorphism from totalizing the degree-zero chain single
after extension and degreewise mapping to the identity on cochain complexes. -/
noncomputable def singleCompExtendTotalIso :
    (((ChainComplex.single₀ C) ⋙
        ComplexShape.embeddingDownNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex C ℤ) :=
  (targetTotalIso (C := C)).trans
    ((mappedSingleTotalFlipIso (C := C)).trans (flippedSingleTotalToId (C := C)))

end HomologicalComplex₂
