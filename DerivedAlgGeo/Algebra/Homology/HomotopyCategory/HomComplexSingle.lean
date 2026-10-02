/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.Additive

/-!
# Hom complexes from a degree-zero single object

For an arbitrary integer-indexed cochain complex, the Hom complex from a
degree-zero single object is the degreewise additive coyoneda functor. The
comparison includes the incoming degree-minus-one boundary; it does not
replace cohomology by the outgoing kernel. A represented additive functor
inherits the same comparison, including its degree-zero homology.

This is a generic Hom-complex extension. No affine, quasicoherent, boundedness,
or injectivity hypothesis is used.

## Main definitions

* `CochainComplex.HomComplex.singleCoyonedaIso`
* `CochainComplex.HomComplex.singleRepresentedIso`
* `CochainComplex.HomComplex.singleRepresentedHomologyAddEquiv`
* `CochainComplex.HomComplex.singleRepresentedHomologyZeroAddEquiv`

## Main results

The isomorphism identifies the full Hom complex, and the additive equivalence
identifies cohomology in every integer degree with represented degreewise
homology. The degree-zero result is a specialization.

## Implementation notes

Mathlib's `fromSingleEquiv` supplies each component. Its formula for the
Hom-complex differential proves compatibility without a support bound.

## References

Mathlib `HomComplexSingle.lean` and `Preadditive/Yoneda/Basic.lean` at pin
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

Hom complex, additive coyoneda, represented functor, cohomology
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The Hom complex from a degree-zero single object is the additive coyoneda
functor applied degreewise. The component maps are Mathlib's
`Cochain.fromSingleEquiv`; `Cochain.δ_fromSingleMk` supplies differential
compatibility at every integer degree. -/
noncomputable def singleCoyonedaIso (X : C) (K : CochainComplex C ℤ) :
    HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (X := X) (K := K) (zero_add n)).toAddCommGrpIso)
    (by
      intro i j hij
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro α
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective α i (zero_add i)
      simp only [CategoryTheory.comp_apply, AddEquiv.toAddCommGrpIso_hom]
      change Cochain.fromSingleEquiv (zero_add i)
          (Cochain.fromSingleMk f (zero_add i)) ≫ K.d i j =
        Cochain.fromSingleEquiv (zero_add j)
          (δ i j (Cochain.fromSingleMk f (zero_add i)))
      rw [Cochain.fromSingleEquiv_fromSingleMk,
        Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j),
        Cochain.fromSingleEquiv_fromSingleMk])

/-- Specialize `singleCoyonedaIso` along a supplied representation of a
zero-morphism-preserving functor. The representation is a natural isomorphism
of functors; the complex comparison does not require a separate additivity or
exactness hypothesis. -/
noncomputable def singleRepresentedIso
    (X : C) (F : C ⥤ AddCommGrpCat.{v}) [F.PreservesZeroMorphisms]
    (e : preadditiveCoyoneda.obj (op X) ≅ F) (K : CochainComplex C ℤ) :
    HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      (F.mapHomologicalComplex (.up ℤ)).obj K :=
  singleCoyonedaIso X K ≪≫ (NatIso.mapHomologicalComplex e (.up ℤ)).app K

/-- Degree-`n` classes in the Hom complex are degree-`n` homology of any
represented zero-morphism-preserving functor applied degreewise. In
particular, the quotient retains boundaries from degree `n - 1`. -/
noncomputable def singleRepresentedHomologyAddEquiv
    (X : C) (F : C ⥤ AddCommGrpCat.{v}) [F.PreservesZeroMorphisms]
    (e : preadditiveCoyoneda.obj (op X) ≅ F) (K : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass ((CochainComplex.singleFunctor C 0).obj X) K n ≃+
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology n :=
  (homologyAddEquiv _ K n).symm.trans
    (HomologicalComplex.homologyMapIso
      (singleRepresentedIso X F e K) n).addCommGroupIsoToAddEquiv

/-- Degree-zero specialization of `singleRepresentedHomologyAddEquiv`. -/
noncomputable def singleRepresentedHomologyZeroAddEquiv
    (X : C) (F : C ⥤ AddCommGrpCat.{v}) [F.PreservesZeroMorphisms]
    (e : preadditiveCoyoneda.obj (op X) ≅ F) (K : CochainComplex C ℤ) :
    CohomologyClass ((CochainComplex.singleFunctor C 0).obj X) K 0 ≃+
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology 0 :=
  singleRepresentedHomologyAddEquiv X F e K 0

end CochainComplex.HomComplex
