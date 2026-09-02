/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Objects
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Exceptional

/-!
# Enriques categories

Definition 4.2 of arXiv:1912.04332v2 calls a linear triangulated category
`m`-Enriques when its Serre functor satisfies `S² ≅ [2m]`, with
`m ∈ (1/2)ℤ`.  The integral parameter `twiceDimension` used here is exactly
`2m`; it avoids introducing a rational index for a shift that is intrinsically
integer-valued.

The Serre functor is required to be an autoequivalence as part of the package.
`SerreFunctorData` alone does not assert essential surjectivity at this level of
generality, so that fact is an explicit field rather than an invalid theorem.

The file also proves Remark 4.3(iii): if a positive-dimensional Serre functor
is itself a shift, the category contains no exceptional objects.  This is a
genuine consequence of Serre duality and the exceptional-object vanishing
clause; no geometry enters.
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]

/-- An Enriques-category structure of half-integral dimension
`twiceDimension / 2`. -/
structure EnriquesCategoryData (twiceDimension : ℤ)
    extends SerreCategoryData k C where
  /-- The square of the Serre functor is the indicated shift. -/
  squareShift : Nonempty (serre.S ⋙ serre.S ≅ shiftFunctor C twiceDimension)

/-- The paper's `2`-Enriques categories, for which `S² ≅ [4]`. -/
abbrev TwoEnriquesCategoryData := EnriquesCategoryData k C 4

namespace EnriquesCategoryData

variable {k C} {twiceDimension : ℤ}
  (A : EnriquesCategoryData k C twiceDimension)

/-- The half-integral Enriques dimension, retained as a readable invariant. -/
def dimension : ℚ := (twiceDimension : ℚ) / 2

/-- A selected square-to-shift isomorphism from the property-valued field. -/
noncomputable def serreSquareIso :
    A.serre.S ⋙ A.serre.S ≅ shiftFunctor C twiceDimension :=
  A.squareShift.some

/-- Objectwise form of `S² ≅ [2m]`. -/
noncomputable def serreSquareObjIso (E : C) :
    A.serre.S.obj (A.serre.S.obj E) ≅ E⟦twiceDimension⟧ :=
  (A.serreSquareIso).app E

/-- The chosen Serre functor can be used as an equivalence by instance search
inside a consumer without making equivalence a global instance. -/
theorem hasSerreEquivalence : A.serre.S.IsEquivalence :=
  A.serreIsEquivalence

end EnriquesCategoryData

variable {k C}

/-- If a nonzero shift is a Serre functor, no object can be exceptional.

This is Remark 4.3(iii) of arXiv:1912.04332v2.  The proof compares dimensions:
Serre duality identifies `End(E)` with the dual of `Hom(E,S E)`, the displayed
Serre/shift isomorphism identifies the latter with `Hom(E,E[n])`, and
exceptionality makes the first one-dimensional and the last zero. -/
theorem no_exceptional_of_serre_iso_shift [HomFinite k C]
    (D : SerreFunctorData k C) (n : ℤ) (hn : n ≠ 0)
    (hS : Nonempty (D.S ≅ shiftFunctor C n)) (E : C) :
    ¬ IsExceptional k E := by
  intro hE
  have hAlg : Function.Bijective (Algebra.linearMap k (End E)) := by
    simpa only [Algebra.coe_linearMap] using hE.algebraMap_bijective
  let endEquiv : k ≃ₗ[k] End E :=
    LinearEquiv.ofBijective (Algebra.linearMap k (End E)) hAlg
  have hend : Module.finrank k (End E) = 1 := by
    rw [← endEquiv.finrank_eq, Module.finrank_self]
  have hserre := D.finrank_hom_eq E E
  have htransport :
      Module.finrank k (E ⟶ D.S.obj E) =
        Module.finrank k (E ⟶ E⟦n⟧) :=
    (Linear.homCongr k (Iso.refl E) (hS.some.app E)).finrank_eq
  have hsub : Subsingleton (E ⟶ E⟦n⟧) :=
    ⟨fun f g ↦ by rw [hE.hom_shift_eq_zero n hn f,
      hE.hom_shift_eq_zero n hn g]⟩
  have hzero : Module.finrank k (E ⟶ E⟦n⟧) = 0 :=
    Module.finrank_zero_of_subsingleton
  exact one_ne_zero (hend.symm.trans (hserre.trans (htransport.trans hzero)))

end CategoryTheory.SerreFunctor
