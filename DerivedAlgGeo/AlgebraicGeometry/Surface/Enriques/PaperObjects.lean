/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.Residual
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Classification

/-!
# Serre and object-classification data for the Enriques papers

This file connects the abstract Serre, spherical, and pseudoprojective APIs to
the Enriques residual category constructed from an isotropic 10-collection.
It records exactly the categorical conclusions used in arXiv:1912.04332v2 and
arXiv:2104.13610v2:

* the ambient derived category is `2`-Enriques, so its Serre functor squares
  to shift by four;
* the residual category has a chosen Serre autoequivalence;
* Paper I's ten `3`-spherical candidates are classified up to shift; and
* Paper II's length-one and longer-block candidates classify respectively the
  `3`-spherical and `3`-pseudoprojective objects.

The geometry proving these statements is deliberately exposed as supplied
data.  The current repository constructs the residual full subcategory but
does not yet construct its admissible projection or mutation functors, nor the
Ext computations for the projected candidates.  Consequently this file does
not manufacture those deep theorems from weaker hypotheses.  Its purpose is
to give them a precise, reusable Lean interface and to prove their formal
consumer consequences.
-/

universe u t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.SerreFunctor
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EnriquesSurface.IsotropicCollection

open Scheme.Modules

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y]
variable {C : SmoothProperVariety.CanonicalSheafData k Y 2}
  [SmoothProperVariety.IsEnriquesSurface k Y C]
variable {D : Cohomology.FiniteCohomology k Y} {S : D.LinearConnectingSystem}
variable (T : IsotropicCollection (Y := Y) (C := C) D S)

attribute [local instance] residualComponent_isTriangulated

/-- The Serre-theoretic categorical input for the two Enriques papers.

The ambient field is the formal content of the statement that `D^b(Y)` is a
`2`-Enriques category.  The residual field is kept separate: the papers give
the right orthogonal its own Serre autoequivalence, but do not assert that the
residual category is itself `2`-Enriques. -/
structure PaperCategoryData (exceptional : T.ExceptionalityData)
    (semiorthogonal : T.SemiorthogonalityData) where
  /-- The ambient derived category is `2`-Enriques. -/
  ambientEnriques : TwoEnriquesCategoryData k (DerivedCat Y)
  /-- The chosen Serre autoequivalence of the residual category. -/
  residualSerre :
    SerreCategoryData k (T.ResidualCategory exceptional semiorthogonal)

namespace PaperCategoryData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
  (P : T.PaperCategoryData exceptional semiorthogonal)

/-- Objectwise ambient relation `S_Y²(E) ≅ E[4]`. -/
noncomputable def ambientSerreSquareObjIso (E : DerivedCat Y) :
    P.ambientEnriques.serre.S.obj
      (P.ambientEnriques.serre.S.obj E) ≅ E⟦(4 : ℤ)⟧ :=
  P.ambientEnriques.serreSquareObjIso E

/-- The selected residual Serre functor is an autoequivalence. -/
theorem residualSerreIsEquivalence :
    P.residualSerre.serre.S.IsEquivalence :=
  P.residualSerre.serreIsEquivalence

end PaperCategoryData

/-- Paper I, Proposition 4.10, specialized to the residual category of the
isotropic 10-collection: ten `3`-spherical candidates, pairwise distinct up to
shift, classify all `3`-spherical objects. -/
abbrev PaperISphericalClassificationData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    (P : T.PaperCategoryData exceptional semiorthogonal) :=
  SphericalClassificationData P.residualSerre.serre 3 (Fin 10)

namespace PaperISphericalClassificationData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
  {P : T.PaperCategoryData exceptional semiorthogonal}
  (A : T.PaperISphericalClassificationData P)

/-- Exact Paper I classification: a residual object is `3`-spherical exactly
when it is a shift of one of the ten candidates. -/
theorem spherical_iff
    (E : T.ResidualCategory exceptional semiorthogonal) :
    IsSphericalObject P.residualSerre.serre 3 E ↔
      ∃ i : Fin 10, IsShiftOf E (A.candidate i) :=
  A.complete E

/-- Distinct Paper I candidates are not isomorphic after any shift. -/
theorem candidate_not_shift {i j : Fin 10} (hij : i ≠ j) :
    ¬ IsShiftOf (A.candidate i) (A.candidate j) :=
  A.candidate_not_isShiftOf hij

end PaperISphericalClassificationData

/-- Paper II, Theorem 2.7, specialized to degree three.  The index type keeps
track of the exceptional blocks and `blockLength` separates length-one
spherical candidates from longer pseudoprojective candidates. -/
abbrev PaperIIObjectClassificationData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    (P : T.PaperCategoryData exceptional semiorthogonal) (ι : Type t) :=
  MixedClassificationData P.residualSerre.serre 3 ι

namespace PaperIIObjectClassificationData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
  {P : T.PaperCategoryData exceptional semiorthogonal}
  {ι : Type t}
  (A : T.PaperIIObjectClassificationData P ι)

/-- Exact spherical half of Paper II's classification theorem. -/
theorem spherical_iff
    (E : T.ResidualCategory exceptional semiorthogonal) :
    IsSphericalObject P.residualSerre.serre 3 E ↔
      ∃ i, A.blockLength i = 1 ∧ IsShiftOf E (A.candidate i) :=
  A.spherical_complete E

/-- Exact pseudoprojective half of Paper II's classification theorem. -/
theorem pseudoprojective_iff
    (E : T.ResidualCategory exceptional semiorthogonal) :
    IsPseudoprojectiveObject P.residualSerre.serre 3 E ↔
      ∃ i, 2 ≤ A.blockLength i ∧ IsShiftOf E (A.candidate i) :=
  A.pseudoprojective_complete E

/-- A longer-block candidate cannot also be spherical. -/
theorem longer_candidate_not_spherical {i : ι}
    (hi : 2 ≤ A.blockLength i) :
    ¬ IsSphericalObject P.residualSerre.serre 3 (A.candidate i) :=
  (A.candidate_pseudoprojective hi).not_isSphericalObject (by omega)

/-- Distinct spherical Paper II candidates are not isomorphic up to shift. -/
theorem spherical_candidate_not_shift {i j : ι}
    (hi : A.blockLength i = 1) (hij : i ≠ j) :
    ¬ IsShiftOf (A.candidate i) (A.candidate j) :=
  A.spherical_candidate_not_isShiftOf hi hij

/-- Distinct pseudoprojective Paper II candidates are not isomorphic up to
shift. -/
theorem pseudoprojective_candidate_not_shift {i j : ι}
    (hi : 2 ≤ A.blockLength i) (hij : i ≠ j) :
    ¬ IsShiftOf (A.candidate i) (A.candidate j) :=
  A.pseudoprojective_candidate_not_isShiftOf hi hij

end PaperIIObjectClassificationData

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection
