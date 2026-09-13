/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.FiniteCohomologyCopowerK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomologyEuler
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearEvaluationK0

/-!
# Finite-presentation realization for scalar-linear evaluation

A supplied finite cohomology presentation for every dg Hom-complex proves the
shared rank-one `K₀` formula for scalar-linear evaluation when all scalar-linear
copowers exist.

The presentation family remains explicit: finite-dimensional bounded Hom in
`H⁰` does not provide formality.  The result also makes no exactness claim for
the evaluation functor and supplies no comparison with additive evaluation
data.  The scalar-universe restriction belongs to the finite-free copower
realization consumed here, not to the generic numerical predicate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace LinearEvaluationData

variable (k : Type v) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]
  {E : C}

/-- Supplied finite cohomology presentations compute every scalar-linear
evaluation class by the Euler pairing. -/
theorem IsEulerCopower.ofFiniteCohomologyPresentations
    [HasLinearCopowers k C] (V : LinearEvaluationData k E)
    (P : ∀ X : C, CochainComplex.FiniteCohomologyPresentation
      (DGLinear.homComplex k E X)) : V.IsEulerCopower k := by
  let W := ofHasLinearCopowers k E
  apply IsEulerCopower.ofCompare (V := W) (W := V)
  intro X
  let P_X := P X
  letI (i : {i // i ∈ P_X.degrees}) :
      Module.Finite k ((DGLinear.homComplex k E X).homology i.1) :=
    Module.Finite.equiv (H0.homologyShiftLinearEquiv (k := k) E X i.1).symm
  change K₀.of (H0 C)
      (show H0 C from linearCopowerObj (C := C) (DGLinear.homComplex k E X) E) =
    chiRight k (H0 C) (show H0 C from E) (K₀.of (H0 C) X) •
      K₀.of (H0 C) (show H0 C from E)
  rw [P_X.linearCopowerK₀Of E,
    H0.homComplex_homologyEulerChar_eq_chiHom, chiRight_of]

end LinearEvaluationData

end CategoryTheory
