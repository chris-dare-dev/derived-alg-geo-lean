/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearEvaluation
import DerivedAlgGeo.Algebra.Homology.DGCategory.FunctorCategoryH0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomology
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Triangle
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.RankOne

/-!
# Euler-class realization for scalar-linear evaluation data

`LinearEvaluationData.IsEulerCopower` specializes the shared objectwise
rank-one `K₀` interface to `RHom(E,-) ⊗ₖ E` and is invariant under the
canonical comparison between choices.

The predicate makes no exactness claim for the evaluation functor.  Although
additive and scalar-linear evaluation data use the same numerical interface,
this supplies no comparison between their different universal properties.
The finite-presentation realization is owned downstream by the homotopy-
category DG-enhancement layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace LinearEvaluationData

section Predicate

variable (k : Type w) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]
  {E : C}

/-- Scalar-linear evaluation realizes the Euler copower formula when its
object classes are the rank-one operator `χ(E,-) [E]`. -/
def IsEulerCopower (V : LinearEvaluationData k E) : Prop :=
  K₀.IsRankOne V.functor.h0
    (chiRight k (H0 C) (show H0 C from E))
    (K₀.of (H0 C) (show H0 C from E))

/-- The scalar-linear Euler copower formula is independent of the chosen
linear evaluation data. -/
theorem IsEulerCopower.ofCompare {V W : LinearEvaluationData k E}
    (hV : V.IsEulerCopower k) : W.IsEulerCopower k := by
  exact K₀.IsRankOne.ofIso hV (DGFunctor.h0Iso (V.compareIso W))

end Predicate

end LinearEvaluationData

end CategoryTheory
