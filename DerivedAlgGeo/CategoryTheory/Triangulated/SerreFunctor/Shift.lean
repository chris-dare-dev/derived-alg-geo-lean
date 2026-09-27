/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Conjugation
import Mathlib.CategoryTheory.Shift.Basic

/-!
# Serre functors and shifts

The shift comparison comes from conjugation by the shift equivalence and
uniqueness of the Serre functor. Applying Serre uniqueness directly to
`S ⋙ [1]` and `[1] ⋙ S` is invalid: either functor represents the dual of
`Hom(A, B⟦-1⟧)`, rather than the dual of `Hom(A, B)`.

The displayed comparison here is pointwise in the shift index. A coherent
`CommShift ℤ` structure and preservation of distinguished triangles require
additional proofs; the latter is the separate research seam #1576.

## Main definition

`SerreFunctorData.commShiftIso n` specializes linear conjugation transport to
the equivalence given by the single shift `n`.
-/

universe w v u

namespace CategoryTheory.SerreFunctor.SerreFunctorData

open CategoryTheory

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]

/-- The Serre functor commutes with each shift, by conjugation with the
corresponding shift equivalence. This is the orientation used in #898;
Mathlib's `CommShift` stores the inverse orientation. -/
noncomputable def commShiftIso (D : SerreFunctorData k C) (n : ℤ)
    [(shiftFunctor C n).Additive] [(shiftFunctor C n).Linear k] :
    D.S ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ D.S := by
  letI : (shiftEquiv C n).functor.Additive := by
    change (shiftFunctor C n).Additive
    infer_instance
  letI : (shiftEquiv C n).functor.Linear k := by
    change (shiftFunctor C n).Linear k
    infer_instance
  exact (D.transportIso (shiftEquiv C n)).symm

end CategoryTheory.SerreFunctor.SerreFunctorData
