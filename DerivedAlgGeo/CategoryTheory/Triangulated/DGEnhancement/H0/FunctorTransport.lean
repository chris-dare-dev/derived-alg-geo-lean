/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Adjunction
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor

/-!
# Transporting `H⁰` dg functors through ordinary equivalences

For a dg functor `F : C ⟶ D` and ordinary equivalences `H⁰ C ≌ X` and
`H⁰ D ≌ Y`, this file packages the conjugate functor

`X ⥤ H⁰ C ⥤ H⁰ D ⥤ Y`

using Mathlib's existing `CommShift`, triangulated-functor, and equivalence
interfaces.  The source inverse shift comparison is derived from the supplied
forward comparison by `Equivalence.commShiftInverse`; no duplicate transport
or exactness structure is introduced.

The equivalence constructor assumes only that `F.h0` is an equivalence.  It
does not infer a dg quasi-equivalence, and the exactness declarations require
the ordinary comparison equivalences to be supplied as triangulated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY uC uD uX uY

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace DGFunctor

variable {C : Type uC} {D : Type uD} {X : Type uX} {Y : Type uY}
  [DGCategory.{v} C] [DGCategory.{v} D]
  [Category.{vX} X] [Category.{vY} Y]

/-- The ordinary functor obtained by passing a dg functor to `H⁰` and changing
source and target along supplied category equivalences. -/
abbrev transportedH0 (F : DGFunctor C D) (eC : H0 C ≌ X)
    (eD : H0 D ≌ Y) : X ⥤ Y :=
  (eC.inverse ⋙ F.h0) ⋙ eD.functor

/-- Equivalence of `F.h0` makes its ordinary transport an equivalence. -/
theorem transportedH0_isEquivalence (F : DGFunctor C D)
    (eC : H0 C ≌ X) (eD : H0 D ≌ Y) (hF : F.h0.IsEquivalence) :
    (F.transportedH0 eC eD).IsEquivalence := by
  letI : F.h0.IsEquivalence := hF
  infer_instance

/-- The ordinary equivalence obtained by transporting an equivalence `F.h0`
through the supplied endpoint equivalences. -/
noncomputable def transportedH0Equivalence (F : DGFunctor C D)
    (eC : H0 C ≌ X) (eD : H0 D ≌ Y) (hF : F.h0.IsEquivalence) : X ≌ Y := by
  letI : F.h0.IsEquivalence := hF
  exact (eC.symm.trans F.h0.asEquivalence).trans eD

section Shift

variable [IsPretriangulated C] [IsPretriangulated D]
  [HasShift X ℤ] [HasShift Y ℤ]
  {eC : H0 C ≌ X} {eD : H0 D ≌ Y}
  [eC.functor.CommShift ℤ] [eD.functor.CommShift ℤ]

/-- The coherent shift comparison on the ordinary transport of `H⁰ F`.

The source inverse comparison is Mathlib's mate of the supplied forward
comparison.  The remaining structure is inherited by functor composition. -/
@[reducible]
noncomputable def transportedH0CommShift (F : DGFunctor C D) :
    (F.transportedH0 eC eD).CommShift ℤ := by
  letI : eC.inverse.CommShift ℤ := eC.commShiftInverse ℤ
  letI : F.h0.CommShift ℤ := F.h0CommShift
  infer_instance

section Exact

variable [Limits.HasZeroObject X] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [Limits.HasZeroObject Y] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eC.functor.IsTriangulated] [eD.functor.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary transport of every dg functor between pretriangulated dg
categories is triangulated when the endpoint equivalences are triangulated. -/
theorem transportedH0IsTriangulated (F : DGFunctor C D) :
    letI : (F.transportedH0 eC eD).CommShift ℤ :=
      F.transportedH0CommShift
    (F.transportedH0 eC eD).IsTriangulated := by
  letI : eC.inverse.CommShift ℤ := eC.commShiftInverse ℤ
  letI : eC.CommShift ℤ := eC.commShift_of_functor ℤ
  letI : eC.IsTriangulated :=
    Equivalence.IsTriangulated.mk' eC inferInstance
  letI : F.h0.CommShift ℤ := F.h0CommShift
  letI : F.h0.IsTriangulated := F.h0IsTriangulated
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The transported equivalence is a triangulated equivalence under the same
endpoint hypotheses.  Its inverse comparison and exactness are Mathlib's
canonical mates of the forward package. -/
theorem transportedH0EquivalenceIsTriangulated (F : DGFunctor C D)
    (hF : F.h0.IsEquivalence) :
    letI : (F.transportedH0Equivalence eC eD hF).functor.CommShift ℤ :=
      F.transportedH0CommShift
    letI : (F.transportedH0Equivalence eC eD hF).inverse.CommShift ℤ :=
      (F.transportedH0Equivalence eC eD hF).commShiftInverse ℤ
    letI : (F.transportedH0Equivalence eC eD hF).CommShift ℤ :=
      (F.transportedH0Equivalence eC eD hF).commShift_of_functor ℤ
    (F.transportedH0Equivalence eC eD hF).IsTriangulated := by
  letI : (F.transportedH0Equivalence eC eD hF).functor.CommShift ℤ :=
    F.transportedH0CommShift
  letI : (F.transportedH0Equivalence eC eD hF).inverse.CommShift ℤ :=
    (F.transportedH0Equivalence eC eD hF).commShiftInverse ℤ
  letI : (F.transportedH0Equivalence eC eD hF).CommShift ℤ :=
    (F.transportedH0Equivalence eC eD hF).commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ F.transportedH0IsTriangulated

end Exact

end Shift


end DGFunctor

end CategoryTheory
