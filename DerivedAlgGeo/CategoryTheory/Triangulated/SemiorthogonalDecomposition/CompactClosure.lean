/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Orthogonal
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Basic
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Compact generation and semiorthogonality

Compactness propagates Hom-vanishing from the summands of a coproduct to the
coproduct itself. This file combines that fact with the universal property of
`ObjectProperty.coprodClosure` to extend semiorthogonality through coproducts
and extensions on both sides.

The indexing universe is kept explicit. This is the closure step needed for
the perfect-to-quasicoherent passage in Proposition 3.15 of
arXiv:1902.08184.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ObjectProperty

/-- Semiorthogonality of two shift-stable generating properties extends to
their triangulated envelopes. -/
theorem triangEnvelope_le_rightOrthogonal_triangEnvelope
    (P Q : ObjectProperty C) [P.IsStableUnderShift ℤ]
    [Q.IsStableUnderShift ℤ] (h : Q ≤ P.rightOrthogonal) :
    Q.triangEnvelope ≤ P.triangEnvelope.rightOrthogonal := by
  rw [ObjectProperty.triangEnvelope_le_iff]
  have hP : P.triangEnvelope ≤ Q.leftOrthogonal := by
    rw [ObjectProperty.triangEnvelope_le_iff]
    intro X hX Y f hY
    exact h Y hY f hX
  intro Y hY X f hX
  exact hP X hX f hY

/-- Adding all shifts before taking the triangulated envelope does not change
the result. -/
theorem shiftClosure_triangEnvelope_eq (P : ObjectProperty C)
    [P.Nonempty] [IsTriangulated C] :
    (P.shiftClosure ℤ).triangEnvelope = P.triangEnvelope := by
  apply le_antisymm
  · rw [ObjectProperty.triangEnvelope_le_iff]
    rw [ObjectProperty.shiftClosure_le_iff]
    exact P.le_triangEnvelope
  · exact ObjectProperty.monotone_triangEnvelope
      (ObjectProperty.le_shiftClosure P)

end ObjectProperty

namespace IsCompactObject

variable {K : C} (hK : IsCompactObject.{w} K)

include hK

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The right orthogonal to one compact object is closed under coproducts in
the compactness universe. -/
theorem singletonRightOrthogonalIsClosedUnderColimitsOfShape (ι : Type w) :
    (ObjectProperty.singleton K).rightOrthogonal.IsClosedUnderColimitsOfShape
      (Discrete ι) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩ Y f hY
    obtain rfl := (ObjectProperty.singleton_iff K Y).mp hY
    let H := preadditiveCoyoneda.obj (op K)
    letI : PreservesColimitsOfShape (Discrete ι) H := hK ι
    have hZero : IsZero (hX.diag ⋙ H) := by
      apply Functor.isZero
      intro j
      rw [IsZero.iff_id_eq_zero]
      ext g
      change g = 0
      exact hX.prop_diag_obj j g (by simp)
    have hApex : IsZero (H.obj X) := by
      change IsZero ((H.mapCocone hX.cocone).pt)
      exact (isColimitOfPreserves H hX.isColimit).isZero_pt hZero
    have hf := DFunLike.congr_fun
      (congrArg ConcreteCategory.hom
        ((IsZero.iff_id_eq_zero (H.obj X)).1 hApex)) f
    change ConcreteCategory.hom (𝟙 (H.obj X)) f =
      ConcreteCategory.hom (0 : H.obj X ⟶ H.obj X) f
    exact hf

/-- A compact object left-orthogonal to the generators remains
left-orthogonal to their coproduct-and-extension closure. -/
theorem leftOrthogonal_coprodClosure {P : ObjectProperty C}
    (h : P.leftOrthogonal K) : P.coprodClosure.{w}.leftOrthogonal K := by
  letI (ι : Type w) :
      (ObjectProperty.singleton K).rightOrthogonal.IsClosedUnderColimitsOfShape
        (Discrete ι) :=
    singletonRightOrthogonalIsClosedUnderColimitsOfShape (K := K) hK ι
  have hle : P ≤ (ObjectProperty.singleton K).rightOrthogonal := by
    intro Y hY X f hX
    obtain rfl := (ObjectProperty.singleton_iff K X).mp hX
    exact h f hY
  have hclosure :
      P.coprodClosure.{w} ≤ (ObjectProperty.singleton K).rightOrthogonal :=
    P.coprodClosure_le hle
  intro Y f hY
  exact hclosure Y hY f (by simp)

end IsCompactObject

namespace ObjectProperty

/-- If every generator in `P` is compact and `P` is left-orthogonal to `Q`,
then the two coproduct-and-extension closures remain left-orthogonal. -/
theorem coprodClosure_le_leftOrthogonal_coprodClosure
    {P Q : ObjectProperty C}
    (hcompact : P ≤ compactObjects.{w})
    (horth : P ≤ Q.leftOrthogonal) :
    P.coprodClosure.{w} ≤ Q.coprodClosure.{w}.leftOrthogonal := by
  apply P.coprodClosure_le (Q := Q.coprodClosure.{w}.leftOrthogonal)
  intro K hK
  exact IsCompactObject.leftOrthogonal_coprodClosure
    (hcompact K hK) (horth K hK)

/-- Right-orthogonal form of
`coprodClosure_le_leftOrthogonal_coprodClosure`, matching the orientation of
`SemiorthogonalSequence.semiorthogonal`. -/
theorem coprodClosure_le_rightOrthogonal_coprodClosure
    {P Q : ObjectProperty C}
    (hcompact : P ≤ compactObjects.{w})
    (horth : Q ≤ P.rightOrthogonal) :
    Q.coprodClosure.{w} ≤ P.coprodClosure.{w}.rightOrthogonal := by
  have horth' : P ≤ Q.leftOrthogonal := by
    intro X hX Y f hY
    exact horth Y hY f hX
  have hclosure :=
    coprodClosure_le_leftOrthogonal_coprodClosure hcompact horth'
  intro Y hY X f hX
  exact hclosure X hX f hY

end ObjectProperty

end CategoryTheory
