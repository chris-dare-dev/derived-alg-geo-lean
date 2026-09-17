/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import DerivedAlgGeo.Algebra.Homology.DGCategory.FullSubcategory.Pretriangulated
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.Pretriangulated

/-!
# The K-projective model, and the second consumer of `DGFullSubcategory`

`dg-enhancements-e8`, part four. `DdgProj A` is the full dg subcategory of
`C^dg A` on the K-projective complexes.

## Why this file exists

`dg-enhancements-e8` asks for a *reusable* full dg subcategory root and for a
second consumer of it, and this is the second consumer. The point is not that
the K-projective model is needed downstream today -- `dg-enhancements-e9` is
stated for the K-injective side -- but that a root with one consumer is
indistinguishable from a one-off. Every line below that is not the predicate
itself is inherited, which is the claim being tested.

## The duality is in Mathlib, not here

Each step is the mirror of `KInjective.lean` with `rightOrthogonal` replaced by
`leftOrthogonal`, and in every case the mirrored lemma is one Mathlib already
has:

| K-injective | K-projective |
|---|---|
| `isKInjective_iff_rightOrthogonal` | `isKProjective_iff_leftOrthogonal` |
| `IsKInjective.rightOrthogonal` | `IsKProjective.leftOrthogonal` |
| `(L⟦n⟧).IsKInjective` | `(K⟦n⟧).IsKProjective` |
| `isKInjective_of_injective` (below) | `isKProjective_of_projective` (above) |

The bound flips with the variance, which is the one asymmetry worth reading
twice: an inhabitant here is `IsStrictlyLE d` with projective terms, not
`IsStrictlyGE d` with injective ones.

`ObjectProperty.ext_of_isTriangulatedClosed₃` is used on the same side in both
files, because the mapping cone is the third vertex either way; it is the
orthogonality that is dualised, not the triangle.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex CategoryTheory.Limits

namespace Cdg

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **A mapping cone of a map between K-projective complexes is K-projective.**
The mirror of `isKInjective_mappingCone`, across `leftOrthogonal`. -/
lemma isKProjective_mappingCone {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [K.IsKProjective] [L.IsKProjective] :
    (mappingCone φ).IsKProjective := by
  have hK : (HomotopyCategory.subcategoryAcyclic A).leftOrthogonal
      ((HomotopyCategory.quotient _ _).obj K) := IsKProjective.leftOrthogonal K
  have hL : (HomotopyCategory.subcategoryAcyclic A).leftOrthogonal
      ((HomotopyCategory.quotient _ _).obj L) := IsKProjective.leftOrthogonal L
  rw [isKProjective_iff_leftOrthogonal]
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ) hK hL

/-- The K-projective objects of `C^dg A`, as a predicate on its objects. -/
def IsKProjectiveObj (K : Cdg A) : Prop := (of A K).IsKProjective

/-- `IsKProjectiveObj` is Mathlib's `IsKProjective`, read through `Cdg.of`. -/
lemma isKProjectiveObj_iff (K : Cdg A) :
    IsKProjectiveObj K ↔ (of A K).IsKProjective := Iff.rfl

variable (A) in
/-- The dg category of K-projective complexes, as the full dg subcategory of
`C^dg A` on them. -/
def DdgProj : Type max u v := DGFullSubcategory (IsKProjectiveObj (A := A))

namespace DdgProj

/-- The K-projective model is a dg category, by `DGFullSubcategory`. -/
instance instDGCategoryDdgProj : DGCategory.{v} (DdgProj A) :=
  inferInstanceAs
    (DGCategory.{v} (DGFullSubcategory (IsKProjectiveObj (A := A))))

/-- A K-projective complex, as an object of the model. -/
def mk (K : Cdg A) (hK : IsKProjectiveObj K) : DdgProj A :=
  DGFullSubcategory.mk (P := IsKProjectiveObj (A := A)) K hK

/-- A strictly bounded-above complex of projectives is an object of the model.
Note the direction: bounded **above** with **projective** terms, dual to
`Ddg.ofGE`. -/
def ofLE (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [∀ n : ℤ, Projective (K.X n)] : DdgProj A :=
  mk (K : Cdg A) (isKProjective_of_projective K d)

end DdgProj

/-! ### The three closure conditions, mirrored -/

/-- `IsKProjectiveObj` holds of a zero complex. -/
lemma containsZeroObject_isKProjectiveObj [HasZeroObject A] :
    DGFullSubcategory.ContainsZeroObject (IsKProjectiveObj (A := A)) := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := CochainComplex A ℤ)
  refine ⟨(Z : Cdg A), ⟨fun {_} f _ => ⟨Homotopy.ofEq (hZ.eq_of_src f 0)⟩⟩, ?_⟩
  show Cochain.ofHom (𝟙 Z) = 0
  simp [hZ.eq_of_src (𝟙 Z) 0]

/-- `IsKProjectiveObj` is closed under shifts. -/
lemma closedUnderShift_isKProjectiveObj :
    DGFullSubcategory.ClosedUnderShift (IsKProjectiveObj (A := A)) := by
  intro K hK n
  haveI : (of A K).IsKProjective := hK
  exact ⟨shiftObj K n, inferInstanceAs (((of A K)⟦n⟧).IsKProjective),
    ⟨isShiftBy K n⟩⟩

/-- `IsKProjectiveObj` is closed under cones. -/
lemma closedUnderCone_isKProjectiveObj :
    DGFullSubcategory.ClosedUnderCone (IsKProjectiveObj (A := A)) := by
  intro K L hK hL f hf
  haveI : (of A K).IsKProjective := hK
  haveI : (of A L).IsKProjective := hL
  exact ⟨coneObj f hf, isKProjective_mappingCone (coneHom f hf), ⟨isConeOf f hf⟩⟩

/-- The K-projective model is pretriangulated, by the same theorem and the same
three inputs as the K-injective one. -/
instance instIsPretriangulatedDdgProj [HasZeroObject A] :
    IsPretriangulated.{v} (DdgProj A) :=
  DGFullSubcategory.isPretriangulated containsZeroObject_isKProjectiveObj
    closedUnderShift_isKProjectiveObj closedUnderCone_isKProjectiveObj

end Cdg

end CategoryTheory
