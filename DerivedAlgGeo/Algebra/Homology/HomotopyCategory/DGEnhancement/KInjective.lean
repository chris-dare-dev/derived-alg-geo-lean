/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import DerivedAlgGeo.Algebra.Homology.DGCategory.FullSubcategory.Pretriangulated
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.Pretriangulated

/-!
# `D^dg A`: the K-injective model of the derived dg enhancement

`dg-enhancements-e8`, part three. `Ddg A` is the full dg subcategory of
`C^dg A` on the K-injective complexes. It is the first consumer of
`DGFullSubcategory`; `KProjective.lean` is the second.

## Nothing here constructs a resolution

The whole point of building on Mathlib's `CochainComplex.IsKInjective` is that
this file consumes resolution theory rather than restating it. Concretely, the
three closure conditions of `DGFullSubcategory.isPretriangulated` are
discharged as follows, and not one of them is an assumption:

| condition | discharged by |
|---|---|
| `ContainsZeroObject` | a zero complex receives only the zero map |
| `ClosedUnderShift` | Mathlib's instance `(L⟦n⟧).IsKInjective` |
| `ClosedUnderCone` | `isKInjective_mappingCone`, below |

The shift row is exact rather than approximate: `Cdg.shiftObj K n` is *defined*
as `(of A K)⟦n⟧`, so Mathlib's instance is about the very object the dg shift
witness names. The same holds for cones, where `Cdg.coneObj f hf` is
`mappingCone (coneHom f hf)`.

## The one thing Mathlib does not already have

Mathlib proves that K-injectives are the right orthogonal of the acyclic
complexes (`isKInjective_iff_rightOrthogonal`) and that a right orthogonal of a
triangulated subcategory is triangulated, but it never puts the two together to
say that a mapping cone of a map between K-injectives is K-injective.
`isKInjective_mappingCone` does exactly that and nothing more: move both
hypotheses across the orthogonality characterisation, apply
`ext_of_isTriangulatedClosed₃` to the cone's distinguished triangle in the
homotopy category, and move back.

That it is a triangulated-subcategory argument rather than a homotopy
construction is the reason it is three lines. A direct proof -- given an
acyclic `K` and a map into the cone, split it and patch the two homotopies --
would be a page, and would be reproving `IsTriangulatedClosed₃`.

## Inhabitation

`isKInjective_of_injective` is Mathlib's supply of objects: a complex that is
strictly bounded below and injective in every degree is K-injective. `ofGE`
packages one as an object of `Ddg A`, so the model is not vacuous under a
hypothesis this repository invented.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex CategoryTheory.Limits

namespace Cdg

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **A mapping cone of a map between K-injective complexes is K-injective.**

Both hypotheses and the conclusion are moved across
`isKInjective_iff_rightOrthogonal`; in between, the statement is that the right
orthogonal of the acyclic complexes is closed under the third vertex of a
distinguished triangle, which is Mathlib's
`ObjectProperty.ext_of_isTriangulatedClosed₃`. -/
lemma isKInjective_mappingCone {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [K.IsKInjective] [L.IsKInjective] :
    (mappingCone φ).IsKInjective := by
  have hK : (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal
      ((HomotopyCategory.quotient _ _).obj K) := IsKInjective.rightOrthogonal K
  have hL : (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal
      ((HomotopyCategory.quotient _ _).obj L) := IsKInjective.rightOrthogonal L
  rw [isKInjective_iff_rightOrthogonal]
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ) hK hL

/-- The K-injective objects of `C^dg A`, as a predicate on its objects.

Named rather than written inline, because it is the parameter of `Ddg` and
every closure lemma below is a statement about it. -/
def IsKInjectiveObj (K : Cdg A) : Prop := (of A K).IsKInjective

/-- `IsKInjectiveObj` is Mathlib's `IsKInjective`, read through `Cdg.of`. -/
lemma isKInjectiveObj_iff (K : Cdg A) :
    IsKInjectiveObj K ↔ (of A K).IsKInjective := Iff.rfl

variable (A) in
/-- **`D^dg A`**: the derived dg enhancement on the K-injective model, as the
full dg subcategory of `C^dg A` on the K-injective complexes. -/
def Ddg : Type max u v := DGFullSubcategory (IsKInjectiveObj (A := A))

namespace Ddg

/-- `D^dg A` is a dg category, by `DGFullSubcategory`. No axiom is reproved
here; see that file on why every one of them is the ambient one applied. -/
instance instDGCategoryDdg : DGCategory.{v} (Ddg A) :=
  inferInstanceAs (DGCategory.{v} (DGFullSubcategory (IsKInjectiveObj (A := A))))

/-- A K-injective complex, as an object of `D^dg A`. -/
def mk (K : Cdg A) (hK : IsKInjectiveObj K) : Ddg A :=
  DGFullSubcategory.mk (P := IsKInjectiveObj (A := A)) K hK

/-- A strictly bounded-below complex of injectives is an object of `D^dg A`.
This is the model's non-vacuity, and it rests on Mathlib's
`isKInjective_of_injective` rather than on any hypothesis stated here. -/
def ofGE (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyGE d]
    [∀ n : ℤ, Injective (K.X n)] : Ddg A :=
  mk (K : Cdg A) (isKInjective_of_injective K d)

end Ddg

/-! ### The three closure conditions

Each is a statement about `IsKInjectiveObj` alone, checkable here, and each is
discharged by Mathlib. -/

/-- `IsKInjectiveObj` holds of a zero complex: every map into a zero object is
the zero map, which is homotopic to zero by `Homotopy.ofEq`. -/
lemma containsZeroObject_isKInjectiveObj [HasZeroObject A] :
    DGFullSubcategory.ContainsZeroObject (IsKInjectiveObj (A := A)) := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := CochainComplex A ℤ)
  refine ⟨(Z : Cdg A), ⟨fun {_} f _ => ⟨Homotopy.ofEq (hZ.eq_of_tgt f 0)⟩⟩, ?_⟩
  show Cochain.ofHom (𝟙 Z) = 0
  simp [hZ.eq_of_src (𝟙 Z) 0]

/-- `IsKInjectiveObj` is closed under shifts. The shift witness `Cdg.isShiftBy`
names `Cdg.shiftObj K n`, which is `(of A K)⟦n⟧` definitionally, so Mathlib's
shift instance applies to it directly. -/
lemma closedUnderShift_isKInjectiveObj :
    DGFullSubcategory.ClosedUnderShift (IsKInjectiveObj (A := A)) := by
  intro K hK n
  haveI : (of A K).IsKInjective := hK
  exact ⟨shiftObj K n, inferInstanceAs (((of A K)⟦n⟧).IsKInjective),
    ⟨isShiftBy K n⟩⟩

/-- `IsKInjectiveObj` is closed under cones. The cone witness `Cdg.isConeOf`
names `Cdg.coneObj f hf`, which is `mappingCone (coneHom f hf)`, so this is
`isKInjective_mappingCone`. -/
lemma closedUnderCone_isKInjectiveObj :
    DGFullSubcategory.ClosedUnderCone (IsKInjectiveObj (A := A)) := by
  intro K L hK hL f hf
  haveI : (of A K).IsKInjective := hK
  haveI : (of A L).IsKInjective := hL
  exact ⟨coneObj f hf, isKInjective_mappingCone (coneHom f hf), ⟨isConeOf f hf⟩⟩

/-- **`D^dg A` is pretriangulated.** Every input is a closure property of
K-injectivity discharged above; the representability of shifts and cones is
inherited from `C^dg A` by restriction. -/
instance instIsPretriangulatedDdg [HasZeroObject A] :
    IsPretriangulated.{v} (Ddg A) :=
  DGFullSubcategory.isPretriangulated containsZeroObject_isKInjectiveObj
    closedUnderShift_isKInjectiveObj closedUnderCone_isKInjectiveObj

end Cdg

end CategoryTheory
