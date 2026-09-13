/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Rotate
import DerivedAlgGeo.CategoryTheory.Shift.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionConePresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.FunctorTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor

/-!
# Presenting dg-adjunction cotwist triangles on ordinary categories

The ordinary presentation of a dg adjunction unit gives a pointwise
distinguished family

`𝟭 X ⟶ F G ⟶ transportedUnitCone ⟶ (𝟭 X)⟦1⟧`.

This file applies Mathlib's inverse rotation to obtain the conventional
cotwist triangle

`transportedCotwist ⟶ 𝟭 X ⟶ F G ⟶ transportedCotwist⟦1⟧`,

where `transportedCotwist` is the pointwise `[-1]` shift of the transported
unit cone.  It also compares this ordinary functor with the transport of the
actual shifted dg cone.  The comparison reuses `DGFunctor.shiftedFunctorH0Iso`
and the source equivalence's `CommShift` structure.

The canonical pointwise shift and the generic transported-`H⁰` package also
give an explicit `CommShift` and exactness result.  An ordinary
autoequivalence is packaged only under the supplied hypothesis that the
unshifted cone is an equivalence on `H⁰`.  No dg quasi-equivalence,
Fourier--Mukai comparison, choice independence, or sphericality is inferred.
Distinguishedness remains pointwise; this is not a distinguished triangle in
the functor category.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY uC uD uX uY

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace DGAdjunction

variable {C : Type uC} {D : Type uD} {X : Type uX} {Y : Type uY}
  [DGCategory.{v} C] [DGCategory.{v} D]
  [Category.{vX} X] [Category.{vY} Y]
  {L : DGFunctor C D} {R : DGFunctor D C}
  {eC : H0 C ≌ X} {eD : H0 D ≌ Y}
  {F : X ⥤ Y} {G : Y ⥤ X}
  {A : DGAdjunction L R}

namespace UnitConeData

variable [IsPretriangulated C] (K : A.UnitConeData)

/-- The actual shifted dg unit cone, after passing to `H⁰` and transporting
through the ordinary source equivalence.  No exactness is asserted. -/
noncomputable abbrev transportedDGCotwist (eC : H0 C ≌ X) : X ⥤ X :=
  eC.inverse ⋙ (K.unitCone.shiftedFunctor (-1 : ℤ)).h0 ⋙ eC.functor

variable [HasShift X ℤ]

/-- The conventional ordinary cotwist associated to the transported unit
cone: its pointwise `[-1]` shift. -/
noncomputable abbrev transportedCotwist (eC : H0 C ≌ X) : X ⥤ X :=
  (shiftFunctor (X ⥤ X) (-1 : ℤ)).obj (K.transportedUnitCone eC)

variable [eC.functor.CommShift ℤ]

/-- Transporting the actual shifted dg unit cone agrees naturally with
pointwise shifting the transported unshifted cone. -/
noncomputable def transportedCotwistH0Iso :
    K.transportedDGCotwist eC ≅ K.transportedCotwist eC :=
  DGFunctor.transportedShiftedFunctorH0Iso
    K.unitCone (-1 : ℤ) eC eC

/-- The coherent shift comparison on the pointwise transported cotwist.

This is the composite of the generic transported-`H⁰` comparison and the
canonical comparison on the ordinary shift functor. -/
@[reducible]
noncomputable def transportedCotwistCommShift [Preadditive X]
    [∀ n : ℤ, (shiftFunctor X n).Additive] :
    (K.transportedCotwist eC).CommShift ℤ := by
  letI : (K.unitCone.transportedH0 eC eC).CommShift ℤ :=
    K.unitCone.transportedH0CommShift
  letI : (shiftFunctor X (-1 : ℤ)).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift X (-1 : ℤ)
  change (K.unitCone.transportedH0 eC eC ⋙
    shiftFunctor X (-1 : ℤ)).CommShift ℤ
  infer_instance

omit [IsPretriangulated C] [eC.functor.CommShift ℤ] in
/-- Equivalence of the unshifted unit cone on `H⁰` makes the conventional
transported cotwist an ordinary autoequivalence. -/
theorem transportedCotwist_isEquivalence
    (hK : K.unitCone.h0.IsEquivalence) :
    (K.transportedCotwist eC).IsEquivalence := by
  letI : (K.unitCone.transportedH0 eC eC).IsEquivalence :=
    K.unitCone.transportedH0_isEquivalence eC eC hK
  change (K.unitCone.transportedH0 eC eC ⋙
    shiftFunctor X (-1 : ℤ)).IsEquivalence
  infer_instance

/-- The ordinary autoequivalence presented by the conventional transported
cotwist, under an explicit equivalence hypothesis on the unshifted cone. -/
noncomputable def transportedCotwistEquivalence
    (hK : K.unitCone.h0.IsEquivalence) : X ≌ X :=
  (K.unitCone.transportedH0Equivalence eC eC hK).trans
    (shiftEquiv X (-1 : ℤ))

section Exact

variable [Limits.HasZeroObject X] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eC.functor.IsTriangulated]

set_option backward.isDefEq.respectTransparency false in
/-- The conventional transported cotwist is triangulated.  Exactness of the
shifted cone is unconditional in the cone choice; the ordinary comparison
equivalence must be supplied as triangulated. -/
theorem transportedCotwistIsTriangulated :
    letI : (K.transportedCotwist eC).CommShift ℤ :=
      K.transportedCotwistCommShift (eC := eC)
    (K.transportedCotwist eC).IsTriangulated := by
  letI : (K.unitCone.transportedH0 eC eC).CommShift ℤ :=
    K.unitCone.transportedH0CommShift
  letI : (K.unitCone.transportedH0 eC eC).IsTriangulated :=
    K.unitCone.transportedH0IsTriangulated
  letI : (shiftFunctor X (-1 : ℤ)).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift X (-1 : ℤ)
  letI : (shiftFunctor X (-1 : ℤ)).IsTriangulated :=
    Pretriangulated.shiftFunctorIsTriangulated X (-1 : ℤ)
  change (K.unitCone.transportedH0 eC eC ⋙
    shiftFunctor X (-1 : ℤ)).IsTriangulated
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Under the explicit equivalence hypothesis, the transported cotwist
equivalence carries Mathlib's canonical triangulated-equivalence package. -/
theorem transportedCotwistEquivalenceIsTriangulated
    (hK : K.unitCone.h0.IsEquivalence) :
    letI : (K.transportedCotwistEquivalence (eC := eC) hK).functor.CommShift ℤ :=
      K.transportedCotwistCommShift (eC := eC)
    letI : (K.transportedCotwistEquivalence (eC := eC) hK).inverse.CommShift ℤ :=
      (K.transportedCotwistEquivalence (eC := eC) hK).commShiftInverse ℤ
    letI : (K.transportedCotwistEquivalence (eC := eC) hK).CommShift ℤ :=
      (K.transportedCotwistEquivalence (eC := eC) hK).commShift_of_functor ℤ
    (K.transportedCotwistEquivalence (eC := eC) hK).IsTriangulated := by
  letI : (K.transportedCotwistEquivalence (eC := eC) hK).functor.CommShift ℤ :=
    K.transportedCotwistCommShift (eC := eC)
  letI : (K.transportedCotwistEquivalence (eC := eC) hK).inverse.CommShift ℤ :=
    (K.transportedCotwistEquivalence (eC := eC) hK).commShiftInverse ℤ
  letI : (K.transportedCotwistEquivalence (eC := eC) hK).CommShift ℤ :=
    (K.transportedCotwistEquivalence (eC := eC) hK).commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _
    (K.transportedCotwistIsTriangulated (eC := eC))

end Exact

end UnitConeData

namespace H0Presentation

variable [IsPretriangulated C] [HasShift X ℤ] [Preadditive X]
  [eC.functor.CommShift ℤ]
  (P : H0Presentation (L := L) (R := R) eC eD F G)
  (K : A.UnitConeData)

/-- The inverse rotation of the presented unshifted unit triangle:
`transportedCotwist ⟶ 𝟭 X ⟶ F G ⟶ transportedCotwist⟦1⟧`.

Mathlib's `invRotate` owns the sign and the shift cancellation map. -/
noncomputable def presentedCotwistTriangle : X ⥤ Triangle X :=
  P.presentedUnitTriangle K ⋙ invRotate X

/-- The first projection is strictly the pointwise-shifted transported unit
cone. -/
theorem presentedCotwistTriangle_comp_π₁ :
    P.presentedCotwistTriangle K ⋙ Triangle.π₁ =
      K.transportedCotwist eC :=
  rfl

/-- The second projection is strictly the identity functor. -/
theorem presentedCotwistTriangle_comp_π₂ :
    P.presentedCotwistTriangle K ⋙ Triangle.π₂ = 𝟭 X :=
  rfl

/-- The third projection is strictly the presented adjunction composite. -/
theorem presentedCotwistTriangle_comp_π₃ :
    P.presentedCotwistTriangle K ⋙ Triangle.π₃ = F ⋙ G :=
  rfl

@[simp]
theorem presentedCotwistTriangle_obj₁ (Z : X) :
    ((P.presentedCotwistTriangle K).obj Z).obj₁ =
      (K.transportedCotwist eC).obj Z :=
  rfl

@[simp]
theorem presentedCotwistTriangle_obj₂ (Z : X) :
    ((P.presentedCotwistTriangle K).obj Z).obj₂ = Z :=
  rfl

@[simp]
theorem presentedCotwistTriangle_obj₃ (Z : X) :
    ((P.presentedCotwistTriangle K).obj Z).obj₃ = (F ⋙ G).obj Z :=
  rfl

@[simp]
theorem presentedCotwistTriangle_mor₂ (Z : X) :
    ((P.presentedCotwistTriangle K).obj Z).mor₂ =
      (P.toAdjunction A).unit.app Z :=
  rfl

/-- At the natural-transformation level, inverse rotation moves the
adjunction unit into the second map. -/
theorem presentedCotwistTriangle_unit :
    Functor.whiskerLeft (P.presentedCotwistTriangle K)
        Triangle.π₂Toπ₃ = (P.toAdjunction A).unit :=
  rfl

section Distinguished

variable [Limits.HasZeroObject X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eC.functor.IsTriangulated]

/-- Every value of the conventional transported cotwist triangle is
distinguished. -/
theorem presentedCotwistTriangle_obj_distinguished (Z : X) :
    (P.presentedCotwistTriangle K).obj Z ∈ distTriang X :=
  inv_rot_of_distTriang _ (P.presentedUnitTriangle_obj_distinguished K Z)

end Distinguished

end H0Presentation

end DGAdjunction

end CategoryTheory
