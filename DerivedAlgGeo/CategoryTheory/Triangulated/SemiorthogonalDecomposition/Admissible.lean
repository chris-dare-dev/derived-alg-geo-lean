/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Orientation
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.Data.Fin.VecNotation

/-!
# Admissible triangulated object properties

An object property is right (respectively left) admissible when the inclusion of its full
subcategory has a right (respectively left) adjoint.  Completing the counit (respectively unit)
of that adjunction gives the two orthogonal decomposition triangles.

For a right-admissible `P`, the third vertex of the counit triangle is the object usually called
the **left mutation** of `X` through `P`.  This file deliberately records the triangle and not a
mutation object or functor.  Cones are not functorial in a bare triangulated category, so a
mutation functor needs an enhancement (the dg-enhancement lane, issues #853--#855).  The familiar
formula for mutation through an exceptional object additionally needs finite-dimensional Hom
spaces, which are outside the present coherent-sheaf linearity interface (issue #332).

No theorem here claims that an arbitrary triangulated object property is admissible, or that an
operation on object properties preserves admissibility.  Admissibility remains an explicit
hypothesis in every decomposition theorem.

The two-block construction feeds the classically ordered family
`⟨P.rightOrthogonal, P⟩` to
`SemiorthogonalSequence.ofReverseFin`.  Thus its root-facing components are `P` followed by
`P.rightOrthogonal`: the root vanishes Hom from earlier to later, while the literature reads a
semiorthogonal decomposition in the reverse direction.  `Orientation.lean` is the single source
of truth for that convention.
-/

open CategoryTheory
open scoped ZeroObject

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]
variable [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The object property of being a zero object. -/
abbrev zeroObjects : ObjectProperty C := fun X ↦ Limits.IsZero X

/-- The top object property is triangulated. -/
instance topIsTriangulated : (⊤ : ObjectProperty C).IsTriangulated where
  toContainsZero := inferInstance
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := .mk' (by simp)

/-- Being a zero object is invariant under isomorphism. -/
instance zeroObjectsIsClosedUnderIsomorphisms :
    (zeroObjects (C := C)).IsClosedUnderIsomorphisms where
  of_iso e hX := hX.of_iso e.symm

/-- Zero objects form a triangulated object property. -/
instance zeroObjectsIsTriangulated :
    (zeroObjects (C := C)).IsTriangulated where
  toContainsZero := inferInstance
  toIsStableUnderShift :=
    ⟨fun n ↦ ⟨fun _ hX ↦ Functor.map_isZero (shiftFunctor C n) hX⟩⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    T.isZero₂_of_isZero₁₃ hT h₁ h₃)

/-- A triangulated object property is right admissible when its inclusion has a right adjoint. -/
def IsRightAdmissible (P : ObjectProperty C) [P.IsTriangulated] : Prop :=
  ∃ G : C ⥤ P.FullSubcategory, Nonempty (P.ι ⊣ G)

/-- A triangulated object property is left admissible when its inclusion has a left adjoint. -/
def IsLeftAdmissible (P : ObjectProperty C) [P.IsTriangulated] : Prop :=
  ∃ L : C ⥤ P.FullSubcategory, Nonempty (L ⊣ P.ι)

/-- A triangulated object property is admissible when it is both left and right admissible. -/
def IsAdmissible (P : ObjectProperty C) [P.IsTriangulated] : Prop :=
  P.IsLeftAdmissible ∧ P.IsRightAdmissible

/-- The top object property is right admissible, through its canonical equivalence with `C`. -/
theorem top_isRightAdmissible :
    IsRightAdmissible (⊤ : ObjectProperty C) :=
  ⟨(ObjectProperty.topEquivalence C).inverse,
    ⟨(ObjectProperty.topEquivalence C).toAdjunction⟩⟩

/-- The top object property is left admissible, through its canonical equivalence with `C`. -/
theorem top_isLeftAdmissible :
    IsLeftAdmissible (⊤ : ObjectProperty C) :=
  ⟨(ObjectProperty.topEquivalence C).symm.functor,
    ⟨(ObjectProperty.topEquivalence C).symm.toAdjunction⟩⟩

private noncomputable def zeroSubcategoryObject :
    (zeroObjects (C := C)).FullSubcategory :=
  ⟨0, Limits.isZero_zero C⟩

private noncomputable def zeroProjection :
    C ⥤ (zeroObjects (C := C)).FullSubcategory :=
  (Functor.const C).obj zeroSubcategoryObject

private noncomputable def homFromZeroEquiv
    (X : (zeroObjects (C := C)).FullSubcategory) (Y : C) :
    ((zeroObjects (C := C)).ι.obj X ⟶ Y) ≃ (X ⟶ zeroSubcategoryObject) where
  toFun _ := homMk 0
  invFun _ := 0
  left_inv f := X.property.eq_of_src _ _
  right_inv f := by
    apply hom_ext
    exact X.property.eq_of_src _ _

private noncomputable def homToZeroEquiv
    (X : C) (Y : (zeroObjects (C := C)).FullSubcategory) :
    (zeroSubcategoryObject ⟶ Y) ≃ (X ⟶ (zeroObjects (C := C)).ι.obj Y) where
  toFun _ := 0
  invFun _ := homMk 0
  left_inv f := by
    apply hom_ext
    exact Y.property.eq_of_tgt _ _
  right_inv f := Y.property.eq_of_tgt _ _

private noncomputable def zeroRightAdjunction :
    (zeroObjects (C := C)).ι ⊣ zeroProjection :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homFromZeroEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        exact X'.property.eq_of_src _ _
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply hom_ext
        exact X.property.eq_of_src _ _ }

private noncomputable def zeroLeftAdjunction :
    zeroProjection ⊣ (zeroObjects (C := C)).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homToZeroEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply hom_ext
        exact Y.property.eq_of_tgt _ _
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact Y'.property.eq_of_tgt _ _ }

/-- Zero objects are right admissible: the right adjoint is the constant zero functor. -/
theorem zeroObjects_isRightAdmissible :
    IsRightAdmissible (zeroObjects (C := C)) :=
  ⟨zeroProjection, ⟨zeroRightAdjunction⟩⟩

/-- Zero objects are left admissible: the left adjoint is the constant zero functor. -/
theorem zeroObjects_isLeftAdmissible :
    IsLeftAdmissible (zeroObjects (C := C)) :=
  ⟨zeroProjection, ⟨zeroLeftAdjunction⟩⟩

/-- The counit triangle of a right-admissible property has its third vertex in the right
orthogonal.  The right adjoint is triangulated because it is adjoint to the triangulated
inclusion; after applying it, full faithfulness makes the mapped counit an isomorphism, hence its
cone a zero object. -/
theorem IsRightAdmissible.exists_distTriang_mem_rightOrthogonal
    {P : ObjectProperty C} [P.IsTriangulated] (hP : P.IsRightAdmissible) (X : C) :
    P.extensionProduct P.rightOrthogonal X := by
  obtain ⟨G, ⟨adj⟩⟩ := hP
  letI : P.ι.Full := P.fullyFaithfulι.full
  letI : P.ι.Faithful := P.fullyFaithfulι.faithful
  letI : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  letI := adj.rightAdjointCommShift ℤ
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  letI : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  obtain ⟨Z, g, h, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle (adj.counit.app X)
  refine ⟨P.ι.obj (G.obj X), Z, adj.counit.app X, g, h, hT,
    (G.obj X).property, ?_⟩
  set_option backward.isDefEq.respectTransparency false in
    haveI : IsIso (G.map (adj.counit.app X)) := by infer_instance
  have hGZ : Limits.IsZero (G.obj Z) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (G.mapTriangle.obj (Pretriangulated.Triangle.mk _ _ _))
      (G.map_distinguished _ hT) (by
        change IsIso (G.map (adj.counit.app X))
        infer_instance)
  intro Y f hY
  let Y' : P.FullSubcategory := ⟨Y, hY⟩
  apply (adj.homEquiv Y' Z).injective
  exact hGZ.eq_of_tgt _ _

/-- The unit triangle of a left-admissible property has its first vertex in the left orthogonal. -/
theorem IsLeftAdmissible.exists_distTriang_mem_leftOrthogonal
    {P : ObjectProperty C} [P.IsTriangulated] (hP : P.IsLeftAdmissible) (X : C) :
    P.leftOrthogonal.extensionProduct P X := by
  obtain ⟨L, ⟨adj⟩⟩ := hP
  letI : P.ι.Full := P.fullyFaithfulι.full
  letI : P.ι.Faithful := P.fullyFaithfulι.faithful
  letI := adj.leftAdjointCommShift ℤ
  letI : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  letI : L.IsTriangulated := adj.isTriangulated_leftAdjoint
  obtain ⟨W, f, h, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle₁ (adj.unit.app X)
  refine ⟨W, P.ι.obj (L.obj X), f, adj.unit.app X, h, hT, ?_,
    (L.obj X).property⟩
  set_option backward.isDefEq.respectTransparency false in
    haveI : IsIso (L.map (adj.unit.app X)) := by infer_instance
  have hLW : Limits.IsZero (L.obj W) :=
    Pretriangulated.Triangle.isZero₁_of_isIso₂
      (L.mapTriangle.obj (Pretriangulated.Triangle.mk _ _ _))
      (L.map_distinguished _ hT) (by
        change IsIso (L.map (adj.unit.app X))
        infer_instance)
  intro Y g hY
  let Y' : P.FullSubcategory := ⟨Y, hY⟩
  apply (adj.homEquiv W Y').symm.injective
  exact hLW.eq_of_src _ _

/-- Right admissibility is equivalently consumed as the equality saying that every object is an
extension of an object of `P` by an object of `P.rightOrthogonal`. -/
theorem IsRightAdmissible.extensionProduct_rightOrthogonal_eq_top
    {P : ObjectProperty C} [P.IsTriangulated] (hP : P.IsRightAdmissible) :
    P.extensionProduct P.rightOrthogonal = ⊤ := by
  rw [eq_top_iff]
  exact fun X _ ↦ hP.exists_distTriang_mem_rightOrthogonal X

/-- The dual extension-product form of left admissibility. -/
theorem IsLeftAdmissible.leftOrthogonal_extensionProduct_eq_top
    {P : ObjectProperty C} [P.IsTriangulated] (hP : P.IsLeftAdmissible) :
    P.leftOrthogonal.extensionProduct P = ⊤ := by
  rw [eq_top_iff]
  exact fun X _ ↦ hP.exists_distTriang_mem_leftOrthogonal X

omit [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The right orthogonal of all objects is precisely the zero-object property. -/
@[simp]
theorem top_rightOrthogonal :
    (⊤ : ObjectProperty C).rightOrthogonal = zeroObjects := by
  ext X
  constructor
  · intro hX
    change Limits.IsZero X
    rw [Limits.IsZero.iff_id_eq_zero]
    exact hX (CategoryStruct.id X) trivial
  · intro hX Y f _
    exact hX.eq_of_tgt f 0

omit [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Every object is right orthogonal to the zero objects. -/
@[simp]
theorem zeroObjects_rightOrthogonal :
    (zeroObjects (C := C)).rightOrthogonal = ⊤ := by
  ext X
  constructor
  · intro _
    trivial
  · intro _ Y f hY
    exact hY.eq_of_src f 0

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated.SemiorthogonalSequence

open ObjectProperty

variable {C : Type u} [Category.{v} C]
variable [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The root-facing two-block sequence attached to a right-admissible `P`.

It is constructed by passing the classically ordered family `![P.rightOrthogonal, P]` to
`ofReverseFin`; consequently component `0` is `P` and component `1` is `P.rightOrthogonal`.
See `Orientation.lean` for the convention reversal. -/
def twoBlock (P : ObjectProperty C) [P.IsTriangulated] (_hP : P.IsRightAdmissible) :
    SemiorthogonalSequence C (Fin 2) :=
  ofReverseFin 2 ![P.rightOrthogonal, P] (by
    intro i j hij
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 1 := Fin.ext (by omega)
    subst i
    subst j
    simp)

@[simp]
theorem twoBlock_component_zero (P : ObjectProperty C) [P.IsTriangulated]
    (hP : P.IsRightAdmissible) :
    (twoBlock P hP).component 0 = P := by
  simp [twoBlock]

@[simp]
theorem twoBlock_component_one (P : ObjectProperty C) [P.IsTriangulated]
    (hP : P.IsRightAdmissible) :
    (twoBlock P hP).component 1 = P.rightOrthogonal := by
  simp [twoBlock]

/-- The two blocks are triangulated object properties. -/
theorem twoBlock_hasTriangulatedComponents (P : ObjectProperty C) [P.IsTriangulated]
    (hP : P.IsRightAdmissible) :
    (twoBlock P hP).HasTriangulatedComponents := by
  intro i
  by_cases hi : i = 0
  · subst i
    change P.IsTriangulated
    infer_instance
  · have hi' : i = 1 := Fin.ext (by omega)
    subst i
    change P.rightOrthogonal.IsTriangulated
    infer_instance

/-- A right-admissible two-block sequence is strongly full with the explicit bound `1`.
`triangEnvelopeIter 0` already closes under shifts, binary products and retracts; the counit
triangle contributes the single extension counted by `triangEnvelopeIter_succ`. -/
theorem twoBlock_isStronglyFull (P : ObjectProperty C) [P.IsTriangulated]
    (hP : P.IsRightAdmissible) :
    (twoBlock P hP).IsStronglyFull := by
  refine ⟨1, ?_⟩
  rw [eq_top_iff]
  rintro X -
  obtain ⟨A, Z, f, g, h, hT, hA, hZ⟩ :=
    hP.exists_distTriang_mem_rightOrthogonal X
  have hAtotal : (twoBlock P hP).total A :=
    (twoBlock P hP).component_le_total 0 A (by simpa using hA)
  have hZtotal : (twoBlock P hP).total Z :=
    (twoBlock P hP).component_le_total 1 Z (by simpa using hZ)
  rw [ObjectProperty.triangEnvelopeIter_succ]
  apply ObjectProperty.le_retractClosure
  exact ⟨A, Z, f, g, h, hT,
    (by simpa only [ObjectProperty.triangEnvelopeIter_zero] using
      ((twoBlock P hP).total.le_triangEnvelopeIter 0 A hAtotal)),
    (twoBlock P hP).total.le_triangEnvelopeIter 0 Z hZtotal⟩

/-- For `P = ⊤`, the two blocks are all objects followed by the zero objects. -/
@[simp]
theorem twoBlock_top_component (i : Fin 2) :
    (twoBlock (⊤ : ObjectProperty C) ObjectProperty.top_isRightAdmissible).component i =
      if i = 0 then ⊤ else ObjectProperty.zeroObjects := by
  fin_cases i <;> simp

/-- For the zero-object property, the two blocks are zero objects followed by all objects. -/
@[simp]
theorem twoBlock_zeroObjects_component (i : Fin 2) :
    (twoBlock (ObjectProperty.zeroObjects (C := C))
      ObjectProperty.zeroObjects_isRightAdmissible).component i =
        if i = 0 then ObjectProperty.zeroObjects else ⊤ := by
  fin_cases i <;> simp

end CategoryTheory.Triangulated.SemiorthogonalSequence
