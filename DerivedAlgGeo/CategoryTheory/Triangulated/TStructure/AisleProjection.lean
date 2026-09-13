/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Projection
import DerivedAlgGeo.CategoryTheory.Preadditive.CompactObject
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Right projections onto t-structure aisles

The nonpositive truncation of a t-structure is the canonical right adjoint to
the inclusion of its aisle. Mathlib constructs the ambient truncation functor
and proves its universal mapping property; this file packages that property
as the chosen right projection used by the semiorthogonal-decomposition API.

The ambient projector is naturally isomorphic to `truncLE`. Consequently any
coproduct-preservation theorem for truncation transfers directly to the
chosen projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u w

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  (t : TStructure C)

instance aisleInclusionIsLE (n : ℤ) (X : (t.le n).FullSubcategory) :
    t.IsLE ((t.le n).ι.obj X) n :=
  ⟨X.property⟩

/-- The truncation functor with its codomain restricted to the aisle. -/
def aisleProjection (n : ℤ) : C ⥤ (t.le n).FullSubcategory where
  obj X := ⟨(t.truncLE n).obj X, (inferInstance : t.IsLE _ n).le⟩
  map f := ObjectProperty.homMk ((t.truncLE n).map f)
  map_id X := ObjectProperty.hom_ext _ (by simp)
  map_comp f g := ObjectProperty.hom_ext _ (by simp)

@[simp]
theorem aisleProjection_obj_obj (n : ℤ) (X : C) :
    ((t.aisleProjection n).obj X).obj = (t.truncLE n).obj X :=
  rfl

@[simp]
theorem aisleProjection_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((t.aisleProjection n).map f).hom = (t.truncLE n).map f :=
  rfl

/-- The universal Hom equivalence for the aisle truncation. -/
def aisleProjectionHomEquiv (n : ℤ)
    (X : (t.le n).FullSubcategory) (Y : C) :
    ((t.le n).ι.obj X ⟶ Y) ≃ (X ⟶ (t.aisleProjection n).obj Y) where
  toFun f := by
    letI : t.IsLE ((t.le n).ι.obj X) n := ⟨X.property⟩
    exact ObjectProperty.homMk (t.liftTruncLE f n)
  invFun f := f.hom ≫ (t.truncLEι n).app Y
  left_inv f := by
    letI hXι : t.IsLE ((t.le n).ι.obj X) n := ⟨X.property⟩
    letI hX : t.IsLE X.obj n := ⟨X.property⟩
    exact t.liftTruncLE_ι f n
  right_inv f := by
    letI hXι : t.IsLE ((t.le n).ι.obj X) n := ⟨X.property⟩
    letI hX : t.IsLE X.obj n := ⟨X.property⟩
    apply ObjectProperty.hom_ext
    apply t.to_truncLE_obj_ext
    exact t.liftTruncLE_ι (f.hom ≫ (t.truncLEι n).app Y) n

@[simp]
theorem aisleProjectionHomEquiv_apply (n : ℤ)
    (X : (t.le n).FullSubcategory) (Y : C) (f : (t.le n).ι.obj X ⟶ Y) :
    t.aisleProjectionHomEquiv n X Y f =
      ObjectProperty.homMk (t.liftTruncLE f n) := by
  letI : t.IsLE ((t.le n).ι.obj X) n := ⟨X.property⟩
  rfl

@[simp]
theorem aisleProjectionHomEquiv_symm_apply (n : ℤ)
    (X : (t.le n).FullSubcategory) (Y : C)
    (f : X ⟶ (t.aisleProjection n).obj Y) :
    (t.aisleProjectionHomEquiv n X Y).symm f =
      f.hom ≫ (t.truncLEι n).app Y :=
  rfl

/-- The inclusion of a t-structure aisle is left adjoint to truncation into
that aisle. -/
def aisleProjectionAdjunction (n : ℤ) :
    (t.le n).ι ⊣ t.aisleProjection n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := t.aisleProjectionHomEquiv n
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        rw [aisleProjectionHomEquiv_symm_apply,
          aisleProjectionHomEquiv_symm_apply]
        change (f.hom ≫ g.hom) ≫ (t.truncLEι n).app Y =
          f.hom ≫ g.hom ≫ (t.truncLEι n).app Y
        simp only [Category.assoc]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        letI hXι : t.IsLE ((t.le n).ι.obj X) n := ⟨X.property⟩
        letI hX : t.IsLE X.obj n := ⟨X.property⟩
        rw [aisleProjectionHomEquiv_apply, aisleProjectionHomEquiv_apply]
        apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom]
        change t.liftTruncLE (f ≫ g) n =
          t.liftTruncLE f n ≫ (t.truncLE n).map g
        apply t.to_truncLE_obj_ext
        rw [t.liftTruncLE_ι]
        rw [Category.assoc, (t.truncLEι n).naturality g]
        rw [← Category.assoc, t.liftTruncLE_ι]
        simp }

/-- The canonical chosen right projection onto an aisle. -/
def aisleRightProjectionData (n : ℤ) :
    ObjectProperty.RightProjectionData (t.le n) where
  projection := t.aisleProjection n
  adjunction := t.aisleProjectionAdjunction n

/-- The ambient endofunctor of the aisle projection is naturally isomorphic
to the ordinary truncation functor. -/
def aisleRightProjectionDataAmbientIso (n : ℤ) :
    (t.aisleRightProjectionData n).ambientProjection ≅ t.truncLE n :=
  Iso.refl _

/-- Coproduct preservation of truncation transfers to the ambient aisle
projector. -/
theorem aisleRightProjectionData_preservesSmallCoproducts (n : ℤ)
    (h : (t.truncLE n).PreservesSmallCoproducts.{w}) :
    (t.aisleRightProjectionData n).ambientProjection.PreservesSmallCoproducts.{w} :=
  fun κ ↦ by
    letI : PreservesColimitsOfShape (Discrete κ) (t.truncLE n) := h κ
    exact preservesColimitsOfShape_of_natIso
      (t.aisleRightProjectionDataAmbientIso n).symm

/-- An aisle which is also triangulated is right admissible. The extra
triangulatedness does not hold for an arbitrary t-structure aisle, but does
hold when the aisle is a coproduct closure of a triangulated property. -/
theorem le_isRightAdmissible (n : ℤ) (h : (t.le n).IsTriangulated) :
    (t.le n).IsRightAdmissible :=
  (t.aisleRightProjectionData n).isRightAdmissible h

end CategoryTheory.Triangulated.TStructure
