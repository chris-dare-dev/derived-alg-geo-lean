/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Strong

/-!
# Restriction of semiorthogonal sequences

A zero-preserving faithful functor reflects the vanishing that defines a
semiorthogonal sequence. Consequently a sequence on the target restricts to
the inverse-image components on the source. The intended consumer is a fully
faithful inclusion of a bounded or coherent full subcategory.

The second half restricts a chosen right projection along the inclusion of an
object property, provided the ambient projection preserves that property.
This is the precise categorical obligation needed when passing a strong
semiorthogonal decomposition to a bounded subcategory.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ w

namespace CategoryTheory.Triangulated.SemiorthogonalSequence

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
  {ι : Type w} [Preorder ι]

/-- Restrict a semiorthogonal sequence along a faithful functor that preserves
zero morphisms. Each component is pulled back as an object property. -/
def inverseImage (T : SemiorthogonalSequence D ι) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.Faithful] :
    SemiorthogonalSequence C ι where
  component i := (T.component i).inverseImage F
  semiorthogonal := by
    intro i j hij Y hY X f hX
    exact F.map_eq_zero_iff.mp (T.hom_eq_zero hij hX hY (F.map f))

@[simp]
theorem inverseImage_component (T : SemiorthogonalSequence D ι)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] (i : ι) :
    (T.inverseImage F).component i = (T.component i).inverseImage F :=
  rfl

/-- The restricting functor is tautologically compatible with the restricted
and ambient sequences. -/
theorem inverseImage_compatible (T : SemiorthogonalSequence D ι)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] :
    (T.inverseImage F).CompatibleWith F T :=
  fun _ _ hX ↦ hX

end CategoryTheory.Triangulated.SemiorthogonalSequence

namespace CategoryTheory.ObjectProperty.RightProjectionData

variable {C : Type u₁} [Category.{v₁} C]
  {P Q : ObjectProperty C} (R : RightProjectionData Q)

/-- Forget that an object of `P` lies in the inverse image of `Q`, retaining
its `Q`-membership in the ambient category. -/
def inverseImageInclusion :
    (Q.inverseImage P.ι).FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift ((Q.inverseImage P.ι).ι ⋙ P.ι) (fun X ↦ X.property)

/-- The inverse-image inclusion is fully faithful. -/
def inverseImageInclusionFullyFaithful :
    (inverseImageInclusion (P := P) (Q := Q)).FullyFaithful where
  preimage f := homMk (homMk f.hom)

/-- The right projection restricted to `P`, landing in the inverse-image
component inside `P.FullSubcategory`. The preservation hypothesis says that
the projected ambient object still lies in `P`. -/
def restrictedProjection
    (hP : P ≤ P.inverseImage R.ambientProjection) :
    P.FullSubcategory ⥤ (Q.inverseImage P.ι).FullSubcategory where
  obj X :=
    ⟨⟨R.projectObj X.obj, hP X.obj X.property⟩, (R.project X.obj).property⟩
  map f := homMk (homMk (R.projection.map f.hom).hom)
  map_id X := by
    apply hom_ext
    apply hom_ext
    simp
  map_comp f g := by
    apply hom_ext
    apply hom_ext
    simp

/-- A chosen right projection restricts along a full-subcategory inclusion
when its ambient endofunctor preserves the defining object property. -/
def restrict (hP : P ≤ P.inverseImage R.ambientProjection) :
    RightProjectionData (Q.inverseImage P.ι) where
  projection := R.restrictedProjection hP
  adjunction := R.adjunction.restrictFullyFaithful
    (inverseImageInclusionFullyFaithful (P := P) (Q := Q))
    P.fullyFaithfulι
    (Iso.refl _)
    (Iso.refl _)

end CategoryTheory.ObjectProperty.RightProjectionData

namespace CategoryTheory.Triangulated.SemiorthogonalSequence.RightProjectionData

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {ι : Type w} [Preorder ι]
  {S : SemiorthogonalSequence C ι} (Q : S.RightProjectionData)
  (P : ObjectProperty C) [P.IsTriangulated]

/-- All component projections preserve an object property `P`. -/
def Preserves (P : ObjectProperty C) : Prop :=
  ∀ i, P ≤ P.inverseImage (Q.ambientProjection i)

/-- Restrict all chosen component projections to a full subcategory. -/
def restrict (hP : Q.Preserves P) :
    (S.inverseImage P.ι).RightProjectionData where
  componentProjection i := (Q.componentProjection i).restrict (hP i)

/-- Restricting chosen projections proves that the inverse-image sequence is
strong in the paper's sense. Repleteness of the ambient components is needed
to transport their triangulated closure through the inclusion. -/
theorem inverseImage_isStrong (hS : S.HasTriangulatedComponents)
    (hIso : ∀ i, (S.component i).IsClosedUnderIsomorphisms)
    (hP : Q.Preserves P) : (S.inverseImage P.ι).IsStrong := by
  intro i
  letI : (S.component i).IsTriangulated := hS i
  letI : (S.component i).IsClosedUnderIsomorphisms := hIso i
  letI : P.ι.CommShift ℤ := inferInstance
  letI : P.ι.IsTriangulated := inferInstance
  change ((S.component i).inverseImage P.ι).IsRightAdmissible
  exact ((Q.componentProjection i).restrict (hP i)).isRightAdmissible
    (by infer_instance)

end CategoryTheory.Triangulated.SemiorthogonalSequence.RightProjectionData
