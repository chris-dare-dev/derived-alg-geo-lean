/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Projection
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Strong semiorthogonal decompositions and compatible functors

This file records the vocabulary of Definitions 3.3, 3.5, and 3.7 of
arXiv:1902.08184 without adding any geometric existence claim.

Here **strong** has the paper's meaning: every component is right admissible.
It is deliberately distinct from `SemiorthogonalSequence.IsStronglyFull`,
which says that the components generate after uniformly many extensions.

A compatible functor carries each source component into the component with
the same index. Chosen component projections are kept as data, separately
from proposition-valued admissibility, and their underlying ambient
endofunctors can be assigned a cohomological amplitude relative to a
t-structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v₁ u₁ v₂ u₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A functor has cohomological amplitude `[a, b]` if it sends every
t-cohomological window `[p, q]` into the target window `[p + a, q + b]`.
This is Definition 3.7 of arXiv:1902.08184. -/
def HasCohomologicalAmplitude (F : C ⥤ D) (t : TStructure C)
    (t' : TStructure D) (a b : ℤ) : Prop :=
  ∀ (p q : ℤ) (X : C), t.IsGE X p → t.IsLE X q →
    t'.IsGE (F.obj X) (p + a) ∧ t'.IsLE (F.obj X) (q + b)

/-- A t-exact functor has cohomological amplitude `[0, 0]`. -/
theorem hasCohomologicalAmplitude_zero (F : C ⥤ D) (t : TStructure C)
    (t' : TStructure D) [F.IsTExact t t'] :
    F.HasCohomologicalAmplitude t t' 0 0 := by
  intro p q X hGE hLE
  letI : t.IsGE X p := hGE
  letI : t.IsLE X q := hLE
  exact ⟨by
      simpa using
        (isGE_map_of_isLeftTExact (F := F) (t := t) (t' := t') X p),
    by
      simpa using
        (isLE_map_of_isRightTExact (F := F) (t := t) (t' := t') X q)⟩

/-- An amplitude interval can be enlarged on either side. -/
theorem HasCohomologicalAmplitude.weaken {F : C ⥤ D}
    {t : TStructure C} {t' : TStructure D} {a b a' b' : ℤ}
    (hF : F.HasCohomologicalAmplitude t t' a b)
    (ha : a' ≤ a) (hb : b ≤ b') :
    F.HasCohomologicalAmplitude t t' a' b' := by
  intro p q X hGE hLE
  obtain ⟨hGE', hLE'⟩ := hF p q X hGE hLE
  letI : t'.IsGE (F.obj X) (p + a) := hGE'
  letI : t'.IsLE (F.obj X) (q + b) := hLE'
  exact ⟨t'.isGE_of_ge (F.obj X) (p + a') (p + a) (by omega),
    t'.isLE_of_le (F.obj X) (q + b) (q + b') (by omega)⟩

end CategoryTheory.Functor

namespace CategoryTheory.Triangulated.SemiorthogonalSequence

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
  {ι : Type w} [Preorder ι]

variable (S : SemiorthogonalSequence C ι)

/-- A functor is compatible with two semiorthogonal sequences when it maps
the component at every index into the component with the same index. This is
Definition 3.3 of arXiv:1902.08184. -/
def CompatibleWith (F : C ⥤ D) (T : SemiorthogonalSequence D ι) : Prop :=
  ∀ i, S.component i ≤ (T.component i).inverseImage F

/-- The identity functor is compatible with a sequence. -/
theorem compatibleWith_id : S.CompatibleWith (𝟭 C) S :=
  fun _ _ hX ↦ hX

/-- Compatibility is closed under composition. -/
theorem CompatibleWith.comp
    {E : Type*} [Category E] [HasZeroMorphisms E]
    {T : SemiorthogonalSequence D ι} {U : SemiorthogonalSequence E ι}
    {F : C ⥤ D} {G : D ⥤ E}
    (hF : S.CompatibleWith F T) (hG : T.CompatibleWith G U) :
    S.CompatibleWith (F ⋙ G) U :=
  fun i X hX ↦ hG i (F.obj X) (hF i X hX)

section Strong

variable [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- A strong semiorthogonal sequence in the sense of Definition 3.5 of
arXiv:1902.08184: every component is right admissible. -/
def IsStrong : Prop :=
  ∀ i, (S.component i).IsRightAdmissible

/-- Strongness supplies triangulated closure of every component. -/
theorem IsStrong.hasTriangulatedComponents (hS : S.IsStrong) :
    S.HasTriangulatedComponents :=
  fun i ↦ (hS i).1

/-- A simultaneous choice of right-adjoint projections for all components of
a semiorthogonal sequence. -/
structure RightProjectionData where
  /-- The chosen right projection onto the component at `i`. -/
  componentProjection (i : ι) :
    ObjectProperty.RightProjectionData (S.component i)

namespace RightProjectionData

variable {S} (Q : S.RightProjectionData)

/-- The ambient endofunctor projecting onto component `i`. -/
abbrev ambientProjection (i : ι) : C ⥤ C :=
  (Q.componentProjection i).ambientProjection

/-- All component projections have the specified cohomological amplitude. -/
def HasCohomologicalAmplitude (t : TStructure C) (a b : ℤ) : Prop :=
  ∀ i, (Q.ambientProjection i).HasCohomologicalAmplitude t t a b

end RightProjectionData

/-- Choose projection data for every component of a strong sequence. -/
noncomputable def IsStrong.rightProjectionData (hS : S.IsStrong) :
    S.RightProjectionData where
  componentProjection i :=
    ObjectProperty.RightProjectionData.ofIsRightAdmissible (hS i)

end Strong

end CategoryTheory.Triangulated.SemiorthogonalSequence
