/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Semiorthogonal sequences

This file defines the generic root for semiorthogonal decompositions.  The root is a sequence of
object properties with the expected ordered Hom-vanishing.  Generation, strong generation, and
closure of the components under the triangulated operations are deliberately separate predicates:
none of them is smuggled into the carrier.

The components are object properties rather than new full subcategory structures.  This lets the
root reuse Mathlib's orthogonals and triangulated envelope, and lets geometric realizations add
their own closure and base-change theorems without creating a sibling hierarchy.
-/

open CategoryTheory

universe v u w

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type w} [Preorder ι]

/-- An ordered family of object properties in which maps from an earlier component to a later
component vanish.  Fullness and triangulated closure are independent refinements below. -/
structure SemiorthogonalSequence (C : Type u) [Category.{v} C]
    [Limits.HasZeroMorphisms C] (ι : Type w) [Preorder ι] where
  /-- The component at an index. -/
  component : ι → ObjectProperty C
  /-- Maps from an earlier component to a later component vanish. -/
  semiorthogonal : ∀ ⦃i j : ι⦄, i < j → component j ≤ (component i).rightOrthogonal

namespace SemiorthogonalSequence

variable (S : SemiorthogonalSequence C ι)

/-- The property of lying in one of the components.  This is the common generator property used
by both classical and strong fullness. -/
def total : ObjectProperty C := ⨆ i, S.component i

lemma component_le_total (i : ι) : S.component i ≤ S.total :=
  le_iSup S.component i

lemma hom_eq_zero ⦃i j : ι⦄ (hij : i < j) ⦃X Y : C⦄
    (hX : S.component i X) (hY : S.component j Y) (f : X ⟶ Y) : f = 0 :=
  S.semiorthogonal hij Y hY f hX

/-- Each component is a triangulated object property.  This is independent of fullness. -/
def HasTriangulatedComponents
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ i, (S.component i).IsTriangulated

/-- Classical fullness: the union of the components generates under shifts, binary products,
retracts, and arbitrarily many extensions. -/
def IsFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  S.total.IsClassicalTriangulatedGenerator

/-- Strong fullness: the union of the components generates after a uniformly bounded number of
extensions.  This is stronger than `IsFull`, not a field of the sequence. -/
def IsStronglyFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  S.total.IsStrongTriangulatedGenerator

lemma IsStronglyFull.isFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (hS : S.IsStronglyFull) : S.IsFull :=
  hS.isClassicalTriangulatedGenerator

/-- Transport the components along a functor once orthogonality of their essential images has
been proved in the target.  In particular, a geometric pullback theorem supplies `h`; pullback is
not a field of the semiorthogonal sequence. -/
def map {D : Type*} [Category* D] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    (h : ∀ ⦃i j : ι⦄, i < j →
      (S.component j).map F ≤ ((S.component i).map F).rightOrthogonal) :
    SemiorthogonalSequence D ι where
  component i := (S.component i).map F
  semiorthogonal := h

@[simp]
lemma map_component {D : Type*} [Category* D] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    (h : ∀ ⦃i j : ι⦄, i < j →
      (S.component j).map F ≤ ((S.component i).map F).rightOrthogonal) (i : ι) :
    (S.map F h).component i = (S.component i).map F := rfl

/-- Restrict a semiorthogonal sequence along a strictly monotone map of index types. -/
def reindex {κ : Type*} [Preorder κ] (f : κ → ι)
    (hf : ∀ ⦃i j : κ⦄, i < j → f i < f j) : SemiorthogonalSequence C κ where
  component i := S.component (f i)
  semiorthogonal := by
    intro i j hij
    exact S.semiorthogonal (hf hij)

@[simp]
lemma reindex_component {κ : Type*} [Preorder κ] (f : κ → ι)
    (hf : ∀ ⦃i j : κ⦄, i < j → f i < f j) (i : κ) :
    (reindex S f hf).component i = S.component (f i) := rfl

end SemiorthogonalSequence

end CategoryTheory.Triangulated
