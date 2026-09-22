/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndFilteredColimits

/-!
# Formal owner boundaries for Theorem 5.3

This module records the reusable categorical consequences of Theorem 5.3 of
arXiv:1902.08184v4 without claiming the scheme-level base-change theorems.

## Main definitions

* `inRange` packages the lower- and upper-truncation conditions used by the
  bounded-range formulas.
* `PreservesFilteredColimitTruncations` is owned by the categorical
  t-structure module; its `PreservesColimit` binders remain direct owner
  inputs.

## Main results

* `inclusion_isTExact` and `aisle_eq_coprodClosure` reuse the canonical
  `IndExtensionData` consequences.
* The exactness transport lemmas expose one-sided and two-sided hypotheses
  separately, so a caller cannot accidentally strengthen (4a) or (4b).
* `inRange_iff_of_components` and
  `local_inRange_iff_of_components` compose explicit lower- and
  upper-truncation comparison formulas; they do not package a geometric
  descent theorem as a carrier.

## Implementation notes

Theorem 5.3(3), the flat/fpqc formulas, and (5.3)--(5.4) are geometric owner
boundaries in this repository. The functor, local t-structure, comparison
formula, finite-amplitude, and S-locality hypotheses must be supplied by the
owning geometry layer. This file only composes those inputs with the canonical
t-structure API.

## References

* BLMNPS, arXiv:1902.08184v4, Lemma 5.1 and Theorem 5.3.

## Tags

`Theorem53`, `base-change`, `t-structure`, `filtered-colimit`, `owner-boundary`
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u w' v' u'

namespace AlgebraicGeometry.DerivedCategory.Families

namespace Theorem53

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

open CategoryTheory.Triangulated.TStructure

/-! ### Lemma 5.1: reuse the canonical Ind-extension -/

/-- The inclusion t-exactness consequence already proved by `IndExtensionData`.

The extension data is the theorem output for the categorical layer; no second
bridge carrier is needed to expose this consequence at the family owner. -/
theorem inclusion_isTExact
    {P : ObjectProperty C} [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (extension : IndExtensionData.{w} P small large) :
    P.ι.IsTExact small large :=
  extension.inclusion_isTExact P small large

/-- The coproduct-and-extension aisle comparison supplied by the Ind extension. -/
theorem aisle_eq_coprodClosure
    {P : ObjectProperty C} [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (extension : IndExtensionData.{w} P small large) :
    large.le 0 = (boundedAisle P small).coprodClosure.{w} :=
  extension.largeAisle

/-! ### (5.1)/(5.2): bounded-range owner formulas -/

/-- Membership in the inclusive bounded interval `[a,b]` of a t-structure. -/
def inRange (t : TStructure C) (X : C) (a b : ℤ) : Prop :=
  t.IsGE X a ∧ t.IsLE X b

/-- Compose source-shaped lower- and upper-truncation descent formulas.

The restriction functors and local t-structures are explicit arguments. The
two component formulas are the external flat/fpqc owner theorems, not fields
hidden inside a new descent carrier. -/
theorem inRange_iff_of_components
    {t : TStructure C}
    {I : Type w'} {D : I → Type u'}
    [∀ i, Category.{v'} (D i)]
    [∀ i, HasZeroObject (D i)] [∀ i, HasShift (D i) ℤ]
    [∀ i, Preadditive (D i)]
    [∀ (i) (n : ℤ), (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (D i)]
    (restriction : ∀ i, C ⥤ D i)
    (localTStructure : ∀ i, TStructure (D i))
    (isGE_iff : ∀ (X : C) (a : ℤ),
      t.IsGE X a ↔
        ∀ i, (localTStructure i).IsGE ((restriction i).obj X) a)
    (isLE_iff : ∀ (X : C) (b : ℤ),
      t.IsLE X b ↔
        ∀ i, (localTStructure i).IsLE ((restriction i).obj X) b)
    (X : C) (a b : ℤ) :
    inRange t X a b ↔
      ∀ i, inRange (localTStructure i) ((restriction i).obj X) a b := by
  constructor
  · rintro ⟨hGE, hLE⟩ i
    exact ⟨(isGE_iff X a).1 hGE i, (isLE_iff X b).1 hLE i⟩
  · intro h
    refine ⟨(isGE_iff X a).2 (fun i => (h i).1), ?_⟩
    exact (isLE_iff X b).2 (fun i => (h i).2)

/-! ### (3), (4a)--(4d): exactness owner boundaries -/

/-- Transport coconnective membership from an explicit right t-exact functor.

Instantiate `F` with the actual tensor/projection operation at its geometry
owner; the categorical layer does not pretend that an arbitrary functor is
the tensor operation from Theorem 5.3(3). -/
theorem rightTExact_isLE_map
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {t : TStructure C} {t' : TStructure D}
    (F : C ⥤ D) (hF : F.IsRightTExact t t') (X : C) (n : ℤ)
    [t.IsLE X n] :
    t'.IsLE (F.obj X) n := by
  letI : F.IsRightTExact t t' := hF
  exact Functor.isLE_map_of_isRightTExact (F := F) (t := t) (t' := t') X n

/-- Transport connective membership from an explicit left t-exact functor. -/
theorem leftTExact_isGE_map
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {t : TStructure C} {t' : TStructure D}
    (F : C ⥤ D) (hF : F.IsLeftTExact t t') (X : C) (n : ℤ)
    [t.IsGE X n] :
    t'.IsGE (F.obj X) n := by
  letI : F.IsLeftTExact t t' := hF
  exact Functor.isGE_map_of_isLeftTExact (F := F) (t := t) (t' := t') X n

/-- Transport a bounded-range membership statement from a genuinely t-exact
functor.

This is the shape for clauses whose source statement uses both halves; the
one-sided clauses use `rightTExact_isLE_map` or `leftTExact_isGE_map` instead.
Both conclusions are returned together so the two-sided hypothesis is used
by the formal proof. -/
theorem tExact_isRange_map
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {t : TStructure C} {t' : TStructure D}
    (F : C ⥤ D) (hF : F.IsTExact t t') (X : C) (a b : ℤ)
    [t.IsGE X a] [t.IsLE X b] :
    inRange t' (F.obj X) a b := by
  letI : F.IsTExact t t' := hF
  exact ⟨
    Functor.isGE_map_of_isLeftTExact (F := F) (t := t) (t' := t') X a,
    Functor.isLE_map_of_isRightTExact (F := F) (t := t) (t' := t') X b⟩

/-! ### (5.3)/(5.4): local comparison owner boundary -/

/-- Compose separate lower- and upper-truncation comparison formulas.

The finite-amplitude, S-locality, and local pushforward arguments that produce
the two formulas remain explicit at the geometry owner.  In particular, the
caller can instantiate the comparison formulas with the affine-local maps
from (5.3)--(5.4), while this theorem performs only the formal conjunction
composition. -/
theorem local_inRange_iff_of_components
    {t₁ t₂ : TStructure C}
    (isGE_iff : ∀ (X : C) (a : ℤ),
      t₁.IsGE X a ↔ t₂.IsGE X a)
    (isLE_iff : ∀ (X : C) (b : ℤ),
      t₁.IsLE X b ↔ t₂.IsLE X b)
    (X : C) (a b : ℤ) :
    inRange t₁ X a b ↔ inRange t₂ X a b :=
  by
    constructor
    · rintro ⟨hGE, hLE⟩
      exact ⟨(isGE_iff X a).1 hGE, (isLE_iff X b).1 hLE⟩
    · rintro ⟨hGE, hLE⟩
      exact ⟨(isGE_iff X a).2 hGE, (isLE_iff X b).2 hLE⟩

end Theorem53

end AlgebraicGeometry.DerivedCategory.Families
