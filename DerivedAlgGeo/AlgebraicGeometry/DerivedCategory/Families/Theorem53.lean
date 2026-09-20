/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndFilteredColimits

/-!
# Formal boundaries for Theorem 5.3

This module records the reusable categorical part of Theorem 5.3 of
arXiv:1902.08184v4 without pretending that the scheme-level base-change
theorems are present in the repository.  The existing
`IndExtensionData` is the only t-structure/Ind carrier.  The bridge module
proves its restriction consequences and takes filtered-colimit preservation as
the explicit Lemma 5.1 owner input.

The remaining clauses are represented by source-shaped owner data:
`RangeDescentData` is the bounded-interval form of (5.1)/(5.2), and
`RightTExactData`/`TExactData` are the formal tensor and (4a)--(4d) inputs.
Their constructors do not assert that a geometric pullback, descent square, or
tensor has the required property.  They only make a supplied comparison
available to the formal composition theorems below.
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

/-! ### Lemma 5.1 and the affine bridge -/

/-- The base datum consumed by the formal part of Lemma 5.1 and Theorem 5.3.

This is intentionally only a wrapper around the existing bridge package: it
does not define an alternative Ind extension or a second large t-structure. -/
structure BaseData
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C) : Prop where
  extension : IndExtensionFilteredColimitData.{w, v} P small large

namespace BaseData

variable {P : ObjectProperty C} [P.IsTriangulated]
  {small : TStructure P.FullSubcategory} {large : TStructure C}

/-- The inclusion part of Lemma 5.1 is proved from the existing Ind extension,
not stored as an additional t-exactness hypothesis. -/
theorem inclusion_isTExact
    (H : BaseData.{w, v} P small large) :
    P.ι.IsTExact small large :=
  H.extension.inclusion_isTExact

/-- The filtered-colimit part of Lemma 5.1 is exposed at the exact mathlib
`PreservesColimit` boundary supplied by the owner. -/
theorem truncation_preserves
    (H : BaseData.{w, v} P small large)
    {J : Type w} [Category.{v} J] [IsFiltered J]
    (K : J ⥤ C) (n : ℤ) :
    PreservesColimit K (large.truncLE n) ∧
      PreservesColimit K (large.truncGE n) :=
  H.extension.truncation_preserves K n

/-- The existing coproduct-and-extension aisle comparison is the affine
closure formula consumed by later base-change code. -/
theorem affineAisle
    (H : BaseData.{w, v} P small large) :
    large.le 0 =
      (boundedAisle P small).coprodClosure.{w} :=
  H.extension.aisle_eq_coprodClosure

end BaseData

/-! ### (5.1)/(5.2): bounded-interval descent owner data -/

/-- Membership in the bounded interval `[a,b]` of a t-structure. -/
def inRange (t : TStructure C) (X : C) (a b : ℤ) : Prop :=
  t.IsGE X a ∧ t.IsLE X b

/-- A family of local restrictions together with the exact bounded-interval
descent formula required by (5.1) or (5.2).

The index type and target categories are parameters so a geometry owner can
instantiate this with flat affine tests or with the affine members of an fpqc
cover.  The formula is an actual iff over the chosen t-structures, not a
proposition-valued placeholder with no comparison functors. -/
structure RangeDescentData
    (t : TStructure C)
    (I : Type w') (D : I → Type u')
    [∀ i, Category.{v'} (D i)]
    [∀ i, HasZeroObject (D i)] [∀ i, HasShift (D i) ℤ]
    [∀ i, Preadditive (D i)]
    [∀ (i) (n : ℤ), (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (D i)] where
  /-- Pullback/restriction to the local test. -/
  restriction : ∀ i, C ⥤ D i
  /-- The chosen local t-structure. -/
  localTStructure : ∀ i, TStructure (D i)
  /-- The bounded-interval descent formula. -/
  range_iff : ∀ (X : C) (a b : ℤ),
    inRange t X a b ↔
      ∀ i, inRange (localTStructure i) ((restriction i).obj X) a b

namespace RangeDescentData

variable {t : TStructure C}
  {I : Type w'} {D : I → Type u'}
  [∀ i, Category.{v'} (D i)]
  [∀ i, HasZeroObject (D i)] [∀ i, HasShift (D i) ℤ]
  [∀ i, Preadditive (D i)]
  [∀ (i) (n : ℤ), (shiftFunctor (D i) n).Additive]
  [∀ i, Pretriangulated (D i)]

/-- The supplied local formula in the orientation used by (5.1)/(5.2). -/
theorem inRange_iff
    (H : RangeDescentData t I D)
    (X : C) (a b : ℤ) :
    inRange t X a b ↔
      ∀ i, inRange (H.localTStructure i) ((H.restriction i).obj X) a b :=
  H.range_iff X a b

end RangeDescentData

/-! ### (3), (4a)--(4d): exactness owner data -/

/-- A supplied right t-exactness comparison, used for the tensor clause (3).
The functor is data, while its right t-exactness is the explicit geometric
input at the operation owner. -/
structure RightTExactData
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (t : TStructure C) (t' : TStructure D) where
  /-- The operation whose right t-exactness is supplied by `rightTExact`. -/
  functor : C ⥤ D
  rightTExact : functor.IsRightTExact t t'

namespace RightTExactData

variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {t : TStructure C} {t' : TStructure D}

/-- Tensoring preserves the coconnective half whenever the owner supplied the
right t-exactness comparison. -/
  theorem isLE_map
    (H : RightTExactData t t') (X : C) (n : ℤ) [t.IsLE X n] :
    t'.IsLE (H.functor.obj X) n := by
  letI : H.functor.IsRightTExact t t' := H.rightTExact
  exact Functor.isLE_map_of_isRightTExact (F := H.functor) (t := t) (t' := t') X n

end RightTExactData

/-- A supplied t-exactness comparison.  This is the reusable shape for each
of Theorem 5.3(4a)--(4d); the four clauses can use different categories and
functors by instantiating this type four times. -/
structure TExactData
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (t : TStructure C) (t' : TStructure D) where
  /-- The operation for which both t-exactness directions are supplied below. -/
  functor : C ⥤ D
  rightTExact : functor.IsRightTExact t t'
  leftTExact : functor.IsLeftTExact t t'

namespace TExactData

variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {t : TStructure C} {t' : TStructure D}

/-- Assemble the two supplied halves into the repository's t-exactness
class.  This is formal class composition, not a geometric exactness proof. -/
theorem isTExact (H : TExactData t t') :
    H.functor.IsTExact t t' := by
  letI : H.functor.IsRightTExact t t' := H.rightTExact
  letI : H.functor.IsLeftTExact t t' := H.leftTExact
  exact Functor.isTExact_of

/-- The supplied t-exact comparison transports coconnective membership. -/
theorem isLE_map
    (H : TExactData t t') (X : C) (n : ℤ) [t.IsLE X n] :
    t'.IsLE (H.functor.obj X) n := by
  letI : H.functor.IsTExact t t' := H.isTExact
  exact Functor.isLE_map_of_isRightTExact (F := H.functor) (t := t) (t' := t') X n

/-- The supplied t-exact comparison also transports connective membership. -/
theorem isGE_map
    (H : TExactData t t') (X : C) (n : ℤ) [t.IsGE X n] :
    t'.IsGE (H.functor.obj X) n := by
  letI : H.functor.IsTExact t t' := H.isTExact
  exact Functor.isGE_map_of_isLeftTExact (F := H.functor) (t := t) (t' := t') X n

end TExactData

/-! ### (5.3)/(5.4): local comparison owner boundary -/

/-- A comparison of two candidate t-structures through their bounded-range
membership.  The source-locality/finiteness argument that produces this iff is
geometric; once supplied, the comparison is available in a source-shaped,
degree-indexed form. -/
structure LocalComparisonData (t₁ t₂ : TStructure C) where
  range_iff : ∀ (X : C) (a b : ℤ),
    inRange t₁ X a b ↔ inRange t₂ X a b

namespace LocalComparisonData

variable {t₁ t₂ : TStructure C}

/-- Project the supplied bounded-range comparison. -/
theorem inRange_iff
    (H : LocalComparisonData t₁ t₂) (X : C) (a b : ℤ) :
    inRange t₁ X a b ↔ inRange t₂ X a b :=
  H.range_iff X a b

end LocalComparisonData

end Theorem53

end AlgebraicGeometry.DerivedCategory.Families
