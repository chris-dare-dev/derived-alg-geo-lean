/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndExtension
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The Ind extension and filtered-colimit truncations

Lemma 5.1 of arXiv:1902.08184v4 uses the Ind presentation of the large
quasi-coherent category, while the repository's reusable categorical output is
`TStructure.IndExtensionData`: its degree-zero aisle is the coproduct-and-
extension closure of the small aisle and its restriction formulas hold in
every degree.

This file is the bridge between those presentations.  It deliberately does
not introduce another Ind category or another t-structure carrier.  The only
additional input is the filtered-colimit preservation statement for the
already chosen truncation functors.  The inclusion t-exactness and the aisle
comparison are obtained from `IndExtensionData` itself.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-! ### The filtered-colimit half of Lemma 5.1 -/

/-- The filtered-colimit preservation obligation for the truncation functors
of an already chosen large t-structure.

This is an owner input for the Ind/filtered-colimit theorem.  It is stated
with mathlib's actual `PreservesColimit` predicate rather than a proposition
named "filtered colimits commute", so callers must provide the diagrams and
the relevant colimit instances at their geometry owner. -/
structure FilteredColimitTruncationData (large : TStructure C) : Prop where
  /-- The coconnective truncation preserves the chosen filtered colimits. -/
  truncLE_preserves :
    ∀ {J : Type w} [Category.{v} J] [IsFiltered J]
      (K : J ⥤ C) (n : ℤ),
      PreservesColimit K (large.truncLE n)
  /-- The connective truncation preserves the chosen filtered colimits. -/
  truncGE_preserves :
    ∀ {J : Type w} [Category.{v} J] [IsFiltered J]
      (K : J ⥤ C) (n : ℤ),
      PreservesColimit K (large.truncGE n)

namespace FilteredColimitTruncationData

variable {large : TStructure C}

/-- Project the owner-supplied filtered-colimit preservation for `truncLE`. -/
theorem preserves_truncLE
    (H : FilteredColimitTruncationData.{w, v} large)
    {J : Type w} [Category.{v} J] [IsFiltered J]
    (K : J ⥤ C) (n : ℤ) :
    PreservesColimit K (large.truncLE n) :=
  H.truncLE_preserves K n

/-- Project the owner-supplied filtered-colimit preservation for `truncGE`. -/
theorem preserves_truncGE
    (H : FilteredColimitTruncationData.{w, v} large)
    {J : Type w} [Category.{v} J] [IsFiltered J]
    (K : J ⥤ C) (n : ℤ) :
    PreservesColimit K (large.truncGE n) :=
  H.truncGE_preserves K n

end FilteredColimitTruncationData

/-! ### One bridge package, with the existing Ind carrier -/

/-- The formal bridge used by the Lemma 5.1/Theorem 5.3 adapters.

`indExtension` is the sole t-structure carrier.  This record merely pairs it
with the filtered-colimit preservation owner input; it does not define a
second Ind extension, a second aisle, or a parallel truncation hierarchy. -/
structure IndExtensionFilteredColimitData
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C) : Prop where
  indExtension : IndExtensionData.{w} P small large
  truncation : FilteredColimitTruncationData.{w, v} large

namespace IndExtensionFilteredColimitData

variable {P : ObjectProperty C} [P.IsTriangulated]
  {small : TStructure P.FullSubcategory} {large : TStructure C}

/-- Lemma 5.1's truncation conclusion at the chosen filtered-colimit size. -/
theorem truncation_preserves
    (H : IndExtensionFilteredColimitData.{w, v} P small large)
    {J : Type w} [Category.{v} J] [IsFiltered J]
    (K : J ⥤ C) (n : ℤ) :
    PreservesColimit K (large.truncLE n) ∧
      PreservesColimit K (large.truncGE n) :=
  ⟨H.truncation.preserves_truncLE K n,
    H.truncation.preserves_truncGE K n⟩

/-- The inclusion t-exactness in Lemma 5.1 is the proved consequence of the
existing Ind-extension restriction formulas. -/
theorem inclusion_isTExact
    (H : IndExtensionFilteredColimitData.{w, v} P small large) :
    P.ι.IsTExact small large :=
  H.indExtension.inclusion_isTExact P small large

/-- The chosen form of the existing one-functor restriction. -/
def restriction
    (H : IndExtensionFilteredColimitData.{w, v} P small large) :
    small.Restriction P.ι :=
  H.indExtension.restriction P small large

/-- The Ind extension's aisle comparison, exposed at the bridge boundary. -/
theorem aisle_eq_coprodClosure
    (H : IndExtensionFilteredColimitData.{w, v} P small large) :
    large.le 0 = (boundedAisle P small).coprodClosure.{w} :=
  H.indExtension.largeAisle

end IndExtensionFilteredColimitData

end CategoryTheory.Triangulated.TStructure
