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

This file records the additional filtered-colimit owner predicate for the
already chosen truncation functors.  It deliberately does not introduce
another Ind category or another t-structure carrier: the inclusion
t-exactness and aisle comparison remain consequences of `IndExtensionData`.
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

This is an owner predicate, not a carrier for an Ind extension.  It keeps the
actual mathlib `PreservesColimit` obligations visible at the geometry owner:
for every filtered diagram and every degree, both truncation functors must
preserve that diagram's colimit.  The canonical `IndExtensionData` remains
the sole owner of the Ind-extension and t-structure consequences. -/
def PreservesFilteredColimitTruncations (large : TStructure C) : Prop :=
  ∀ {J : Type w} [Category.{v} J] [IsFiltered J]
    (K : J ⥤ C) (n : ℤ),
    PreservesColimit K (large.truncLE n) ∧
      PreservesColimit K (large.truncGE n)

end CategoryTheory.Triangulated.TStructure
