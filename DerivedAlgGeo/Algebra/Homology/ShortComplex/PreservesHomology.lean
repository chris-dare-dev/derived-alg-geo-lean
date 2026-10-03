/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The homology quotient under a preserving functor

The canonical left-homology quotient commutes with the comparison iso for a
functor preserving the chosen left homology data.

## Main definitions

No new carrier is introduced; this module extends Mathlib's `CategoryTheory.ShortComplex`.

## Main results

* `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom` identifies the two
  paths from mapped cycles to the image of homology.
* `CategoryTheory.ShortComplex.leftHomologyπ_mapLeftHomologyIso_hom` gives the
  left-homology statement with weaker existence hypotheses.

## Implementation notes

Both statements follow from the pinned left-homology data equations, and the
full homology statement uses the canonical homology comparison.

## References

Mathlib's `ShortComplex/PreservesHomology.lean` at pin
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

short complex, homology, preserving functor
-/

namespace CategoryTheory.ShortComplex

open CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable (T : ShortComplex C)
  [F.PreservesLeftHomologyOf T]

set_option backward.defeqAttrib.useBackward true in
/-- The left-homology quotient commutes with a functor preserving this left
homology, without requiring homology of either whole short complex. -/
theorem leftHomologyπ_mapLeftHomologyIso_hom [T.HasLeftHomology] :
    (T.map F).leftHomologyπ ≫ (T.mapLeftHomologyIso F).hom =
      (T.mapCyclesIso F).hom ≫ F.map T.leftHomologyπ := by
  rw [T.leftHomologyData.mapLeftHomologyIso_eq,
    T.leftHomologyData.mapCyclesIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom_assoc]
  simp only [ShortComplex.LeftHomologyData.map_π, ← Functor.map_comp]
  rw [ShortComplex.LeftHomologyData.π_comp_leftHomologyIso_inv]

variable [T.HasHomology] [(T.map F).HasHomology]

set_option backward.defeqAttrib.useBackward true in
/-- The homology quotient agrees with its image under the left-homology
comparison, without requiring homology in any other short complex. -/
theorem homologyπ_mapHomologyIso_hom :
    (T.map F).homologyπ ≫ (T.mapHomologyIso F).hom =
      (T.mapCyclesIso F).hom ≫ F.map T.homologyπ := by
  rw [T.leftHomologyData.mapHomologyIso_eq, T.leftHomologyData.mapCyclesIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  simp only [ShortComplex.LeftHomologyData.map_π, ← Functor.map_comp]
  rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

end
end CategoryTheory.ShortComplex
