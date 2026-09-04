/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of colimits through composition

This file records preservation results that only concern functor composition.
No adjunction is involved.
-/

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {L : C ⥤ D} (F : D ⥤ E) {K : Type*} [Category K]

/-- If `L` and `L ⋙ F` both preserve the colimit of `d`, then `F` preserves the colimit of
`d ⋙ L`. -/
lemma preservesColimit_comp_left (d : K ⥤ C) [HasColimit d] [PreservesColimit d L]
    [PreservesColimit d (L ⋙ F)] : PreservesColimit (d ⋙ L) F := by
  refine preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves L (colimit.isColimit d)) ?_
  exact isColimitOfPreserves (L ⋙ F) (colimit.isColimit d)

end CategoryTheory.Limits
