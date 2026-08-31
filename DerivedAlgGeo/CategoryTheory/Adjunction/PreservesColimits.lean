/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Transporting preservation of colimits across a reflective adjunction

This file records two generic tools for proving that a functor out of a
reflective target preserves colimits. They mention no sites or sheaves; the
module-sheaf forgetful functor is one consumer.
-/

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [IsIso adj.counit] (F : D ⥤ E)
  {K : Type*} [Category K]

/-- If `L` and `L ⋙ F` both preserve the colimit of `d`, then `F` preserves the colimit of
`d ⋙ L`. No adjunction is involved: `L.mapCocone` of a colimit cocone is a colimit cocone
of `d ⋙ L`, and `F` sends it to one because `L ⋙ F` preserves the original. -/
lemma preservesColimit_comp_left (d : K ⥤ C) [HasColimit d] [PreservesColimit d L]
    [PreservesColimit d (L ⋙ F)] : PreservesColimit (d ⋙ L) F := by
  refine preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves L (colimit.isColimit d)) ?_
  exact isColimitOfPreserves (L ⋙ F) (colimit.isColimit d)

include adj in
/-- **Transport along a reflector.** If the counit of `L ⊣ G` is invertible — so `D` is a
reflective target of `L` — then a functor `F` out of `D` preserves colimits of shape `K` as
soon as `L` and `L ⋙ F` do.

Every `d : K ⥤ D` is isomorphic to `(d ⋙ G) ⋙ L`, and the previous lemma applies to
`d ⋙ G`. -/
lemma preservesColimitsOfShape_of_comp_left [HasColimitsOfShape K C]
    [PreservesColimitsOfShape K L] [PreservesColimitsOfShape K (L ⋙ F)] :
    PreservesColimitsOfShape K F where
  preservesColimit {d} := by
    have e : (d ⋙ G) ⋙ L ≅ d :=
      (d.associator G L).symm ≪≫ Functor.isoWhiskerLeft d (asIso adj.counit) ≪≫ d.rightUnitor
    have : PreservesColimit ((d ⋙ G) ⋙ L) F := preservesColimit_comp_left F (d ⋙ G)
    exact preservesColimit_of_iso_diagram F e

end CategoryTheory.Adjunction
