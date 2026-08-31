/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Limits.Preserves.Composition
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Preservation of colimits on reflective targets

This file applies the generic composition result to an ordinary adjunction of
functors whose counit is invertible. The theorem remains in Mathlib's
`CategoryTheory.Adjunction` namespace because it extends that structure, while
its physical owner is limit-preservation theory.
-/

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [IsIso adj.counit] (F : D ⥤ E)
  {K : Type*} [Category K]

include adj in
/-- **Transport along a reflector.** If the counit of `L ⊣ G` is invertible — so `D` is a
reflective target of `L` — then a functor `F` out of `D` preserves colimits of shape `K` as
soon as `L` and `L ⋙ F` do.

Every `d : K ⥤ D` is isomorphic to `(d ⋙ G) ⋙ L`, and
`Limits.preservesColimit_comp_left` applies to `d ⋙ G`. -/
lemma preservesColimitsOfShape_of_comp_left [HasColimitsOfShape K C]
    [PreservesColimitsOfShape K L] [PreservesColimitsOfShape K (L ⋙ F)] :
    PreservesColimitsOfShape K F where
  preservesColimit {d} := by
    have e : (d ⋙ G) ⋙ L ≅ d :=
      (d.associator G L).symm ≪≫ Functor.isoWhiskerLeft d (asIso adj.counit) ≪≫ d.rightUnitor
    have : PreservesColimit ((d ⋙ G) ⋙ L) F :=
      Limits.preservesColimit_comp_left F (d ⋙ G)
    exact preservesColimit_of_iso_diagram F e

end CategoryTheory.Adjunction
