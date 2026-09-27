/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Naturality of the preserved-colimit comparison

The canonical comparison from a functor applied to a colimit to the colimit of its
image is natural also in the preserving functor. Mathlib's `preservesColimitNatIso`
records naturality in the diagram; this file records the other variable.
-/

namespace CategoryTheory

open Limits

universe w w' v v' u u'

variable {J : Type w} [Category.{w'} J]
  {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] [HasColimitsOfShape J D]
  {H H' : C ⥤ D}
  (α : H ⟶ H') (F : J ⥤ C)

variable [HasColimit F] [PreservesColimit F H] [PreservesColimit F H']

set_option backward.isDefEq.respectTransparency false in
/-- Naturality in the preserving functor complements Mathlib's diagram naturality
for `preservesColimitIso`. Compare both sides on each colimit injection. -/
@[reassoc]
lemma preservesColimitIso_naturality :
    α.app (colimit F) ≫ (preservesColimitIso H' F).hom =
      (preservesColimitIso H F).hom ≫ colim.map (F.whiskerLeft α) := by
  rw [← cancel_epi (preservesColimitIso H F).inv]
  apply colimit.hom_ext
  intro j
  simp only [ι_preservesColimitIso_inv_assoc]
  rw [α.naturality_assoc]
  simp only [← Category.assoc, ι_preservesColimitIso_hom]
  exact (ι_colimMap (F.whiskerLeft α) j).symm

end CategoryTheory
