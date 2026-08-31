/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Naturality of the extension homology isomorphism

Extending a complex along a `ComplexShape.Embedding` does not change its homology, and Mathlib
records the isomorphism `HomologicalComplex.extendHomologyIso` together with its compatibility
with `homologyπ`, `homologyι`, cycles, and opcycles — but not its naturality in the complex.

Naturality is what a comparison argument needs when the complex varies. Here the `ℕ`-indexed
Čech complex is extended to `ℤ`, and the comparison has to commute with the map induced by a
morphism of sheaves; that requires the extension isomorphism to commute with induced maps.

Both lemmas follow from the cycles-level identity by cancelling the epimorphism `homologyπ`.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c') [e.IsRelIff]
  {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

set_option backward.isDefEq.respectTransparency false in
omit [e.IsRelIff] in
/-- The cycles isomorphism for an extended complex commutes with induced maps.

The cycles of an extension are the cycles of the original in the corresponding degree, and both
sides agree after cancelling the mono `iCycles`. -/
@[reassoc]
lemma extendCyclesIso_naturality :
    cyclesMap (extendMap φ e) j' ≫ (L.extendCyclesIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ cyclesMap φ j := by
  rw [← cancel_mono (L.iCycles j)]
  simp only [Category.assoc, extendCyclesIso_hom_iCycles, cyclesMap_i, cyclesMap_i_assoc,
    extendCyclesIso_hom_iCycles_assoc, extendMap_f φ e hj']
  simp

omit [e.IsRelIff] in
set_option backward.isDefEq.respectTransparency false in
/-- The homology isomorphism for an extended complex commutes with induced maps.

This is the statement the Čech comparison needs, since the Čech complex is `ℕ`-indexed and the
comparison chain is `ℤ`-indexed. It follows from the cycles version by cancelling `homologyπ`. -/
@[reassoc]
lemma extendHomologyIso_naturality :
    homologyMap (extendMap φ e) j' ≫ (L.extendHomologyIso e hj').hom =
      (K.extendHomologyIso e hj').hom ≫ homologyMap φ j := by
  rw [← cancel_epi ((K.extend e).homologyπ j'), homologyπ_naturality_assoc,
    homologyπ_extendHomologyIso_hom, homologyπ_extendHomologyIso_hom_assoc,
    homologyπ_naturality, ← Category.assoc, extendCyclesIso_naturality,
    Category.assoc]

end HomologicalComplex
