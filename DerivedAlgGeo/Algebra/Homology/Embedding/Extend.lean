/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Naturality of extension for a single complex

Mathlib's `HomologicalComplex.extendSingleIso` identifies the extension of a
complex supported at one degree with a single complex at the embedded degree.
This module packages those objectwise isomorphisms naturally in the supported
object.

## Main results

* `HomologicalComplex.singleCompExtendIso` is natural for an arbitrary
  embedding of complex shapes and compatible source and target degrees.
* `HomologicalComplex.singleCompExtendAtImageIso` uses the canonical target
  degree supplied by the embedding.

## Implementation notes

Naturality is checked at the supported degree, where both maps reduce to the
original morphism. The source and target use the same ambient zero-morphism
and decidable-index instances, so the comparison specializes directly to
existing single-complex functors.

## References

The components are Mathlib's `HomologicalComplex.extendSingleIso` and its
supported-degree formula `HomologicalComplex.extendSingleIso_hom_f`.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
variable {c : ComplexShape ι} {c' : ComplexShape ι'}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `extendSingleIso` in the object placed at the supported degree.
The equality identifies the chosen target degree with the embedding's image. -/
noncomputable def singleCompExtendIso (e : c.Embedding c') (i : ι) (i' : ι')
    (h : e.f i = i') :
    single C c i ⋙ e.extendFunctor C ≅ single C c' i' :=
  NatIso.ofComponents (fun X => extendSingleIso e X i i' h) (by
    intro X Y f
    apply to_single_hom_ext
    dsimp only [Functor.comp_obj, Functor.comp_map]
    simp only [ComplexShape.Embedding.extendFunctor_map]
    simp only [comp_f]
    rw [extendMap_f _ _ h,
      extendSingleIso_hom_f,
      extendSingleIso_hom_f,
      single_map_f_self,
      single_map_f_self]
    simp)

/-- Choosing the image degree removes the equality argument from
`singleCompExtendIso`. -/
noncomputable def singleCompExtendAtImageIso (e : c.Embedding c') (i : ι) :
    single C c i ⋙ e.extendFunctor C ≅ single C c' (e.f i) :=
  singleCompExtendIso e i (e.f i) rfl

end HomologicalComplex
