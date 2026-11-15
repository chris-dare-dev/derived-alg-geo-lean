/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Descent of finite presentation along faithfully flat ring maps

Mathlib's `Mathlib/RingTheory/Finiteness/Descent.lean` shows that finiteness of a module descends
along a faithfully flat ring map (Stacks 03C4 (1)). This file adds finite presentation
(Stacks 03C4 (2)).

## Main definitions

None: the file adds a theorem about Mathlib's `Module.FinitePresentation`.

## Main results

* `Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`:
  Stacks 03C4 (2).

## Implementation notes

`M` is finite by Stacks 03C4 (1). Choose `f : Rⁿ ↠ M`. Flatness of `T` identifies `T ⊗[R] ker f`
with the kernel of `T ⊗[R] Rⁿ ↠ T ⊗[R] M` (`LinearMap.tensorKerEquiv`), which is finitely
generated because `T ⊗[R] M` is finitely presented. So `ker f` is finite, again by 03C4 (1).

As in Mathlib, the base change is written `T ⊗[R] M`, with `T` on the left.

## References

* [Stacks: Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)

## Tags

finite presentation, faithfully flat, descent
-/

open TensorProduct

namespace Module.FinitePresentation

variable {R : Type*} [CommRing R]

/-- **Stacks 03C4 (2).** Finite presentation descends along a faithfully flat ring map: if
`T ⊗[R] M` is a finitely presented `T`-module, then `M` is a finitely presented `R`-module.

Faithful flatness cannot be dropped: for `R = ℤ`, `T = ℚ` and `M = ℚ/ℤ`, the module
`ℚ ⊗[ℤ] ℚ/ℤ = 0` is finitely presented over `ℚ`, but `ℚ/ℤ` is not finitely generated over `ℤ`. -/
lemma of_finitePresentation_tensorProduct_of_faithfullyFlat
    (T : Type*) [CommRing T] [Algebra R T] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R T] [Module.FinitePresentation T (T ⊗[R] M)] :
    Module.FinitePresentation R M := by
  have : Module.Finite R M := .of_finite_tensorProduct_of_faithfullyFlat T
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  refine Module.finitePresentation_of_surjective f hf ?_
  have : Module.Finite T (LinearMap.ker (AlgebraTensorModule.lTensor T T f)) :=
    .of_fg <| fg_ker _ <| LinearMap.lTensor_surjective T hf
  have : Module.Finite T (T ⊗[R] LinearMap.ker f) := .equiv (LinearMap.tensorKerEquiv T T f).symm
  rw [← Module.Finite.iff_fg]
  exact .of_finite_tensorProduct_of_faithfullyFlat T

end Module.FinitePresentation
