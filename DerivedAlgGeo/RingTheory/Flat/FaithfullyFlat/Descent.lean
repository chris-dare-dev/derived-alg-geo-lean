/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness over a third ring along flat and faithfully flat ring maps

Let `S → S'` be a map of `R`-algebras and `M` an `S`-module that is also an `R`-module through
`S`. This file compares `R`-flatness of `M` with `R`-flatness of `S' ⊗[S] M` (Stacks 0584).
Mathlib's `Module.Flat.of_flat_tensorProduct` is the case where the third ring is the base.

## Main definitions

None: the file adds theorems about Mathlib's `Module.Flat`.

## Main results

* `Module.Flat.tensorProduct_of_flat`: Stacks 0584 (1), flatness over `R` ascends along a flat
  map `S → S'`.
* `Module.Flat.of_flat_tensorProduct_of_faithfullyFlat`: Stacks 0584 (2), flatness over `R`
  descends along a faithfully flat map `S → S'`.

## Implementation notes

`AlgebraTensorModule.assoc` identifies `(S' ⊗[S] M) ⊗[R] N` with `S' ⊗[S] (M ⊗[R] N)`, naturally
in the `R`-module `N`. Tensoring an injection `N → P` with `S' ⊗[S] M` is therefore `S' ⊗[S] -`
applied to its tensor with `M`. Flatness of `S'` over `S` preserves the injectivity, and faithful
flatness reflects it (`Module.FaithfullyFlat.lTensor_injective_iff_injective`).

`S' ⊗[S] M` is an `R`-module through `S'`, by Mathlib's `TensorProduct.leftModule`.

## References

* [Stacks: Tag 0584](https://stacks.math.columbia.edu/tag/0584)

## Tags

flat, faithfully flat, base change, descent
-/

open TensorProduct

namespace Module.Flat

variable {R S S' M : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
  [Algebra S S'] [IsScalarTower R S S'] [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

/-- `(S' ⊗[S] M) ⊗[R] -` is `S' ⊗[S] (M ⊗[R] -)` through `AlgebraTensorModule.assoc`. -/
private lemma assoc_comp_lTensor {N P : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid P]
    [Module R P] (f : N →ₗ[R] P) :
    (AlgebraTensorModule.assoc R S S S' M P).toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor S (S' ⊗[S] M) f =
      (AlgebraTensorModule.lTensor S M f).lTensor S' ∘ₗ
        (AlgebraTensorModule.assoc R S S S' M N).toLinearMap := by
  ext
  simp

/-- `𝟙 (S' ⊗[S] M) ⊗ f` is injective exactly when `𝟙 S' ⊗ (𝟙 M ⊗ f)` is. -/
private lemma lTensor_injective_iff {N P : Type*} [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] (f : N →ₗ[R] P) :
    Function.Injective (f.lTensor (S' ⊗[S] M)) ↔
      Function.Injective ((AlgebraTensorModule.lTensor S M f).lTensor S') := by
  have h : AlgebraTensorModule.assoc R S S S' M P ∘ f.lTensor (S' ⊗[S] M) =
      (AlgebraTensorModule.lTensor S M f).lTensor S' ∘ AlgebraTensorModule.assoc R S S S' M N :=
    funext <| LinearMap.congr_fun (assoc_comp_lTensor f)
  rw [← (AlgebraTensorModule.assoc R S S S' M P).injective.of_comp_iff, h,
    EquivLike.injective_comp]

/-- **Stacks 0584 (1).** Flatness over `R` ascends along a flat map `S → S'` of `R`-algebras: if
`M` is an `S`-module that is flat over `R`, then `S' ⊗[S] M` is flat over `R`. -/
lemma tensorProduct_of_flat [Module.Flat S S'] [Module.Flat R M] :
    Module.Flat R (S' ⊗[S] M) := by
  rw [iff_lTensor_injectiveₛ]
  intro P _ _ N
  rw [lTensor_injective_iff]
  exact lTensor_preserves_injective_linearMap _ <|
    lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- **Stacks 0584 (2).** Flatness over `R` descends along a faithfully flat map `S → S'` of
`R`-algebras: if `M` is an `S`-module and `S' ⊗[S] M` is flat over `R`, then `M` is flat over
`R`.

Faithful flatness cannot be weakened to flatness: for `R = S = ℤ`, `S' = ℚ` and `M = ℤ/2`, the
module `ℚ ⊗[ℤ] ℤ/2 = 0` is flat over `ℤ`, but `ℤ/2` is not. -/
lemma of_flat_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat S S']
    [Module.Flat R (S' ⊗[S] M)] : Module.Flat R M := by
  rw [iff_lTensor_injectiveₛ]
  intro P _ _ N
  rw [← AlgebraTensorModule.coe_lTensor (A := S),
    ← FaithfullyFlat.lTensor_injective_iff_injective S S', ← lTensor_injective_iff]
  exact lTensor_preserves_injective_linearMap _ Subtype.val_injective

end Module.Flat
