/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Products and kernels of flat modules

## Main results

* `Module.Flat.prod`: a product of two flat modules is flat.
* `Module.Flat.ker_of_surjective`: the kernel of a surjection between flat modules is flat
  (Stacks 00HM, second assertion).

## References

* [Stacks: Tag 00HM](https://stacks.math.columbia.edu/tag/00HM)
-/

universe u v w

open TensorProduct

namespace Module.Flat

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A product of two flat modules is flat. -/
instance prod [Flat R M] [Flat R N] : Flat R (M × N) := by
  refine iff_lTensor_preserves_injective_linearMap.mpr fun P P' _ _ _ _ f hf ↦ ?_
  have hcomm : (TensorProduct.prodLeft R R M N P').toLinearMap ∘ₗ f.lTensor (M × N) =
      (f.lTensor M).prodMap (f.lTensor N) ∘ₗ (TensorProduct.prodLeft R R M N P).toLinearMap := by
    ext x p <;> simp
  have hinj : Function.Injective ((f.lTensor M).prodMap (f.lTensor N) ∘ₗ
      (TensorProduct.prodLeft R R M N P).toLinearMap) :=
    (Prod.map_injective.mpr ⟨lTensor_preserves_injective_linearMap f hf,
      lTensor_preserves_injective_linearMap f hf⟩).comp (TensorProduct.prodLeft R R M N P).injective
  rw [← hcomm, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- Stacks 00HM, second assertion: the kernel of a surjection between flat modules is flat. -/
theorem ker_of_surjective [Flat R M] [Flat R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Flat R (LinearMap.ker f) := by
  refine iff_rTensor_preserves_injective_linearMap.mpr fun P P' _ _ _ _ g hg ↦ ?_
  have hcomm : (LinearMap.ker f).subtype.lTensor P' ∘ₗ g.rTensor (LinearMap.ker f) =
      g.rTensor M ∘ₗ (LinearMap.ker f).subtype.lTensor P := by
    ext p x
    simp
  have hinj : Function.Injective (g.rTensor M ∘ₗ (LinearMap.ker f).subtype.lTensor P) :=
    (rTensor_preserves_injective_linearMap g hg).comp
      (LinearMap.lTensor_injective_of_exact_of_flat f hf _ (LinearMap.ker f).subtype_injective
        (LinearMap.exact_subtype_ker_map f) P)
  rw [← hcomm, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

end Module.Flat
