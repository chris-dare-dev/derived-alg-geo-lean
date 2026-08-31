/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Semilinear maps on exterior powers

This file constructs the exterior power of a semilinear map between modules.
It is ordinary linear algebra and has no categorical or geometric hypotheses.
-/

open LinearMap

universe u v

namespace LinearMap

variable {R S : Type u} [CommRing R] [CommRing S]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module S N]

/-- A semilinear map induces a semilinear map on exterior powers. -/
noncomputable def exteriorPower (n : ℕ) (σ : R →+* S) (f : M →ₛₗ[σ] N) :
    (⋀[R]^n M) →ₛₗ[σ] (⋀[S]^n N) := by
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  let a : M [⋀^(Fin n)]→ₗ[R] (⋀[S]^n N) :=
    { toFun := fun x => _root_.exteriorPower.ιMulti S n (f ∘ x)
      map_update_add' := by
        intro _ x i m m'
        have hu (a : M) : f ∘ Function.update x i a =
            Function.update (f ∘ x) i (f a) := by
          funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [Function.update, h]
        rw [hu, hu, hu, f.map_add]
        exact (_root_.exteriorPower.ιMulti S n).map_update_add _ _ _ _
      map_update_smul' := by
        intro _ x i r m
        have hu (a : M) : f ∘ Function.update x i a =
            Function.update (f ∘ x) i (f a) := by
          funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [Function.update, h]
        rw [hu, hu, f.map_smulₛₗ]
        exact (_root_.exteriorPower.ιMulti S n).map_update_smul _ _ _ _
      map_eq_zero_of_eq' := by
        intro x i j h hij
        apply (_root_.exteriorPower.ιMulti S n).map_eq_zero_of_eq
        · simpa using congrArg f h
        · exact hij }
  let g : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) :=
    _root_.exteriorPower.alternatingMapLinearEquiv a
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul r x }

@[simp]
theorem exteriorPower_ιMulti (n : ℕ) (σ : R →+* S) (f : M →ₛₗ[σ] N)
    (x : Fin n → M) :
    exteriorPower n σ f (_root_.exteriorPower.ιMulti R n x) =
      _root_.exteriorPower.ιMulti S n (f ∘ x) := by
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  change _root_.exteriorPower.alternatingMapLinearEquiv _
      (_root_.exteriorPower.ιMulti R n x) = _
  rw [_root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end LinearMap
