/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.BilinearForm.Isometry
import Mathlib.Tactic

/-!
# Reflection in a vector of norm minus two

For a module `M` over a commutative ring `R` with a bilinear form `B`, and a
vector `s` with `B s s = -2`, the map

```
ρ_s(v) = v + B v s • s
```

is the reflection in the hyperplane `s^⊥`. The `-2` is what makes the usual
formula `v - 2⟪v,s⟫/⟪s,s⟫ · s` integral: the denominator cancels the `2`, so no
division is needed and the reflection is defined on the module rather than on
its rationalisation.

## This is stated over an arbitrary ambient form, not over one extension

`Lattice/Mukai/Reflection.lean` used to own this argument on the single
carrier `ℤ × N × ℤ`, even though nothing in it is about that carrier: every
step is bilinearity, symmetry, or the one hypothesis `B s s = -2`. It is
restated here on `(R, M, B)`, and the Mukai file specialises it at
`B := Mukai.pairingBilin b`. There is one reflection, not two.

**This is not the spherical twist.** On a K3 surface the Seidel--Thomas twist
`T_E` acts on the Mukai lattice as `ρ_{v(E)}`, and that statement is the
eventual reason this theory exists. But `T_E` is an autoequivalence of
`Dᵇ(Coh X)`, its construction needs an evaluation triangle and a functorial
cone, and none of that is available here or asserted here.

## Which hypothesis does what

The split is not the expected one, and stating it over an arbitrary form is
what makes it visible:

* **additivity** needs neither symmetry of `B` nor `B s s = -2`. It is
  bilinearity alone, so `reflectHom` is a linear map for *every* `s`;
* **involutivity** needs `B s s = -2` and nothing else;
* **isometry** needs symmetry of `B` as well, and fails without it -- the two
  cross terms only cancel against `B v s * B w s * B s s` once they are equal.

`-2` is the hypothesis rather than a `IsSpherical`-style predicate on purpose:
spherical-class vocabulary is application vocabulary, and it stays with the
application.
-/

namespace BilinearForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : M →ₗ[R] M →ₗ[R] R)

/-- Reflection in `s`: `ρ_s(v) = v + B v s • s`.

For `B s s = -2` this is the reflection in `s^⊥`; for other `s` it is still a
well-defined additive map, but is neither an involution nor an isometry. The
definition deliberately takes no hypothesis so that `reflectHom` below is
available unconditionally. -/
def reflect (s v : M) : M := v + B v s • s

theorem reflect_apply (s v : M) : reflect B s v = v + B v s • s := rfl

@[simp] theorem reflect_zero (s : M) : reflect B s 0 = 0 := by simp [reflect]

theorem reflect_add (s v w : M) :
    reflect B s (v + w) = reflect B s v + reflect B s w := by
  simp only [reflect, map_add, LinearMap.add_apply, add_smul]
  abel

theorem reflect_smul (a : R) (s v : M) :
    reflect B s (a • v) = a • reflect B s v := by
  simp only [reflect, map_smul, LinearMap.smul_apply, smul_add, smul_eq_mul,
    mul_smul]

theorem reflect_neg (s v : M) : reflect B s (-v) = -reflect B s v := by
  simp only [reflect, map_neg, LinearMap.neg_apply, neg_smul, neg_add_rev]
  abel

/-- `ρ_s` as a linear endomorphism.

No hypothesis on `s`: additivity is bilinearity of `B`, nothing more. -/
def reflectHom (s : M) : M →ₗ[R] M where
  toFun := reflect B s
  map_add' := reflect_add B s
  map_smul' := by intro a v; simpa using reflect_smul B a s v

@[simp] theorem reflectHom_apply (s v : M) : reflectHom B s v = reflect B s v := rfl

theorem apply_reflect_right (s : M) (hs : B s s = -2) (v : M) :
    B (reflect B s v) s = -B v s := by
  rw [reflect, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hs]
  ring

theorem reflect_reflect (s : M) (hs : B s s = -2) (v : M) :
    reflect B s (reflect B s v) = v := by
  conv_lhs => rw [reflect, apply_reflect_right B s hs, reflect]
  rw [neg_smul]
  abel

theorem reflect_involutive (s : M) (hs : B s s = -2) :
    Function.Involutive (reflect B s) := reflect_reflect B s hs

theorem reflect_bijective (s : M) (hs : B s s = -2) :
    Function.Bijective (reflect B s) := (reflect_involutive B s hs).bijective

/-- `ρ_s` as a linear automorphism, with itself as inverse. Needs
`B s s = -2`, which is what makes it an involution. -/
def reflectEquiv (s : M) (hs : B s s = -2) : M ≃ₗ[R] M :=
  { reflectHom B s with
    invFun := reflect B s
    left_inv := reflect_reflect B s hs
    right_inv := reflect_reflect B s hs }

@[simp] theorem reflectEquiv_apply (s : M) (hs : B s s = -2) (v : M) :
    reflectEquiv B s hs v = reflect B s v := rfl

@[simp] theorem reflectEquiv_symm_apply (s : M) (hs : B s s = -2) (v : M) :
    (reflectEquiv B s hs).symm v = reflect B s v := rfl

@[simp] theorem reflect_self (s : M) (hs : B s s = -2) : reflect B s s = -s := by
  rw [reflect, hs]
  module

theorem reflect_of_apply_eq_zero {s v : M} (h : B v s = 0) : reflect B s v = v := by
  rw [reflect, h, zero_smul, add_zero]

theorem apply_reflect_eq_zero_iff (s : M) (hs : B s s = -2) (v : M) :
    B (reflect B s v) s = 0 ↔ B v s = 0 := by
  rw [apply_reflect_right B s hs, neg_eq_zero]

theorem apply_reflect_reflect (hb : ∀ x y : M, B x y = B y x)
    (s : M) (hs : B s s = -2) (v w : M) :
    B (reflect B s v) (reflect B s w) = B v w := by
  have hsw : B s w = B w s := hb s w
  simp only [reflect, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hs, hsw]
  ring

theorem self_reflect (hb : ∀ x y : M, B x y = B y x) (s : M) (hs : B s s = -2)
    (v : M) : B (reflect B s v) (reflect B s v) = B v v :=
  apply_reflect_reflect B hb s hs v v

/-- `ρ_s` as an isometry of `B`. This is the first statement to need symmetry
of `B` as well as `B s s = -2`. -/
def reflectIsometry (hb : ∀ x y : M, B x y = B y x) (s : M) (hs : B s s = -2) :
    B →bᵢ B where
  toLinearMap := reflectHom B s
  map_app' v w := apply_reflect_reflect B hb s hs v w

@[simp] theorem reflectIsometry_apply (hb : ∀ x y : M, B x y = B y x)
    (s : M) (hs : B s s = -2) (v : M) :
    reflectIsometry B hb s hs v = reflect B s v := rfl

@[simp] theorem reflect_neg_left (s v : M) : reflect B (-s) v = reflect B s v := by
  simp only [reflect, map_neg, neg_smul, smul_neg, neg_neg]

end BilinearForm
