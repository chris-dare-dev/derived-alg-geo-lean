/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm

/-!
# The spherical twist on `K₀`

For an object `E` of a `k`-linear pretriangulated category with an Euler form,

```
τ_E(x) = x - χ(E, x) • [E]
```

is an additive endomorphism of `K₀ C`. On a K3 surface this is the shadow on
`K₀` of the Seidel--Thomas twist `T_E`, and under the Mukai vector it is the
lattice reflection `ρ_{v(E)}` of `LinearAlgebra/Lattice/Mukai/Reflection.lean`.

**This is not the spherical twist**, in exactly the sense that `Reflection.lean`
is not either. `T_E` is an autoequivalence of `Dᵇ(Coh X)` defined by the cone of
an evaluation map; its construction needs a Hom-complex tensor and a functorial
cone, and neither is available here or asserted here. Everything below is a
theorem about the additive group `K₀ C` and the biadditive form `chiK₀`, true
whether or not any object of `C` is spherical and whether or not any surface
exists.

Note which hypotheses do what. The split mirrors `Reflection.lean` term for
term, which is the point:

* **additivity** of `τ_E` needs neither symmetry of `χ` nor `χ(E,E) = 2`. It is
  biadditivity of `chiK₀` alone, so `twistK₀` is an `AddMonoidHom` for *every*
  `E`;
* **involutivity** needs `χ(E,E) = 2` and nothing else;
* **preservation of `χ`** needs symmetry of `χ` as well, and fails without it —
  the two cross terms only cancel against `χ(E,x)·χ(E,y)·χ(E,E)` once they are
  equal.

## Symmetry of `χ` is a hypothesis, never an instance

Over a general `k`-linear triangulated category `χ` is **not** symmetric.
Symmetry is a consequence of Serre duality, which this file does not have and
must not assume; it is carried as an explicit argument to the one theorem that
needs it, in the shape `Reflection.lean` uses for symmetry of `b`. No
`SymmetricEuler` class is introduced here, and none should be.

## Why `chiK₀` and not `chiHom`

`chiHom` is junk-total — see the module docstring of
`GrothendieckGroup/EulerForm.lean`. It is defined for every pair of objects in
every `k`-linear pretriangulated category and returns a meaningless number when
`HomFiniteBounded` fails, because `finrank` is `0` on a non-finite module and
`finsum` is `0` on an infinitely-supported family. A twist built on `chiHom`
without `HomFiniteBounded` would compile and `twistK₀_twistK₀` would be false,
because the additivity that carries `χ(E, τ_E x) = -χ(E, x)` is precisely what
that hypothesis buys. `chiK₀` already carries it.

## Main results

* `twistK₀` — `τ_E` as an `AddMonoidHom`, for arbitrary `E`.
* `chiK₀_twistK₀_left` — `χ(E, τ_E x) = -χ(E, x)`; the one computation the rest
  consumes, and the only place `χ(E,E) = 2` is spent.
* `twistK₀_twistK₀` — `τ_E` is an involution; `twistK₀Equiv`, the resulting
  automorphism of `K₀ C`.
* `twistK₀_self` — `τ_E [E] = -[E]`, and `twistK₀_of_chi_eq_zero` — `τ_E` fixes
  the left kernel of `χ(E, -)` pointwise. Together these say `τ_E` is a
  *reflection* rather than merely an involution.
* `chiK₀_twistK₀_twistK₀` — `τ_E` preserves `χ` when `χ` is symmetric.
-/

universe w u v

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-! ### The map, and its additivity

Stated for an arbitrary `E`. No sphericity hypothesis appears until
`chiK₀_twistK₀_left`, so everything in this section holds for every object and
is not a statement about spherical objects at all. -/

/-- **The spherical twist on `K₀`**: `τ_E(x) = x - χ(E, x) • [E]`.

An `AddMonoidHom` with no hypothesis on `E`: additivity is biadditivity of
`chiK₀`, nothing more. Since `chiK₀ k C (K₀.of C E)` is already a
`K₀ C →+ ℤ`, the coefficient is a homomorphism and the subtraction is taken in
the `AddCommGroup` `K₀ C`. -/
noncomputable def twistK₀ (E : C) : K₀ C →+ K₀ C where
  toFun x := x - chiK₀ k C (K₀.of C E) x • K₀.of C E
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, add_smul]
    abel

/-- Not `@[simp]`: unfolding `twistK₀` everywhere would put `twistK₀_self` and
`twistK₀_of` out of simp-normal form. Rewrite with it explicitly. -/
theorem twistK₀_apply (E : C) (x : K₀ C) :
    twistK₀ k C E x = x - chiK₀ k C (K₀.of C E) x • K₀.of C E :=
  rfl

@[simp]
theorem twistK₀_zero (E : C) : twistK₀ k C E 0 = 0 :=
  map_zero _

/-- `τ_E [F] = [F] - χ(E, F) • [E]`, the form on classes of objects. -/
theorem twistK₀_of (E F : C) :
    twistK₀ k C E (K₀.of C F) = K₀.of C F - chiHom k C E F • K₀.of C E := by
  rw [twistK₀_apply, chiK₀_of_of]

/-! ### The pairing against `E`

One computation, isolated because both the involution and the `χ`-preservation
proof consume it. The analogue of `Mukai.pairing_reflect_right`. -/

/-- Twisting reverses the Euler form against `E` itself. This is where
`χ(E, E) = 2` is spent. -/
theorem chiK₀_twistK₀_left {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    chiK₀ k C (K₀.of C E) (twistK₀ k C E x) = -chiK₀ k C (K₀.of C E) x := by
  rw [twistK₀_apply, map_sub, map_zsmul, hE, smul_eq_mul]
  ring

/-! ### Involutivity -/

/-- **`τ_E` is an involution** when `χ(E, E) = 2`. -/
theorem twistK₀_twistK₀ {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    twistK₀ k C E (twistK₀ k C E x) = x := by
  conv_lhs => rw [twistK₀_apply, chiK₀_twistK₀_left k C hE, twistK₀_apply]
  rw [neg_smul]
  abel

theorem twistK₀_involutive {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) :
    Function.Involutive (twistK₀ k C E) :=
  twistK₀_twistK₀ k C hE

theorem twistK₀_bijective {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) :
    Function.Bijective (twistK₀ k C E) :=
  (twistK₀_involutive k C hE).bijective

/-- `τ_E` as an additive automorphism of `K₀ C`, with itself as inverse. -/
noncomputable def twistK₀Equiv {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) :
    K₀ C ≃+ K₀ C :=
  { twistK₀ k C E with
    invFun := twistK₀ k C E
    left_inv := twistK₀_twistK₀ k C hE
    right_inv := twistK₀_twistK₀ k C hE }

@[simp]
theorem twistK₀Equiv_apply {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    twistK₀Equiv k C hE x = twistK₀ k C E x :=
  rfl

@[simp]
theorem twistK₀Equiv_symm_apply {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    (twistK₀Equiv k C hE).symm x = twistK₀ k C E x :=
  rfl

/-! ### The reflection property

`twistK₀_self` and `twistK₀_of_chi_eq_zero` are what distinguish a reflection
from an arbitrary involution: the `-1` eigenspace contains `[E]` and the `+1`
eigenspace contains the left kernel of `χ(E, -)`. -/

/-- `τ_E [E] = -[E]`. Needs `χ(E, E) = 2` but not symmetry. -/
theorem twistK₀_self {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) :
    twistK₀ k C E (K₀.of C E) = -K₀.of C E := by
  rw [twistK₀_apply, hE]
  module

/-- `τ_E` fixes the left kernel of `χ(E, -)` pointwise. No hypothesis on `E` at
all; the analogue of `Mukai.reflect_of_pairing_eq_zero`. -/
theorem twistK₀_of_chi_eq_zero {E : C} {x : K₀ C}
    (h : chiK₀ k C (K₀.of C E) x = 0) :
    twistK₀ k C E x = x := by
  rw [twistK₀_apply, h, zero_smul, sub_zero]

/-- The twisted class lies in the left kernel of `χ(E, -)` exactly when the
original one does. -/
theorem chiK₀_twistK₀_eq_zero_iff {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    chiK₀ k C (K₀.of C E) (twistK₀ k C E x) = 0
      ↔ chiK₀ k C (K₀.of C E) x = 0 := by
  rw [chiK₀_twistK₀_left k C hE, neg_eq_zero]

/-! ### Preservation of `χ`

The first statement in this file to need symmetry of `χ`, carried explicitly.
See the module docstring on why it is not an instance. -/

/-- **`τ_E` preserves the Euler form**, when `χ` is symmetric and `χ(E,E) = 2`.

Both hypotheses are needed and neither is decoration: symmetry makes the two
cross terms equal, and `χ(E,E) = 2` is what they then cancel against. -/
theorem chiK₀_twistK₀_twistK₀
    (hsymm : ∀ x y : K₀ C, chiK₀ k C x y = chiK₀ k C y x) {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x y : K₀ C) :
    chiK₀ k C (twistK₀ k C E x) (twistK₀ k C E y) = chiK₀ k C x y := by
  have hxE : chiK₀ k C x (K₀.of C E) = chiK₀ k C (K₀.of C E) x := hsymm _ _
  simp only [twistK₀_apply, map_sub, map_zsmul, AddMonoidHom.sub_apply,
    AddMonoidHom.zsmul_apply, hE, hxE, smul_eq_mul]
  ring

end CategoryTheory.Triangulated.SphericalTwist
