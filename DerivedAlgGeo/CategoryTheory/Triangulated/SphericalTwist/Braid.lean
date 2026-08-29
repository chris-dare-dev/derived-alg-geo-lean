/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Mukai

/-!
# The braid relation on `K₀`

For an `A₂`-configuration the two triple composites of `K₀` twists agree,

```
τ_A ∘ τ_B ∘ τ_A = τ_B ∘ τ_A ∘ τ_B,
```

under `χ(A,A) = χ(B,B) = 2` and `χ(A,B)·χ(B,A) = 1`. This is the Weyl-group
braid relation for the reflections `ρ_{v(A)}, ρ_{v(B)}`, seen through the Euler
form directly and with no lattice in sight.

## This does NOT imply the functorial braid relation

The Seidel--Thomas theorem is `T_A T_B T_A ≅ T_B T_A T_B`, an isomorphism of
autoequivalences of `Dᵇ(Coh X)`. The identity proved here is its shadow on `K₀`
and is **far weaker**: `K₀` sees only the class of an object, so an equality of
maps on `K₀` says nothing about the functors that induce them. The functorial
claim is stated — supplied, not proved — alongside the rest of the functorial
layer; nothing in this file is evidence for it.

## The computation

Write `α := χ(A, -)` and `β := χ(B, -)`, both `K₀ C →+ ℤ`, and put
`p := α [B] = χ(A,B)`, `q := β [A] = χ(B,A)`. From `τ_E x = x - χ(E,x)·[E]`,

```
α (τ_B x) = α x - p · β x,      β (τ_A x) = β x - q · α x,
```

and `α (τ_A x) = -α x` when `α [A] = 2`. Chaining these,

```
α (τ_B (τ_A x)) = -α x - p·β x + (p·q)·α x = -p · β x,
```

where `p·q = 1` is spent, and symmetrically `β (τ_A (τ_B x)) = -q · α x`. Both
triple composites therefore evaluate to the same element,

```
x + (p · β x - α x) • [A] + (q · α x - β x) • [B],
```

which is `braid_expand` below. The braid relation is that lemma applied twice,
once with `A` and `B` exchanged, and the two right-hand sides then differ only
by the order of two summands.

## No symmetry of `χ`

The computation never compares `p` with `q`, so **no symmetry hypothesis appears
anywhere in this file** and none may be added. A proof reaching for
`Mukai.pairing_comm` or a symmetric-`χ` assumption has taken a detour; the
direct route is shorter.

## Trap: the hypothesis is `p · q = 1`, not `p = q = 1`

Over `ℤ`, `p·q = 1` means `p = q = 1` or `p = q = -1`, and **both are genuine
`A₂` configurations** under this repository's sign convention: `χ(A,B) =
-⟪v(A), v(B)⟫`, so the Mukai pairing is `∓1`. Writing the hypothesis as
`χ(A,B) = 1` alone is strictly stronger than needed and silently excludes half
the configurations. It is stated as a product and consumed as a product; no
case split on the sign is needed, and adding one would double the proof.

## Main results

* `SphericalPairData` — the three Euler-form hypotheses, bundled as a `Prop`.
* `braid_expand` — the normal form of `τ_A ∘ τ_B ∘ τ_A`, spending `χ(A,A) = 2`
  and `p·q = 1` and nothing else.
* `twistK₀_braid` — the braid relation, as an equality of `AddMonoidHom`s.
* `MukaiRealization.reflect_braid` — the same identity transported to the
  lattice, as a corollary of `map_twistK₀`.
-/

universe w u v

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **`χ` against a twisted class.** `χ(F, τ_E x) = χ(F,x) - χ(E,x)·χ(F,E)`.

The two-object generalization of `chiK₀_twistK₀_left`, which is the case `F = E`
with `χ(E,E) = 2` substituted. Carries no hypothesis at all. -/
theorem chiK₀_twistK₀_right (E F : C) (x : K₀ C) :
    chiK₀ k C (K₀.of C F) (twistK₀ k C E x)
      = chiK₀ k C (K₀.of C F) x
        - chiK₀ k C (K₀.of C E) x * chiK₀ k C (K₀.of C F) (K₀.of C E) := by
  rw [twistK₀_apply, map_sub, map_zsmul, smul_eq_mul]

/-- **An `A₂`-configuration, spelled at the level of the Euler form.**

A `Prop`: the three fields are equalities in `ℤ` and the structure carries no
data. Named `...Data` rather than `SphericalPair` because it is Euler-form
data and not the object-level `A₂`-configuration of the literature — no object
of `C` is asserted to be spherical, and no functor is involved.

`a_two` is stated as a product; see the module docstring on why
`χ(A,B) = 1` would be the wrong hypothesis. -/
structure SphericalPairData (A B : C) : Prop where
  /-- `A` has Euler self-form `2`. -/
  chi_A : chiK₀ k C (K₀.of C A) (K₀.of C A) = 2
  /-- `B` has Euler self-form `2`. -/
  chi_B : chiK₀ k C (K₀.of C B) (K₀.of C B) = 2
  /-- The `A₂` condition, as a product. -/
  a_two : chiK₀ k C (K₀.of C A) (K₀.of C B)
    * chiK₀ k C (K₀.of C B) (K₀.of C A) = 1

variable {k C}

namespace SphericalPairData

/-- The configuration is symmetric in its two objects. This is what lets the
braid relation be `braid_expand` applied twice rather than proved twice. -/
theorem symm {A B : C} (h : SphericalPairData k C A B) :
    SphericalPairData k C B A where
  chi_A := h.chi_B
  chi_B := h.chi_A
  a_two := by rw [mul_comm]; exact h.a_two

end SphericalPairData

/-- **The normal form of `τ_A ∘ τ_B ∘ τ_A`.**

Note what this costs: `χ(A,A) = 2` and `χ(A,B)·χ(B,A) = 1`. It does **not** need
`χ(B,B) = 2`, which is why the braid relation can be assembled from this lemma
and its mirror image. See the module docstring for the computation. -/
theorem braid_expand {A B : C}
    (hA : chiK₀ k C (K₀.of C A) (K₀.of C A) = 2)
    (hAB : chiK₀ k C (K₀.of C A) (K₀.of C B)
      * chiK₀ k C (K₀.of C B) (K₀.of C A) = 1) (x : K₀ C) :
    twistK₀ k C A (twistK₀ k C B (twistK₀ k C A x))
      = x + (chiK₀ k C (K₀.of C A) (K₀.of C B) * chiK₀ k C (K₀.of C B) x
              - chiK₀ k C (K₀.of C A) x) • K₀.of C A
          + (chiK₀ k C (K₀.of C B) (K₀.of C A) * chiK₀ k C (K₀.of C A) x
              - chiK₀ k C (K₀.of C B) x) • K₀.of C B := by
  simp only [twistK₀_apply, map_sub, map_zsmul, hA]
  match_scalars <;>
    first
      | linear_combination (-((chiK₀ k C) (K₀.of C A) x)) * hAB
      | ring_nf

/-- **The braid relation, pointwise.** -/
theorem twistK₀_braid_apply {A B : C} (h : SphericalPairData k C A B)
    (x : K₀ C) :
    twistK₀ k C A (twistK₀ k C B (twistK₀ k C A x))
      = twistK₀ k C B (twistK₀ k C A (twistK₀ k C B x)) := by
  rw [braid_expand h.chi_A h.a_two x,
    braid_expand h.symm.chi_A h.symm.a_two x]
  abel

/-- **The braid relation**, as an equality of endomorphisms of `K₀ C`.

`τ_A ∘ τ_B ∘ τ_A = τ_B ∘ τ_A ∘ τ_B`. The shadow on `K₀` of Seidel--Thomas;
see the module docstring on why it does not imply that theorem. -/
theorem twistK₀_braid {A B : C} (h : SphericalPairData k C A B) :
    (twistK₀ k C A).comp ((twistK₀ k C B).comp (twistK₀ k C A))
      = (twistK₀ k C B).comp ((twistK₀ k C A).comp (twistK₀ k C B)) :=
  AddMonoidHom.ext fun x => twistK₀_braid_apply h x

namespace MukaiRealization

variable {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **The braid relation transported to the lattice.**

A corollary of `map_twistK₀`, not an independent lattice theorem: a general
braid relation for `Mukai.reflect` belongs in
`LinearAlgebra/Lattice/Mukai/Reflection.lean` and would be a separate change.
This says only that the identity holds *on the image of* `v`. -/
theorem reflect_braid (R : MukaiRealization k C b) {A B : C}
    (h : SphericalPairData k C A B) (x : K₀ C) :
    Mukai.reflect b (R.v (K₀.of C A)) (Mukai.reflect b (R.v (K₀.of C B))
        (Mukai.reflect b (R.v (K₀.of C A)) (R.v x)))
      = Mukai.reflect b (R.v (K₀.of C B)) (Mukai.reflect b (R.v (K₀.of C A))
          (Mukai.reflect b (R.v (K₀.of C B)) (R.v x))) := by
  rw [← R.map_twistK₀, ← R.map_twistK₀, ← R.map_twistK₀, ← R.map_twistK₀,
    ← R.map_twistK₀, ← R.map_twistK₀, twistK₀_braid_apply h]

end MukaiRealization

end CategoryTheory.Triangulated.SphericalTwist
