/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Braid
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition

/-!
# The functorial braid relation: a supplied statement, and its `K₀` shadow

For an `A₂`-configuration `(A, B)` the Seidel--Thomas theorem is the isomorphism of functors
`T_A T_B T_A ≅ T_B T_A T_B`. It is **stated here, never proved and never asserted**:
`BraidStatement dA dB` carries that isomorphism as its single field, and nothing constructs an
inhabitant.

An inhabitant is a claim about the supplied `dA`, `dB`, and Seidel--Thomas supports it only when
those are the genuine twists: `SphericalTwistData` records no more than a cone-like functor with the
right `K₀` shadow, so for padded or otherwise non-genuine data the isomorphism can fail even for a
genuine `A₂`-configuration. The dg realizations of `ObjectTwistData.lean` are the genuine ones.

## References

Seidel--Thomas, [arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2). Definition 1.1(b): an
`A_m`-configuration is a family of `m` spherical objects with `dim Hom^•(E_i, E_j) = 1` for
`|i - j| = 1` and `0` for `|i - j| ≥ 2`, the dimension being total over all degrees. Theorem 1.2
(second part) gives `T_{E_i} T_{E_{i+1}} T_{E_i} ≅ T_{E_{i+1}} T_{E_i} T_{E_{i+1}}` for such a
family, up to graded natural isomorphism, and Theorem 2.17 is the abstract form. Proposition 2.13
proves the displayed isomorphism for two `n`-spherical objects with `n > 0` and total
`dim Hom^•(E_2, E_1) = 1`.

## Main definitions and results

* `BraidStatement` — the supplied isomorphism `T_A T_B T_A ≅ T_B T_A T_B`.
* `map_braid_of_sphericalPairData` — the `K₀` braid identity for the Euler-form data.
* `BraidStatement.map_braid`, `BraidStatement.twistK₀_braid` — what a supplied isomorphism forces.

## What is proved: only the `K₀` shadow, and only in one direction

The two `K₀` facts below are the entire content, and both are far weaker than the functorial
statement, because `K₀` sees an object only through its class.

* `map_braid_of_sphericalPairData`: for the Euler-form data `SphericalPairData` of `Braid.lean`,
  the induced maps `K₀.map (T_A T_B T_A)` and `K₀.map (T_B T_A T_B)` agree. This is
  `twistK₀_braid` read through `SphericalTwistData.map_eq_twistK₀`: the lattice identity is a
  consequence of the geometry's `K₀` action, not a parallel story.
* `BraidStatement.map_braid`: a `BraidStatement` **implies** the same equality, from `K₀.map_congr`
  alone, with no use of `SphericalPairData`. It is a consistency check that the supplied
  isomorphism cannot contradict what is proved: for a pair whose `K₀` twists do not braid there is
  no `BraidStatement`, so supplying one is a claim a lattice computation can refute.

Nothing projects the other way: the equality of two maps on `K₀` gives no isomorphism of
functors.

## What the statement is not

`SphericalPairData` is the Euler-form shadow of an `A₂`-configuration, not the configuration
itself: it does not record that `Hom^•(A, B)` is one-dimensional. The structure here records no
hypothesis at all, so an inhabitant is a claim about a specific pair and must be supplied only for a
genuine `A₂`-configuration. The isomorphism is of underlying functors; the graded natural
isomorphism of Seidel--Thomas also respects the shift isomorphisms, which is not recorded.
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {k : Type w} [DivisionRing k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]

/-- **The functorial braid relation `T_A T_B T_A ≅ T_B T_A T_B`, as a supplied statement.**
Supplied, not proved; see the module docstring for what an inhabitant claims. -/
structure BraidStatement {A B : C} (dA : SphericalTwistData k C A)
    (dB : SphericalTwistData k C B) where
  /-- The natural isomorphism, in diagrammatic order: `T_A` applied first. -/
  iso : dA.T ⋙ dB.T ⋙ dA.T ≅ dB.T ⋙ dA.T ⋙ dB.T

variable {A B : C} (dA : SphericalTwistData k C A) (dB : SphericalTwistData k C B)

section Twist

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The `K₀` shadow of the braid relation, from the Euler-form data.** `twistK₀_braid`
transported through `SphericalTwistData.map_eq_twistK₀`. The hypothesis is the product condition
`χ(A,B)·χ(B,A) = 1` of `SphericalPairData`, not `χ(A,B) = 1`. -/
theorem map_braid_of_sphericalPairData (h : SphericalPairData k C A B) :
    K₀.map (dA.T ⋙ dB.T ⋙ dA.T) = K₀.map (dB.T ⋙ dA.T ⋙ dB.T) := by
  rw [map_comp_comp_eq_twistK₀, map_comp_comp_eq_twistK₀, twistK₀_braid h]

end Twist

namespace BraidStatement

variable {dA dB} (S : BraidStatement dA dB)

include S

/-- **The consistency check.** A supplied braid isomorphism forces the `K₀` identity, without the
Euler-form data. -/
theorem map_braid : K₀.map (dA.T ⋙ dB.T ⋙ dA.T) = K₀.map (dB.T ⋙ dA.T ⋙ dB.T) :=
  K₀.map_congr S.iso

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- The same, as the identity `τ_A τ_B τ_A = τ_B τ_A τ_B` of `K₀` twists. -/
theorem twistK₀_braid :
    (twistK₀ k C A).comp ((twistK₀ k C B).comp (twistK₀ k C A)) =
      (twistK₀ k C B).comp ((twistK₀ k C A).comp (twistK₀ k C B)) := by
  rw [← map_comp_comp_eq_twistK₀ dA dB dA, ← map_comp_comp_eq_twistK₀ dB dA dB, S.map_braid]

end BraidStatement

end CategoryTheory.Triangulated.SphericalTwist
