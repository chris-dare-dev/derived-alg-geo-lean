/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Braid
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition

/-!
# The functorial braid relation: a supplied statement and its `K₀` shadow

The Seidel--Thomas isomorphism `T_A T_B T_A ≅ T_B T_A T_B` for an `A₂`-configuration is stated here
and neither proved nor asserted: a braid statement carries it as its single field, and nothing in
the repository inhabits it. Only the `K₀` shadow is proved, in the two directions below, and it is
far weaker than the functorial statement, because `K₀` sees an object only through its class.

## Main definitions

* `CategoryTheory.Triangulated.SphericalTwist.BraidStatement`: the supplied isomorphism.

## Main results

* `CategoryTheory.Triangulated.SphericalTwist.map_braid_of_sphericalPairData`:
  the Euler-form data of `SphericalTwist/Braid.lean` gives the braid identity for the induced maps
  of the supplied twists on `K₀`.
* `CategoryTheory.Triangulated.SphericalTwist.BraidStatement.map_braid` and
  `CategoryTheory.Triangulated.SphericalTwist.BraidStatement.twistK₀_braid`:
  a supplied isomorphism forces that identity with no Euler-form hypothesis, so a pair whose
  numerical twists do not braid has no braid statement. Nothing projects the other way.

## Implementation notes

The statement takes no hypothesis on `A` and `B`. The Euler-form data is the shadow of an
`A₂`-configuration and does not record that `Hom^•(A, B)` is one-dimensional, so it is not a
hypothesis here; the traps are on the structure.

## References

Seidel--Thomas, [arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2): Definition 1.1(b), an
`A_m`-configuration has total `dim Hom^•(E_i, E_j) = 1` for adjacent indices and `0` for indices at
distance at least `2`; Theorem 1.2 (second part) and Theorem 2.17, the braid relation up to graded
natural isomorphism; Proposition 2.13, two `n`-spherical objects with `n > 0` and total
`dim Hom^•(E_2, E_1) = 1`.

## Tags

spherical twist, braid relation, Grothendieck group, supplied statement
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {k : Type w} [DivisionRing k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]

/-- **The Seidel--Thomas braid relation `T_A T_B T_A ≅ T_B T_A T_B` (their Theorem 1.2, second part,
and Proposition 2.13), as a supplied statement.** Never inhabited here.

The structure takes no hypothesis, so an inhabitant is a claim about this specific pair of data.
Seidel--Thomas support it only when `dA` and `dB` are the genuine twists, as for the autoequivalence
statement, and `(A, B)` is an `A₂`-configuration, which the Euler-form data does not record. The
isomorphism is of underlying functors; compatibility with the shift isomorphisms is not recorded.
Its `K₀` consequence is the first theorem of this namespace. -/
structure BraidStatement {A B : C} (dA : SphericalTwistData k C A)
    (dB : SphericalTwistData k C B) where
  /-- The natural isomorphism, in diagrammatic order: `T_A` is applied first. -/
  iso : dA.T ⋙ dB.T ⋙ dA.T ≅ dB.T ⋙ dA.T ⋙ dB.T

variable {A B : C} (dA : SphericalTwistData k C A) (dB : SphericalTwistData k C B)

section Twist

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The `K₀` shadow of the braid relation, from the Euler-form data**: the braid identity of the
numerical twists, transported along the induced maps of the supplied twists. The hypothesis is the
product condition `χ(A,B)·χ(B,A) = 1`, not `χ(A,B) = 1`. -/
theorem map_braid_of_sphericalPairData (h : SphericalPairData k C A B) :
    K₀.map (dA.T ⋙ dB.T ⋙ dA.T) = K₀.map (dB.T ⋙ dA.T ⋙ dB.T) := by
  rw [dA.map_comp_comp_eq_twistK₀ dB dA, dB.map_comp_comp_eq_twistK₀ dA dB, twistK₀_braid h]

end Twist

namespace BraidStatement

variable {dA dB} (S : BraidStatement dA dB)

include S

/-- A supplied braid isomorphism forces equal induced maps on `K₀`, because naturally isomorphic
functors induce the same map, with no Euler-form hypothesis. -/
theorem map_braid : K₀.map (dA.T ⋙ dB.T ⋙ dA.T) = K₀.map (dB.T ⋙ dA.T ⋙ dB.T) :=
  K₀.map_congr S.iso

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- A supplied braid isomorphism forces the lattice identity `τ_A τ_B τ_A = τ_B τ_A τ_B` of the
numerical twists, with no Euler-form hypothesis: the previous theorem read through the induced map
of a three-fold composite. The root braid theorem derives the same identity from the Euler-form
data; for a pair whose numerical twists do not braid, no braid statement exists. -/
theorem twistK₀_braid :
    (twistK₀ k C A).comp ((twistK₀ k C B).comp (twistK₀ k C A)) =
      (twistK₀ k C B).comp ((twistK₀ k C A).comp (twistK₀ k C B)) := by
  rw [← dA.map_comp_comp_eq_twistK₀ dB dA, ← dB.map_comp_comp_eq_twistK₀ dA dB, S.map_braid]

end BraidStatement

end CategoryTheory.Triangulated.SphericalTwist
