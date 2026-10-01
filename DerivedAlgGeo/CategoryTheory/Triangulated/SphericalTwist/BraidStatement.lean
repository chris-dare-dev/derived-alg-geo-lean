/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Braid
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition

/-!
# The functorial braid relation: a supplied statement, and its `K₀` shadow

For an `A₂`-configuration `(A, B)` the Seidel--Thomas theorem (*Braid group actions on derived
categories of coherent sheaves*) is the
isomorphism of functors `T_A T_B T_A ≅ T_B T_A T_B`. It is **stated here, never proved and never
asserted**: `BraidStatement dA dB` carries that isomorphism as its single field, and nothing
constructs an inhabitant.

## What is proved: only the `K₀` shadow, and only in one direction

The two `K₀` facts below are the entire content, and both are far weaker than the functorial
statement, because `K₀` sees an object only through its class.

* `map_braid_of_pair`: for the Euler-form data `SphericalPairData` of `Braid.lean`, the induced
  maps `K₀.map (T_A T_B T_A)` and `K₀.map (T_B T_A T_B)` agree. This is `twistK₀_braid` read
  through `SphericalTwistData.map_eq_twistK₀`: the lattice identity is a consequence of the
  geometry's `K₀` action, not a parallel story.
* `BraidStatement.map_braid`: a `BraidStatement` **implies** the same equality, from `K₀.map_congr`
  alone, with no use of `SphericalPairData`. It is a consistency check that the supplied
  isomorphism cannot contradict what is proved: for a pair whose `K₀` twists do not braid there is
  no `BraidStatement`, so supplying one is a claim a lattice computation can refute.

Nothing projects the other way: the equality of two maps on `K₀` gives no isomorphism of
functors.

## What the statement is not

`SphericalPairData` is the Euler-form shadow of an `A₂`-configuration, not the configuration
itself. The literature's hypothesis also asks for a one-dimensional total `Hom(A, B)`; the
structure here records no hypothesis at all, so an inhabitant is a claim about a specific pair and
must be supplied only for a genuine `A₂`-configuration. The isomorphism is of underlying functors;
its compatibility with the shift isomorphisms is not recorded.
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {k : Type w} [DivisionRing k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HomFiniteBounded k C] [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The functorial braid relation `T_A T_B T_A ≅ T_B T_A T_B`, as a supplied statement.**
Supplied, not proved; see the module docstring for what an inhabitant claims. -/
structure BraidStatement {A B : C} (dA : SphericalTwistData k C A)
    (dB : SphericalTwistData k C B) where
  /-- The natural isomorphism, in diagrammatic order: `T_A` applied first. -/
  iso : dA.T ⋙ dB.T ⋙ dA.T ≅ dB.T ⋙ dA.T ⋙ dB.T

variable {A B : C} (dA : SphericalTwistData k C A) (dB : SphericalTwistData k C B)

/-- The `K₀` map of the three-fold composite `T_A T_B T_A` is the composite of the three twists. -/
theorem map_braid_left :
    K₀.map (dA.T ⋙ dB.T ⋙ dA.T) =
      (twistK₀ k C A).comp ((twistK₀ k C B).comp (twistK₀ k C A)) := by
  rw [K₀.map_comp, K₀.map_comp, dA.map_eq_twistK₀, dB.map_eq_twistK₀]
  rfl

/-- **The `K₀` shadow of the braid relation, from the Euler-form data.** -/
theorem map_braid_of_pair (h : SphericalPairData k C A B) :
    K₀.map (dA.T ⋙ dB.T ⋙ dA.T) = K₀.map (dB.T ⋙ dA.T ⋙ dB.T) := by
  rw [map_braid_left, map_braid_left, twistK₀_braid h]

namespace BraidStatement

variable {dA dB} (S : BraidStatement dA dB)

include S

/-- **The consistency check.** A supplied braid isomorphism forces the `K₀` identity, without the
Euler-form data. -/
theorem map_braid : K₀.map (dA.T ⋙ dB.T ⋙ dA.T) = K₀.map (dB.T ⋙ dA.T ⋙ dB.T) :=
  K₀.map_congr S.iso

/-- The same, as the identity `τ_A τ_B τ_A = τ_B τ_A τ_B` of `K₀` twists. -/
theorem twistK₀_braid :
    (twistK₀ k C A).comp ((twistK₀ k C B).comp (twistK₀ k C A)) =
      (twistK₀ k C B).comp ((twistK₀ k C A).comp (twistK₀ k C B)) := by
  rw [← map_braid_left dA dB, ← map_braid_left dB dA, S.map_braid]

end BraidStatement

end CategoryTheory.Triangulated.SphericalTwist
