/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.StabilityAction

/-!
# `T_E` is an autoequivalence: a supplied statement, and what follows from it

`SphericalTwistData` (in `Definition.lean`) supplies the functor `T_E`. That it is an
autoequivalence is the Seidel--Thomas theorem, and **it is stated here, never proved and never
asserted**.

* `AutoequivalenceStatement d h` carries its conclusion as fields, under the hypothesis
  `h : IsSphericalObject k 2 E`: a triangulated autoequivalence `Φ`, with its inverse and the
  instances of both (`TriEquiv`), and a natural isomorphism `Φ ≅ T`. Nothing constructs an
  inhabitant, and no axiom stands in for one.
* `AutoequivalenceStatement.toTwistShaped` closes the circle of the lane: a supplied statement turns
  a `SphericalTwistData` into a `TwistShaped` of `StabilityAction.lean`, so the supplied twist acts
  on stability conditions by the Mukai reflection `ρ_{v(E)}`. The `K₀` action of `Φ` is `twistK₀`
  because `Φ ≅ T` and `K₀.map T = twistK₀` is `SphericalTwistData.map_eq_twistK₀`, proved.

## Main definitions and results

* `AutoequivalenceStatement` — the supplied conclusion, for a given `d` and `h`.
* `AutoequivalenceStatement.toTwistShaped` — the supplied twist is twist-shaped.
* `AutoequivalenceStatement.act_Z` — it acts on stability conditions through `ρ_{v(E)}`.

## What an inhabitant claims

`SphericalTwistData` records no more than a cone-like triangulated functor with the right `K₀`
shadow: nothing ties its `copower` and `ev` to `Hom^•(E,-) ⊗ E` and the evaluation map. So
Seidel--Thomas supports an inhabitant only when `d` is the genuine twist datum, as the dg
realizations of `ObjectTwistData.lean` are. Padding a genuine datum by the triangle
`P F ⟶ 0 ⟶ (P F)⟦1⟧` with `P = 𝟭 ⊞ ⟦1⟧`, so that `[P F] = 0`, preserves every field, including the
class of the copower, but adds the summands `F⟦1⟧ ⊕ F⟦2⟧` to `T F`, which an autoequivalence cannot
have. An inhabitant is a claim about the specific `d`.

## What the hypothesis is, and is not

The hypothesis `h` is `IsSphericalObject k 2 E` of `Basic.lean`: the Ext profile alone, with no
Serre-functor clause and none of the finiteness clauses of Seidel--Thomas' Definition 2.9. This is
the clause the `K₀` consequences need (`χ(E,E) = 2`), and on a K3, where `ω_X ≅ O_X` makes the
second clause of Definition 1.1(a) automatic, it is sphericity. It is **not** sufficient for the
theorem in general: `AlgebraicGeometry/Surface/Spherical.lean` records a surface with the same Ext
profile on which `T_E` is not an autoequivalence. So the statement must be supplied only where the
full hypothesis of Seidel--Thomas holds, and its inhabitant is a claim about that case.

## What the isomorphism does not record

`iso` is a natural isomorphism of underlying functors. Seidel--Thomas work with exact functors,
that is functors with their shift isomorphisms, up to graded natural isomorphism, and compatibility
with the two shift isomorphisms is not recorded here. So `Φ`'s `CommShift` datum and `T`'s are not
asserted to agree. The statement is thereby weaker than the literature's, and no weaker than what is
consumed: `K₀.map_congr` needs only the natural isomorphism.

The order-two statement of `StabilityAction.lean` remains about the lattice and not the functor:
`T_E` has infinite order.

## References

Seidel--Thomas, [arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2): Theorem 1.2 (first
part) says `T_E` is an exact self-equivalence of `Dᵇ(X)` for a spherical `E` on a smooth complex
projective `X`. Proposition 2.10 is the abstract form, for an `n`-spherical `E` in the sense of
their Definition 2.9 (a bounded complex of injectives with finite-dimensional Homs, the Ext profile
and a nondegenerate pairing); Definition 2.14 transfers that notion to `Dᵇ(S')`, and Lemma 3.1
identifies it on a smooth projective `X` with `E ⊗ ω_X ≅ E`. Huybrechts, *Fourier--Mukai
transforms in algebraic geometry*, Proposition 8.6, is the same statement.
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [HomFiniteBounded k C] [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The Seidel--Thomas autoequivalence theorem for `T_E` (their Proposition 2.10), as a supplied
statement**: `d.T` is naturally isomorphic to the functor of a triangulated autoequivalence, whose
inverse and instances `TriEquiv` carries. Never inhabited here.

The parameter `h` is the Ext profile only and is not sufficient for the theorem
(`AlgebraicGeometry/Surface/Spherical.lean` records a counterexample), so an inhabitant may be
supplied only where `E` is spherical in Seidel--Thomas' full sense and `d` is the genuine twist.
`h` is consumed only by `toTwistShaped`, for `χ(E,E) = 2`. -/
structure AutoequivalenceStatement {E : C} (d : SphericalTwistData k C E)
    (h : IsSphericalObject k (2 : ℤ) E) where
  /-- The autoequivalence, with its inverse and the instances of both. -/
  equiv : TriEquiv C
  /-- Its underlying functor is `T`, up to natural isomorphism. -/
  iso : equiv.e.functor ≅ d.T

namespace AutoequivalenceStatement

variable {E : C} {d : SphericalTwistData k C E} {h : IsSphericalObject k (2 : ℤ) E}
  (S : AutoequivalenceStatement d h) {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **The supplied twist is twist-shaped.** `Φ ≅ T` and `K₀.map T = twistK₀` give
`K₀.map Φ = twistK₀`, and `χ(E,E) = 2` is `chiK₀_of_self_eq_two`. -/
noncomputable def toTwistShaped (R : MukaiRealization k C b) : TwistShaped R E where
  Φ := S.equiv
  map_eq := (K₀.map_congr S.iso).trans d.map_eq_twistK₀
  chi_self := chiK₀_of_self_eq_two h

omit [IsTriangulated C] in
/-- The autoequivalence of the constructed `TwistShaped` is the supplied one. -/
@[simp]
theorem toTwistShaped_Φ (R : MukaiRealization k C b) : (S.toTwistShaped R).Φ = S.equiv :=
  rfl

/-- **The supplied twist acts on stability conditions through the reflection.** The charge of
`T_E • σ` is the charge of `σ` precomposed with the Mukai reflection `ρ_{v(E)}`; this is
`TwistShaped.act_Z` at the twist-shaped pair that `toTwistShaped` produces. -/
theorem act_Z (R : MukaiRealization k C b) (σ : StabilityCondition.WithClassMap C R.v)
    (x : Mukai.MukaiLattice N) :
    (AutPairQuot.mk (S.toTwistShaped R).toAutPair • σ).Z x = σ.Z ((S.toTwistShaped R).lam x) :=
  (S.toTwistShaped R).act_Z σ x

end AutoequivalenceStatement

end CategoryTheory.Triangulated.SphericalTwist
