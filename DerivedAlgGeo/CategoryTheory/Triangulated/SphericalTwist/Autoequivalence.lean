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

* `AutoequivalenceStatement d` carries its conclusion as a field: for a `2`-spherical `E`, a
  triangulated autoequivalence `Φ`, with its inverse and the instances of both (`TriEquiv`), and a
  natural isomorphism `Φ ≅ T`. Nothing constructs an inhabitant, and no axiom stands in for one.
* `AutoequivalenceStatement.toTwistShaped` closes the circle of the lane: a supplied statement turns
  a `SphericalTwistData` into a `TwistShaped` of `StabilityAction.lean`, so the supplied twist acts
  on stability conditions by the Mukai reflection `ρ_{v(E)}`. The `K₀` action of `Φ` is `twistK₀`
  because `Φ ≅ T` and `K₀.map T = twistK₀` is `SphericalTwistData.map_eq_twistK₀`, proved.

## Sources

Seidel--Thomas, [arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2): Theorem 1.2 (first
part) says `T_E` is an exact self-equivalence of `Dᵇ(X)` for a spherical `E` on a smooth complex
projective `X`; Proposition 2.10 is the abstract form, for an `n`-spherical `E` in the sense of
their Definition 2.14. That definition has a fourth clause, a nondegenerate pairing
`Hom^i(F,E) × Hom^{n-i}(E,F) → Hom^n(E,E)`, which Lemma 3.1 identifies on a smooth projective `X`
with `E ⊗ ω_X ≅ E`. Huybrechts, *Fourier--Mukai transforms in algebraic geometry*, Proposition 8.6,
is the same statement.

## What the hypothesis is, and is not

The field's hypothesis is `IsSphericalObject k 2 E` of `Basic.lean`: the Ext profile alone, with no
Serre-functor clause and none of Definition 2.14's finiteness clauses. This is the clause the `K₀`
consequences need (`χ(E,E) = 2`), and on a K3, where `ω_X ≅ O_X` makes the second clause of
Definition 1.1(a) automatic, it is sphericity. It is **not** sufficient for the theorem in general:
`AlgebraicGeometry/Surface/Spherical.lean` records a surface with the same Ext profile on which
`T_E` is not an autoequivalence. So the statement must be supplied only where the full hypothesis of
Seidel--Thomas holds, and its inhabitant is a claim about that case.

## What the isomorphism does not record

`iso` is a natural isomorphism of underlying functors. Seidel--Thomas work with exact functors,
that is functors with their shift isomorphisms, up to graded natural isomorphism, and compatibility
with the two shift isomorphisms is not recorded here. So `Φ`'s `CommShift` datum and `T`'s are not
asserted to agree. The statement is thereby weaker than the literature's, and no weaker than what is
consumed: `K₀.map_congr` needs only the natural isomorphism.

The order-two statement of `StabilityAction.lean` remains about the lattice and not the functor:
`T_E` has infinite order.
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [HomFiniteBounded k C] [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The Seidel--Thomas autoequivalence theorem for `T_E`, as a supplied statement.**

For a `2`-spherical `E`, `T` is isomorphic to a triangulated autoequivalence, whose inverse and
instances `TriEquiv` carries. Supplied, not proved; see the module docstring for the hypothesis. -/
structure AutoequivalenceStatement {E : C} (d : SphericalTwistData k C E) where
  /-- The autoequivalence, with its inverse and the instances of both. -/
  equiv : IsSphericalObject k (2 : ℤ) E → TriEquiv C
  /-- Its underlying functor is `T`, up to natural isomorphism. -/
  iso : ∀ h : IsSphericalObject k (2 : ℤ) E, Nonempty ((equiv h).e.functor ≅ d.T)

namespace AutoequivalenceStatement

variable {E : C} {d : SphericalTwistData k C E} (S : AutoequivalenceStatement d)
  {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **The supplied twist is twist-shaped.** `Φ ≅ T` and `K₀.map T = twistK₀` give
`K₀.map Φ = twistK₀`, and `χ(E,E) = 2` is `chiK₀_of_self_eq_two`. -/
noncomputable def toTwistShaped (R : MukaiRealization k C b) (h : IsSphericalObject k (2 : ℤ) E) :
    TwistShaped R E where
  Φ := S.equiv h
  map_eq := (K₀.map_congr (S.iso h).some).trans d.map_eq_twistK₀
  chi_self := chiK₀_of_self_eq_two h

omit [IsTriangulated C] in
@[simp]
theorem toTwistShaped_Φ (R : MukaiRealization k C b) (h : IsSphericalObject k (2 : ℤ) E) :
    (S.toTwistShaped R h).Φ = S.equiv h :=
  rfl

/-- **The supplied twist acts on stability conditions through the reflection.** The charge of
`T_E • σ` is the charge of `σ` precomposed with the Mukai reflection `ρ_{v(E)}`; this is
`TwistShaped.act_Z` at the twist-shaped pair that `toTwistShaped` produces. -/
theorem act_Z (R : MukaiRealization k C b) (h : IsSphericalObject k (2 : ℤ) E)
    (σ : StabilityCondition.WithClassMap C R.v) (x : Mukai.MukaiLattice N) :
    (AutPairQuot.mk (S.toTwistShaped R h).toAutPair • σ).Z x =
      σ.Z ((S.toTwistShaped R h).lam x) :=
  (S.toTwistShaped R h).act_Z σ x

end AutoequivalenceStatement

end CategoryTheory.Triangulated.SphericalTwist
