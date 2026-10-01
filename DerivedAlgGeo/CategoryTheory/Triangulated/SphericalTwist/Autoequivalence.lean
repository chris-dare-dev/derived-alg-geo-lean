/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.StabilityAction

/-!
# `T_E` is an autoequivalence: a supplied statement

The Seidel--Thomas theorem that `T_E` is an autoequivalence is stated here and neither proved nor
asserted: an autoequivalence statement carries its conclusion as fields, and nothing in the
repository inhabits it. A supplied statement turns a supplied twist into a twist-shaped
autoequivalence, so the twist acts on stability conditions through the Mukai reflection.

## Main definitions

* `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData.toTwistShaped`:
  a twist with an autoequivalence isomorphic to it is twist-shaped.
* `CategoryTheory.Triangulated.SphericalTwist.AutoequivalenceStatement`:
  the supplied conclusion, for given twist data and hypothesis.

## Main results

* `CategoryTheory.Triangulated.SphericalTwist.AutoequivalenceStatement.toTwistShaped`:
  a supplied statement makes the twist data twist-shaped.
* `CategoryTheory.Triangulated.SphericalTwist.AutoequivalenceStatement.act_Z`:
  the charge of the twisted stability condition is the charge precomposed with the reflection
  `ρ_{v(E)}`.

## Implementation notes

The conclusion is a bundled autoequivalence, carrying its inverse and their instances, because the
induced map on `K₀` needs those instances. The isomorphism with the twist is of underlying
functors; Seidel--Thomas work with exact functors up to graded natural isomorphism, so
compatibility with the shift isomorphisms is not recorded. That is weaker than the literature and
no weaker than what is consumed, since the induced map on `K₀` depends only on the natural
isomorphism.

## References

Seidel--Thomas, [arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2): Theorem 1.2 (first
part) and Proposition 2.10, for `n`-spherical objects in the sense of Definition 2.9, a bounded
complex of injectives with finite-dimensional Homs, the Ext profile and a nondegenerate pairing.
Definition 2.14 transfers that notion to `Dᵇ(S')`, and Lemma 3.1 identifies it with `E ⊗ ω_X ≅ E`
on a smooth projective variety. Huybrechts, *Fourier--Mukai transforms in algebraic geometry*,
Proposition 8.6.

## Tags

spherical twist, autoequivalence, supplied statement
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

section Projection

variable {k : Type w} [DivisionRing k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [HomFiniteBounded k C] [∀ n : ℤ, (shiftFunctor C n).Linear k]
  {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **A supplied twist with an autoequivalence is twist-shaped.** An isomorphism `Φ ≅ T` and
`K₀.map T = twistK₀` give `K₀.map Φ = twistK₀`, and `hχ` is the sphericity `χ(E,E) = 2` that a
twist-shaped pair records. This is the projection to the stability layer, kept out of
`SphericalTwist/Definition.lean` so that the root imports no stability module. -/
noncomputable def SphericalTwistData.toTwistShaped {E : C} (d : SphericalTwistData k C E)
    (Φ : TriEquiv C) (e : Φ.e.functor ≅ d.T)
    (hχ : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (R : MukaiRealization k C b) :
    TwistShaped R E :=
  ⟨Φ, (K₀.map_congr e).trans d.map_eq_twistK₀, hχ⟩

end Projection

section Statement

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [HomFiniteBounded k C] [∀ n : ℤ, (shiftFunctor C n).Linear k]
  {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **The Seidel--Thomas autoequivalence theorem for `T_E` (their Proposition 2.10), as a supplied
statement**: `d.T` is naturally isomorphic to the functor of a triangulated autoequivalence.
Never inhabited here.

An inhabitant is a claim about the specific `d`. The twist data records only a cone-like
triangulated functor with the right class on `K₀`, so padding a genuine datum by the triangle
`P F ⟶ 0 ⟶ (P F)⟦1⟧` with `P = 𝟭 ⊞ ⟦1⟧` preserves every field and adds the summands
`F⟦1⟧ ⊕ F⟦2⟧` to `T F`, which an autoequivalence cannot have. The hypothesis `h` is the Ext profile
alone: in Seidel--Thomas' terms it gives (K3), the ambient Hom-finiteness gives (K2), and the
nondegenerate pairing (K4) is missing, which is why `AlgebraicGeometry/Surface/Spherical.lean`
records a surface with this profile whose twist is not an autoequivalence. Supply an inhabitant
only where `d` is genuine and `E` is spherical in the full sense. The hypothesis is consumed only
by the projection to the stability layer, for `χ(E,E) = 2`. -/
structure AutoequivalenceStatement {E : C} (d : SphericalTwistData k C E)
    (h : IsSphericalObject k (2 : ℤ) E) where
  /-- The autoequivalence, with its inverse and the instances of both. -/
  equiv : TriEquiv C
  /-- Its underlying functor is `T`, up to natural isomorphism. -/
  iso : equiv.e.functor ≅ d.T

namespace AutoequivalenceStatement

variable {E : C} {d : SphericalTwistData k C E} {h : IsSphericalObject k (2 : ℤ) E}
  (S : AutoequivalenceStatement d h)

/-- A supplied statement makes the twist data twist-shaped: the projection of the previous
section at the supplied autoequivalence, with `χ(E,E) = 2` from the Ext-profile hypothesis. -/
noncomputable def toTwistShaped (R : MukaiRealization k C b) : TwistShaped R E :=
  d.toTwistShaped S.equiv S.iso (chiK₀_of_self_eq_two h) R

omit [IsTriangulated C] in
/-- The autoequivalence of the constructed twist-shaped pair is the supplied one. -/
@[simp]
theorem toTwistShaped_Φ (R : MukaiRealization k C b) : (S.toTwistShaped R).Φ = S.equiv :=
  rfl

/-- The charge of the twisted stability condition is the charge precomposed with the reflection
`ρ_{v(E)}`: the action lemma of the twist-shaped pair that the statement constructs. -/
theorem act_Z (R : MukaiRealization k C b) (σ : StabilityCondition.WithClassMap C R.v)
    (x : Mukai.MukaiLattice N) :
    (AutPairQuot.mk (S.toTwistShaped R).toAutPair • σ).Z x = σ.Z ((S.toTwistShaped R).lam x) :=
  (S.toTwistShaped R).act_Z σ x

end AutoequivalenceStatement

end Statement

end CategoryTheory.Triangulated.SphericalTwist
