/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Mukai
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap

/-!
# A twist-shaped autoequivalence acts on stability conditions by the reflection

This connects the lattice half of the spherical-twist lane to the stability machinery: an
autoequivalence whose action on `K₀` is the twist `τ_E` becomes a group element acting on
`WithClassMap C v`, and that action is transport along the Mukai reflection `ρ_{v(E)}`.

It is the precise form of "the spherical twist acts on `Stab(X)` through the reflection" that is
available **before** the twist is constructed.

## Nothing here constructs a twist

`TwistShaped` is supplied data and is named to say so. It carries an autoequivalence together with
the hypothesis that its `K₀` action *is* `twistK₀`. That is the property `T_E` will have once it
exists; building `T_E` is a separate lane, and no inhabitant of `TwistShaped` is produced here.

## Two things not to conclude

**The quotient is not `Aut(D)`.** `AutPairQuot` quotients by a bare natural isomorphism of
underlying functors, leaving the `CommShift` datum unconstrained, so it is a priori *coarser* than
exact autoequivalences up to isomorphism of exact functors. `Slicing/Quotient.lean` says this
explicitly. No statement here is about `Aut(Dᵇ(X))`.

**The order-two statement is about the lattice, not the functor.** `reflect_reflect` makes `lam`
an involution, so the class of a twist-shaped pair squares to one whose lattice part is the
identity. It does **not** follow that `T_E` has order two in any automorphism group — it does not;
`T_E` has infinite order. `τ_E` being an involution on `K₀` says nothing about the functor.

## Why `[IsTriangulated C]` is in the variable block

`GroupAction.AutPair` is declared under a section carrying it, so it does not arrive from the
sphericity hypotheses: `chiK₀` and `twistK₀` need only the pretriangulated structure, and
`EulerForm.lean`'s variable list omits it. Leaving it out makes `AutPair` fail to elaborate here
for a reason that looks unrelated to the mathematics.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

namespace CategoryTheory.Triangulated.SphericalTwist

variable {k : Type w} [DivisionRing k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k] [HomFiniteBounded k C]
variable {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **An autoequivalence shaped like the twist at `E`.**

Supplied, not constructed: the `K₀` action is *asserted* to be `twistK₀`. `Φ` is a `TriEquiv`
rather than a bare `C ≌ C` precisely so that its additivity, shift-compatibility and
triangulatedness travel as instances, which is what makes `K₀.map Φ.e.functor` well-formed. -/
structure TwistShaped (R : MukaiRealization k C b) (E : C) where
  /-- The autoequivalence, with its instances alongside. -/
  Φ : TriEquiv C
  /-- Its action on `K₀` is the twist. This is the whole content of "twist-shaped". -/
  map_eq : K₀.map Φ.e.functor = twistK₀ k C E
  /-- Sphericity, in the only form this file needs. -/
  chi_self : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2

namespace TwistShaped

variable {R : MukaiRealization k C b} {E : C} (T : TwistShaped R E)

include T

omit [IsTriangulated C] in
/-- **The inverse acts by the twist too.**

Not free, and not waved at. `K₀.map_congr` on the unit isomorphism upgrades "`Φ⁻¹ ∘ Φ` is
naturally isomorphic to the identity" into an equality of maps on `K₀`; composing that with
`map_eq` and involutivity of `twistK₀` identifies the inverse's action. -/
theorem map_inverse_eq : K₀.map T.Φ.e.inverse = twistK₀ k C E := by
  have hid : (K₀.map T.Φ.e.inverse).comp (K₀.map T.Φ.e.functor) = AddMonoidHom.id (K₀ C) := by
    rw [← K₀.map_comp, K₀.map_congr T.Φ.e.unitIso.symm, K₀.map_id]
  refine AddMonoidHom.ext fun x ↦ ?_
  have hx : K₀.map T.Φ.e.inverse (twistK₀ k C E (twistK₀ k C E x)) = twistK₀ k C E x := by
    have := DFunLike.congr_fun hid (twistK₀ k C E x)
    rwa [AddMonoidHom.coe_comp, Function.comp_apply, T.map_eq] at this
  rwa [twistK₀_twistK₀ k C T.chi_self x] at hx

omit [IsTriangulated C] in
/-- The Mukai vector of `E` is spherical, from `chi_self` through the realization. -/
theorem isSpherical_v : Mukai.IsSpherical b (R.v (K₀.of C E)) := by
  have h := R.chi_eq_neg_pairing (K₀.of C E) (K₀.of C E)
  rw [T.chi_self] at h
  rw [Mukai.IsSpherical, Mukai.selfPairing]
  omega

/-- The lattice automorphism attached to a twist-shaped pair: the Mukai reflection in `v(E)`. -/
noncomputable def lam : Mukai.MukaiLattice N ≃+ Mukai.MukaiLattice N :=
  (Mukai.reflectEquiv b (R.v (K₀.of C E)) T.isSpherical_v).toAddEquiv

omit [IsTriangulated C] in
/-- **The compatibility `AutPair` asks for.** `v ∘ K₀(Φ⁻¹) = ρ ∘ v`, which is `map_inverse_eq`
followed by `map_twistK₀`. -/
theorem compat (x : K₀ C) : R.v (K₀.map T.Φ.e.inverse x) = T.lam (R.v x) := by
  rw [T.map_inverse_eq, R.map_twistK₀ E x]
  rfl

/-- **The group element.** -/
noncomputable def toAutPair : AutPair R.v where
  Φ := T.Φ
  lam := T.lam
  compat := T.compat

omit [IsTriangulated C] in
@[simp]
theorem toAutPair_lam : (T.toAutPair).lam = T.lam := rfl

omit [IsTriangulated C] in
@[simp]
theorem toAutPair_Φ : (T.toAutPair).Φ = T.Φ := rfl

/-- **The action is transport along the reflection.** The existing `actStabAut` is reused, not
restated; this records that the group element built here is the one that transport describes. -/
theorem act_eq (σ : StabilityCondition.WithClassMap C R.v) :
    AutPairQuot.mk T.toAutPair • σ =
      actStabAut T.Φ.e R.v T.lam.toAddMonoidHom T.compat σ :=
  rfl

/-- The slicing moves by the autoequivalence. Reuses the existing `simp` lemma. -/
theorem act_slicing (σ : StabilityCondition.WithClassMap C R.v) :
    (AutPairQuot.mk T.toAutPair • σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing T.Φ.e :=
  rfl

/-- The charge is precomposed with the reflection. -/
theorem act_Z (σ : StabilityCondition.WithClassMap C R.v) (x : Mukai.MukaiLattice N) :
    (AutPairQuot.mk T.toAutPair • σ).Z x = σ.Z (T.lam x) :=
  rfl

omit [IsTriangulated C] in
/-- **The order-two statement, at the level the quotient supports.**

The lattice part of the square is the identity, by `reflect_reflect`. Read the module docstring
before generalising this: it is a statement about `lam`, not about `Φ`, and `T_E` does not have
order two in any automorphism group. -/
theorem lam_lam (x : Mukai.MukaiLattice N) : T.lam (T.lam x) = x :=
  Mukai.reflect_reflect b _ T.isSpherical_v x

end TwistShaped

end CategoryTheory.Triangulated.SphericalTwist
