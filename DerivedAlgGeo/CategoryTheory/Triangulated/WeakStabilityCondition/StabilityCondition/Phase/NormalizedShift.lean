/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# Normalized phase shifts

The universal cover `G̃L⁺(2, ℝ)` is standardly presented as pairs `(T, f)`
with `T ∈ GL⁺(2, ℝ)` and `f : ℝ ≃o ℝ` satisfying `f (φ + 1) = f φ + 1`,
subject to `T` and `f` inducing the same map on `S¹`. This file builds the
phase-relabeling factor `f` as a self-contained mathematical object.

The `f` component acts on slicings by relabelling phases; the `T` component
acts on central charges. Splitting them exposes the algebraic and analytic
properties of phase relabelling independently.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

/-- An order-isomorphism of `ℝ` commuting with `φ ↦ φ + 1`.

The phase-relabelling half of an element of `G̃L⁺(2, ℝ)`. The `φ + 1`
equivariance is what makes it descend to the circle `ℝ / 2ℤ`, and it is why
the shift functor `[1]` interacts with the action the way §8 needs.

**On `≃o` rather than "increasing".** Bridgeland §8 asks only for an
*increasing* `f` with `f(φ + 1) = f(φ) + 1`, and a priori that is weaker:
`φ ↦ ⌊φ⌋ + (φ - ⌊φ⌋)/2` is strictly increasing and `+1`-equivariant but is not
a bijection. The narrowing is harmless because pairing with an *invertible* `T`
forces bijectivity — but that forcing happens in `GLTilde`, not here, so this
structure on its own is strictly narrower than the paper's phrase. -/
structure NormalizedShift where
  /-- The underlying increasing bijection of `ℝ`. -/
  toOrderIso : ℝ ≃o ℝ
  /-- Equivariance for the unit shift. -/
  map_add_one : ∀ φ : ℝ, toOrderIso (φ + 1) = toOrderIso φ + 1

namespace NormalizedShift

variable {f g : NormalizedShift}

/-- A normalized shift is determined by its underlying order-isomorphism.

`map_add_one` is a `Prop`, so it carries no data to disagree about. -/
theorem toOrderIso_injective :
    Function.Injective NormalizedShift.toOrderIso := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  subst h
  rfl

@[ext]
theorem ext' (h : ∀ φ, f.toOrderIso φ = g.toOrderIso φ) : f = g := by
  apply toOrderIso_injective
  exact DFunLike.ext _ _ h

/-- The inverse of a normalized shift is again `+1`-equivariant.

Apply `f` to both sides and use injectivity: this is the only step of the
group structure that is not immediate from composition. -/
theorem symm_map_add_one (f : NormalizedShift) (ψ : ℝ) :
    f.toOrderIso.symm (ψ + 1) = f.toOrderIso.symm ψ + 1 := by
  apply f.toOrderIso.injective
  rw [OrderIso.apply_symm_apply, f.map_add_one, OrderIso.apply_symm_apply]

/-- Normalized shifts form a group under composition.

The phase-relabelling factor of `G̃L⁺(2, ℝ)` is a group in its own right,
before pairing it with `GL⁺(2, ℝ)`. -/
instance group : Group NormalizedShift where
  mul f g :=
    { toOrderIso := g.toOrderIso.trans f.toOrderIso
      map_add_one := fun φ => by
        simp only [OrderIso.trans_apply, g.map_add_one, f.map_add_one] }
  one :=
    { toOrderIso := OrderIso.refl ℝ
      map_add_one := fun _ => rfl }
  inv f :=
    { toOrderIso := f.toOrderIso.symm
      map_add_one := f.symm_map_add_one }
  mul_assoc _ _ _ := by ext φ; rfl
  one_mul _ := by ext φ; rfl
  mul_one _ := by ext φ; rfl
  inv_mul_cancel f := by
    ext φ
    exact f.toOrderIso.symm_apply_apply φ

@[simp]
theorem mul_apply (f g : NormalizedShift) (φ : ℝ) :
    (f * g).toOrderIso φ = f.toOrderIso (g.toOrderIso φ) := rfl

@[simp]
theorem one_apply (φ : ℝ) : (1 : NormalizedShift).toOrderIso φ = φ := rfl

@[simp]
theorem inv_apply (f : NormalizedShift) (φ : ℝ) :
    f⁻¹.toOrderIso φ = f.toOrderIso.symm φ := rfl

end NormalizedShift

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
