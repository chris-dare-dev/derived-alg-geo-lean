/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.

Portions adapted from mattrobball/BridgelandStability, revision 9e48f23
(Apache-2.0, Copyright (c) 2026 Mathlib Contributors); see LICENSE.md.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.PostnikovTower
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Owner-authored Harder--Narasimhan filtrations and slicings

These are the root data structures for the repository-owned stability API.
They are deliberately small: operations on filtrations, interval categories,
local finiteness, and stability conditions are migrated in later slices.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Harder--Narasimhan filtration: a Postnikov tower whose factors have
strictly decreasing phases and lie in their corresponding phase slices. -/
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C)
    extends PostnikovTower C E where
  /-- Phase of each factor. -/
  φ : Fin n → ℝ
  /-- Factor phases are strictly decreasing. -/
  hφ : StrictAnti φ
  /-- Each factor belongs to its recorded phase slice. -/
  semistable : ∀ j, P (φ j) (toPostnikovTower.factor j)

/-- A Bridgeland slicing on a pretriangulated category. -/
structure Slicing where
  /-- Semistable objects of phase `φ`. -/
  P : ℝ → ObjectProperty C
  /-- Phase slices are invariant under isomorphism. -/
  closedUnderIso : ∀ φ, (P φ).IsClosedUnderIsomorphisms
  /-- The zero object belongs to every phase slice. -/
  zero_mem : ∀ φ, P φ (0 : C)
  /-- Shifting by one increases phase by one. -/
  shift_iff : ∀ φ X, P φ X ↔ P (φ + 1) (X⟦(1 : ℤ)⟧)
  /-- Morphisms from higher phase to lower phase vanish. -/
  hom_vanishing : ∀ φ₁ φ₂ A B,
    φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0
  /-- Every object admits an HN filtration. -/
  hn_exists : ∀ E, Nonempty (HNFiltration C P E)

attribute [instance] Slicing.closedUnderIso

@[ext]
theorem Slicing.ext {s t : Slicing C} (hP : s.P = t.P) : s = t := by
  cases s
  cases t
  simp_all

/-- A zero object belongs to every phase slice, not only the chosen zero
object used by the structure field. -/
theorem Slicing.zero_mem_of_isZero (s : Slicing C) (φ : ℝ) (X : C) (hX : IsZero X) :
    s.P φ X :=
  ObjectProperty.prop_of_iso _ ((isZero_zero C).iso hX) (s.zero_mem φ)

/-- Forward form of the shift axiom. -/
theorem Slicing.shift (s : Slicing C) (φ : ℝ) (X : C) (h : s.P φ X) :
    s.P (φ + 1) (X⟦(1 : ℤ)⟧) :=
  (s.shift_iff φ X).mp h

/-- Backward form of the shift axiom. -/
theorem Slicing.unshift (s : Slicing C) (φ : ℝ) (X : C)
    (h : s.P (φ + 1) (X⟦(1 : ℤ)⟧)) : s.P φ X :=
  (s.shift_iff φ X).mpr h

/-- Iterating the slicing axiom shifts a semistable object by a natural
number and adds that number to its phase. -/
theorem Slicing.shift_nat (s : Slicing C) (φ : ℝ) (X : C) (n : ℕ) :
    s.P φ X → s.P (φ + (n : ℝ)) (X⟦(n : ℤ)⟧) := by
  induction n with
  | zero =>
      intro h
      simp only [Nat.cast_zero, add_zero]
      exact (s.P φ).prop_of_iso ((shiftFunctorZero C ℤ).app X).symm h
  | succ n ih =>
      intro h
      have h' := (s.shift_iff (φ + ↑n) ((shiftFunctor C (↑n : ℤ)).obj X)).mp (ih h)
      have phase : φ + ↑n + 1 = φ + (↑(n + 1) : ℝ) := by push_cast; ring
      rw [phase] at h'
      exact (s.P _).prop_of_iso
        ((shiftFunctorAdd' C (↑n : ℤ) 1 ((↑n : ℤ) + 1) (by omega)).app X).symm h'

/-- Inverse form of `Slicing.shift_nat`. -/
theorem Slicing.unshift_nat (s : Slicing C) (φ : ℝ) (X : C) (n : ℕ) :
    s.P (φ + (n : ℝ)) (X⟦(n : ℤ)⟧) → s.P φ X := by
  induction n with
  | zero =>
      intro h
      simp only [Nat.cast_zero, add_zero] at h
      exact (s.P φ).prop_of_iso ((shiftFunctorZero C ℤ).app X) h
  | succ n ih =>
      intro h
      apply ih
      have phase : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
      rw [phase] at h
      have h' := (s.P _).prop_of_iso
        ((shiftFunctorAdd' C (↑n : ℤ) 1 ((↑n : ℤ) + 1) (by omega)).app X) h
      rw [← add_assoc] at h'
      exact (s.shift_iff (φ + ↑n) ((shiftFunctor C (↑n : ℤ)).obj X)).mpr h'

/-- Shifting by any integer adds that integer to the phase. -/
theorem Slicing.shift_int (s : Slicing C) (φ : ℝ) (X : C) (n : ℤ) :
    s.P φ X ↔ s.P (φ + n) (X⟦n⟧) := by
  cases n with
  | ofNat m => exact ⟨s.shift_nat C φ X m, s.unshift_nat C φ X m⟩
  | negSucc m =>
      let addIso :=
        (shiftFunctorAdd' C (Int.negSucc m) ((m + 1 : ℕ) : ℤ) 0 (by omega)).app X
      let zeroIso := (shiftFunctorZero C ℤ).app X
      constructor
      · intro h
        have h₀ := (s.P φ).prop_of_iso zeroIso.symm h
        have h₁ := (s.P φ).prop_of_iso addIso h₀
        have phase : φ = φ + ↑(Int.negSucc m) + ((m + 1 : ℕ) : ℝ) := by
          simp [Int.negSucc_eq]; ring
        rw [phase] at h₁
        exact s.unshift_nat C _ _ (m + 1) h₁
      · intro h
        have h₁ := s.shift_nat C _ _ (m + 1) h
        have phase : φ + ↑(Int.negSucc m) + ((m + 1 : ℕ) : ℝ) = φ := by
          simp [Int.negSucc_eq]; ring
        rw [phase] at h₁
        have h₂ := (s.P φ).prop_of_iso addIso.symm h₁
        exact (s.P φ).prop_of_iso zeroIso h₂

end CategoryTheory.Triangulated
