/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Top exterior powers

This file records the ordinary linear-algebra models for top exterior powers
used by determinant constructions.
-/

universe u

namespace Module

variable (R : Type u) [CommRing R]

/-- The algebraic local model for the determinant of a free rank-`n` module. -/
abbrev topExteriorPower (n : ℕ) := ⋀[R]^n (Fin n → R)

/-- The top exterior power of a free rank-`n` module has rank one. -/
theorem finrank_topExteriorPower [Nontrivial R] (n : ℕ) :
    finrank R (topExteriorPower R n) = 1 := by
  rw [exteriorPower.finrank_eq]
  simp

/-- The unique `n`-element powerset of `ULift (Fin n)` used by the free-module model. -/
def topPowerset (n : ℕ) :
    Set.powersetCard (ULift.{u} (Fin n)) n :=
  ⟨Finset.univ, by simp⟩

@[reducible]
private noncomputable def topPowersetUnique (n : ℕ) :
    Unique (Set.powersetCard (ULift.{u} (Fin n)) n) where
  default := topPowerset n
  uniq s := Subtype.ext (Finset.eq_univ_of_card s.1 (by simpa using s.2))

/-- The top exterior power of a free rank-`n` module is the coefficient ring. -/
noncomputable def topExteriorFreeEquiv (n : ℕ) :
    (⋀[R]^n (ULift.{u} (Fin n) →₀ R)) ≃ₗ[R] R := by
  letI : Unique (Set.powersetCard (ULift.{u} (Fin n)) n) := topPowersetUnique n
  exact ((Finsupp.basisSingleOne (R := R)).exteriorPower n).repr |>.trans
    (Finsupp.uniqueLinearEquiv R R default)

lemma topExteriorFreeEquiv_ιMulti (n : ℕ)
    (x : Fin n → (ULift.{u} (Fin n) →₀ R)) :
    topExteriorFreeEquiv R n (_root_.exteriorPower.ιMulti R n x) =
      (Matrix.of fun i j ↦
        x i (Set.powersetCard.ofFinEmbEquiv.symm
          (topPowerset.{u} n) j)).det := by
  letI : Unique (Set.powersetCard (ULift.{u} (Fin n)) n) := topPowersetUnique n
  rw [topExteriorFreeEquiv]
  change ((Finsupp.basisSingleOne (R := R)).exteriorPower n).repr
      (_root_.exteriorPower.ιMulti R n x) default = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 2

end Module
