/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Basic

/-!
# Harder--Narasimhan filtrations for owner stability functions

This file owns the finite subobject-chain data attached to an abelian stability
function.  Existence is kept as an explicit property of a stability function;
uniqueness and construction criteria build on this representation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A Harder--Narasimhan filtration of a nonzero object for an abelian
stability function.  It is a strictly increasing finite chain of subobjects
whose successive quotients are semistable with strictly decreasing phases. -/
structure AbelianHNFiltration (Z : StabilityFunction A) (E : A) where
  /-- Number of semistable factors. -/
  n : ℕ
  /-- An HN filtration has at least one factor. -/
  nonempty : 0 < n
  /-- The chain from zero to the whole object. -/
  chain : Fin (n + 1) → Subobject E
  /-- The chain is strictly increasing. -/
  chain_strictMono : StrictMono chain
  /-- The initial term is zero. -/
  chain_bot : chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥
  /-- The final term is the whole object. -/
  chain_top : chain ⟨n, n.lt_succ_iff.mpr le_rfl⟩ = ⊤
  /-- Phases of successive quotients. -/
  phase : Fin n → ℝ
  /-- Successive phases strictly decrease. -/
  phase_strictAnti : StrictAnti phase
  /-- The declared phase is the intrinsic phase of each quotient. -/
  factor_phase : ∀ j : Fin n,
    Z.phase (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ)))) = phase j
  /-- Each successive quotient is semistable. -/
  factor_semistable : ∀ j : Fin n,
    Z.IsSemistable (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ))))

namespace AbelianHNFiltration

/-- The highest HN phase. -/
def phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) : ℝ :=
  F.phase ⟨0, F.nonempty⟩

/-- The lowest HN phase. -/
def phiMinus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) : ℝ :=
  F.phase ⟨F.n - 1, Nat.sub_lt F.nonempty (by decide)⟩

/-- Every factor phase lies between the HN extrema. -/
theorem phase_mem_range {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (i : Fin F.n) :
    F.phiMinus ≤ F.phase i ∧ F.phase i ≤ F.phiPlus := by
  constructor
  · exact F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (by lia))
  · exact F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (by lia))

/-- The lowest HN phase does not exceed the highest. -/
theorem phiMinus_le_phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) : F.phiMinus ≤ F.phiPlus :=
  (F.phase_mem_range ⟨0, F.nonempty⟩).1

end AbelianHNFiltration

namespace StabilityFunction

/-- A stability function has the HN property when every nonzero object admits
an owner HN filtration. -/
def HasHNProperty (Z : StabilityFunction A) : Prop :=
  ∀ E : A, ¬IsZero E → Nonempty (AbelianHNFiltration Z E)

end StabilityFunction

end CategoryTheory.Triangulated
