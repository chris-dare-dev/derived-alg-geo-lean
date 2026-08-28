/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finite filtrations in an abelian category

This file records the common categorical root of finite filtrations.  A filtration of `M` has
objects `F 0, ..., F n`, short exact successive-quotient sequences, a proof that `F 0` is zero,
and a chosen identification `F n ≅ M`.

Keeping this root independent of schemes prevents geometric filtrations (for example, the
almost-disconnected filtrations of arXiv:2607.28411, Appendix B) from growing their own
incompatible tower type.
-/

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- A finite filtration of an object by successive short exact sequences.

`object i.castSucc ⟶ object i.succ ⟶ graded i` is the `i`th short exact sequence.  The
endpoint data express `F₀ = 0` and `Fₙ = M` without making either equality definitional. -/
structure FiniteFiltration (M : C) where
  /-- The number of graded pieces. -/
  length : ℕ
  /-- The objects `F₀, ..., Fₙ` in the filtration. -/
  object : Fin (length + 1) → C
  /-- The inclusion `Fᵢ ⟶ Fᵢ₊₁`. -/
  inclusion : ∀ i : Fin length, object i.castSucc ⟶ object i.succ
  /-- The `i`th graded piece `Fᵢ₊₁/Fᵢ`. -/
  graded : Fin length → C
  /-- The quotient projection `Fᵢ₊₁ ⟶ Fᵢ₊₁/Fᵢ`. -/
  projection : ∀ i : Fin length, object i.succ ⟶ graded i
  /-- Consecutive maps compose to zero. -/
  zero : ∀ i, inclusion i ≫ projection i = 0
  /-- Each step realizes its named graded piece as the quotient. -/
  shortExact : ∀ i,
    (ShortComplex.mk (inclusion i) (projection i) (zero i)).ShortExact
  /-- The bottom term is zero. -/
  initialIsZero : IsZero (object 0)
  /-- The top term is the filtered object. -/
  terminalIso : object (Fin.last length) ≅ M

namespace FiniteFiltration

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {M : C}

/-- The short complex presenting the `i`th successive quotient. -/
def step (F : FiniteFiltration C M) (i : Fin F.length) : ShortComplex C :=
  ShortComplex.mk (F.inclusion i) (F.projection i) (F.zero i)

theorem step_shortExact (F : FiniteFiltration C M) (i : Fin F.length) :
    (F.step i).ShortExact :=
  F.shortExact i

end FiniteFiltration

end CategoryTheory
