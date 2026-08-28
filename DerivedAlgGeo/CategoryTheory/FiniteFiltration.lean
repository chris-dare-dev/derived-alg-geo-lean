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

universe v v₂ u u₂

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
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- The short complex presenting the `i`th successive quotient. -/
def step (F : FiniteFiltration C M) (i : Fin F.length) : ShortComplex C :=
  ShortComplex.mk (F.inclusion i) (F.projection i) (F.zero i)

theorem step_shortExact (F : FiniteFiltration C M) (i : Fin F.length) :
    (F.step i).ShortExact :=
  F.shortExact i

/-- Apply an exact functor to every term and every successive quotient of a finite filtration.

This is the common categorical operation used when a geometric filtration is pulled back by a
flat morphism: the geometric leaf only has to identify its pullback functor and the images of the
graded pieces.  Exactness stays here, rather than being rebuilt in each almost-disconnected or
stability-condition consumer. -/
def map (F : FiniteFiltration C M) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    FiniteFiltration D (G.obj M) where
  length := F.length
  object i := G.obj (F.object i)
  inclusion i := G.map (F.inclusion i)
  graded i := G.obj (F.graded i)
  projection i := G.map (F.projection i)
  zero i := by
    rw [← G.map_comp, F.zero i, G.map_zero]
  shortExact i := by
    change ((F.step i).map G).ShortExact
    exact (F.step_shortExact i).map_of_exact G
  initialIsZero := G.map_isZero F.initialIsZero
  terminalIso := G.mapIso F.terminalIso

@[simp]
theorem map_length (F : FiniteFiltration C M) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F.map G).length = F.length :=
  rfl

@[simp]
theorem map_object (F : FiniteFiltration C M) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (i : Fin ((F.map G).length + 1)) :
    (F.map G).object i = G.obj (F.object i) :=
  rfl

@[simp]
theorem map_graded (F : FiniteFiltration C M) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (i : Fin (F.map G).length) :
    (F.map G).graded i = G.obj (F.graded i) :=
  rfl

@[simp]
theorem map_id (F : FiniteFiltration C M) : F.map (𝟭 C) = F := by
  cases F
  rfl

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

@[simp]
theorem map_comp (F : FiniteFiltration C M) (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {E : Type*} [Category E] [HasZeroMorphisms E] (H : D ⥤ E)
    [H.PreservesZeroMorphisms] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    F.map (G ⋙ H) = (F.map G).map H := by
  cases F
  rfl

end FiniteFiltration

end CategoryTheory
