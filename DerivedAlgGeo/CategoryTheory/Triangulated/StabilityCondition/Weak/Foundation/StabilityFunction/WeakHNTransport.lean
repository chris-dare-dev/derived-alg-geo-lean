/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeTransport

/-!
# Transporting Harder–Narasimhan filtrations

`WeakSlopeTransport.lean` moves the slope data along an equivalence of abelian categories. This
file moves the filtrations, and therefore `HasHNProperty` itself, which is the point of the
exercise: an existence theorem proved on one category becomes an existence theorem on any
equivalent one.

## Why this is not automatic

A filtration is not a homomorphism. It is a strictly increasing chain of subobjects from bottom to
top, together with the slope and the semistability of the cokernel of each step. So three things
have to move, and each needs its own input:

* the chain, by `Subobject.mapEquivalence` — an order isomorphism, so strictness and the two
  endpoints survive, which a merely monotone map would not give;
* the factors, by `Subobject.cokernelOfLEMapFunctorIso` — the factors are cokernels of chain steps,
  not subobjects;
* the slopes and semistability of those factors, by `congr_topSlope_functor` and
  `congr_isSemistable`.

## The last step

Transporting a filtration of `Z` produces a filtration of `e.functor.obj Z`, but `HasHNProperty`
on the target category asks for a filtration of an arbitrary object `E`. Taking `Z` to be
`e.inverse.obj E` leaves a counit isomorphism to cross, so a filtration must also move along an
isomorphism of the object it filters. `AbelianWeakHNFiltration.ofIso` in `WeakTruncation.lean`
already does exactly that, and is reused rather than rebuilt.
-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Triangulated

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace WeakSlopeData

variable (D : WeakSlopeData A) (e : A ≌ B)
  [e.functor.PreservesMonomorphisms] [e.inverse.PreservesMonomorphisms]

/-- **A filtration transported along an equivalence.**

The chain is the image of the chain under the order isomorphism on subobject lattices; the slope
vector is unchanged; the factors are identified with the images of the original factors, which is
what `Subobject.cokernelOfLEMapFunctorIso` supplies. -/
def congrFiltration {Z : A}
    (G : AbelianWeakHNFiltration D.toWeakStabilityFunction Z) :
    AbelianWeakHNFiltration (D.congr e).toWeakStabilityFunction (e.functor.obj Z) where
  n := G.n
  nonempty := G.nonempty
  chain := fun j ↦ Subobject.mapEquivalence e Z (G.chain j)
  chain_strictMono := (Subobject.mapEquivalence e Z).strictMono.comp G.chain_strictMono
  chain_bot := by
    rw [G.chain_bot]
    exact (Subobject.mapEquivalence e Z).map_bot
  chain_top := by
    rw [G.chain_top]
    exact (Subobject.mapEquivalence e Z).map_top
  μ := G.μ
  μ_anti := G.μ_anti
  factor_slope := fun j ↦ by
    rw [← G.factor_slope j]
    refine Eq.trans ((D.congr e).toWeakStabilityFunction.slope_eq_of_iso
      (Subobject.cokernelOfLEMapFunctorIso e.functor
        (le_of_lt (G.chain_strictMono (Fin.castSucc_lt_succ (i := j)))))) ?_
    exact congr_topSlope_functor D e _
  factor_semistable := fun j ↦
    (D.congr e).toWeakStabilityFunction.isSemistable_of_iso
      (Subobject.cokernelOfLEMapFunctorIso e.functor
        (le_of_lt (G.chain_strictMono (Fin.castSucc_lt_succ (i := j))))).symm
      (congr_isSemistable D e (G.factor_semistable j))

@[simp]
theorem congrFiltration_n {Z : A}
    (G : AbelianWeakHNFiltration D.toWeakStabilityFunction Z) :
    (D.congrFiltration e G).n = G.n := rfl

@[simp]
theorem congrFiltration_μ {Z : A}
    (G : AbelianWeakHNFiltration D.toWeakStabilityFunction Z) :
    (D.congrFiltration e G).μ = G.μ := rfl

/-- **The Harder–Narasimhan property transports along an equivalence.**

This is the payoff. Filter the pullback of the object, transport the filtration, and cross the
counit isomorphism with `ofIso`. -/
theorem congr_hasHNProperty (h : D.toWeakStabilityFunction.HasHNProperty) :
    (D.congr e).toWeakStabilityFunction.HasHNProperty := by
  intro E hE
  obtain ⟨G⟩ := h (e.inverse.obj E) (not_isZero_inverse_obj e hE)
  exact ⟨(D.congrFiltration e G).ofIso (e.counitIso.app E)⟩

end WeakSlopeData

end CategoryTheory.Triangulated
