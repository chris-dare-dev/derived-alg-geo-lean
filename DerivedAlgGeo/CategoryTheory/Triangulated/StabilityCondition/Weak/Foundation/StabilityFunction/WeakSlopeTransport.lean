/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeTop
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Functorial

/-!
# Transporting weak slope data along an equivalence of abelian categories

`WeakSlopeData A` is two homomorphisms out of `K₀Ab A` together with two sign conditions, so an
equivalence `e : A ≌ B` carries it to `WeakSlopeData B` by precomposing with `K₀Ab.congr e`. This
file does that and records what the transported rank, degree, slope and charge are.

## Why it is needed

Numerical data is written on the category the objects live in. The stability machinery is written
on the heart of a t-structure. `Algebra/Homology/DerivedCategory/Heart.lean` identifies the two for
the canonical t-structure, and this file is what lets a slope defined on the first be read on the
second — the concrete case being the μ-slope of the Gieseker lane, which is defined on coherent
sheaves while the Mukai tilt assembly wants it on a heart.

## The direction to keep straight

`congr` transports *along* `e`, so the transported data on `B` evaluates an object by pulling it
back through `e.inverse`. Both readings are recorded: `congr_rank` is the one that holds by
definition, and `congr_rank_functor` is the one a consumer starting from an object of `A` wants.
Nothing is transported by `rfl` alone — `congr_rank_functor` needs the unit isomorphism, which is
why it is a theorem and not a `simp` unfolding.

## What is not here

The Harder–Narasimhan property is not transported. That is a statement about chains of subobjects
and their cokernels rather than about a homomorphism, so it needs the equivalence to be carried
through `Subobject` and `cokernel`, and it is a separate piece of work.
-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Triangulated

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- An equivalence reflects nonzero objects: the inverse of a nonzero object is nonzero. -/
theorem not_isZero_inverse_obj (e : A ≌ B) {E : B} (hE : ¬IsZero E) :
    ¬IsZero (e.inverse.obj E) := by
  intro hz
  exact hE ((e.functor.map_isZero hz).of_iso (e.counitIso.app E).symm)

namespace WeakSlopeData

variable (D : WeakSlopeData A) (e : A ≌ B)

/-- **Weak slope data transported along an equivalence.**

Both homomorphisms are precomposed with `K₀Ab.congr e` run backwards, so the transported data reads
an object of `B` by pulling it back to `A`. The two sign conditions transport because the pullback
of a nonzero object is nonzero. -/
def congr : WeakSlopeData B where
  rankHom := D.rankHom.comp (K₀Ab.congr e).symm.toAddMonoidHom
  degreeHom := D.degreeHom.comp (K₀Ab.congr e).symm.toAddMonoidHom
  rank_nonneg E := by
    simpa using D.rank_nonneg (e.inverse.obj E)
  degree_nonneg_of_rank_zero E hE hrank := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, K₀Ab.congr_symm_of] at hrank ⊢
    exact D.degree_nonneg_of_rank_zero _ (not_isZero_inverse_obj e hE) hrank

@[simp]
theorem congr_rank (E : B) : (D.congr e).rank E = D.rank (e.inverse.obj E) := by
  simp [congr, rank]

@[simp]
theorem congr_degree (E : B) : (D.congr e).degree E = D.degree (e.inverse.obj E) := by
  simp [congr, degree]

/-- The Grothendieck class of a transported object is the original class. Everything below is this
one equation read through a different homomorphism. -/
theorem congr_symm_of_functor (X : A) :
    (K₀Ab.congr e).symm (K₀Ab.of (e.functor.obj X)) = K₀Ab.of X := by
  rw [K₀Ab.congr_symm_of]
  exact K₀Ab.of_iso (e.unitIso.app X).symm

/-- The reading a consumer starting from an object of `A` wants. It is the unit isomorphism, not
`rfl`. It is deliberately not a `simp` lemma: `congr_rank` already rewrites the left-hand side to
the `e.inverse` form, so both cannot fire. -/
theorem congr_rank_functor (X : A) : (D.congr e).rank (e.functor.obj X) = D.rank X := by
  rw [congr_rank]
  exact D.rank_iso (e.unitIso.app X).symm

theorem congr_degree_functor (X : A) : (D.congr e).degree (e.functor.obj X) = D.degree X := by
  rw [congr_degree]
  exact D.degree_iso (e.unitIso.app X).symm

@[simp]
theorem congr_charge (E : B) : (D.congr e).charge E = D.charge (e.inverse.obj E) := by
  apply Complex.ext <;> simp

theorem congr_charge_functor (X : A) : (D.congr e).charge (e.functor.obj X) = D.charge X := by
  apply Complex.ext
  · simp only [charge_re, congr_degree_functor]
  · simp only [charge_im, congr_rank_functor]

@[simp]
theorem congr_slope (E : B) : (D.congr e).slope E = D.slope (e.inverse.obj E) := by
  simp only [slope, congr_rank, congr_degree]

theorem congr_slope_functor (X : A) : (D.congr e).slope (e.functor.obj X) = D.slope X := by
  simp only [slope, congr_rank_functor, congr_degree_functor]

/-- The honest slope transports too. The two cases are rank zero, where both sides are `⊤`, and
positive rank, where both sides are the coerced ratio. -/
@[simp]
theorem congr_topSlope (E : B) : (D.congr e).topSlope E = D.topSlope (e.inverse.obj E) := by
  have hrank : (D.congr e).rank E = D.rank (e.inverse.obj E) := congr_rank D e E
  rcases eq_or_lt_of_le ((D.congr e).rank_nonneg E) with h | h
  · rw [(D.congr e).topSlope_of_rank_zero h.symm,
      D.topSlope_of_rank_zero (by rw [← hrank]; exact h.symm)]
  · rw [(D.congr e).topSlope_of_rank_pos h,
      D.topSlope_of_rank_pos (by rw [← hrank]; exact h), congr_slope]

theorem congr_topSlope_functor (X : A) :
    (D.congr e).topSlope (e.functor.obj X) = D.topSlope X := by
  have hrank : (D.congr e).rank (e.functor.obj X) = D.rank X := congr_rank_functor D e X
  rcases eq_or_lt_of_le ((D.congr e).rank_nonneg (e.functor.obj X)) with h | h
  · rw [(D.congr e).topSlope_of_rank_zero h.symm,
      D.topSlope_of_rank_zero (by rw [← hrank]; exact h.symm)]
  · rw [(D.congr e).topSlope_of_rank_pos h,
      D.topSlope_of_rank_pos (by rw [← hrank]; exact h), congr_slope_functor]

end WeakSlopeData

end CategoryTheory.Triangulated
