/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Objects

/-!
# Spherical objects without a Serre functor, and their Euler characteristic

`IsSphericalObject k n E` says `Hom(E, E⟦i⟧)` vanishes off `{0, n}` and is the base field at both.
From it, `chiHom_self_eq` computes `χ(E,E) = 1 + (-1)ⁿ`, and at `n = 2` that discharges the
hypothesis `χ(E,E) = 2` which the spherical twist's involutivity consumes — so a caller holding a
spherical object no longer supplies it by hand.

## Why a second sphericity predicate, and how it relates to the first

`SerreFunctor/Objects.lean` already has `SerreFunctor.IsSphericalObject D n E`, relative to a chosen
Serre functor, carrying a fourth clause `S(E) ≅ E⟦n⟧`. This one is deliberately **weaker**: a
general `k`-linear pretriangulated category has no Serre functor at all, and the Euler computation
needs none. Rather than leave two parallel predicates, `of_serreFunctor` projects the Serre-relative
one onto this one, so the Euler computation proved here is available there too. The projection is
one-way and must stay so: nothing here reconstructs a Serre functor.

## Trap: `n = 0` makes the Euler computation false, not vacuous

The structure is perfectly inhabitable at `n = 0` — `vanishing`'s two side conditions collapse into
one, the support is `{0}`, and `end_one` and `top_one` say the same thing up to `shiftFunctor 0`.
There `χ(E,E) = 1`, while `1 + (-1)⁰ = 2`. So `chiHom_self_eq` **without** `hn : n ≠ 0` is false
rather than vacuous, and an implementer who drops the hypothesis is left with an unprovable goal —
or closes it by silently strengthening the structure, which is worse. The hypothesis is what makes
`{0, n}` a two-element set so the sum splits. The degenerate value is recorded separately as
`chiHom_self_eq_one_of_zero`.

## Trap: the spelling of the vanishing clause

`vanishing` reads `∀ f : E ⟶ E⟦i⟧, f = 0`, and must not read `IsZero (E ⟶ E⟦i⟧)`. That Hom is a
bare `Type`; `IsZero` there demands an object both initial and terminal, and `Type` has none, so the
field would be unsatisfiable, the structure uninhabitable, and every theorem below vacuously true —
while compiling and passing every gate. `AlgebraicGeometry/Surface/Spherical.lean` records the same
trap; the spelling is copied from it deliberately.

## What is not here

No Serre-duality argument deriving `top_one` from `end_one`: the two clauses stay independent, as
they do in the K3-specific profile. The twist itself, the Mukai lattice and the braid relation are
their own files.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits Module

namespace CategoryTheory.Triangulated.SphericalTwist

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]

/-- **An `n`-spherical object**, with no Serre functor in sight. -/
structure IsSphericalObject (k : Type w) [Field k] [Linear k C] (n : ℤ) (E : C) : Prop where
  /-- `Hom(E, E⟦i⟧) = 0` away from degrees `0` and `n`. Stated as "every morphism is zero"; see
  the trap in the module docstring. -/
  vanishing : ∀ i : ℤ, i ≠ 0 → i ≠ n → ∀ f : E ⟶ E⟦i⟧, f = 0
  /-- `End(E) ≅ k`: the object is simple. -/
  end_one : Nonempty ((E ⟶ E) ≃ₗ[k] k)
  /-- `Hom(E, E⟦n⟧) ≅ k`. Independent of `end_one` at this generality. -/
  top_one : Nonempty ((E ⟶ E⟦n⟧) ≃ₗ[k] k)

namespace IsSphericalObject

variable {n : ℤ} {E F : C} (h : IsSphericalObject k n E)

include h

/-- A spherical object is nonzero: a zero object has a subsingleton endomorphism space, and
`end_one` would make the field one too. -/
theorem not_isZero : ¬IsZero E := by
  intro hE
  have hsub : Subsingleton (E ⟶ E) := ⟨fun f g ↦ hE.eq_of_src f g⟩
  have : Subsingleton k := h.end_one.some.toEquiv.symm.subsingleton
  exact (not_subsingleton k) this

theorem finrank_end : finrank k (E ⟶ E) = 1 := by
  rw [h.end_one.some.finrank_eq, finrank_self]

theorem finrank_top : finrank k (E ⟶ E⟦n⟧) = 1 := by
  rw [h.top_one.some.finrank_eq, finrank_self]

theorem finrank_hom_eq_zero (i : ℤ) (hi₀ : i ≠ 0) (hin : i ≠ n) :
    finrank k (E ⟶ E⟦i⟧) = 0 := by
  have : Subsingleton (E ⟶ E⟦i⟧) :=
    ⟨fun f g ↦ by rw [h.vanishing i hi₀ hin f, h.vanishing i hi₀ hin g]⟩
  exact finrank_zero_of_subsingleton

/-- `Hom(E, E⟦0⟧)` is the base field too. The zero shift is not syntactically the identity, so
the endomorphism statement does not apply to it directly. -/
theorem finrank_shift_zero : finrank k (E ⟶ (shiftFunctor C (0 : ℤ)).obj E) = 1 := by
  have e : (E ⟶ (shiftFunctor C (0 : ℤ)).obj E) ≃ₗ[k] (E ⟶ E) :=
    Linear.homCongr k (Iso.refl E) ((shiftFunctorZero C ℤ).app E)
  rw [e.finrank_eq, h.finrank_end]

/-- Sphericity transports along an isomorphism. -/
theorem of_iso (e : E ≅ F) : IsSphericalObject k n F where
  vanishing i hi₀ hin f := by
    have := h.vanishing i hi₀ hin (e.hom ≫ f ≫ (shiftFunctor C i).map e.inv)
    have he : f = e.inv ≫ (e.hom ≫ f ≫ (shiftFunctor C i).map e.inv) ≫
        (shiftFunctor C i).map e.hom := by
      simp [← Functor.map_comp]
    rw [he, this, zero_comp, comp_zero]
  end_one := ⟨(Linear.homCongr k e e).symm.trans h.end_one.some⟩
  top_one := ⟨(Linear.homCongr k e ((shiftFunctor C n).mapIso e)).symm.trans h.top_one.some⟩

end IsSphericalObject

section Euler

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {n : ℤ} {E : C}

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- **The Euler characteristic of a spherical object**, `χ(E,E) = 1 + (-1)ⁿ`.

The support of `i ↦ (-1)ⁱ · dim Hom(E, E⟦i⟧)` sits inside `{0, n}`, so the `finsum` is a two-term
sum — and it is two terms only because `n ≠ 0`. See the trap in the module docstring: without `hn`
the statement is false at `n = 0`, not vacuous.

No `HomFiniteBounded` hypothesis: sphericity bounds the support by itself. -/
theorem chiHom_self_eq (h : IsSphericalObject k n E) (hn : n ≠ 0) :
    chiHom k C E E = 1 + (n.negOnePow : ℤ) := by
  have hsupp : (Function.support fun i : ℤ ↦ (i.negOnePow : ℤ) * finrank k (E ⟶ E⟦i⟧)) ⊆
      (({0, n} : Finset ℤ) : Set ℤ) := by
    intro i hi
    by_contra hmem
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hmem
    exact hi (by simp [h.finrank_hom_eq_zero i hmem.1 hmem.2])
  have hsum : chiHom k C E E =
      ∑ i ∈ ({0, n} : Finset ℤ), (i.negOnePow : ℤ) * finrank k (E ⟶ E⟦i⟧) :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  simp [Finset.sum_pair (Ne.symm hn), h.finrank_shift_zero, h.finrank_top]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The degenerate value the hypothesis of `chiHom_self_eq` rules out. -/
theorem chiHom_self_eq_one_of_zero (h : IsSphericalObject k (0 : ℤ) E) :
    chiHom k C E E = 1 := by
  have hsupp : (Function.support fun i : ℤ ↦ (i.negOnePow : ℤ) * finrank k (E ⟶ E⟦i⟧)) ⊆
      (({0} : Finset ℤ) : Set ℤ) := by
    intro i hi
    by_contra hmem
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hmem
    exact hi (by simp [h.finrank_hom_eq_zero i hmem hmem])
  have hsum : chiHom k C E E =
      ∑ i ∈ ({0} : Finset ℤ), (i.negOnePow : ℤ) * finrank k (E ⟶ E⟦i⟧) :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  simp [h.finrank_shift_zero]

section K₀

variable [HomFiniteBounded k C] [∀ m : ℤ, (shiftFunctor C m).Linear k] [IsTriangulated C]

omit [IsTriangulated C] in
/-- **`χ(E,E) = 2` for a `2`-spherical object.** This is the exact hypothesis the spherical
twist's involutivity consumes, discharged rather than assumed. -/
theorem chiK₀_of_self_eq_two (h : IsSphericalObject k (2 : ℤ) E) :
    chiK₀ k C (K₀.of C E) (K₀.of C E) = 2 := by
  rw [chiK₀_of_of, chiHom_self_eq h two_ne_zero,
    show (2 : ℤ) = 2 * 1 by norm_num, Int.negOnePow_two_mul]
  norm_num

namespace IsSphericalObject

omit [IsTriangulated C] in
/-- The twist on `K₀` is involutive at a `2`-spherical object. -/
theorem twistK₀_involutive (h : IsSphericalObject k (2 : ℤ) E) :
    Function.Involutive (twistK₀ k C E) :=
  SphericalTwist.twistK₀_involutive k C (chiK₀_of_self_eq_two h)

omit [IsTriangulated C] in
/-- The twist on `K₀` is bijective at a `2`-spherical object. -/
theorem twistK₀_bijective (h : IsSphericalObject k (2 : ℤ) E) :
    Function.Bijective (twistK₀ k C E) :=
  SphericalTwist.twistK₀_bijective k C (chiK₀_of_self_eq_two h)

end IsSphericalObject

end K₀

end Euler

/-- **The Serre-relative predicate projects onto this one.**

One direction only, and it must stay so: this predicate has no Serre functor, so nothing here
reconstructs the `S(E) ≅ E⟦n⟧` clause that is dropped. -/
theorem IsSphericalObject.of_serreFunctor {D : SerreFunctor.SerreFunctorData k C} {m : ℕ} {E : C}
    (h : SerreFunctor.IsSphericalObject D m E) : IsSphericalObject k (m : ℤ) E where
  vanishing := h.vanishing
  end_one := h.end_one
  top_one := h.top_one

end CategoryTheory.Triangulated.SphericalTwist
