/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Basic

/-!
# Exceptional objects in a k-linear pretriangulated category

An object `E` is **exceptional** when it has no self-maps into a nonzero
shift and its endomorphism ring is exactly the base field. This file defines
the predicate and proves the theorems that consume each clause, so that
neither clause ships as decoration: every endomorphism is a scalar multiple
of the identity, an exceptional object is nonzero, its endomorphism ring has
no idempotents besides `0` and `1`, it is not isomorphic to any nonzero shift
of itself, and every map between two distinct shifts of it vanishes.

## Why `algebraMap` bijectivity rather than a bundled isomorphism

The endomorphism clause is `Function.Bijective (algebraMap k (End E))`,
against Mathlib's `Algebra k (End E)` instance from
`Mathlib/CategoryTheory/Linear/Basic.lean`. Bijectivity is
proposition-valued, so two proofs of exceptionality of the same object are
equal and no second carrier appears; a bundled `k ≃ₐ[k] End E` would be data.
Per `docs/architecture/abstraction-tree.md`, no `KLinearCategory` or other
new linearity class is introduced — Mathlib's `Preadditive` and `Linear`
carry everything.

## The trap the vanishing clause avoids

The clause is `∀ f : E ⟶ E⟦n⟧, f = 0`, never `IsZero (E ⟶ E⟦n⟧)` on a bare
`Type`: the latter would compile, pass every gate, and make the structure
uninhabitable, because `IsZero` there speaks about a zero object of `Type`,
not about the zero morphism.

## Transport hypotheses are assumptions at this pin

`IsExceptional.shift` carries `[∀ n : ℤ, (shiftFunctor C n).Linear k]`
explicitly: `k`-linearity of the shift is not derivable from
`[Linear k C] [Pretriangulated C]` at this pin —
`Mathlib/CategoryTheory/Shift/Linear.lean:30` carries the same instance
argument, and the only global instances of that shape in the library are for
`DerivedCategory` and for localizations. Without it the ring isomorphism
`End (E⟦m⟧) ≅ End E` is not a `k`-algebra map and bijectivity of `algebraMap`
does not transport. `of_equivalence` likewise assumes `[e.functor.Linear k]`.

## Main definitions

* `IsExceptional` — the predicate. Its fields consume only
  `[Preadditive C] [Linear k C] [HasShift C ℤ]`, so the predicate is statable
  before a category's triangulation is assembled; the pretriangulated setting
  of the title is where the notion lives mathematically, not a requirement of
  the definition.

## Main results

* `IsExceptional.end_eq_smul_id`, `IsExceptional.not_isZero`,
  `IsExceptional.end_eq_zero_or_eq_one_of_mul_self` — the endomorphism clause
  at work: scalars, nonvanishing, and indecomposability in element form.
* `IsExceptional.not_nonempty_iso_shift`,
  `IsExceptional.hom_shift_shift_eq_zero` — both clauses at work: no shift
  periodicity, and vanishing between distinct shifts.
* `IsExceptional.shift`, `IsExceptional.of_equivalence` — transport.
* `CategoryTheory.algebraMap_end_apply` — the `smul` unfolding of
  `algebraMap` into an endomorphism ring, a pure linear-category fact.

## References

* Bondal, *Representations of associative algebras and coherent sheaves*,
  Izv. Akad. Nauk SSSR (1989), for the notion of an exceptional object.
* Huybrechts, *Fourier–Mukai Transforms in Algebraic Geometry*, §1.4.

## Tags

exceptional object, semiorthogonal decomposition, linear category
-/

universe u v

namespace CategoryTheory

/-- The `algebraMap` into an endomorphism ring, unfolded to the `smul` form
every later proof works with. A pure linear-category fact — no shift or
triangulation enters — discharged from `Algebra.algebraMap_eq_smul_one` and
`End.one_def`. -/
theorem algebraMap_end_apply {C : Type u} [Category.{v} C] [Preadditive C]
    {R : Type*} [CommSemiring R] [Linear R C] (c : R) (E : C) :
    algebraMap R (End E) c = c • 𝟙 E := by
  rw [Algebra.algebraMap_eq_smul_one, End.one_def]
  rfl

namespace Triangulated

open CategoryTheory.Limits

variable (k : Type*) [Field k] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasShift C ℤ]

/-- An **exceptional object**: no self-maps into a nonzero shift, and
endomorphism ring exactly the base field. See the module docstring for why
the second clause is `algebraMap` bijectivity rather than a bundled algebra
isomorphism, and why the first is `∀ f, f = 0` rather than an `IsZero`. -/
structure IsExceptional (E : C) : Prop where
  /-- Every self-map into a nonzero shift vanishes. -/
  hom_shift_eq_zero : ∀ n : ℤ, n ≠ 0 → ∀ f : E ⟶ E⟦n⟧, f = 0
  /-- The base field exhausts the endomorphism ring. -/
  algebraMap_bijective : Function.Bijective (algebraMap k (End E))

variable {k}

namespace IsExceptional

variable {E : C} (h : IsExceptional k E)

include h

/-- Every endomorphism of an exceptional object is a scalar multiple of the
identity — surjectivity of `algebraMap`, read through
`algebraMap_end_apply`. -/
theorem end_eq_smul_id (f : End E) : ∃ c : k, f = c • 𝟙 E := by
  obtain ⟨c, hc⟩ := h.algebraMap_bijective.2 f
  exact ⟨c, by rw [← hc, algebraMap_end_apply]⟩

/-- An exceptional object is nonzero: a zero object has `End = 0`, so
`algebraMap` would identify `1` and `0` in `k`, against injectivity. -/
theorem not_isZero : ¬ IsZero E := by
  intro hE
  have h10 : algebraMap k (End E) 1 = algebraMap k (End E) 0 := by
    rw [algebraMap_end_apply, algebraMap_end_apply, one_smul, zero_smul]
    exact hE.eq_of_src _ _
  exact one_ne_zero (h.algebraMap_bijective.1 h10)

-- Named `end_…` deliberately: `EnumDecls.lean`'s `.eq_` filter drops any
-- component starting `eq_` (#998), so the issue's spelling
-- `eq_zero_or_eq_one_of_mul_self` would silently vanish from the declaration
-- sweep and escape the audit-completeness gate.
/-- The endomorphism ring of an exceptional object has no idempotents besides
`0` and `1`: transport the idempotent along the algebra bijection and use
that a field has only trivial idempotents. This is indecomposability in the
element form a mutation or decomposition argument consumes; no abstract
`Indecomposable` class is introduced, because nothing here would inhabit
it. -/
theorem end_eq_zero_or_eq_one_of_mul_self (e : End E) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨c, hc⟩ := h.algebraMap_bijective.2 e
  have hcc : c * c = c := h.algebraMap_bijective.1 (by rw [map_mul, hc]; exact he)
  rcases mul_eq_zero.1
      (show c * (c - 1) = 0 by rw [mul_sub, mul_one, hcc, sub_self]) with h0 | h1
  · exact Or.inl (by rw [← hc, h0, map_zero])
  · exact Or.inr (by rw [← hc, sub_eq_zero.mp h1, map_one])

/-- An exceptional object is not isomorphic to any nonzero shift of itself:
the forward half of such an isomorphism vanishes by the shift clause, so
`𝟙 E = e.hom ≫ e.inv = 0` and `E` is zero, against `not_isZero`. -/
theorem not_nonempty_iso_shift (n : ℤ) (hn : n ≠ 0) : ¬ Nonempty (E ≅ E⟦n⟧) := by
  rintro ⟨e⟩
  refine h.not_isZero ((IsZero.iff_id_eq_zero E).mpr ?_)
  rw [← e.hom_inv_id, h.hom_shift_eq_zero n hn e.hom, zero_comp]

/-- Every map between two distinct shifts of an exceptional object vanishes.
Obtained by transporting to `E ⟶ E⟦b - a⟧` along the shift by `-a`; this
needs only that `shiftFunctor C (-a)` is an equivalence, not linearity or
additivity, and it is the exact form the collection layer consumes. -/
theorem hom_shift_shift_eq_zero (a b : ℤ) (hab : a ≠ b) (f : E⟦a⟧ ⟶ E⟦b⟧) :
    f = 0 := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h0 :
      (shiftFunctorZero C ℤ).inv.app E ≫
        (shiftFunctorAdd' C a (-a) 0 (add_neg_cancel a)).hom.app E ≫
          (shiftFunctor C (-a)).map f ≫
            (shiftFunctorAdd' C b (-a) (b - a) (sub_eq_add_neg b a).symm).inv.app E
        = 0 :=
    h.hom_shift_eq_zero (b - a) hne _
  have h1 := (cancel_epi ((shiftFunctorZero C ℤ).inv.app E)).1
    (h0.trans comp_zero.symm)
  have h2 := (cancel_epi
      ((shiftFunctorAdd' C a (-a) 0 (add_neg_cancel a)).hom.app E)).1
    (h1.trans comp_zero.symm)
  have h3 := (cancel_mono
      ((shiftFunctorAdd' C b (-a) (b - a) (sub_eq_add_neg b a).symm).inv.app E)).1
    (h2.trans zero_comp.symm)
  exact (shiftFunctor C (-a)).map_injective
    (h3.trans ((shiftFunctor C (-a)).map_zero _ _).symm)

/-- Exceptionality transports along shifts. `k`-linearity of the shift is an
explicit hypothesis at this pin — see the module docstring — because without
it `algebraMap` bijectivity does not move: the transport identifies
`algebraMap` into `End (E⟦m⟧)` with the shift functor's action on `End E`,
which is a `k`-algebra map only when the functor is `k`-linear. -/
theorem shift [∀ n : ℤ, (shiftFunctor C n).Linear k] (m : ℤ) :
    IsExceptional k (E⟦m⟧) := by
  have hcomp : ∀ c : k,
      algebraMap k (End (E⟦m⟧)) c = (shiftFunctor C m).map (algebraMap k (End E) c) := by
    intro c
    rw [algebraMap_end_apply, algebraMap_end_apply, Functor.Linear.map_smul,
      Functor.map_id]
  constructor
  · intro n hn f
    have h0 : f ≫ (shiftFunctorAdd' C m n (m + n) rfl).inv.app E = 0 :=
      h.hom_shift_shift_eq_zero m (m + n) (by omega) _
    exact (cancel_mono ((shiftFunctorAdd' C m n (m + n) rfl).inv.app E)).1
      (h0.trans zero_comp.symm)
  · exact ⟨fun c c' hcc => h.algebraMap_bijective.1
        ((shiftFunctor C m).map_injective (by rw [← hcomp, ← hcomp, hcc])),
      fun g => ((shiftFunctor C m).map_surjective g).elim fun g' hg' =>
        (h.algebraMap_bijective.2 g').elim fun c hc => ⟨c, by rw [hcomp, hc, hg']⟩⟩

/-- Exceptionality transports along a shift-commuting `k`-linear equivalence.
The functor's linearity is an assumption for the same reason as in `shift`.
Nothing else is assumed of the target: neither clause consumes a
triangulation, additivity of the target's shifts, or a zero object, so the
adapter is usable before any of those are assembled — which is also why the
issue's `[e.functor.IsTriangulated]` hypothesis is deliberately absent. -/
theorem of_equivalence {D : Type*} [Category.{v} D] [Preadditive D]
    [Linear k D] [HasShift D ℤ] (e : C ≌ D)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear k] :
    IsExceptional k (e.functor.obj E) := by
  have hcomp : ∀ c : k,
      algebraMap k (End (e.functor.obj E)) c
        = e.functor.map (algebraMap k (End E) c) := by
    intro c
    rw [algebraMap_end_apply, algebraMap_end_apply, Functor.Linear.map_smul,
      Functor.map_id]
  constructor
  · intro n hn f
    obtain ⟨g, hg⟩ :=
      e.functor.map_surjective (f ≫ (e.functor.commShiftIso n).inv.app E)
    have hf0 : f ≫ (e.functor.commShiftIso n).inv.app E = 0 :=
      hg.symm.trans ((congrArg e.functor.map (h.hom_shift_eq_zero n hn g)).trans
        (e.functor.map_zero _ _))
    exact (cancel_mono ((e.functor.commShiftIso n).inv.app E)).1
      (hf0.trans zero_comp.symm)
  · exact ⟨fun c c' hcc => h.algebraMap_bijective.1
        (e.functor.map_injective (by rw [← hcomp, ← hcomp, hcc])),
      fun g => (e.functor.map_surjective g).elim fun g' hg' =>
        (h.algebraMap_bijective.2 g').elim fun c hc => ⟨c, by rw [hcomp, hc, hg']⟩⟩

end IsExceptional

end Triangulated

end CategoryTheory
