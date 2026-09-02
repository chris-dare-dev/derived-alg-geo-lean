/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Basic
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Spherical and pseudoprojective objects

This file formalizes Definitions 4.1 of arXiv:1912.04332v2 and 2.1 of
arXiv:2104.13610v2 in a generic `k`-linear category with a chosen Serre
functor.

An `n`-spherical object has one-dimensional self-Hom in degrees `0` and `n`,
vanishing in every other degree, and is carried to its `n`-shift by the Serre
functor.  An `n`-pseudoprojective object has one-dimensional self-Hom in every
degree from `0` through `n`, vanishing outside that interval, and satisfies the
same Serre condition.

For pseudoprojective objects the paper asserts an isomorphism of graded vector
spaces only.  No multiplication or truncated-polynomial algebra structure is
part of the definition here.

As throughout the repository, vanishing is stated as `∀ f, f = 0`; applying
`IsZero` to the bare type of morphisms would make the predicate uninhabitable.
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]

/-- An `n`-spherical object relative to a chosen Serre functor. -/
structure IsSphericalObject (D : SerreFunctorData k C) (n : ℕ) (E : C) : Prop where
  /-- Self-Homs vanish away from degrees `0` and `n`. -/
  vanishing : ∀ i : ℤ, i ≠ 0 → i ≠ (n : ℤ) → ∀ f : E ⟶ E⟦i⟧, f = 0
  /-- The endomorphism space is the base field. -/
  end_one : Nonempty ((E ⟶ E) ≃ₗ[k] k)
  /-- The top self-Hom is the base field. -/
  top_one : Nonempty ((E ⟶ E⟦(n : ℤ)⟧) ≃ₗ[k] k)
  /-- The Serre functor carries the object to its `n`-shift. -/
  serre_shift : Nonempty (D.S.obj E ≅ E⟦(n : ℤ)⟧)

/-- An `n`-pseudoprojective object relative to a chosen Serre functor. -/
structure IsPseudoprojectiveObject (D : SerreFunctorData k C) (n : ℕ) (E : C) : Prop where
  /-- Every self-Hom from degree `0` through degree `n` is the base field. -/
  inRange_one : ∀ i : ℕ, i ≤ n → Nonempty ((E ⟶ E⟦(i : ℤ)⟧) ≃ₗ[k] k)
  /-- Self-Homs vanish outside the interval `[0,n]`. -/
  vanishing : ∀ i : ℤ, (i < 0 ∨ (n : ℤ) < i) → ∀ f : E ⟶ E⟦i⟧, f = 0
  /-- The Serre functor carries the object to its `n`-shift. -/
  serre_shift : Nonempty (D.S.obj E ≅ E⟦(n : ℤ)⟧)

namespace IsSphericalObject

variable {D : SerreFunctorData k C} {n : ℕ} {E F : C}
  (h : IsSphericalObject D n E)

include h

/-- A spherical object is nonzero. -/
theorem not_isZero : ¬ IsZero E := by
  intro hE
  have hsub : Subsingleton (E ⟶ E) := ⟨fun f g ↦ hE.eq_of_src f g⟩
  have : Subsingleton k := h.end_one.some.toEquiv.symm.subsingleton
  exact (not_subsingleton k) this

/-- The endomorphism space of a spherical object is one-dimensional. -/
theorem finrank_end : Module.finrank k (E ⟶ E) = 1 := by
  rw [h.end_one.some.finrank_eq, Module.finrank_self]

/-- The top self-Hom of a spherical object is one-dimensional. -/
theorem finrank_top : Module.finrank k (E ⟶ E⟦(n : ℤ)⟧) = 1 := by
  rw [h.top_one.some.finrank_eq, Module.finrank_self]

/-- Every other self-Hom has dimension zero. -/
theorem finrank_hom_eq_zero (i : ℤ) (hi₀ : i ≠ 0) (hin : i ≠ (n : ℤ)) :
    Module.finrank k (E ⟶ E⟦i⟧) = 0 := by
  have : Subsingleton (E ⟶ E⟦i⟧) :=
    ⟨fun f g ↦ by rw [h.vanishing i hi₀ hin f, h.vanishing i hi₀ hin g]⟩
  exact Module.finrank_zero_of_subsingleton

/-- Sphericity is invariant under isomorphism. -/
theorem of_iso (e : E ≅ F) : IsSphericalObject D n F where
  vanishing i hi₀ hin f := by
    have hz := h.vanishing i hi₀ hin
      ((Linear.homCongr k e ((shiftFunctor C i).mapIso e)).symm f)
    have := congrArg (Linear.homCongr k e ((shiftFunctor C i).mapIso e)) hz
    simpa using this
  end_one := ⟨(Linear.homCongr k e.symm e.symm).trans h.end_one.some⟩
  top_one :=
    ⟨(Linear.homCongr k e.symm
      ((shiftFunctor C (n : ℤ)).mapIso e.symm)).trans h.top_one.some⟩
  serre_shift := ⟨(D.S.mapIso e).symm ≪≫ h.serre_shift.some ≪≫
    (shiftFunctor C (n : ℤ)).mapIso e⟩

end IsSphericalObject

namespace IsPseudoprojectiveObject

variable {D : SerreFunctorData k C} {n : ℕ} {E F : C}
  (h : IsPseudoprojectiveObject D n E)

include h

/-- A pseudoprojective object is nonzero. -/
theorem not_isZero : ¬ IsZero E := by
  intro hE
  have hsub : Subsingleton (E ⟶ E⟦(0 : ℤ)⟧) :=
    ⟨fun f g ↦ hE.eq_of_src f g⟩
  have : Subsingleton k := (h.inRange_one 0 (Nat.zero_le n)).some.toEquiv.symm.subsingleton
  exact (not_subsingleton k) this

/-- Every in-range self-Hom is one-dimensional. -/
theorem finrank_inRange (i : ℕ) (hi : i ≤ n) :
    Module.finrank k (E ⟶ E⟦(i : ℤ)⟧) = 1 := by
  rw [(h.inRange_one i hi).some.finrank_eq, Module.finrank_self]

/-- Every out-of-range self-Hom has dimension zero. -/
theorem finrank_hom_eq_zero (i : ℤ) (hi : i < 0 ∨ (n : ℤ) < i) :
    Module.finrank k (E ⟶ E⟦i⟧) = 0 := by
  have : Subsingleton (E ⟶ E⟦i⟧) :=
    ⟨fun f g ↦ by rw [h.vanishing i hi f, h.vanishing i hi g]⟩
  exact Module.finrank_zero_of_subsingleton

/-- Pseudoprojectivity is invariant under isomorphism. -/
theorem of_iso (e : E ≅ F) : IsPseudoprojectiveObject D n F where
  inRange_one i hi :=
    ⟨(Linear.homCongr k e.symm
      ((shiftFunctor C (i : ℤ)).mapIso e.symm)).trans (h.inRange_one i hi).some⟩
  vanishing i hi f := by
    have hz := h.vanishing i hi
      ((Linear.homCongr k e ((shiftFunctor C i).mapIso e)).symm f)
    have := congrArg (Linear.homCongr k e ((shiftFunctor C i).mapIso e)) hz
    simpa using this
  serre_shift := ⟨(D.S.mapIso e).symm ≪≫ h.serre_shift.some ≪≫
    (shiftFunctor C (n : ℤ)).mapIso e⟩

/-- For `n ≥ 2`, a pseudoprojective object cannot be spherical: degree one
is nonzero for the former and vanishes for the latter. -/
theorem not_isSphericalObject (hn : 2 ≤ n) : ¬ IsSphericalObject D n E := by
  intro hs
  have hsub : Subsingleton (E ⟶ E⟦(1 : ℤ)⟧) :=
    ⟨fun f g ↦ by
      rw [hs.vanishing 1 one_ne_zero (by omega) f,
        hs.vanishing 1 one_ne_zero (by omega) g]⟩
  have : Subsingleton k := (h.inRange_one 1 (by omega)).some.toEquiv.symm.subsingleton
  exact (not_subsingleton k) this

end IsPseudoprojectiveObject

/-- In dimension one, the spherical and pseudoprojective profiles coincide. -/
theorem isSphericalObject_one_iff_isPseudoprojectiveObject_one
    (D : SerreFunctorData k C) (E : C) :
    IsSphericalObject D 1 E ↔ IsPseudoprojectiveObject D 1 E := by
  constructor
  · intro h
    refine
      { inRange_one := ?_
        vanishing := ?_
        serre_shift := h.serre_shift }
    · intro i hi
      interval_cases i
      · exact ⟨(Linear.homCongr k (Iso.refl E)
          ((shiftFunctorZero C ℤ).symm.app E)).symm.trans h.end_one.some⟩
      · simpa using h.top_one
    · intro i hi f
      exact h.vanishing i (by omega) (by omega) f
  · intro h
    refine
      { vanishing := ?_
        end_one := ?_
        top_one := ?_
        serre_shift := h.serre_shift }
    · intro i hi₀ hi₁ f
      exact h.vanishing i (by omega) f
    · exact ⟨(Linear.homCongr k (Iso.refl E)
        ((shiftFunctorZero C ℤ).symm.app E)).trans
          (h.inRange_one 0 (by omega)).some⟩
    · simpa using h.inRange_one 1 (by omega)

end CategoryTheory.SerreFunctor
