/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.Rouquier
import DerivedAlgGeo.CategoryTheory.Triangulated.Generators.Composition

/-! # Generation-time composition and Rouquier dimension

This file applies the generic envelope-composition law to the repository's `ℕ∞`-valued
generation time and Rouquier dimension.

## Main definitions

This file introduces no definitions; it reuses `generationTime`, `rouquierDim`, and Mathlib's
envelope tower.

## Main results

* `CategoryTheory.ObjectProperty.generationTime_add_one_submultiplicative`:
  generation time plus one is submultiplicative.
* `CategoryTheory.Triangulated.isStrongTriangulatedGenerator_of_classical_of_rouquierDim_ne_top`:
  finite Rouquier dimension makes classical generators strong.
* `CategoryTheory.Triangulated.generationTime_ne_top_of_classical_of_rouquierDim_ne_top`:
  finite Rouquier dimension bounds the generation time of every classical generator.

## Implementation notes

The `+1` records the shift between iterated-envelope indices and Rouquier's stage indices:
`triangEnvelopeIter n` is stage `n + 1`. This form handles infinite values without subtracting
one from an `ℕ∞` bound. The expanded expression `a * b + a + b` is `⊤` if either input is `⊤`;
`0 * ⊤ = 0` is relevant only to a bare product.

## References

* Raphaël Rouquier, *Dimensions of triangulated categories*.
* The Stacks Project, Section 13.36, Lemma 13.36.6,
  [tag 0FXA](https://stacks.math.columbia.edu/tag/0FXA).
* `Mathlib.CategoryTheory.Triangulated.Generators`

## Tags

generation time, Rouquier dimension, triangulated category, submultiplicativity
-/
universe v u

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

private lemma triangEnvelopeIter_bot_of_not_nonempty (P : ObjectProperty C) (n : ℕ)
    (hP : ¬ P.Nonempty) : P.triangEnvelopeIter n = ⊥ := by
  have hbot : P = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot P).mp hP
  subst P
  simp [triangEnvelopeIter]

private lemma generationTime_top_of_bot_left_of_nonempty_right (Q : ObjectProperty C)
    (hQ : Q.Nonempty) : (⊥ : ObjectProperty C).generationTime Q = ⊤ := by
  apply (generationTime_eq_top_iff ⊥ Q).2
  intro n hn
  rw [triangEnvelopeIter_bot_of_not_nonempty ⊥ n
    ((ObjectProperty.not_nonempty_iff_eq_bot (⊥ : ObjectProperty C)).mpr rfl)] at hn
  exact ((ObjectProperty.not_nonempty_iff_eq_bot Q).mpr (le_antisymm hn bot_le)) hQ

private lemma generationTime_zero_of_bot_right (P : ObjectProperty C) :
    P.generationTime ⊥ = 0 := by
  apply (generationTime_eq_zero_iff P ⊥).2
  exact bot_le

variable [IsTriangulated C]

/-- Generation time plus one is submultiplicative.

The additive law `generationTime P R ≤ generationTime P Q + generationTime Q R` is false.
For a counterexample, take the bounded derived category of finite-length modules over
`A = k[t]/(t^6)`, let `S = A/(t)`, `T = A/(t^3)`, `P = singleton S`,
`Q = singleton T`, and `R = singleton A`. Then `P.generationTime Q = 2` by the
length-three composition series, and `Q.generationTime R = 1` by the exact sequence
`0 → t^3 A → A → T → 0`, since `t^3 A ≃ T`. Objects in
`P.triangEnvelopeIter n` have cohomology modules of Loewy length at most `n + 1`: this holds
for shifts, finite sums, and retracts at stage zero, and each extension by a semisimple module
adds at most one Loewy layer. This bound makes the generation times exact: `T` has Loewy
length three, while `A` has Loewy length six, a length-six composition series, and a filtration
by two copies of `T`. Also, `A` is not in `Q.triangEnvelopeIter 0`, whose cohomology modules
have Loewy length at most three, so `Q.generationTime R = 1`. Thus
`P.generationTime R = 5`, while additivity would give `5 ≤ 2 + 1`, which is false. In tower indices,
the `iter 2` then `iter 1` composition lands in `iter 5`; additivity predicts `iter 3`,
which is Rouquier's `⟨P⟩₄`. The composition law gives the upper bound
`⟨P⟩₃ ⋆ ⟨P⟩₃ ⊆ ⟨P⟩₆`. -/
theorem generationTime_add_one_submultiplicative (P Q R : ObjectProperty C) :
    P.generationTime R + 1 ≤ (P.generationTime Q + 1) * (Q.generationTime R + 1) := by
  by_cases hP : P.Nonempty
  · letI := hP
    set a := P.generationTime Q
    set b := Q.generationTime R
    set c := P.generationTime R
    by_cases ha : a = ⊤
    · simp [a, ha]
    by_cases hb : b = ⊤
    · simp [a, b, hb]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ha
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hb
    have hQ : Q ≤ P.triangEnvelopeIter m := by
      apply (generationTime_le_coe_iff P Q m).1
      simp [a, hm]
    have hR : R ≤ Q.triangEnvelopeIter n := by
      apply (generationTime_le_coe_iff Q R n).1
      simp [b, hn]
    have hcomp : (P.triangEnvelopeIter m).triangEnvelopeIter n ≤
        P.triangEnvelopeIter (m * n + m + n) := triangEnvelopeIter_compose P m n
    have hreach : R ≤ P.triangEnvelopeIter (m * n + m + n) := by
      exact hR.trans ((monotone_triangEnvelopeIter hQ n).trans hcomp)
    have hc : c ≤ (m * n + m + n : ℕ∞) := by
      apply (generationTime_le_coe_iff P R (m * n + m + n)).2 hreach
    calc
      c + 1 ≤ (m * n + m + n : ℕ∞) + 1 := by
        simpa [add_comm] using add_le_add_right hc 1
      _ = ((m + 1 : ℕ) : ℕ∞) * ((n + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast (show m * n + m + n + 1 = (m + 1) * (n + 1) by
          rw [Nat.mul_succ, Nat.add_mul, Nat.one_mul]
          omega)
      _ = (a + 1) * (b + 1) := by rw [← hm, ← hn]; simp
  · have hPbot : P = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot P).mp hP
    subst P
    by_cases hQ : Q.Nonempty
    · have ha : (⊥ : ObjectProperty C).generationTime Q = ⊤ :=
        generationTime_top_of_bot_left_of_nonempty_right Q hQ
      simp [ha]
    · have hQbot : Q = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot Q).mp hQ
      subst Q
      by_cases hR : R.Nonempty
      · have hb : (⊥ : ObjectProperty C).generationTime R = ⊤ :=
          generationTime_top_of_bot_left_of_nonempty_right R hR
        simp [hb]
      · have hRbot : R = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot R).mp hR
        subst R
        simp [generationTime_zero_of_bot_right]


end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Pretriangulated Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Finite Rouquier dimension supplies a strongly generating singleton; the bounded Stacks
comparison transfers its finite stage to `P`. -/
theorem isStrongTriangulatedGenerator_of_classical_of_rouquierDim_ne_top
    (P : ObjectProperty C) (hP : P.IsClassicalTriangulatedGenerator)
    (hD : rouquierDim C ≠ ⊤) : P.IsStrongTriangulatedGenerator := by
  obtain ⟨G, hG⟩ := (rouquierDim_ne_top_iff_exists_strong C).mp hD
  exact ObjectProperty.isStrongTriangulatedGenerator_of_isClassical_of_singleton_strong
    P G hP hG

/-- The strong-generation result and the generation-time characterization of strong generators
give the finite generation-time bound. -/
theorem generationTime_ne_top_of_classical_of_rouquierDim_ne_top
    (P : ObjectProperty C) (hP : P.IsClassicalTriangulatedGenerator)
    (hD : rouquierDim C ≠ ⊤) : P.generationTime ⊤ ≠ ⊤ :=
  (ObjectProperty.isStrongTriangulatedGenerator_iff_generationTime_ne_top P).1
    (isStrongTriangulatedGenerator_of_classical_of_rouquierDim_ne_top P hP hD)

end CategoryTheory.Triangulated
