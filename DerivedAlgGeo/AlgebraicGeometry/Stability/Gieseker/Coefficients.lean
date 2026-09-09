/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HilbertPolynomial

/-!
# Hilbert coefficients: multiplicity and degree

The Hilbert function of a coherent sheaf has finite-difference degree at most `P.dim`, so it is
determined by its `P.dim + 1` Newton coefficients. This file extracts them, proves that the top
two are additive on short exact sequences by exhibiting them as homomorphisms out of the
Grothendieck group, and proves the Gregory–Newton representation that recovers the Hilbert
function from them.

`multiplicity` is the top coefficient and plays the role of rank; `hilbertDegreeCoefficient` is
the next one down and plays the role of degree. Both are *finite-difference* coefficients: if
the Hilbert polynomial has leading term `e · n ^ dim / dim !`, then `multiplicity F` is `e`,
that is `dim !` times the classical leading coefficient. Nothing here divides by a factorial,
and no statement below silently reads these as the classical coefficients.

## The comparison at infinity

`reducedHilbert` divides the Hilbert function by the multiplicity, and comparing two of these
functions for large `n` is what Gieseker stability is. The comparison is possible only because
`hilbertFunction_eq_sum_choose` writes the function as a *finite* binomial sum whose length is
`P.dim + 1` and does not depend on `n`; without it, `DegreeLE` alone says nothing about
behaviour at infinity. That representation therefore lives here, with the coefficients, and not
in the file that defines the order.

## The junk value

`reducedHilbert P F` divides by `multiplicity P F`, and Lean's division returns `0` when that is
`0`. A sheaf of multiplicity zero — one whose support has dimension below `P.dim` — therefore has
reduced Hilbert function identically `0` rather than being undefined. Every statement about
`reducedHilbert` below carries a positivity hypothesis instead of relying on the quotient, and
the purity conjunct of Gieseker semistability, defined in `Basic.lean`, is what keeps such a
sheaf out of the semistability quantifier. The same junk value is what would make the
comparison theorem of `MuStability.lean` false without purity.
-/

universe u

open CategoryTheory Limits Finset

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open NumericalPolynomial

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable (P : PolarizedVarietyData k X)

/-! ### The Newton coefficients -/

/-- The Hilbert function of a zero sheaf vanishes identically, because it factors through the
Grothendieck group and the class of a zero object is `0`. -/
theorem hilbertFunction_of_isZero {F : Coh X} (hF : IsZero F) :
    P.hilbertFunction F = 0 := by
  rw [← P.hilbertHom_of F, K₀Ab.of_isZero hF, map_zero]

/-- **The `j`th Hilbert coefficient**: the `j`-fold forward difference of the Hilbert function,
evaluated at the origin. -/
noncomputable def hilbertCoefficient (F : Coh X) (j : ℕ) : ℤ :=
  coefficient (List.replicate j oneVariableDirection) (oneVariable (P.hilbertFunction F))

/-- The Hilbert coefficient is the iterated ordinary forward difference at `0`. This is the
existing one-variable bridge `NumericalPolynomial.coefficient_oneVariable`, not a new one. -/
theorem hilbertCoefficient_eq_fwdDiff (F : Coh X) (j : ℕ) :
    P.hilbertCoefficient F j = (fwdDiff (1 : ℤ))^[j] (P.hilbertFunction F) 0 :=
  coefficient_oneVariable _ j

/-- Iterating the forward difference past the vanishing order kills every later coefficient. -/
theorem hilbertCoefficient_eq_zero_of_lt (F : Coh X) {j : ℕ} (hj : P.dim < j) :
    P.hilbertCoefficient F j = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, j = r + (P.dim + 1) := ⟨j - (P.dim + 1), by omega⟩
  have hzero : ∀ s : ℕ, (fwdDiff (1 : ℤ))^[s] (0 : ℤ → ℤ) = 0 := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih =>
        rw [Function.iterate_succ_apply', ih]
        funext x
        simp [fwdDiff]
  rw [P.hilbertCoefficient_eq_fwdDiff F, Function.iterate_add_apply,
    P.fwdDiff_hilbertFunction F, hzero r]
  rfl

/-- A zero sheaf has vanishing Hilbert coefficients. -/
theorem hilbertCoefficient_of_isZero {F : Coh X} (hF : IsZero F) (j : ℕ) :
    P.hilbertCoefficient F j = 0 := by
  have h0 : oneVariable (P.hilbertFunction F) = 0 := by
    rw [P.hilbertFunction_of_isZero hF]
    rfl
  rw [hilbertCoefficient, h0, coefficient_zero]

/-- Hilbert coefficients are invariant under isomorphism. -/
theorem hilbertCoefficient_eq_of_iso {F G : Coh X} (e : F ≅ G) (j : ℕ) :
    P.hilbertCoefficient F j = P.hilbertCoefficient G j := by
  rw [hilbertCoefficient, hilbertCoefficient, P.hilbertFunction_eq_of_iso e]

/-- Hilbert coefficients are additive on short exact sequences, coefficient by coefficient. -/
theorem hilbertCoefficient_additive (S : ShortComplex (Coh X)) (hS : S.ShortExact) (j : ℕ) :
    P.hilbertCoefficient S.X₂ j =
      P.hilbertCoefficient S.X₁ j + P.hilbertCoefficient S.X₃ j := by
  have hfun : oneVariable (P.hilbertFunction S.X₂) =
      oneVariable (P.hilbertFunction S.X₁) + oneVariable (P.hilbertFunction S.X₃) := by
    funext n
    exact P.hilbertFunction_additive S hS (n 0)
  rw [hilbertCoefficient, hilbertCoefficient, hilbertCoefficient, hfun, coefficient_add]

/-! ### Multiplicity and degree -/

/-- **The multiplicity**: the top Hilbert coefficient, playing the role of rank. It is `dim !`
times the classical leading coefficient of the Hilbert polynomial; see the module docstring. -/
noncomputable def multiplicity (F : Coh X) : ℤ := P.hilbertCoefficient F P.dim

/-- **The degree coefficient**: the Hilbert coefficient one below the top, playing the role of
degree. At `P.dim = 0` truncated subtraction makes this the multiplicity again, which is the
correct degenerate reading: a zero-dimensional polarization has no degree direction. -/
noncomputable def hilbertDegreeCoefficient (F : Coh X) : ℤ :=
  P.hilbertCoefficient F (P.dim - 1)

theorem multiplicity_of_isZero {F : Coh X} (hF : IsZero F) : P.multiplicity F = 0 :=
  P.hilbertCoefficient_of_isZero hF _

theorem multiplicity_eq_of_iso {F G : Coh X} (e : F ≅ G) :
    P.multiplicity F = P.multiplicity G :=
  P.hilbertCoefficient_eq_of_iso e _

theorem hilbertDegreeCoefficient_eq_of_iso {F G : Coh X} (e : F ≅ G) :
    P.hilbertDegreeCoefficient F = P.hilbertDegreeCoefficient G :=
  P.hilbertCoefficient_eq_of_iso e _

/-- **Multiplicity as a homomorphism out of the Grothendieck group.** The type is exactly the
`rankHom` field of `WeakSlopeData`, so the instantiation in `MuStability.lean` needs no
adapter on this coordinate. -/
noncomputable def multiplicityHom : K₀Ab (Coh X) →+ ℤ :=
  K₀Ab.liftOf P.multiplicity
    (fun S hS ↦ P.hilbertCoefficient_additive S hS P.dim)

@[simp]
theorem multiplicityHom_of (F : Coh X) :
    P.multiplicityHom (K₀Ab.of F) = P.multiplicity F :=
  K₀Ab.liftOf_of _ _ F

/-- **The degree coefficient as a homomorphism out of the Grothendieck group.** -/
noncomputable def degreeHom : K₀Ab (Coh X) →+ ℤ :=
  K₀Ab.liftOf P.hilbertDegreeCoefficient
    (fun S hS ↦ P.hilbertCoefficient_additive S hS (P.dim - 1))

@[simp]
theorem degreeHom_of (F : Coh X) :
    P.degreeHom (K₀Ab.of F) = P.hilbertDegreeCoefficient F :=
  K₀Ab.liftOf_of _ _ F

/-- **The reduced Hilbert function.** At `multiplicity P F = 0` this is Lean's junk value `0`
rather than an undefined quotient; see the module docstring, and note that every statement
about it below assumes positive multiplicity. -/
noncomputable def reducedHilbert (F : Coh X) : ℤ → ℚ :=
  fun n ↦ (P.hilbertFunction F n : ℚ) / (P.multiplicity F : ℚ)

theorem reducedHilbert_apply (F : Coh X) (n : ℤ) :
    P.reducedHilbert F n = (P.hilbertFunction F n : ℚ) / (P.multiplicity F : ℚ) := rfl

/-! ### The Gregory–Newton representation -/

/-- Two binomial sums of the same coefficient sequence agree once the sequence vanishes above
`d`, whichever of `n` and `d` is larger. -/
private theorem sum_choose_eq_sum_choose {c : ℕ → ℤ} {d : ℕ}
    (hc : ∀ j, d < j → c j = 0) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℤ) * c j =
      ∑ j ∈ range (d + 1), (n.choose j : ℤ) * c j := by
  have hsub : ∀ a b : ℕ, a ≤ b → range (a + 1) ⊆ range (b + 1) := by
    intro a b hab x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  rcases le_total n d with hnd | hdn
  · refine Finset.sum_subset (hsub n d hnd) ?_
    intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simpa using hj), Nat.cast_zero, zero_mul]
  · refine (Finset.sum_subset (hsub d n hdn) ?_).symm
    intro j _ hj
    rw [hc j (by simpa using hj), mul_zero]

/-- **Gregory–Newton.** The Hilbert function is the binomial sum of its Hilbert coefficients,
over a range fixed by `P.dim` rather than by `n`. This is the representation that lets two
Hilbert functions be compared for large `n`. -/
theorem hilbertFunction_eq_sum_choose (F : Coh X) (n : ℕ) :
    P.hilbertFunction F n =
      ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * P.hilbertCoefficient F j := by
  have hnewton := shift_eq_sum_fwdDiff_iter (M := ℤ) (G := ℤ) (1 : ℤ)
    (P.hilbertFunction F) n 0
  rw [show (0 : ℤ) + n • (1 : ℤ) = (n : ℤ) by simp] at hnewton
  have hterm : ∀ j ∈ range (n + 1),
      n.choose j • (fwdDiff (1 : ℤ))^[j] (P.hilbertFunction F) 0 =
        (n.choose j : ℤ) * P.hilbertCoefficient F j := by
    intro j _
    rw [P.hilbertCoefficient_eq_fwdDiff F j, nsmul_eq_mul]
  rw [hnewton, Finset.sum_congr rfl hterm]
  exact sum_choose_eq_sum_choose (fun j hj ↦ P.hilbertCoefficient_eq_zero_of_lt F hj) n

/-- The reduced Hilbert function as a binomial sum of normalized coefficients. -/
theorem reducedHilbert_eq_sum_choose (F : Coh X) (n : ℕ) :
    P.reducedHilbert F n =
      ∑ j ∈ range (P.dim + 1),
        (n.choose j : ℚ) * ((P.hilbertCoefficient F j : ℚ) / (P.multiplicity F : ℚ)) := by
  rw [reducedHilbert_apply, P.hilbertFunction_eq_sum_choose F n]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
