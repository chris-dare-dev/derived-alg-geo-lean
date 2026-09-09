/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Slope
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeTop

/-!
# μ-stability on `Coh X`, the first geometric slope datum

`WeakSlopeData` asks for a rank, a degree, and two positivity facts. The Hilbert multiplicity and
degree coefficient of `Coefficients.lean` are already homomorphisms out of `K₀Ab (Coh X)`, so
coherent sheaves on a polarized variety become an inhabitant of the repository's abstract slope
theory by supplying only the two positivity facts. Everything downstream — the charge
`Z(E) = -degree E + i · rank E`, the weak slope in `WithTop ℝ`, the phase, the order bridge
`phase_le_iff_slope_le`, weak semistability, and the whole `WeakStabilityFunctionOn` interface —
then arrives rather than being rebuilt.

## What is supplied

`MuPositivityData` carries exactly the two facts `WeakSlopeData` needs and this pin cannot prove,
because both are consequences of ampleness of the polarization, which does not exist here:
multiplicity is nonnegative, and a nonzero sheaf of multiplicity zero has nonnegative degree
coefficient. These are geometric input, not proof holes.
`Weak/Foundation/StabilityFunction/WeakSlope.lean`'s own docstring says the corresponding two
fields are geometric input there too, and that both hold on a polarised surface; the strict form
of the second is false on a surface, which is why the curve case below is a separate datum.

## Rank stays integral, degree does not

`WeakSlopeData.degreeHom` is real-valued, so the integral degree coefficient is composed with
`Int.castAddHom ℝ` here. The rank stays integral, and that is not incidental: integrality of the
rank is what the boundary arguments of the Mukai lane use. The multiplicity homomorphism is
therefore handed over unchanged.

## The comparison with Gieseker stability, and why purity is needed

`giesekerSemistable_implies_muSemistable` is the only direction of the classical chain delivered
here. It is **false without purity**. `WeakStabilityFunctionOn.IsSemistable` quantifies over every
nonzero `B : Subobject F` and compares in `WithTop ℝ`, where a multiplicity-zero subobject has
slope `⊤` and would destabilise `F` — while satisfying the Gieseker order vacuously, because its
reduced Hilbert function is the junk value `0`. The purity conjunct of `IsGiesekerSemistable` is
exactly what rules that out: every nonzero subobject then has positive multiplicity, both slopes
are finite, and the lexicographic criterion read at `P.dim - 1` is the slope comparison.

The reverse implication, μ-stable implies Gieseker-stable, is *not* delivered, and neither is any
statement about strict stability in either direction.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- **The two positivity facts a polarization supplies.** Both are consequences of ampleness and
neither is provable at this pin; see the module docstring. -/
structure MuPositivityData (P : PolarizedVarietyData k X) where
  /-- Multiplicity is nonnegative — geometric input. -/
  multiplicity_nonneg : ∀ F : Coh X, 0 ≤ P.multiplicity F
  /-- A nonzero sheaf of multiplicity zero has nonnegative degree coefficient — geometric input,
  and what puts such a sheaf on the closed rather than the strictly negative real axis. -/
  degree_nonneg_of_multiplicity_zero : ∀ F : Coh X, ¬IsZero F → P.multiplicity F = 0 →
    0 ≤ P.hilbertDegreeCoefficient F

/-- **The curve form of the same input**, with the strict inequality. It is false on a surface,
where a skyscraper has multiplicity and degree coefficient both zero; see
`Weak/Foundation/StabilityFunction/WeakSlope.lean`. -/
structure MuCurvePositivityData (P : PolarizedVarietyData k X) where
  /-- Multiplicity is nonnegative — geometric input. -/
  multiplicity_nonneg : ∀ F : Coh X, 0 ≤ P.multiplicity F
  /-- A nonzero sheaf of multiplicity zero has positive degree coefficient — the curve
  condition. -/
  degree_pos_of_multiplicity_zero : ∀ F : Coh X, ¬IsZero F → P.multiplicity F = 0 →
    0 < P.hilbertDegreeCoefficient F

/-- Forgetting the strict inequality, exactly as `SlopeData.toWeakSlopeData` does. -/
theorem MuCurvePositivityData.toMuPositivityData {P : PolarizedVarietyData k X}
    (h : MuCurvePositivityData P) : MuPositivityData P where
  multiplicity_nonneg := h.multiplicity_nonneg
  degree_nonneg_of_multiplicity_zero := fun F hF h0 ↦
    (h.degree_pos_of_multiplicity_zero F hF h0).le

namespace PolarizedVarietyData

variable (P : PolarizedVarietyData k X)

/-! ### The slope datum -/

/-- **Coherent sheaves on a polarized variety, as a weak slope datum.** Rank is the Hilbert
multiplicity, degree is the Hilbert degree coefficient cast to `ℝ`, and the two positivity fields
are the supplied geometric input. No new carrier: this is an instance of the abstract
structure. -/
noncomputable def weakSlopeData (h : MuPositivityData P) : WeakSlopeData (Coh X) where
  rankHom := P.multiplicityHom
  degreeHom := (Int.castAddHom ℝ).comp P.degreeHom
  rank_nonneg := fun F ↦ by
    rw [P.multiplicityHom_of F]
    exact h.multiplicity_nonneg F
  degree_nonneg_of_rank_zero := fun F hF h0 ↦ by
    rw [P.multiplicityHom_of F] at h0
    have := h.degree_nonneg_of_multiplicity_zero F hF h0
    simpa [P.degreeHom_of F] using (by exact_mod_cast this :
      (0 : ℝ) ≤ ((P.hilbertDegreeCoefficient F : ℤ) : ℝ))

variable {P}

@[simp]
theorem weakSlopeData_rank (h : MuPositivityData P) (F : Coh X) :
    (P.weakSlopeData h).rank F = P.multiplicity F :=
  P.multiplicityHom_of F

@[simp]
theorem weakSlopeData_degree (h : MuPositivityData P) (F : Coh X) :
    (P.weakSlopeData h).degree F = ((P.hilbertDegreeCoefficient F : ℤ) : ℝ) := by
  show (Int.castAddHom ℝ) (P.degreeHom (K₀Ab.of F)) = _
  rw [P.degreeHom_of F]
  rfl

theorem weakSlopeData_charge (h : MuPositivityData P) (F : Coh X) :
    (P.weakSlopeData h).charge F =
      ⟨-((P.hilbertDegreeCoefficient F : ℤ) : ℝ), ((P.multiplicity F : ℤ) : ℝ)⟩ := by
  rw [WeakSlopeData.charge, weakSlopeData_degree, weakSlopeData_rank]

/-- The weak slope of the datum, as a ratio of Hilbert coefficients. -/
theorem weakSlopeData_slope (h : MuPositivityData P) (F : Coh X) :
    (P.weakSlopeData h).slope F =
      ((P.hilbertDegreeCoefficient F : ℤ) : ℝ) / ((P.multiplicity F : ℤ) : ℝ) := by
  rw [WeakSlopeData.slope, weakSlopeData_degree, weakSlopeData_rank]

/-- **The honest slope at positive multiplicity**: the ratio, coerced into `WithTop ℝ`. -/
theorem weakSlopeData_topSlope_of_multiplicity_pos (h : MuPositivityData P) {F : Coh X}
    (hF : 0 < P.multiplicity F) :
    (P.weakSlopeData h).topSlope F =
      ((((P.hilbertDegreeCoefficient F : ℤ) : ℝ) / ((P.multiplicity F : ℤ) : ℝ) : ℝ) :
        WithTop ℝ) := by
  have hrank : 0 < (P.weakSlopeData h).rank F := by
    rw [weakSlopeData_rank]
    exact hF
  rw [(P.weakSlopeData h).topSlope_of_rank_pos hrank, weakSlopeData_slope]

/-- **The honest slope at multiplicity zero is `⊤`.** This is not a corner case: it is what makes
the comparison theorem below false without purity. -/
theorem weakSlopeData_topSlope_of_multiplicity_zero (h : MuPositivityData P) {F : Coh X}
    (hF : P.multiplicity F = 0) : (P.weakSlopeData h).topSlope F = ⊤ := by
  have hrank : (P.weakSlopeData h).rank F = 0 := by
    rw [weakSlopeData_rank]
    exact hF
  exact (P.weakSlopeData h).topSlope_of_rank_zero hrank

/-! ### The curve case -/

/-- **The curve form of the slope datum**, from the strict positivity input. -/
noncomputable def slopeData (h : MuCurvePositivityData P) : SlopeData (Coh X) where
  rankHom := P.multiplicityHom
  degreeHom := (Int.castAddHom ℝ).comp P.degreeHom
  rank_nonneg := fun F ↦ by
    rw [P.multiplicityHom_of F]
    exact h.multiplicity_nonneg F
  degree_pos_of_rank_zero := fun F hF h0 ↦ by
    rw [P.multiplicityHom_of F] at h0
    have := h.degree_pos_of_multiplicity_zero F hF h0
    simpa [P.degreeHom_of F] using (by exact_mod_cast this :
      (0 : ℝ) < ((P.hilbertDegreeCoefficient F : ℤ) : ℝ))

/-- **The two presentations agree.** Forgetting the curve condition gives back the surface datum,
field for field, so rank, degree, charge and slope are literally the same. -/
theorem toWeakSlopeData_slopeData (h : MuCurvePositivityData P) :
    (P.slopeData h).toWeakSlopeData = P.weakSlopeData h.toMuPositivityData := rfl

theorem slopeData_rank (h : MuCurvePositivityData P) (F : Coh X) :
    (P.slopeData h).rank F = P.multiplicity F :=
  P.multiplicityHom_of F

theorem slopeData_degree (h : MuCurvePositivityData P) (F : Coh X) :
    (P.slopeData h).degree F = ((P.hilbertDegreeCoefficient F : ℤ) : ℝ) :=
  weakSlopeData_degree h.toMuPositivityData F

theorem slopeData_charge (h : MuCurvePositivityData P) (F : Coh X) :
    (P.slopeData h).charge F =
      ⟨-((P.hilbertDegreeCoefficient F : ℤ) : ℝ), ((P.multiplicity F : ℤ) : ℝ)⟩ :=
  weakSlopeData_charge h.toMuPositivityData F

theorem slopeData_slope (h : MuCurvePositivityData P) (F : Coh X) :
    (P.slopeData h).slope F =
      ((P.hilbertDegreeCoefficient F : ℤ) : ℝ) / ((P.multiplicity F : ℤ) : ℝ) :=
  weakSlopeData_slope h.toMuPositivityData F

/-! ### Comparison with Gieseker semistability -/

/-- The slope is the normalized Hilbert coefficient one below the top, read in `ℝ`. This holds
without any positivity hypothesis, because both sides take the same junk value at multiplicity
zero. -/
theorem weakSlopeData_slope_eq_normalizedCoefficient (h : MuPositivityData P) (F : Coh X) :
    (P.weakSlopeData h).slope F = ((P.normalizedCoefficient F (P.dim - 1) : ℚ) : ℝ) := by
  rw [weakSlopeData_slope, normalizedCoefficient]
  push_cast
  rfl

/-- The Gieseker order between sheaves of positive multiplicity implies the slope inequality,
by the lexicographic criterion read at `P.dim - 1`. -/
theorem weakSlopeData_topSlope_eq_normalizedCoefficient (h : MuPositivityData P) {F : Coh X}
    (hF : 0 < P.multiplicity F) :
    (P.weakSlopeData h).topSlope F =
      ((((P.normalizedCoefficient F (P.dim - 1) : ℚ) : ℝ)) : WithTop ℝ) := by
  have hrank : 0 < (P.weakSlopeData h).rank F := by
    rw [weakSlopeData_rank]
    exact hF
  rw [(P.weakSlopeData h).topSlope_of_rank_pos hrank,
    weakSlopeData_slope_eq_normalizedCoefficient h F]

theorem topSlope_le_of_giesekerLE (h : MuPositivityData P) {F G : Coh X}
    (hF : 0 < P.multiplicity F) (hG : 0 < P.multiplicity G) (hle : P.GiesekerLE F G) :
    (P.weakSlopeData h).topSlope F ≤ (P.weakSlopeData h).topSlope G := by
  rw [weakSlopeData_topSlope_eq_normalizedCoefficient h hF,
    weakSlopeData_topSlope_eq_normalizedCoefficient h hG, WithTop.coe_le_coe, Rat.cast_le]
  exact normalizedCoefficient_pred_le_of_giesekerLE hF hG hle

/-- **Gieseker semistability implies weak μ-semistability.**

The proof uses purity twice and visibly: it is what gives every nonzero subobject positive
multiplicity, so that its slope is finite rather than `⊤`, and it is what puts that subobject
into the Gieseker quantifier with a reduced Hilbert function that is not the junk value. For a
non-pure sheaf the statement is **false**: a nonzero multiplicity-zero subobject has slope `⊤`,
which exceeds every finite slope, while satisfying the Gieseker order vacuously.

Only this direction is delivered. The reverse implication is not in scope. -/
theorem giesekerSemistable_implies_muSemistable (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (P.weakSlopeData h).toWeakStabilityFunction.IsSemistable F := by
  refine ⟨hF.not_isZero, fun B hB ↦ ?_⟩
  have hmono : Mono (B.arrow) := inferInstance
  have hBpos : 0 < P.multiplicity (B : Coh X) := hF.1.2 (B : Coh X) B.arrow hmono hB
  exact topSlope_le_of_giesekerLE h hBpos hF.multiplicity_pos
    (hF.2 (B : Coh X) B.arrow hmono hB)

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
