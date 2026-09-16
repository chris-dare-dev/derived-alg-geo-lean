/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Coefficients
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Slope
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeGeometry
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeTop

/-!
# μ-slope stability on `Coh X`, the first geometric slope datum

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
`Abelian/Stability/Weak/Slope.lean`'s own docstring says the corresponding two
fields are geometric input there too, and that both hold on a polarised surface; the strict form
of the second is false on a surface, which is why the curve case below is a separate datum.

## Rank stays integral, degree does not

`WeakSlopeData.degreeHom` is real-valued, so the integral degree coefficient is composed with
`Int.castAddHom ℝ` here. The rank stays integral, and that is not incidental: integrality of the
rank is what the boundary arguments of the Mukai lane use. The multiplicity homomorphism is
therefore handed over unchanged.

## What this file is not

It is not the Gieseker theory, and it does not import it. μ-stability orders sheaves by one
ratio of Hilbert coefficients; Gieseker stability orders them by the whole reduced Hilbert
polynomial at infinity. The two are compared — in one direction, for pure sheaves — by
`Stability/Comparison.lean`, which imports both siblings and is imported by neither.

Until MO1.08 (#1319) this file was `Gieseker/MuStability.lean`, a child of the Gieseker
directory, and the μ-Harder–Narasimhan existence theorem sat below `Gieseker/HarderNarasimhan/`.
Nothing in either mentions the Gieseker order. Their new home is `Slope/`, a sibling of
`Gieseker/` over the shared `HilbertPolynomial.lean`, `Coefficients.lean` and `Purity.lean`. The
directory name is the only thing that changed: `Slope/HarderNarasimhan/Existence.lean` proves
HN existence for the **μ-slope**, and must not be read as proving it for Gieseker stability.

## Placement

`Slope/` reaches `CategoryTheory/Abelian/Stability/` and stops there. It needs no t-structure, no
heart and no triangulated category, which is what the abelian owner of the slope theory buys:
the geometric instantiation of a slope datum is independent of the derived category the
Bridgeland theory is stated in. `Slope/HarderNarasimhan/HeartTransport.lean` is the one module
that crosses into the derived category, and it is deliberately a leaf.
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
`Abelian/Stability/Weak/Slope.lean`. -/
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

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
