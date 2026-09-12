/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.Seesaw

/-!
# Reducing Grothendieck slope boundedness to quotient degrees

For a fixed coherent sheaf `F`, Grothendieck's boundedness lemma says that the slopes of its
positive-multiplicity subsheaves are bounded above. This file identifies the exact remaining
geometric statement: the codimension-one Hilbert coefficients of the corresponding quotients
are bounded below.

The reduction is an equivalence, not a weakening of `MuHNInput`. Additivity writes
`degree(F) = degree(B) + degree(F/B)`. In one direction, a lower bound for `degree(F/B)` bounds
the numerator of the slope of `B`; in the other, the already-proved bound
`multiplicity(B) ≤ multiplicity(F)` turns a slope bound into a numerator bound and hence a lower
bound for `degree(F/B)`.

## The remaining geometric obligation

Nothing in the current `PolarizedVarietyData` API says that `P.L` is ample, and the tree has no
uniform Castelnuovo--Mumford regularity theorem or equivalent graded-submodule estimate.
Consequently this file does not claim Grothendieck boundedness. It isolates it as the sharp
reusable obligation `quotientDegree_bddBelow` accepted by
`MuHNInput.ofQuotientDegreeLowerBound`: for each ambient sheaf, uniformly lower-bound the
codimension-one Hilbert coefficient of every quotient whose kernel has positive multiplicity.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-- The codimension-one Hilbert coefficient of a coherent sheaf is the sum of those of a
subobject and its canonical quotient. -/
theorem hilbertDegreeCoefficient_eq_add_cokernel {F : Coh X} (B : Subobject F) :
    P.hilbertDegreeCoefficient F =
      P.hilbertDegreeCoefficient (B : Coh X) +
        P.hilbertDegreeCoefficient (cokernel B.arrow) := by
  have hSE : (ShortComplex.mk B.arrow (cokernel.π B.arrow) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel B.arrow }
  exact P.hilbertDegreeCoefficient_shortExact (S :=
    ShortComplex.mk B.arrow (cokernel.π B.arrow) (by simp)) hSE

/-- **Grothendieck slope boundedness is exactly lower boundedness of quotient degrees.**

For a fixed `F`, the slopes of its nonzero positive-multiplicity subobjects are bounded above
if and only if the codimension-one Hilbert coefficients of their canonical quotients are bounded
below. Positive multiplicity already implies that the subobject is nonzero, so no separate
nonzero hypothesis is needed on the quotient-degree side. -/
theorem slope_bddAbove_iff_quotientDegree_bddBelow (h : MuPositivityData P) (F : Coh X) :
    (∃ μ₀ : ℝ, ∀ B : Subobject F, ¬IsZero (B : Coh X) →
      0 < P.multiplicity (B : Coh X) →
        (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) /
          (P.multiplicity (B : Coh X) : ℝ) ≤ μ₀) ↔
      (∃ d₀ : ℤ, ∀ B : Subobject F, 0 < P.multiplicity (B : Coh X) →
        d₀ ≤ P.hilbertDegreeCoefficient (cokernel B.arrow)) := by
  constructor
  · rintro ⟨μ₀, hμ₀⟩
    let U : ℝ := max μ₀ 0
    let C : ℤ := ⌈U * (P.multiplicity F : ℝ)⌉
    refine ⟨P.hilbertDegreeCoefficient F - C, fun B hBpos ↦ ?_⟩
    have hBne : ¬IsZero (B : Coh X) := by
      intro hBzero
      have hBzero' := P.multiplicity_of_isZero hBzero
      omega
    have hmBpos : (0 : ℝ) < (P.multiplicity (B : Coh X) : ℝ) := by
      exact_mod_cast hBpos
    have hslope := hμ₀ B hBne hBpos
    have hdegree_mu : (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤
        μ₀ * (P.multiplicity (B : Coh X) : ℝ) :=
      (div_le_iff₀ hmBpos).mp hslope
    have hμU : μ₀ ≤ U := by
      exact le_max_left _ _
    have hUnonneg : 0 ≤ U := by
      exact le_max_right _ _
    have hmBF : (P.multiplicity (B : Coh X) : ℝ) ≤ (P.multiplicity F : ℝ) := by
      exact_mod_cast P.multiplicity_subobject_le h B
    have hdegree_U : (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤
        U * (P.multiplicity F : ℝ) := by
      calc
        (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤
            μ₀ * (P.multiplicity (B : Coh X) : ℝ) := hdegree_mu
        _ ≤ U * (P.multiplicity (B : Coh X) : ℝ) :=
          mul_le_mul_of_nonneg_right hμU (le_of_lt hmBpos)
        _ ≤ U * (P.multiplicity F : ℝ) :=
          mul_le_mul_of_nonneg_left hmBF hUnonneg
    have hdegree_C_real : (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤ (C : ℝ) := by
      exact le_trans hdegree_U (Int.le_ceil _)
    have hdegree_C : P.hilbertDegreeCoefficient (B : Coh X) ≤ C := by
      exact_mod_cast hdegree_C_real
    have hadd := P.hilbertDegreeCoefficient_eq_add_cokernel B
    omega
  · rintro ⟨d₀, hd₀⟩
    let D : ℝ := ((P.hilbertDegreeCoefficient F - d₀ : ℤ) : ℝ)
    let U : ℝ := max D 0
    refine ⟨U, fun B _ hBpos ↦ ?_⟩
    have hquotient := hd₀ B hBpos
    have hadd := P.hilbertDegreeCoefficient_eq_add_cokernel B
    have hdegree : P.hilbertDegreeCoefficient (B : Coh X) ≤
        P.hilbertDegreeCoefficient F - d₀ := by
      omega
    have hdegree_real : (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤ D := by
      change (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤
        ((P.hilbertDegreeCoefficient F - d₀ : ℤ) : ℝ)
      exact_mod_cast hdegree
    have hmBpos : (0 : ℝ) < (P.multiplicity (B : Coh X) : ℝ) := by
      exact_mod_cast hBpos
    apply (div_le_iff₀ hmBpos).mpr
    calc
      (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) ≤ D := hdegree_real
      _ ≤ U := le_max_left _ _
      _ = U * 1 := by ring
      _ ≤ U * (P.multiplicity (B : Coh X) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact_mod_cast (show (1 : ℤ) ≤ P.multiplicity (B : Coh X) by omega)

end PolarizedVarietyData

/-- On a Noetherian scheme, a uniform lower bound for quotient degree coefficients is exactly
the remaining input needed to construct sheaf-level μ-Harder--Narasimhan filtrations. This
constructor does not assert that bound: it packages a proof of the geometric obligation through
`PolarizedVarietyData.slope_bddAbove_iff_quotientDegree_bddBelow`. -/
theorem MuHNInput.ofQuotientDegreeLowerBound {P : PolarizedVarietyData k X}
    {h : MuPositivityData P} [IsNoetherian X]
    (quotientDegree_bddBelow : ∀ F : Coh X, ∃ d₀ : ℤ, ∀ B : Subobject F,
      0 < P.multiplicity (B : Coh X) →
        d₀ ≤ P.hilbertDegreeCoefficient (cokernel B.arrow)) :
    MuHNInput P h :=
  MuHNInput.ofSlopeBoundedness fun F ↦
    (P.slope_bddAbove_iff_quotientDegree_bddBelow h F).mpr
      (quotientDegree_bddBelow F)

end AlgebraicGeometry.Stability.Gieseker
