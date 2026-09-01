/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Slope
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Cutoff

/-!
# Where the rank-zero objects go

`Slope.lean` puts a nonzero object of rank zero on the negative real axis, by
`degree_pos_of_rank_zero`. This file draws the consequence for the cut of
`Cutoff.lean`: such an object has **phase one**, the largest a phase can be, and
so lies in the torsion class `T β` for every cutoff `β < 1`.

That is not a convention chosen here. It is forced by the charge
`-degree + i · rank`, and it is what makes the geometric statement come out
right: on a surface the rank-zero coherent sheaves are the torsion sheaves, and
Bridgeland's `T β` contains all of them at every `β`.

## Why the Harder–Narasimhan filtration cannot get in the way

Membership in `T β` asks for `β < φ⁻`, not for semistability, so the argument
has to reach the *last* HN factor of a rank-zero object. It is again rank zero:
rank is additive and nonnegative, so a subobject and its quotient both inherit
rank zero from the whole, and the last HN factor is such a quotient. Hence its
phase is one, hence `φ⁻ = 1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace SlopeData

variable (D : SlopeData A)

/-- Rank zero passes to both ends of a short exact sequence, because rank is
additive and never negative. -/
theorem rank_eq_zero_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h : D.rank S.X₂ = 0) : D.rank S.X₁ = 0 ∧ D.rank S.X₃ = 0 := by
  have hadd := D.rank_additive S hS
  have h1 : 0 ≤ D.rank S.X₁ := D.rank_nonneg S.X₁
  have h3 : 0 ≤ D.rank S.X₃ := D.rank_nonneg S.X₃
  omega

/-- **A nonzero object of rank zero has phase one.**  Its charge is
`-degree`, a negative real, and `arg` of a negative real is `π`. -/
theorem phase_eq_one_of_rank_zero {E : A} (hE : ¬IsZero E) (h : D.rank E = 0) :
    D.toStabilityFunction.phase E = 1 := by
  have hdeg : 0 < D.degree E := D.degree_pos_of_rank_zero E hE h
  have hreal : (0 : ℝ) < (D.degree E : ℝ) := by exact_mod_cast hdeg
  have hz : D.charge E = ((-(D.degree E : ℝ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [charge, h]
  rw [StabilityFunction.phase, toStabilityFunction_charge, hz,
    arg_ofReal_of_neg (by linarith)]
  field_simp

/-- **Rank-zero objects are torsion at every cutoff below one.**  The last
Harder–Narasimhan factor of a rank-zero object again has rank zero, so `φ⁻` is
one. -/
theorem mem_hnTors_of_rank_zero (hHN : D.toStabilityFunction.HasHNProperty)
    {β : ℝ} (hβ : β < 1) {E : A} (hE : ¬IsZero E) (h : D.rank E = 0) :
    E ∈ StabilityFunction.hnTors D.toStabilityFunction β := by
  obtain ⟨F⟩ := hHN E hE
  have hn := F.nonempty
  refine Or.inr ⟨F, ?_⟩
  set last : Fin F.n := ⟨F.n - 1, by lia⟩ with hlastdef
  have hlast : F.chain last.succ = ⊤ := by
    have hindex : last.succ = ⟨F.n, by lia⟩ := Fin.ext (by simp [hlastdef]; lia)
    rw [hindex, F.chain_top]
  set i := Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
    (le_of_lt (F.chain_strictMono last.castSucc_lt_succ)) with hidef
  have hSE := StabilityFunction.shortExact_of_mono i
  have hmid : D.rank ((F.chain last.succ : Subobject E) : A) = 0 := by
    rw [hlast]
    rw [D.rank_iso (asIso (⊤ : Subobject E).arrow)]
    exact h
  have hfactor : D.rank (cokernel i) = 0 :=
    (D.rank_eq_zero_of_shortExact hSE hmid).2
  have hne : ¬IsZero (cokernel i) := (F.factor_semistable last).1
  have hphase : D.toStabilityFunction.phase (cokernel i) = 1 :=
    D.phase_eq_one_of_rank_zero hne hfactor
  have : F.phiMinus = 1 := by
    rw [AbelianHNFiltration.phiMinus, ← F.factor_phase last]
    exact hphase
  rw [this]
  exact hβ

end SlopeData

end CategoryTheory.Triangulated
