/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.PhaseArithmetic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.IntrinsicPhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic

/-!
# Rotated charge sums along owner filtrations

Rotated imaginary parts are additive along owner Postnikov towers.  Strict
signs on all nonzero HN factors therefore give a strict sign on the ambient
object as soon as one factor is known to be nonzero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- Rotated imaginary part of a perturbed charge decomposes over an owner
Postnikov tower. -/
theorem rotatedIm_charge_eq_sum (W : Λ →+ ℂ) {E : C}
    (P : PostnikovTower C E) (ψ : ℝ) :
    rotatedIm (W (classOf C κ E)) ψ =
      ∑ i : Fin P.n, rotatedIm (W (classOf C κ (P.factor i))) ψ := by
  rw [classOf_postnikovTower_eq_sum C κ P, map_sum]
  unfold rotatedIm
  rw [Finset.sum_mul]
  exact map_sum Complex.imAddGroupHom _ _

/-- If all nonzero HN factors have negative rotated charge and the first
factor is nonzero, then the ambient charge has negative rotated part. -/
theorem rotatedIm_charge_neg_of_hn (W : Λ →+ ℂ)
    {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hn : 0 < F.n) (hfirst : ¬IsZero (F.factor ⟨0, hn⟩)) (ψ : ℝ)
    (hneg : ∀ i : Fin F.n, ¬IsZero (F.factor i) →
      rotatedIm (W (classOf C κ (F.factor i))) ψ < 0) :
    rotatedIm (W (classOf C κ E)) ψ < 0 := by
  rw [rotatedIm_charge_eq_sum C W F.toPostnikovTower ψ]
  suffices h : 0 < ∑ i : Fin F.n,
      -rotatedIm (W (classOf C κ (F.factor i))) ψ by
    linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
      (f := fun i => rotatedIm (W (classOf C κ (F.factor i))) ψ)]
  apply lt_of_lt_of_le (neg_pos.mpr (hneg ⟨0, hn⟩ hfirst))
  apply Finset.single_le_sum
    (f := fun i => -rotatedIm (W (classOf C κ (F.factor i))) ψ)
  · intro i _
    by_cases hi : IsZero (F.factor i)
    · simp [classOf_isZero C κ hi, rotatedIm]
    · exact (neg_pos.mpr (hneg i hi)).le
  · exact Finset.mem_univ _

/-- If all nonzero HN factors have positive rotated charge and the first
factor is nonzero, then the ambient charge has positive rotated part. -/
theorem rotatedIm_charge_pos_of_hn (W : Λ →+ ℂ)
    {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hn : 0 < F.n) (hfirst : ¬IsZero (F.factor ⟨0, hn⟩)) (ψ : ℝ)
    (hpos : ∀ i : Fin F.n, ¬IsZero (F.factor i) →
      0 < rotatedIm (W (classOf C κ (F.factor i))) ψ) :
    0 < rotatedIm (W (classOf C κ E)) ψ := by
  rw [rotatedIm_charge_eq_sum C W F.toPostnikovTower ψ]
  apply lt_of_lt_of_le (hpos ⟨0, hn⟩ hfirst)
  apply Finset.single_le_sum
    (f := fun i => rotatedIm (W (classOf C κ (F.factor i))) ψ)
  · intro i _
    by_cases hi : IsZero (F.factor i)
    · simp [classOf_isZero C κ hi, rotatedIm]
    · exact (hpos i hi).le
  · exact Finset.mem_univ _

/-- A nonzero interval object has negative rotated charge when each nonzero
semistable factor in the interval does. -/
theorem Slicing.rotatedIm_charge_neg_of_interval (s : Slicing C)
    (W : Λ →+ ℂ) {E : C} {a b ψ : ℝ}
    (hI : s.intervalProp C a b E) (hE : ¬IsZero E)
    (hneg : ∀ (F : C) (φ : ℝ), s.P φ F → ¬IsZero F →
      a < φ → φ < b → rotatedIm (W (classOf C κ F)) ψ < 0) :
    rotatedIm (W (classOf C κ E)) ψ < 0 := by
  obtain ⟨G, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  apply rotatedIm_charge_neg_of_hn C W G hn hfirst ψ
  intro i hi
  apply hneg _ _ (G.semistable i) hi
  · calc
      a < s.phiMinus C E hE := s.phiMinus_gt_of_intervalProp C hE hI
      _ = G.phiMinus C hn := s.phiMinus_eq C E hE G hn hlast
      _ ≤ G.φ i := (G.phase_mem_range C hn i).1
  · calc
      G.φ i ≤ G.phiPlus C hn := (G.phase_mem_range C hn i).2
      _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE G hn hfirst).symm
      _ < b := s.phiPlus_lt_of_intervalProp C hE hI

/-- A nonzero interval object has positive rotated charge when each nonzero
semistable factor in the interval does. -/
theorem Slicing.rotatedIm_charge_pos_of_interval (s : Slicing C)
    (W : Λ →+ ℂ) {E : C} {a b ψ : ℝ}
    (hI : s.intervalProp C a b E) (hE : ¬IsZero E)
    (hpos : ∀ (F : C) (φ : ℝ), s.P φ F → ¬IsZero F →
      a < φ → φ < b → 0 < rotatedIm (W (classOf C κ F)) ψ) :
    0 < rotatedIm (W (classOf C κ E)) ψ := by
  obtain ⟨G, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  apply rotatedIm_charge_pos_of_hn C W G hn hfirst ψ
  intro i hi
  apply hpos _ _ (G.semistable i) hi
  · calc
      a < s.phiMinus C E hE := s.phiMinus_gt_of_intervalProp C hE hI
      _ = G.phiMinus C hn := s.phiMinus_eq C E hE G hn hlast
      _ ≤ G.φ i := (G.phase_mem_range C hn i).1
  · calc
      G.φ i ≤ G.phiPlus C hn := (G.phase_mem_range C hn i).2
      _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE G hn hfirst).symm
      _ < b := s.phiPlus_lt_of_intervalProp C hE hI

end CategoryTheory.Triangulated
