/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Analysis.Complex.PhaseGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Subobject
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Phase geometry for owner stability functions

The phase see-saw for a short exact sequence in an abelian category, read off
the neutral half-plane argument bounds in `Analysis/Complex/PhaseGeometry.lean`.

Those bounds -- `phaseCross`, `arg_add_le_max`, `min_arg_le_arg_add`,
`arg_add_lt_max` and the half-plane closure facts under them -- used to be
declared here. They say nothing about categories, and MO1.13 (#1324) moved them
to their neutral owner so that the Euclidean core of the mass-subadditivity
proof could reach them without reaching stability. This file keeps the
`StabilityFunction` statements, which genuinely need an abelian category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- Upper phase see-saw for a short exact sequence. -/
theorem phase_le_max_of_shortExact (Z : StabilityFunction A)
    (S : ShortComplex A) (hS : S.ShortExact)
    (h₁ : ¬IsZero S.X₁) (h₃ : ¬IsZero S.X₃) :
    Z.phase S.X₂ ≤ max (Z.phase S.X₁) (Z.phase S.X₃) := by
  rw [phase, phase, phase, Z.additive S hS]
  have h := arg_add_le_max (Z.nonzero_mem S.X₁ h₁) (Z.nonzero_mem S.X₃ h₃)
  rw [max_div_div_right Real.pi_pos.le]
  exact (div_le_div_iff_of_pos_right Real.pi_pos).2 h

/-- Lower phase see-saw for a short exact sequence. -/
theorem min_phase_le_of_shortExact (Z : StabilityFunction A)
    (S : ShortComplex A) (hS : S.ShortExact)
    (h₁ : ¬IsZero S.X₁) (h₃ : ¬IsZero S.X₃) :
    min (Z.phase S.X₁) (Z.phase S.X₃) ≤ Z.phase S.X₂ := by
  rw [phase, phase, phase, Z.additive S hS]
  rw [min_div_div_right Real.pi_pos.le]
  exact (div_le_div_iff_of_pos_right Real.pi_pos).2
    (min_arg_le_arg_add (Z.nonzero_mem S.X₁ h₁) (Z.nonzero_mem S.X₃ h₃))

/-- A nonzero quotient of a semistable object has phase at least the source
phase. -/
theorem phase_le_of_epi (Z : StabilityFunction A) {E Q : A}
    (p : E ⟶ Q) [Epi p] (hE : Z.IsSemistable E) (hQ : ¬IsZero Q) :
    Z.phase E ≤ Z.phase Q := by
  by_cases hker : IsZero (kernel p)
  · haveI : Mono p := Preadditive.mono_of_kernel_zero
      (zero_of_source_iso_zero _ hker.isoZero)
    haveI : IsIso p := isIso_of_mono_of_epi p
    exact le_of_eq (Z.phase_eq_of_iso (asIso p))
  · have hker_le : Z.phase (kernel p) ≤ Z.phase E := by
      calc Z.phase (kernel p)
          = Z.phase (kernelSubobject p : A) :=
            Z.phase_eq_of_iso (kernelSubobjectIso p).symm
        _ ≤ Z.phase E := hE.2 _ fun hzero =>
            hker (hzero.of_iso (kernelSubobjectIso p).symm)
    by_contra h
    have hQ_lt : Z.phase Q < Z.phase E := lt_of_not_ge h
    have hshort : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
    have hsum := Z.additive _ hshort
    have hker_mem := Z.nonzero_mem (kernel p) hker
    have hQ_mem := Z.nonzero_mem Q hQ
    have harg_ker : arg (Z.charge (kernel p)) ≤ arg (Z.charge E) := by
      exact (div_le_div_iff_of_pos_right Real.pi_pos).1 hker_le
    have harg_Q : arg (Z.charge Q) < arg (Z.charge E) := by
      exact (div_lt_div_iff_of_pos_right Real.pi_pos).1 hQ_lt
    rw [hsum] at harg_ker harg_Q
    have hub := arg_add_le_max hker_mem hQ_mem
    have hQ_lt_max := lt_of_lt_of_le harg_Q hub
    have hker_gt_Q : arg (Z.charge Q) < arg (Z.charge (kernel p)) := by
      simpa only [lt_max_iff, lt_irrefl, or_false, abelianDatum_cl] using hQ_lt_max
    have hstrict := arg_add_lt_max hker_mem hQ_mem (ne_of_gt hker_gt_Q)
    simp only [abelianDatum_cl] at hstrict
    rw [max_eq_left hker_gt_Q.le] at hstrict
    exact (not_lt_of_ge harg_ker) hstrict

/-- Hom-vanishing between semistable objects of decreasing phase. -/
theorem hom_eq_zero_of_semistable_phase_gt (Z : StabilityFunction A)
    {E F : A} (hE : Z.IsSemistable E) (hF : Z.IsSemistable F)
    (hphase : Z.phase F < Z.phase E) (f : E ⟶ F) : f = 0 := by
  by_contra hf
  have himage : ¬IsZero (image f) := by
    intro hzero
    apply hf
    have hι : image.ι f = 0 := zero_of_source_iso_zero _ hzero.isoZero
    rw [← image.fac f, hι, comp_zero]
  have hsource := Z.phase_le_of_epi (factorThruImage f) hE himage
  have htarget : Z.phase (image f) ≤ Z.phase F := by
    calc Z.phase (image f)
        = Z.phase (imageSubobject f : A) :=
          Z.phase_eq_of_iso (imageSubobjectIso f).symm
      _ ≤ Z.phase F := hF.2 _ fun hzero =>
          himage (hzero.of_iso (imageSubobjectIso f).symm)
  exact (not_lt_of_ge (hsource.trans htarget)) hphase

end StabilityFunction

end CategoryTheory.Triangulated
