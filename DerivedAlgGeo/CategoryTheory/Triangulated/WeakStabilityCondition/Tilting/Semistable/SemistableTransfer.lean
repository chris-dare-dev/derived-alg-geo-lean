/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable.ZeroCharge
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Cohomology.Sequence
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.HarderNarasimhan.Heart

/-!
# Transfer of semistability across the tilt

This file owns the transfer results: semistability on the original heart in the
torsion and torsion-free cases, and semistability of an object whose rotated
charge lies on a fixed ray.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.Tilting
open scoped BigOperators ZeroObject

namespace CategoryTheory.Triangulated.WeakStabilityCondition

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

namespace WeakPreStabilityCondition

/-- A charged torsion-class object which is semistable after the phase tilt
was already semistable in the original heart. -/
theorem weakStabilityFunctionOnHeart_isSemistable_of_phaseTors_phaseTiltSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {E : C}
    (hEtors : phaseTors sigma.slicing beta E)
    (hEss :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).IsSemistable E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).charge E ≠ 0) :
    sigma.weakStabilityFunctionOnHeart.IsSemistable E := by
  let P := slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  have hheart : sigma.slicing.toTStructure.heart E :=
    mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0.le E hEtors.1) hEtors.2
  have hE0 : ¬IsZero E := fun hzero => hcharge (W.charge_isZero hzero)
  have him : 0 < (W.charge E).im := by
    have := phaseTiltCharge_im_pos_of_phaseTors sigma hbeta0 hEtors (by
      change phaseTiltRotation beta (W0.charge E) ≠ 0
      simpa [W, W0] using hcharge)
    simpa [W, W0] using this
  have hHom : ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0 := by
    intro A0 hA0 f
    exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable beta hbeta0.le hbeta1
      hEss hcharge hA0 (Or.inl him) f
  apply (sigma.weakStabilityFunctionOnHeart_isSemistable_iff E hheart hE0).mpr
  apply sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hE0
  apply le_antisymm
  · by_contra hnot
    have hgap : sigma.slicing.phiMinus C E hE0 < sigma.slicing.phiPlus C E hE0 :=
      lt_of_not_ge hnot
    let cut :=
      (sigma.slicing.phiMinus C E hE0 + sigma.slicing.phiPlus C E hE0) / 2
    have hminus_cut : sigma.slicing.phiMinus C E hE0 < cut := by
      dsimp [cut]
      linarith
    have hcut_plus : cut < sigma.slicing.phiPlus C E hE0 := by
      dsimp [cut]
      linarith
    have hbeta_cut : beta < cut :=
      (sigma.slicing.phiMinus_gt_of_gtProp C hE0 hEtors.1).trans hminus_cut
    have hplus_one : sigma.slicing.phiPlus C E hE0 ≤ 1 :=
      sigma.slicing.phiPlus_le_of_leProp C hE0 hEtors.2
    have hcut_one : cut < 1 := hcut_plus.trans_le hplus_one
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      sigma.slicing.exists_hn_nonzero_boundaries C hE0
    have hphase : ∀ j : Fin F.n, beta < F.φ j ∧ F.φ j < 2 := by
      intro j
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hE0 :=
            sigma.slicing.phiMinus_gt_of_gtProp C hE0 hEtors.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
              sigma.slicing.phiMinus_eq C E hE0 F hn hlast
          _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ j ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hE0 := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
              (sigma.slicing.phiPlus_eq C E hE0 F hn hfirst).symm
          _ ≤ 1 := hplus_one
          _ < 2 := by norm_num
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff_with_upper_bound C F hphase hn (t := cut)
    have hXle : sigma.slicing.leProp C 1 X := by
      have hYshift : sigma.slicing.leProp C 1 (Y⟦(-1 : ℤ)⟧) := by
        have hs := sigma.slicing.leProp_shift C cut Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hs
      exact sigma.slicing.leProp_of_triangle C 1 hYshift hEtors.2
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C beta Y := by
      have hXshift : sigma.slicing.gtProp C beta (X⟦(1 : ℤ)⟧) := by
        have hs := sigma.slicing.gtProp_shift C cut X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hs
      exact sigma.slicing.gtProp_of_triangle C beta hEtors.1 hXshift
        (rot_of_distTriang _ hdist)
    have hXtors : phaseTors sigma.slicing beta X :=
      ⟨sigma.slicing.gtProp_anti C hbeta_cut.le X hXgt, hXle⟩
    have hYtors : phaseTors sigma.slicing beta Y :=
      ⟨hYgt, sigma.slicing.leProp_mono C hcut_one.le Y hYle⟩
    have hX0 : ¬IsZero X := by
      intro hzero
      haveI : IsIso g :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f g d) hdist).mp hzero
      have hEle : sigma.slicing.leProp C cut E :=
        ObjectProperty.prop_of_iso (sigma.slicing.leProp C cut) (asIso g).symm hYle
      linarith [sigma.slicing.phiPlus_le_of_leProp C hE0 hEle]
    have hY0 : ¬IsZero Y := by
      intro hzero
      haveI : IsIso f :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g d) hdist).mp hzero
      have hEgt : sigma.slicing.gtProp C cut E :=
        ObjectProperty.prop_of_iso (sigma.slicing.gtProp C cut) (asIso f) hXgt
      linarith [sigma.slicing.phiMinus_gt_of_gtProp C hE0 hEgt]
    have hXheart : sigma.slicing.toTStructure.heart X :=
      mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_anti C hbeta0.le X hXtors.1) hXtors.2
    have hYheart : sigma.slicing.toTStructure.heart Y :=
      mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_anti C hbeta0.le Y hYtors.1) hYtors.2
    have hXtilt : P.tilt.heart X := P.tors_mem_tilt_heart hXtors
    have hYtilt : P.tilt.heart Y := P.tors_mem_tilt_heart hYtors
    have hXcharge : W0.charge X ≠ 0 := by
      intro hXZ
      have hfzero := hHom X ⟨hXheart, hXZ⟩ f
      let X' : P.tilt.heart.FullSubcategory := ⟨X, hXtilt⟩
      let E' : P.tilt.heart.FullSubcategory := ⟨E, hEss.1⟩
      let Y' : P.tilt.heart.FullSubcategory := ⟨Y, hYtilt⟩
      let f' : X' ⟶ E' := ObjectProperty.homMk f
      let g' : E' ⟶ Y' := ObjectProperty.homMk g
      have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
        (C := C) P.tilt (A := X') (B := E') (Q := Y')
          (f := f') (g := g') (δ := d) hdist
      letI : Mono f' := hshort.mono_f
      have hfzero' : f' = 0 := by ext; exact hfzero
      have hXzero' : IsZero X' := IsZero.of_mono_eq_zero f' hfzero'
      exact hX0 (P.tilt.heart.ι.map_isZero hXzero')
    have hYplus : sigma.slicing.phiPlus C Y hY0 ≤ cut :=
      sigma.slicing.phiPlus_le_of_leProp C hY0 hYle
    have hXminus : cut < sigma.slicing.phiMinus C X hX0 :=
      sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXgt
    have hslopeYX : W.slope Y < W.slope X :=
      phaseTilt_slope_lt_of_phase_separated sigma W hYheart hXheart hYtilt hXtilt
        (by rfl) (by rfl) hY0 hX0 (hYplus.trans_lt hXminus)
        (hYplus.trans_lt hcut_one) hXcharge
    have hslopeXY : W.slope X ≤ W.slope Y :=
      hEss.2 hXtilt hYtilt hX0 hY0 f g d hdist
    exact (not_lt_of_ge hslopeXY) hslopeYX
  · exact sigma.slicing.phiMinus_le_phiPlus C E hE0

/-- If the shift of a charged torsion-free object is semistable in the
tilted heart, the unshifted object is semistable in the original heart. -/
theorem weakStabilityFunctionOnHeart_isSemistable_of_phaseFree_shiftSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {U : C}
    (hUfree : phaseFree sigma.slicing beta U)
    (hUss :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable
        (U⟦(1 : ℤ)⟧))
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
        (U⟦(1 : ℤ)⟧) ≠ 0) :
    sigma.weakStabilityFunctionOnHeart.IsSemistable U := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  have hheart : sigma.slicing.toTStructure.heart U :=
    mem_heart_of_bounds sigma.slicing hUfree.1
      (sigma.slicing.leProp_mono C hbeta1.le U hUfree.2)
  have hU0 : ¬IsZero U := by
    intro hzero
    apply hcharge
    exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  apply (sigma.weakStabilityFunctionOnHeart_isSemistable_iff U hheart hU0).mpr
  apply sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hU0
  apply le_antisymm
  · by_contra hnot
    have hgap : sigma.slicing.phiMinus C U hU0 < sigma.slicing.phiPlus C U hU0 :=
      lt_of_not_ge hnot
    let cut :=
      (sigma.slicing.phiMinus C U hU0 + sigma.slicing.phiPlus C U hU0) / 2
    have hminus_cut : sigma.slicing.phiMinus C U hU0 < cut := by
      dsimp [cut]
      linarith
    have hcut_plus : cut < sigma.slicing.phiPlus C U hU0 := by
      dsimp [cut]
      linarith
    have hzero_cut : 0 < cut :=
      (sigma.slicing.phiMinus_gt_of_gtProp C hU0 hUfree.1).trans hminus_cut
    have hplus_beta : sigma.slicing.phiPlus C U hU0 ≤ beta :=
      sigma.slicing.phiPlus_le_of_leProp C hU0 hUfree.2
    have hcut_beta : cut < beta := hcut_plus.trans_le hplus_beta
    have hcut_one : cut < 1 := hcut_beta.trans hbeta1
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      sigma.slicing.exists_hn_nonzero_boundaries C hU0
    have hphase : ∀ j : Fin F.n, (0 : ℝ) < F.φ j ∧ F.φ j < 2 := by
      intro j
      constructor
      · calc
          0 < sigma.slicing.phiMinus C U hU0 :=
            sigma.slicing.phiMinus_gt_of_gtProp C hU0 hUfree.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
              sigma.slicing.phiMinus_eq C U hU0 F hn hlast
          _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ j ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C U hU0 := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
              (sigma.slicing.phiPlus_eq C U hU0 F hn hfirst).symm
          _ ≤ beta := hplus_beta
          _ < 1 := hbeta1
          _ < 2 := by norm_num
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff_with_upper_bound C F hphase hn (t := cut)
    have hXle : sigma.slicing.leProp C beta X := by
      have hYshift : sigma.slicing.leProp C beta (Y⟦(-1 : ℤ)⟧) := by
        have hs := sigma.slicing.leProp_shift C cut Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hs
      exact sigma.slicing.leProp_of_triangle C beta hYshift hUfree.2
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C 0 Y := by
      have hXshift : sigma.slicing.gtProp C 0 (X⟦(1 : ℤ)⟧) := by
        have hs := sigma.slicing.gtProp_shift C cut X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hs
      exact sigma.slicing.gtProp_of_triangle C 0 hUfree.1 hXshift
        (rot_of_distTriang _ hdist)
    have hXfree : phaseFree sigma.slicing beta X :=
      ⟨sigma.slicing.gtProp_anti C hzero_cut.le X hXgt, hXle⟩
    have hYfree : phaseFree sigma.slicing beta Y :=
      ⟨hYgt, sigma.slicing.leProp_mono C hcut_beta.le Y hYle⟩
    have hX0 : ¬IsZero X := by
      intro hzero
      haveI : IsIso g :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f g d) hdist).mp hzero
      have hUle : sigma.slicing.leProp C cut U :=
        ObjectProperty.prop_of_iso (sigma.slicing.leProp C cut) (asIso g).symm hYle
      linarith [sigma.slicing.phiPlus_le_of_leProp C hU0 hUle]
    have hY0 : ¬IsZero Y := by
      intro hzero
      haveI : IsIso f :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g d) hdist).mp hzero
      have hUgt : sigma.slicing.gtProp C cut U :=
        ObjectProperty.prop_of_iso (sigma.slicing.gtProp C cut) (asIso f) hXgt
      linarith [sigma.slicing.phiMinus_gt_of_gtProp C hU0 hUgt]
    have hXheart : sigma.slicing.toTStructure.heart X :=
      mem_heart_of_bounds sigma.slicing hXfree.1
        (sigma.slicing.leProp_mono C hbeta1.le X hXfree.2)
    have hYheart : sigma.slicing.toTStructure.heart Y :=
      mem_heart_of_bounds sigma.slicing hYfree.1
        (sigma.slicing.leProp_mono C hbeta1.le Y hYfree.2)
    have hXtilt : P.tilt.heart (X⟦(1 : ℤ)⟧) := P.free_shift_mem_tilt_heart hXfree
    have hYtilt : P.tilt.heart (Y⟦(1 : ℤ)⟧) := P.free_shift_mem_tilt_heart hYfree
    have hXplus : sigma.slicing.phiPlus C X hX0 ≤ beta :=
      sigma.slicing.phiPlus_le_of_leProp C hX0 hXfree.2
    obtain ⟨hXupper, -⟩ := sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus
      X hXheart hX0 (hXplus.trans_lt hbeta1)
    have hXcharge : W0.charge X ≠ 0 := semiClosedUpperHalfPlane_ne_zero hXupper
    have hYplus : sigma.slicing.phiPlus C Y hY0 ≤ cut :=
      sigma.slicing.phiPlus_le_of_leProp C hY0 hYle
    have hXminus : cut < sigma.slicing.phiMinus C X hX0 :=
      sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXgt
    have hWX : W.charge (X⟦(1 : ℤ)⟧) = phaseTiltRotation beta (-(W0.charge X)) := by
      simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation, K₀.of_shift_one]
    have hWY : W.charge (Y⟦(1 : ℤ)⟧) = phaseTiltRotation beta (-(W0.charge Y)) := by
      simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation, K₀.of_shift_one]
    have hslopeYX : W.slope (Y⟦(1 : ℤ)⟧) < W.slope (X⟦(1 : ℤ)⟧) :=
      phaseTilt_slope_shift_lt_shift_of_phase_separated sigma W hYheart hXheart
        hYtilt hXtilt hWY hWX hY0 hX0 (hYplus.trans_lt hXminus)
        (hYplus.trans_lt hcut_one) hXcharge
    let Tshift := (shiftFunctor (Triangle C) (1 : ℤ)).obj (Triangle.mk f g d)
    have hTshift : Tshift ∈ distTriang C := Triangle.shift_distinguished _ hdist 1
    have hslopeXY : W.slope (X⟦(1 : ℤ)⟧) ≤ W.slope (Y⟦(1 : ℤ)⟧) :=
      hUss.2 hXtilt hYtilt
        (fun h => hX0 (by
          rw [IsZero.iff_id_eq_zero] at h ⊢
          exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using h)))
        (fun h => hY0 (by
          rw [IsZero.iff_id_eq_zero] at h ⊢
          exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using h)))
        Tshift.mor₁ Tshift.mor₂ Tshift.mor₃ hTshift
    exact (not_lt_of_ge hslopeXY) hslopeYX
  · exact sigma.slicing.phiMinus_le_phiPlus C U hU0

/-- A ray criterion for semistability in the tilted heart.  The object has a
single nonzero-charge phase `theta`; the Hom condition excludes zero-charge
subobjects when that ray lies in the open upper half-plane. -/
theorem phaseTiltWeakStabilityFunction_isSemistable_of_ray
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {E : C} (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    {theta m : ℝ} (htheta : theta ∈ Set.Ioc (0 : ℝ) 1) (hm : 0 < m)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E =
        (m : ℂ) *
          Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I))
    (hle : sigma.slicing.leProp C (beta + theta) E)
    (hHom : 0 <
        ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
      ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  refine ⟨hEtilt, ?_⟩
  intro A B hAtilt hBtilt hA0 hB0 f g d hdist
  have hAint := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hAtilt
  have hBint := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hBtilt
  have hBshift : sigma.slicing.leProp C beta (B⟦(-1 : ℤ)⟧) := by
    have hshift := sigma.slicing.leProp_shift C (beta + 1) B (-1) hBint.2
    convert hshift using 1
    all_goals push_cast
    all_goals ring
  have hAle : sigma.slicing.leProp C (beta + theta) A :=
    sigma.slicing.leProp_of_triangle C (beta + theta)
      (sigma.slicing.leProp_mono C (by linarith [htheta.1]) _ hBshift) hle
      (inv_rot_of_distTriang _ hdist)
  have hsum : W.charge E = W.charge A + W.charge B :=
    W.charge_triangle' hdist
  by_cases htheta_one : theta = 1
  · have hEim : (W.charge E).im = 0 := by
      rw [hcharge, htheta_one, Complex.exp_ofReal_mul_I]
      simp
    have hAim_nonneg : 0 ≤ (W.charge A).im := by
      rcases W.upper A hAtilt hA0 with him | ⟨him, -⟩
      · exact him.le
      · exact him.ge
    have hBim_nonneg : 0 ≤ (W.charge B).im := by
      rcases W.upper B hBtilt hB0 with him | ⟨him, -⟩
      · exact him.le
      · exact him.ge
    have him_sum : (W.charge A).im + (W.charge B).im = 0 := by
      have := congrArg Complex.im hsum
      simpa [hEim] using this.symm
    have hAim : (W.charge A).im = 0 := by linarith
    have hBim : (W.charge B).im = 0 := by linarith
    rw [W.slope_of_im_nonpos (by rw [hAim]; exact lt_irrefl 0),
      W.slope_of_im_nonpos (by rw [hBim]; exact lt_irrefl 0)]
  · have htheta_lt : theta < 1 := lt_of_le_of_ne htheta.2 htheta_one
    have hEim : 0 < (W.charge E).im := by
      rw [hcharge, Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, zero_mul, mul_one, add_zero,
        zero_add]
      exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos Real.pi_pos htheta.1)
        (by nlinarith [mul_lt_mul_of_pos_left htheta_lt Real.pi_pos]))
    have hAcross : 0 ≤ cross (W.charge A) (W.charge E) := by
      have hcross := rotatedCharge_cross_ray_nonneg_of_bounds sigma hm.le htheta.2
        hAint.1 hAle
      rw [← hcharge] at hcross
      exact hcross
    have hAcharge : W.charge A ≠ 0 := by
      intro hAzero
      have hsigmaZero : sigma.zeroCharge A :=
        (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A).mp
          ⟨hAtilt, hAzero⟩
      have hfzero : f = 0 := hHom hEim A hsigmaZero f
      let A' : P.tilt.heart.FullSubcategory := ⟨A, hAtilt⟩
      let E' : P.tilt.heart.FullSubcategory := ⟨E, hEtilt⟩
      let B' : P.tilt.heart.FullSubcategory := ⟨B, hBtilt⟩
      let f' : A' ⟶ E' := ObjectProperty.homMk f
      let g' : E' ⟶ B' := ObjectProperty.homMk g
      have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
        (C := C) P.tilt (A := A') (B := E') (Q := B')
          (f := f') (g := g') (δ := d) hdist
      letI : Mono f' := hshort.mono_f
      have hfzero' : f' = 0 := by ext; exact hfzero
      have hAzero' : IsZero A' := IsZero.of_mono_eq_zero f' hfzero'
      exact hA0 ((P.tilt).heart.ι.map_isZero hAzero')
    have hAim : 0 < (W.charge A).im := by
      rcases W.upper A hAtilt hA0 with him | ⟨him, hre⟩
      · exact him
      · exfalso
        have hre0 : (W.charge A).re = 0 := by
          unfold cross at hAcross
          rw [him] at hAcross
          simp only [zero_mul, sub_zero] at hAcross
          nlinarith
        apply hAcharge
        exact Complex.ext hre0 him
    by_cases hBim : 0 < (W.charge B).im
    · have hcrossAB : 0 ≤ cross (W.charge A) (W.charge B) := by
        have heq : cross (W.charge A) (W.charge B) =
            cross (W.charge A) (W.charge E) := by
          rw [hsum]
          simp [cross]
          ring
        rw [heq]
        exact hAcross
      rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim]
      exact_mod_cast (div_le_div_iff₀ hAim hBim).2 (by
        unfold cross at hcrossAB
        nlinarith)
    · rw [W.slope_of_im_nonpos hBim]
      exact le_top

/-! ## The two classes in Lemma 14.17 -/

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition
