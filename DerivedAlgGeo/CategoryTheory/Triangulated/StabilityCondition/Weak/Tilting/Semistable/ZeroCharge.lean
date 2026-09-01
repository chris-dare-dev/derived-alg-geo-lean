/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Semistable.TiltedHeart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Cohomology.Sequence

/-!
# Objects of zero tilted charge

This file owns the degenerate locus of the tilt: zero-charge objects of the
tilted heart lie in `P(1)`, the characterisation of that locus, vanishing of
maps out of it into a tilted-semistable object, and the semistability of the
left endpoint that follows.
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

/-- A zero-charge object of the original slicing heart belongs to the
boundary slice `P(1)`. -/
theorem zeroCharge_mem_P_one
    (sigma : WeakPreStabilityCondition v) {E : C}
    (hEheart : sigma.slicing.toTStructure.heart E)
    (hZ : sigma.Z (v (K₀.of C E)) = 0) :
    sigma.slicing.P 1 E := by
  by_cases hzero : IsZero E
  · exact ObjectProperty.prop_of_iso (sigma.slicing.P 1) hzero.isoZero.symm
      (sigma.slicing.zero_mem 1)
  let W := sigma.weakStabilityFunctionOnHeart
  have hss : W.IsSemistable E := by
    refine ⟨hEheart, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    have hEzero : W.zeroCharge E := ⟨hEheart, hZ⟩
    have hAzero := W.zeroCharge_left hA hB hEzero hdist
    have hBzero := W.zeroCharge_right hA hB hEzero hdist
    rw [W.slope_of_im_nonpos (by simp [hAzero.2]),
      W.slope_of_im_nonpos (by simp [hBzero.2])]
  have hPplus := sigma.mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable
    E hzero hss
  obtain ⟨m, hm, hm_strict, hmZ⟩ :=
    sigma.compat' (sigma.slicing.phiPlus C E hzero) E hPplus hzero
  have hm0c : (m : ℂ) = 0 := by
    rw [hZ, eq_comm, mul_eq_zero] at hmZ
    exact hmZ.resolve_right (Complex.exp_ne_zero _)
  have hm0 : m = 0 := by exact_mod_cast hm0c
  have hinter : ∃ n : ℤ, sigma.slicing.phiPlus C E hzero = (n : ℝ) := by
    by_contra h
    push Not at h
    have := hm_strict h
    linarith
  obtain ⟨n, hncast⟩ := hinter
  have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hEheart
  have hpos : 0 < sigma.slicing.phiPlus C E hzero :=
    lt_of_lt_of_le (sigma.slicing.phiMinus_gt_of_gtProp C hzero hbounds.1)
      (sigma.slicing.phiMinus_le_phiPlus C E hzero)
  have hle : sigma.slicing.phiPlus C E hzero ≤ 1 :=
    sigma.slicing.phiPlus_le_of_leProp C hzero hbounds.2
  have hnpos : 0 < n := by exact_mod_cast (hncast ▸ hpos)
  have hnle : n ≤ 1 := by exact_mod_cast (hncast ▸ hle)
  have hn : n = 1 := by omega
  have hphi : sigma.slicing.phiPlus C E hzero = 1 := by simpa [hn] using hncast
  rw [← hphi]
  exact hPplus

/-- Rotation and HRS tilting do not change the zero-charge subcategory:
the zero-charge objects of the tilted heart are precisely the original-heart
objects of zero original charge. -/
theorem phaseTiltWeakStabilityFunction_zeroCharge_iff
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E ↔
      sigma.zeroCharge E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  constructor
  · rintro ⟨hEtilt, hcharge⟩
    have hZ : sigma.Z (v (CategoryTheory.Triangulated.K₀.of C E)) = 0 := by
      have hmul : sigma.Z (v (CategoryTheory.Triangulated.K₀.of C E)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = 0 := by
        simpa [W] using hcharge
      exact (mul_eq_zero.mp hmul).resolve_right (Complex.exp_ne_zero _)
    by_cases hzero : IsZero E
    · exact ⟨ObjectProperty.prop_of_iso sigma.slicing.toTStructure.heart
          hzero.isoZero.symm
          (mem_heart_of_bounds sigma.slicing
            (sigma.slicing.gtProp_zero C 0) (sigma.slicing.leProp_zero C 1)),
        hZ⟩
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      sigma.slicing.exists_hn_nonzero_boundaries C hzero
    let P := F.toPostnikovTower
    let f : Fin F.n → ℂ := fun i =>
      sigma.Z (v (CategoryTheory.Triangulated.K₀.of C (P.factor i))) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
    have hbounds := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hEtilt
    have hphase : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc beta (beta + 1) := by
      intro i
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hzero :=
            sigma.slicing.phiMinus_gt_of_gtProp C hzero hbounds.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
              sigma.slicing.phiMinus_eq C E hzero F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hzero := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
              (sigma.slicing.phiPlus_eq C E hzero F hn hfirst).symm
          _ ≤ beta + 1 :=
            sigma.slicing.phiPlus_le_of_leProp C hzero hbounds.2
    have hsum : ∑ i, f i = 0 := by
      have hdecomp :
          sigma.Z (v (CategoryTheory.Triangulated.K₀.of C E)) *
              Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
            ∑ i, f i := by
        rw [CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum C P,
          map_sum, map_sum, Finset.sum_mul]
      rw [hZ, zero_mul] at hdecomp
      exact hdecomp.symm
    have hfclosed : ∀ i, WeakUpperClosed (f i) := by
      intro i
      by_cases hi : IsZero (P.factor i)
      · simpa [f, CategoryTheory.Triangulated.K₀.of_isZero C hi] using weakUpperClosed_zero
      obtain ⟨m, hm, -, hmZ⟩ :=
        sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
      dsimp [f]
      rw [hmZ]
      exact rotatedRay_weakUpperClosed hm (hphase i)
    have hfactorZ : ∀ i,
        sigma.Z (v (CategoryTheory.Triangulated.K₀.of C (P.factor i))) = 0 := by
      intro i
      have hfi := weakUpperClosed_eq_zero_of_sum_eq_zero f hfclosed hsum i
      dsimp [f] at hfi
      exact (mul_eq_zero.mp hfi).resolve_right (Complex.exp_ne_zero _)
    have hphase_one_of_nonzero : ∀ i : Fin F.n, ¬IsZero (P.factor i) → F.φ i = 1 := by
      intro i hi
      obtain ⟨m, hm, hm_strict, hmZ⟩ :=
        sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
      have hm0 : m = 0 := by
        rw [hfactorZ i, eq_comm, mul_eq_zero] at hmZ
        exact_mod_cast hmZ.resolve_right (Complex.exp_ne_zero _)
      have hinter : ∃ n : ℤ, F.φ i = (n : ℝ) := by
        by_contra h
        push Not at h
        have := hm_strict h
        linarith
      obtain ⟨n, hncast⟩ := hinter
      have hnpos : 0 < n := by
        exact_mod_cast lt_of_le_of_lt hbeta0 (hncast ▸ (hphase i).1)
      have hnlt : n < 2 := by
        have hnlt_real : (n : ℝ) < 2 := by
          rw [← hncast]
          linarith [(hphase i).2]
        exact_mod_cast hnlt_real
      have : n = 1 := by omega
      simpa [this] using hncast
    have hfirst_phase : F.φ ⟨0, hn⟩ = 1 :=
      hphase_one_of_nonzero ⟨0, hn⟩ hfirst
    have hlast_phase : F.φ ⟨F.n - 1, by lia⟩ = 1 :=
      hphase_one_of_nonzero ⟨F.n - 1, by lia⟩ hlast
    have hP : sigma.slicing.P 1 E := by
      have hplus : sigma.slicing.phiPlus C E hzero = 1 :=
        (sigma.slicing.phiPlus_eq C E hzero F hn hfirst).trans <| by
          simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using hfirst_phase
      have hminus : sigma.slicing.phiMinus C E hzero = 1 :=
        (sigma.slicing.phiMinus_eq C E hzero F hn hlast).trans <| by
          simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using hlast_phase
      have heq : sigma.slicing.phiPlus C E hzero =
          sigma.slicing.phiMinus C E hzero := hplus.trans hminus.symm
      have hPplus := sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hzero heq
      rwa [hplus] at hPplus
    exact ⟨mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_of_semistable C hP (by norm_num))
        (sigma.slicing.leProp_of_semistable C hP le_rfl), hZ⟩
  · rintro ⟨hEheart, hZ⟩
    have hP := sigma.zeroCharge_mem_P_one hEheart hZ
    have hgt : sigma.slicing.gtProp C beta E :=
      sigma.slicing.gtProp_of_semistable C hP hbeta1
    have hle : sigma.slicing.leProp C (beta + 1) E :=
      sigma.slicing.leProp_of_semistable C hP (by linarith)
    have hshiftHeart :
        ((sigma.slicing.phaseShift C beta).toTStructure).heart E := by
      rw [(sigma.slicing.phaseShift C beta).toTStructure_heart_iff]
      exact ⟨(sigma.slicing.phaseShift_gtProp_zero C beta E).mpr hgt,
        (sigma.slicing.phaseShift_leProp C beta 1 E).mpr (by simpa [add_comm] using hle)⟩
    exact ⟨(sigma.phaseTiltHeart_iff_phaseShiftHeart hbeta0 hbeta1 E).mpr hshiftHeart,
      by simp [hZ]⟩

/-- The `moreover` mechanism in Lemma 14.17.  A map from an original
zero-charge object to a nonzero-charge tilted-semistable object vanishes
away from the boundary ray; strict stability gives the same conclusion on
the boundary. -/
theorem hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E A0 : C}
    (hE :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hA0 : sigma.zeroCharge A0)
    (hrefine :
      0 < ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im ∨
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsStable E)
    (f : A0 ⟶ E) : f = 0 := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  have hA0tilt : P.tilt.heart A0 :=
    ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A0).mpr
      hA0).1
  let A0' : H := ⟨A0, hA0tilt⟩
  let E' : H := ⟨E, hE.1⟩
  let f' : A0' ⟶ E' := ObjectProperty.homMk f
  let I : H := Abelian.image f'
  let p : A0' ⟶ I := Abelian.factorThruImage f'
  let i : I ⟶ E' := Abelian.image.ι f'
  haveI : Epi p := by dsimp [p]; infer_instance
  haveI : Mono i := by dsimp [i]; infer_instance
  by_contra hf
  have hI0 : ¬IsZero I := by
    intro hIz
    apply hf
    have hf' : f' = 0 := by
      rw [← Abelian.image.fac f']
      change p ≫ i = 0
      rw [hIz.eq_of_tgt p 0, zero_comp]
    exact congrArg (fun k : A0' ⟶ E' => k.hom) hf'
  let K : H := kernel p
  let S0 : ShortComplex H := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS0 : S0.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S0, K] using ShortComplex.exact_kernel p)
    (by dsimp [S0]; infer_instance)
    (by dsimp [S0]; infer_instance)
  let T0 := P.triangleOfShortExact S0 hS0
  have hT0 : T0 ∈ distTriang C := P.triangleOfShortExact_distinguished S0 hS0
  have hIzero : W.zeroCharge I.obj := by
    apply W.zeroCharge_right K.property I.property
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A0).mpr
        hA0)
    exact hT0
  let Q : H := cokernel i
  let S : ShortComplex H := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S, Q] using ShortComplex.exact_cokernel i)
    (by dsimp [S]; infer_instance)
    (by dsimp [S]; infer_instance)
  let T := P.triangleOfShortExact S hS
  have hT : T ∈ distTriang C := P.triangleOfShortExact_distinguished S hS
  have hsum : W.charge E = W.charge I.obj + W.charge Q.obj := by
    simpa [T, S, I, Q, E'] using W.charge_triangle' hT
  have hQcharge : W.charge Q.obj = W.charge E := by
    rw [hIzero.2, zero_add] at hsum
    exact hsum.symm
  have hQ0 : ¬IsZero Q.obj := fun hQz =>
    hcharge (by rw [← hQcharge]; exact W.charge_isZero hQz)
  have hIambient0 : ¬IsZero I.obj := fun h => hI0
    (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hslope := hE.2 I.property Q.property hIambient0 hQ0
    T.mor₁ T.mor₂ T.mor₃ hT
  rcases hrefine with him | hstable
  · have hQim : 0 < (W.charge Q.obj).im := by rwa [hQcharge]
    rw [W.slope_of_im_nonpos (by rw [hIzero.2]; simp),
      W.slope_of_im_pos hQim] at hslope
    exact WithTop.not_top_le_coe _ hslope
  · have hslope' := hstable.2 I.property Q.property hIambient0 hQ0
      T.mor₁ T.mor₂ T.mor₃ hT
    rw [W.slope_of_im_nonpos (by rw [hIzero.2]; simp)] at hslope'
    exact (not_lt_of_ge le_top) hslope'

/-- A semistable object's subobject with zero-charge quotient is itself
semistable.  The proof forms the composite subobject in the abelian tilted
heart and compares its cokernel charge with the original quotient charge. -/
theorem phaseTilt_isSemistable_left_of_zeroCharge_right
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {A E V : C}
    (hA : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart A)
    (hV : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart V)
    (hE :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E)
    (hVzero :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    {f : A ⟶ E} {g : E ⟶ V} {d : V ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g d ∈ distTriang C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable A := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  refine ⟨hA, ?_⟩
  intro X Y hX hY hX0 hY0 a b e hXY
  let X' : H := ⟨X, hX⟩
  let Y' : H := ⟨Y, hY⟩
  let A' : H := ⟨A, hA⟩
  let E' : H := ⟨E, hE.1⟩
  let V' : H := ⟨V, hV⟩
  let a' : X' ⟶ A' := ObjectProperty.homMk a
  let f' : A' ⟶ E' := ObjectProperty.homMk f
  let Sinner : ShortComplex H := ShortComplex.mk a'
    (ObjectProperty.homMk b : A' ⟶ Y') (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hXY)
  let Souter : ShortComplex H := ShortComplex.mk f'
    (ObjectProperty.homMk g : E' ⟶ V') (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hdist)
  have hSinner : Sinner.ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt hXY
  have hSouter : Souter.ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt hdist
  letI : Mono a' := hSinner.mono_f
  letI : Mono f' := hSouter.mono_f
  let c : X' ⟶ E' := a' ≫ f'
  let Q : H := cokernel c
  let S : ShortComplex H := ShortComplex.mk c (cokernel.π c) (cokernel.condition c)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S, Q] using ShortComplex.exact_cokernel c)
    (by dsimp [S, c]; infer_instance)
    (by dsimp [S]; infer_instance)
  let T := P.triangleOfShortExact S hS
  have hT : T ∈ distTriang C := P.triangleOfShortExact_distinguished S hS
  have hQ0 : ¬IsZero Q.obj := by
    intro hQ
    have hQ' : IsZero Q := ObjectProperty.FullSubcategory.isZero_of_obj_isZero hQ
    haveI : Epi c := Preadditive.epi_of_isZero_cokernel c hQ'
    haveI : Epi f' := epi_of_epi a' f'
    haveI : IsIso f' := isIso_of_mono_of_epi f'
    haveI : IsIso c := isIso_of_mono_of_epi c
    haveI : IsIso a' := IsIso.of_isIso_comp_right a' f'
    have ha' : IsIso a'.hom := by
      change IsIso (P.tilt.heart.ι.map a')
      infer_instance
    haveI : IsIso a := by simpa [a'] using ha'
    have haTriangle : IsIso (Triangle.mk a b e).mor₁ := by
      change IsIso a
      infer_instance
    exact hY0 ((Triangle.isZero₃_iff_isIso₁ (Triangle.mk a b e) hXY).2 haTriangle)
  have hsumOuter : W.charge E = W.charge A + W.charge V := W.charge_triangle' hdist
  have hsumInner : W.charge A = W.charge X + W.charge Y := W.charge_triangle' hXY
  have hsumComp : W.charge E = W.charge X + W.charge Q.obj := by
    simpa [T, S, Q, E', X'] using W.charge_triangle' hT
  have hQcharge : W.charge Q.obj = W.charge Y := by
    apply add_left_cancel (a := W.charge X)
    calc
      W.charge X + W.charge Q.obj = W.charge E := hsumComp.symm
      _ = W.charge A := by rw [hsumOuter, hVzero.2, add_zero]
      _ = W.charge X + W.charge Y := hsumInner
  have hslope := hE.2 hX Q.property hX0 hQ0 T.mor₁ T.mor₂ T.mor₃ hT
  have hslopeQ : W.slope Q.obj = W.slope Y := by
    unfold WeakStabilityFunction.slope
    rw [hQcharge]
  rwa [hslopeQ] at hslope

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition
