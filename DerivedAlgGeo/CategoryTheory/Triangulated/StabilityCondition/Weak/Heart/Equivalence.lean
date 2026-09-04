/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CoreConsequences
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.FiniteSums
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic.Definitions
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weak stability on the heart of a slicing

This file is the semistable-object part of the weak heart--slicing
correspondence from Lemma 14.4 of arXiv:1902.08184v4.  A weak prestability
condition restricts to a weak stability function on its slicing heart.  The
only new boundary case relative to the ordinary construction is phase `1`:
compatibility permits a zero radius there, and therefore the induced heart
charge lands on the closed negative real ray.

The main declarations are:

* `WeakPreStabilityCondition.weakStabilityFunctionOnHeart`;
* charge and zero-charge compatibility for that restriction;
* `Slicing.phiPlus_le_of_heart_subobject`, the triangle-form heart-mono bridge;
* `weakStabilityFunctionOnHeart_isSemistable_iff`, identifying slicing and
  slope semistability for nonzero slicing-heart objects.

The analytic proof splits at phase `1`.  Below `1`, every nonzero HN factor
has strictly positive radius and the ordinary argument-convexity API applies.
At phase `1`, additivity and the closed half-plane force both ends of every
heart short exact sequence to have zero imaginary part, hence slope `+infinity`.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open scoped BigOperators ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Λ : Type*} [AddCommGroup Λ]
variable {v : K₀ C →+ Λ}

private theorem weakUpper_sum {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (hf : ∀ i, 0 ≤ (f i).im ∧ ((f i).im = 0 → (f i).re ≤ 0)) :
    0 < (∑ i, f i).im ∨ ((∑ i, f i).im = 0 ∧ (∑ i, f i).re ≤ 0) := by
  have him_nonneg : 0 ≤ (∑ i, f i).im := by
    simpa using Finset.sum_nonneg (fun i _ => (hf i).1)
  by_cases him : 0 < (∑ i, f i).im
  · exact Or.inl him
  · right
    have him_zero : (∑ i, f i).im = 0 := le_antisymm (le_of_not_gt him) him_nonneg
    refine ⟨him_zero, ?_⟩
    have hsum_im : ∑ i, (f i).im = 0 := by simpa using him_zero
    have hterm_zero : ∀ i, (f i).im = 0 := by
      intro i
      apply le_antisymm _ (hf i).1
      have hi_le : (f i).im ≤ ∑ j, (f j).im := by
        exact Finset.single_le_sum (fun j _ => (hf j).1) (Finset.mem_univ i)
      simpa [hsum_im] using hi_le
    simpa using Finset.sum_nonpos (fun i _ => (hf i).2 (hterm_zero i))

namespace WeakPreStabilityCondition

/-- Restrict a weak prestability condition to its slicing heart. -/
noncomputable def weakStabilityFunctionOnHeart
    (σ : WeakPreStabilityCondition v) :
    WeakStabilityFunction σ.slicing.toTStructure where
  Z := σ.Z.comp v
  nonzero_mem E hrel := by
    obtain ⟨hE, hne⟩ := hrel
    -- `heartDatum`'s positivity is membership of `closedUpperHalfPlane`, which
    -- is this disjunction by definitional unfolding of the set union. Naming
    -- it keeps the argument below in the shape it was written in.
    show 0 < ((σ.Z.comp v) (K₀.of C E)).im ∨
      (((σ.Z.comp v) (K₀.of C E)).im = 0 ∧ ((σ.Z.comp v) (K₀.of C E)).re ≤ 0)
    classical
    have hEheart := (σ.slicing.toTStructure_heart_iff C E).mp hE
    obtain ⟨F, hn, hfirst, hlast⟩ := σ.slicing.exists_hn_nonzero_boundaries C hne
    let P := F.toPostnikovTower
    have hphiMinus : 0 < σ.slicing.phiMinus C E hne :=
      σ.slicing.phiMinus_gt_of_gtProp C hne hEheart.1
    have hphiPlus : σ.slicing.phiPlus C E hne ≤ 1 :=
      σ.slicing.phiPlus_le_of_leProp C hne hEheart.2
    have hphase_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
      intro i
      constructor
      · calc
          0 < σ.slicing.phiMinus C E hne := hphiMinus
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
              σ.slicing.phiMinus_eq C E hne F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C E hne := by
            simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
              (σ.slicing.phiPlus_eq C E hne F hn hfirst).symm
          _ ≤ 1 := hphiPlus
    let f : Fin F.n → ℂ := fun i => σ.Z (v (K₀.of C (P.factor i)))
    have hterm : ∀ i, 0 ≤ (f i).im ∧ ((f i).im = 0 → (f i).re ≤ 0) := by
      intro i
      by_cases hzero : IsZero (P.factor i)
      · have hz : f i = 0 := by simp [f, K₀.of_isZero C hzero]
        simp [hz]
      obtain ⟨m, hm, hm_strict, hmZ⟩ :=
        σ.compat' (F.φ i) (P.factor i) (F.semistable i) hzero
      by_cases hone : F.φ i = 1
      · rw [hone] at hmZ
        rw [show f i = (m : ℂ) * Complex.exp ((Real.pi * (1 : ℝ) : ℂ) * Complex.I) by
          simpa [f] using hmZ]
        constructor
        · simp [Complex.exp_mul_I]
        · intro _
          simp [Complex.exp_mul_I, hm]
      · have hlt : F.φ i < 1 := lt_of_le_of_ne (hphase_mem i).2 hone
        have hnotint : ∀ n : ℤ, F.φ i ≠ (n : ℝ) := by
          intro n hcast
          have hn0 : 0 < n := by exact_mod_cast (hcast ▸ (hphase_mem i).1)
          have hn1 : n < 1 := by exact_mod_cast (hcast ▸ hlt)
          omega
        have hmpos : 0 < m := hm_strict hnotint
        have himpos : 0 < (f i).im := by
          rw [show f i = (m : ℂ) * Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) by
            simpa [f] using hmZ]
          rw [Complex.exp_ofReal_mul_I]
          simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, add_zero]
          simpa using mul_pos hmpos
            (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hphase_mem i).1)
              (by nlinarith [Real.pi_pos]))
        exact ⟨himpos.le, fun hzeroim => absurd hzeroim (ne_of_gt himpos)⟩
    have hsum : (σ.Z.comp v) (K₀.of C E) = ∑ i, f i := by
      change (σ.Z.comp v) (CategoryTheory.Triangulated.K₀.of C E) = ∑ i, f i
      rw [CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum C P, map_sum]
      simp [f]
      rfl
    rw [hsum]
    exact weakUpper_sum f hterm

@[simp]
theorem weakStabilityFunctionOnHeart_Z (σ : WeakPreStabilityCondition v) :
    (σ.weakStabilityFunctionOnHeart :
      WeakStabilityFunction σ.slicing.toTStructure).Z = σ.Z.comp v := rfl

@[simp]
theorem weakStabilityFunctionOnHeart_charge
    (σ : WeakPreStabilityCondition v) (E : C) :
    σ.weakStabilityFunctionOnHeart.charge E = σ.Z (v (K₀.of C E)) := rfl

@[simp]
theorem weakStabilityFunctionOnHeart_zeroCharge_iff
    (σ : WeakPreStabilityCondition v) (E : C) :
    σ.weakStabilityFunctionOnHeart.zeroCharge E ↔
      σ.slicing.toTStructure.heart E ∧ σ.Z (v (K₀.of C E)) = 0 :=
  Iff.rfl

end WeakPreStabilityCondition

namespace SlicingBridge

/-- A heart subobject of a slicing-semistable object has top HN phase at most
the phase of the ambient object.  The subobject is presented by a
distinguished triangle whose three vertices lie in the slicing heart. -/
theorem phiPlus_le_of_heart_subobject (s : Slicing C) {phi : ℝ}
    (hphi : phi ∈ Set.Ioc (0 : ℝ) 1) {E A B : C}
    (hP : s.P phi E)
    (hAheart : s.toTStructure.heart A) (hBheart : s.toTStructure.heart B)
    (hA : ¬IsZero A) {f : A ⟶ E} {g : E ⟶ B} {d : B ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g d ∈ distTriang C) :
    s.phiPlus C A hA ≤ phi := by
  classical
  let t := s.toTStructure
  let A' : t.heart.FullSubcategory := ⟨A, hAheart⟩
  let E' : t.heart.FullSubcategory := ⟨E,
    (s.toTStructure_heart_iff C E).mpr
      ⟨s.gtProp_of_semistable C hP hphi.1,
        s.leProp_of_semistable C hP hphi.2⟩⟩
  let B' : t.heart.FullSubcategory := ⟨B, hBheart⟩
  let f' : A' ⟶ E' := ObjectProperty.homMk f
  let g' : E' ⟶ B' := ObjectProperty.homMk g
  have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
    (C := C) t (A := A') (B := E') (Q := B') (f := f') (g := g') (δ := d) hdist
  letI : Mono f' := hshort.mono_f
  by_contra hgt
  push Not at hgt
  have hAheart' := (s.toTStructure_heart_iff C A).mp hAheart
  obtain ⟨F, hn, hfirst⟩ := s.exists_hn_nonzero_first C hA
  have htop : s.phiPlus C A hA = F.φ ⟨0, hn⟩ :=
    s.phiPlus_eq C A hA F hn hfirst
  have hphase_gt : phi < F.φ ⟨0, hn⟩ := by
    rw [← htop]
    exact hgt
  have hphase_mem : F.φ ⟨0, hn⟩ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · exact lt_trans hphi.1 hphase_gt
    · rw [← htop]
      exact s.phiPlus_le_of_leProp C hA hAheart'.2
  have hfactor_heart : t.heart (F.triangle ⟨0, hn⟩).obj₃ := by
    rw [s.toTStructure_heart_iff C]
    exact ⟨s.gtProp_of_semistable C (F.semistable ⟨0, hn⟩) hphase_mem.1,
      s.leProp_of_semistable C (F.semistable ⟨0, hn⟩) hphase_mem.2⟩
  have halpha : ∃ alpha : (F.triangle ⟨0, hn⟩).obj₃ ⟶ A, alpha ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C s hn hzero)
  rcases halpha with ⟨alpha, halpha⟩
  let X' : t.heart.FullSubcategory := ⟨(F.triangle ⟨0, hn⟩).obj₃, hfactor_heart⟩
  let alpha' : X' ⟶ A' := ObjectProperty.homMk alpha
  have hcomp_ne : alpha ≫ f ≠ 0 := by
    intro hzero
    have hzero' : alpha' ≫ f' = 0 := by
      ext
      exact hzero
    have halpha_zero : alpha' = 0 := (cancel_mono f').mp (by simpa using hzero')
    exact halpha (by simpa [alpha'] using congr_arg (·.hom) halpha_zero)
  exact hcomp_ne <| s.hom_vanishing (F.φ ⟨0, hn⟩) phi _ _ hphase_gt
    (F.semistable ⟨0, hn⟩) hP (alpha ≫ f)

end SlicingBridge

namespace WeakPreStabilityCondition

/-- Below the boundary phase, the induced weak charge is nonzero and its
argument is bounded above by the largest slicing HN phase. -/
theorem charge_mem_upperHalfPlane_and_arg_le_phiPlus
    (σ : WeakPreStabilityCondition v) (E : C)
    (hheart : σ.slicing.toTStructure.heart E) (hE : ¬IsZero E)
    (hplus : σ.slicing.phiPlus C E hE < 1) :
    σ.weakStabilityFunctionOnHeart.charge E ∈ semiClosedUpperHalfPlane ∧
      Complex.arg (σ.weakStabilityFunctionOnHeart.charge E) ≤
        Real.pi * σ.slicing.phiPlus C E hE := by
  classical
  have hEheart := (σ.slicing.toTStructure_heart_iff C E).mp hheart
  obtain ⟨F, hn, hfirst, hlast⟩ := σ.slicing.exists_hn_nonzero_boundaries C hE
  let P := F.toPostnikovTower
  let s : Finset (Fin F.n) := Finset.univ.filter (fun i => ¬IsZero (P.factor i))
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hE
    have hi' : ¬IsZero (P.factor i) := by
      change ¬IsZero (F.triangle i).obj₃
      exact hi
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩⟩
  have hminus : 0 < σ.slicing.phiMinus C E hE :=
    σ.slicing.phiMinus_gt_of_gtProp C hE hEheart.1
  have hphase_mem : ∀ i ∈ s, F.φ i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i hi
    constructor
    · calc
        0 < σ.slicing.phiMinus C E hE := hminus
        _ = F.φ ⟨F.n - 1, by lia⟩ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
            σ.slicing.phiMinus_eq C E hE F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E hE := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
        _ < 1 := hplus
  let f : Fin F.n → ℂ := fun i => σ.Z (v (K₀.of C (P.factor i)))
  have hterm : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane := by
    intro i hi
    have hfactor : ¬IsZero (P.factor i) := by simpa [s, P] using hi
    obtain ⟨m, -, hm_strict, hmZ⟩ :=
      σ.compat' (F.φ i) (P.factor i) (F.semistable i) hfactor
    have hnotint : ∀ n : ℤ, F.φ i ≠ (n : ℝ) := by
      intro n hcast
      have hn0 : 0 < n := by exact_mod_cast (hcast ▸ (hphase_mem i hi).1)
      have hn1 : n < 1 := by exact_mod_cast (hcast ▸ (hphase_mem i hi).2)
      omega
    have hmpos : 0 < m := hm_strict hnotint
    apply mem_semiClosedUpperHalfPlane_of_arg_pos
    have harg : Complex.arg (f i) = Real.pi * F.φ i := by
      rw [show f i = (m : ℂ) * Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) by
        simpa [f] using hmZ]
      rw [Complex.arg_real_mul _ hmpos, Complex.arg_exp_mul_I, toIocMod_eq_self]
      constructor
      · nlinarith [Real.pi_pos, mul_pos Real.pi_pos (hphase_mem i hi).1]
      · have hlt := mul_lt_mul_of_pos_left (hphase_mem i hi).2 Real.pi_pos
        nlinarith
    rw [harg]
    exact mul_pos Real.pi_pos (hphase_mem i hi).1
  have harg_factor : ∀ i ∈ s, Complex.arg (f i) = Real.pi * F.φ i := by
    intro i hi
    have hfactor : ¬IsZero (P.factor i) := by simpa [s, P] using hi
    obtain ⟨m, -, hm_strict, hmZ⟩ :=
      σ.compat' (F.φ i) (P.factor i) (F.semistable i) hfactor
    have hnotint : ∀ n : ℤ, F.φ i ≠ (n : ℝ) := by
      intro n hcast
      have hn0 : 0 < n := by exact_mod_cast (hcast ▸ (hphase_mem i hi).1)
      have hn1 : n < 1 := by exact_mod_cast (hcast ▸ (hphase_mem i hi).2)
      omega
    have hmpos : 0 < m := hm_strict hnotint
    rw [show f i = (m : ℂ) * Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) by
      simpa [f] using hmZ]
    rw [Complex.arg_real_mul _ hmpos, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos (hphase_mem i hi).1]
    · have hlt := mul_lt_mul_of_pos_left (hphase_mem i hi).2 Real.pi_pos
      nlinarith
  have hsum_all : σ.weakStabilityFunctionOnHeart.charge E = ∑ i, f i := by
    rw [weakStabilityFunctionOnHeart_charge]
    change σ.Z (v (CategoryTheory.Triangulated.K₀.of C E)) = ∑ i, f i
    rw [CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum C P, map_sum]
    rw [map_sum]
  let z : Finset (Fin F.n) := Finset.univ.filter (fun i => IsZero (P.factor i))
  have hzero_filter : ∑ i ∈ z, f i = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [f, K₀.of_isZero C hi]
  have hsum_filter : ∑ i, f i = ∑ i ∈ s, f i := by
    calc
      ∑ i, f i = (∑ i ∈ s, f i) + ∑ i ∈ z, f i := by
        simpa [s, z, f] using
          (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := fun i : Fin F.n => ¬IsZero (P.factor i)) (f := f)).symm
      _ = ∑ i ∈ s, f i := by rw [hzero_filter, add_zero]
  have hsup_le :
      s.sup' hs (Complex.arg ∘ f) ≤ Real.pi * σ.slicing.phiPlus C E hE := by
    refine (Finset.sup'_le_iff hs (Complex.arg ∘ f)).2 ?_
    intro i hi
    rw [Function.comp_apply, harg_factor i hi]
    have hle : F.φ i ≤ σ.slicing.phiPlus C E hE := by
      calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E hE := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
    nlinarith [Real.pi_pos, hle]
  rw [hsum_all, hsum_filter]
  exact ⟨sum_mem_semiClosedUpperHalfPlane hs hterm,
    (arg_sum_le_sup_of_semiClosedUpperHalfPlane hs hterm).trans hsup_le⟩

/-- If the induced weak charge has positive imaginary part, its argument is
bounded below by the smallest slicing HN phase.  Zero-charge phase-`1`
factors are discarded from the sum; positive imaginary part guarantees that
at least one charged factor remains. -/
theorem pi_mul_phiMinus_le_charge_arg_of_im_pos
    (σ : WeakPreStabilityCondition v) (E : C)
    (hheart : σ.slicing.toTStructure.heart E) (hE : ¬IsZero E)
    (him : 0 < (σ.weakStabilityFunctionOnHeart.charge E).im) :
    Real.pi * σ.slicing.phiMinus C E hE ≤
      Complex.arg (σ.weakStabilityFunctionOnHeart.charge E) := by
  classical
  have hEheart := (σ.slicing.toTStructure_heart_iff C E).mp hheart
  obtain ⟨F, hn, hfirst, hlast⟩ := σ.slicing.exists_hn_nonzero_boundaries C hE
  let P := F.toPostnikovTower
  let f : Fin F.n → ℂ := fun i => σ.Z (v (K₀.of C (P.factor i)))
  let s : Finset (Fin F.n) := Finset.univ.filter (fun i => f i ≠ 0)
  have hphase_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    constructor
    · calc
        0 < σ.slicing.phiMinus C E hE :=
          σ.slicing.phiMinus_gt_of_gtProp C hE hEheart.1
        _ = F.φ ⟨F.n - 1, by lia⟩ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
            σ.slicing.phiMinus_eq C E hE F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E hE := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
        _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hE hEheart.2
  have hsum_all : σ.weakStabilityFunctionOnHeart.charge E = ∑ i, f i := by
    rw [weakStabilityFunctionOnHeart_charge]
    change σ.Z (v (CategoryTheory.Triangulated.K₀.of C E)) = ∑ i, f i
    rw [CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum C P, map_sum]
    rw [map_sum]
  have hs : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ i, f i = 0 := by
      intro i
      have hi : i ∉ s := by simp [hempty]
      simpa [s] using hi
    have hsum_zero : ∑ i, f i = 0 := Finset.sum_eq_zero fun i _ => hall i
    rw [hsum_all, hsum_zero] at him
    change (0 : ℝ) < 0 at him
    exact (lt_irrefl 0) him
  have hfactor_nonzero : ∀ i ∈ s, ¬IsZero (P.factor i) := by
    intro i hi hzero
    have hfzero : f i = 0 := by simp [f, K₀.of_isZero C hzero]
    exact (by simpa [s] using hi : f i ≠ 0) hfzero
  have hradius_pos : ∀ i ∈ s, ∃ m : ℝ, 0 < m ∧
      f i = (m : ℂ) * Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) := by
    intro i hi
    obtain ⟨m, hm, hm_strict, hmZ⟩ :=
      σ.compat' (F.φ i) (P.factor i) (F.semistable i) (hfactor_nonzero i hi)
    have hfi : f i = (m : ℂ) * Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) := by
      simpa [f] using hmZ
    have hmpos : 0 < m := by
      by_cases hone : F.φ i = 1
      · apply lt_of_le_of_ne hm
        intro hmzero
        have : f i = 0 := by rw [hfi]; simp [← hmzero]
        exact (by simpa [s] using hi : f i ≠ 0) this
      · have hlt : F.φ i < 1 := lt_of_le_of_ne (hphase_mem i).2 hone
        apply hm_strict
        intro n hcast
        have hn0 : 0 < n := by exact_mod_cast (hcast ▸ (hphase_mem i).1)
        have hn1 : n < 1 := by exact_mod_cast (hcast ▸ hlt)
        omega
    exact ⟨m, hmpos, hfi⟩
  have harg_factor : ∀ i ∈ s, Complex.arg (f i) = Real.pi * F.φ i := by
    intro i hi
    obtain ⟨m, hmpos, hfi⟩ := hradius_pos i hi
    rw [hfi, Complex.arg_real_mul _ hmpos, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos (hphase_mem i).1]
    · have hle := mul_le_mul_of_nonneg_left (hphase_mem i).2 Real.pi_pos.le
      nlinarith
  have hterm : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane := by
    intro i hi
    apply mem_semiClosedUpperHalfPlane_of_arg_pos
    rw [harg_factor i hi]
    exact mul_pos Real.pi_pos (hphase_mem i).1
  let z : Finset (Fin F.n) := Finset.univ.filter (fun i => f i = 0)
  have hzero_filter : ∑ i ∈ z, f i = 0 := by
    exact Finset.sum_eq_zero fun i hi => (by simpa [z] using hi)
  have hsum_filter : ∑ i, f i = ∑ i ∈ s, f i := by
    calc
      ∑ i, f i = (∑ i ∈ s, f i) + ∑ i ∈ z, f i := by
        simpa [s, z] using
          (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := fun i : Fin F.n => f i ≠ 0) (f := f)).symm
      _ = ∑ i ∈ s, f i := by rw [hzero_filter, add_zero]
  have hinf_ge :
      Real.pi * σ.slicing.phiMinus C E hE ≤ s.inf' hs (Complex.arg ∘ f) := by
    refine (Finset.le_inf'_iff hs (Complex.arg ∘ f)).2 ?_
    intro i hi
    rw [Function.comp_apply, harg_factor i hi]
    have hle : σ.slicing.phiMinus C E hE ≤ F.φ i := by
      calc
        σ.slicing.phiMinus C E hE = F.φ ⟨F.n - 1, by lia⟩ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
            σ.slicing.phiMinus_eq C E hE F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    exact mul_le_mul_of_nonneg_left hle Real.pi_pos.le
  rw [hsum_all, hsum_filter]
  exact hinf_ge.trans (inf_le_arg_sum_of_semiClosedUpperHalfPlane hs hterm)

/-- Slicing ray membership in `(0,1]` implies slope semistability for the
induced weak stability function on the slicing heart. -/
theorem weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
    (σ : WeakPreStabilityCondition v) {phi : ℝ} (hphi : phi ∈ Set.Ioc (0 : ℝ) 1)
    (E : C) (hP : σ.slicing.P phi E) (hE : ¬IsZero E) :
    σ.weakStabilityFunctionOnHeart.IsSemistable E := by
  let W := σ.weakStabilityFunctionOnHeart
  have hEheart : σ.slicing.toTStructure.heart E :=
    (σ.slicing.toTStructure_heart_iff C E).mpr
      ⟨σ.slicing.gtProp_of_semistable C hP hphi.1,
        σ.slicing.leProp_of_semistable C hP hphi.2⟩
  refine ⟨hEheart, ?_⟩
  intro A B hAheart hBheart hA hB f g d hdist
  have hsum : W.charge E = W.charge A + W.charge B := W.charge_triangle' hdist
  by_cases hone : phi = 1
  · obtain ⟨m, hm, -, hmZ⟩ := σ.compat' phi E hP hE
    have hEim : (W.charge E).im = 0 := by
      rw [show W.charge E = (m : ℂ) * Complex.exp ((Real.pi * (1 : ℝ) : ℂ) * Complex.I) by
        rw [weakStabilityFunctionOnHeart_charge]
        simpa [hone] using hmZ]
      simp [Complex.exp_mul_I]
    have hAim_nonneg : 0 ≤ (W.charge A).im := by
      rcases W.upper A hAheart hA with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    have hBim_nonneg : 0 ≤ (W.charge B).im := by
      rcases W.upper B hBheart hB with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    have him_sum : (W.charge A).im + (W.charge B).im = 0 := by
      have := congrArg Complex.im hsum
      simpa [hEim] using this.symm
    have hAim : (W.charge A).im = 0 := by linarith
    have hBim : (W.charge B).im = 0 := by linarith
    rw [W.slope_of_im_nonpos (by rw [hAim]; exact lt_irrefl 0),
      W.slope_of_im_nonpos (by rw [hBim]; exact lt_irrefl 0)]
  · have hphi_lt : phi < 1 := lt_of_le_of_ne hphi.2 hone
    have hAplus_le : σ.slicing.phiPlus C A hA ≤ phi :=
      SlicingBridge.phiPlus_le_of_heart_subobject (C := C) σ.slicing hphi hP
        hAheart hBheart hA hdist
    have hAplus_lt : σ.slicing.phiPlus C A hA < 1 := hAplus_le.trans_lt hphi_lt
    obtain ⟨hAupper, hAarg⟩ :=
      σ.charge_mem_upperHalfPlane_and_arg_le_phiPlus A hAheart hA hAplus_lt
    have hAarg_phi : Complex.arg (W.charge A) ≤ Real.pi * phi := by
      calc
        Complex.arg (W.charge A) ≤ Real.pi * σ.slicing.phiPlus C A hA := hAarg
        _ ≤ Real.pi * phi := mul_le_mul_of_nonneg_left hAplus_le Real.pi_pos.le
    obtain ⟨m, -, hm_strict, hmZ⟩ := σ.compat' phi E hP hE
    have hnotint : ∀ n : ℤ, phi ≠ (n : ℝ) := by
      intro n hcast
      have hn0 : 0 < n := by exact_mod_cast (hcast ▸ hphi.1)
      have hn1 : n < 1 := by exact_mod_cast (hcast ▸ hphi_lt)
      omega
    have hmpos : 0 < m := hm_strict hnotint
    have hEarg : Complex.arg (W.charge E) = Real.pi * phi := by
      rw [show W.charge E = (m : ℂ) * Complex.exp ((Real.pi * phi : ℝ) * Complex.I) by
        rw [weakStabilityFunctionOnHeart_charge]
        simpa using hmZ]
      rw [Complex.arg_real_mul _ hmpos, Complex.arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> nlinarith [Real.pi_pos, hphi.1, hphi_lt]
    have hEupper : W.charge E ∈ semiClosedUpperHalfPlane := by
      apply mem_semiClosedUpperHalfPlane_of_arg_pos
      rw [hEarg]
      exact mul_pos Real.pi_pos hphi.1
    have harg_le : Complex.arg (W.charge A) ≤ Complex.arg (W.charge E) := by
      rw [hEarg]
      exact hAarg_phi
    have hcrossAE :
        0 ≤ (W.charge A).re * (W.charge E).im -
          (W.charge A).im * (W.charge E).re :=
      cross_nonneg_of_arg_le (im_nonneg_of_mem_semiClosedUpperHalfPlane hAupper)
        (semiClosedUpperHalfPlane_ne_zero hAupper)
        (semiClosedUpperHalfPlane_ne_zero hEupper) harg_le
    have hcrossAB :
        0 ≤ (W.charge A).re * (W.charge B).im -
          (W.charge A).im * (W.charge B).re := by
      have heq :
          (W.charge A).re * (W.charge B).im -
              (W.charge A).im * (W.charge B).re =
            (W.charge A).re * (W.charge E).im -
              (W.charge A).im * (W.charge E).re := by
        rw [hsum]
        simp only [Complex.add_re, Complex.add_im]
        ring
      rw [heq]
      exact hcrossAE
    by_cases hBim : 0 < (W.charge B).im
    · have hAim : 0 < (W.charge A).im := by
        rcases hAupper with h | ⟨hzero, hre⟩
        · exact h
        · rw [hzero] at hcrossAB
          simp only [zero_mul, sub_zero] at hcrossAB
          nlinarith
      rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim]
      exact_mod_cast (div_le_div_iff₀ hAim hBim).2 (by nlinarith [hcrossAB])
    · rw [W.slope_of_im_nonpos hBim]
      exact le_top

/-- A nonzero heart object that is slope-semistable for the induced weak
stability function lies in the slicing at its intrinsic top phase. -/
theorem mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable
    (σ : WeakPreStabilityCondition v) (E : C) (hE : ¬IsZero E)
    (hss : σ.weakStabilityFunctionOnHeart.IsSemistable E) :
    σ.slicing.P (σ.slicing.phiPlus C E hE) E := by
  let W := σ.weakStabilityFunctionOnHeart
  have hheart := hss.1
  have hEbounds := (σ.slicing.toTStructure_heart_iff C E).mp hheart
  apply σ.slicing.semistable_of_phiPlus_eq_phiMinus C hE
  apply le_antisymm
  · by_contra hnot
    have hgap : σ.slicing.phiMinus C E hE < σ.slicing.phiPlus C E hE :=
      lt_of_not_ge hnot
    let cut : ℝ :=
      (σ.slicing.phiMinus C E hE + σ.slicing.phiPlus C E hE) / 2
    have hminus_cut : σ.slicing.phiMinus C E hE < cut := by
      dsimp [cut]
      linarith
    have hcut_plus : cut < σ.slicing.phiPlus C E hE := by
      dsimp [cut]
      linarith
    have hcut_pos : 0 < cut :=
      lt_trans (σ.slicing.phiMinus_gt_of_gtProp C hE hEbounds.1) hminus_cut
    have hplus_one : σ.slicing.phiPlus C E hE ≤ 1 :=
      σ.slicing.phiPlus_le_of_leProp C hE hEbounds.2
    have hcut_one : cut < 1 := hcut_plus.trans_le hplus_one
    obtain ⟨F, hn, hfirst, hlast⟩ := σ.slicing.exists_hn_nonzero_boundaries C hE
    have hphase : ∀ i : Fin F.n, (0 : ℝ) < F.φ i ∧ F.φ i < 2 := by
      intro i
      constructor
      · calc
          0 < σ.slicing.phiMinus C E hE :=
            σ.slicing.phiMinus_gt_of_gtProp C hE hEbounds.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
              σ.slicing.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C E hE := by
            simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
              (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
          _ ≤ 1 := hplus_one
          _ < 2 := by norm_num
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      σ.slicing.exists_split_at_cutoff_with_upper_bound C F hphase hn (t := cut)
    have hXle : σ.slicing.leProp C 1 X := by
      have hYshift : σ.slicing.leProp C 1 (Y⟦(-1 : ℤ)⟧) := by
        have hshift := σ.slicing.leProp_shift C cut Y (-1) hYle
        exact σ.slicing.leProp_mono C (by push_cast; linarith) _ hshift
      exact σ.slicing.leProp_of_triangle C 1 hYshift hEbounds.2
        (inv_rot_of_distTriang _ hdist)
    have hYgt : σ.slicing.gtProp C 0 Y := by
      have hXshift : σ.slicing.gtProp C 0 (X⟦(1 : ℤ)⟧) := by
        have hshift := σ.slicing.gtProp_shift C cut X 1 hXgt
        exact σ.slicing.gtProp_anti C (by push_cast; linarith) _ hshift
      exact σ.slicing.gtProp_of_triangle C 0 hEbounds.1 hXshift
        (rot_of_distTriang _ hdist)
    have hXheart : σ.slicing.toTStructure.heart X :=
      (σ.slicing.toTStructure_heart_iff C X).mpr
        ⟨σ.slicing.gtProp_anti C hcut_pos.le X hXgt, hXle⟩
    have hYheart : σ.slicing.toTStructure.heart Y :=
      (σ.slicing.toTStructure_heart_iff C Y).mpr
        ⟨hYgt, σ.slicing.leProp_mono C hcut_one.le Y hYle⟩
    have hX : ¬IsZero X := by
      intro hzero
      haveI : IsIso g :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f g d) hdist).mp hzero
      have hEle : σ.slicing.leProp C cut E :=
        ObjectProperty.prop_of_iso (σ.slicing.leProp C cut) (asIso g).symm hYle
      have hle := σ.slicing.phiPlus_le_of_leProp C hE hEle
      linarith
    have hY : ¬IsZero Y := by
      intro hzero
      haveI : IsIso f :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g d) hdist).mp hzero
      have hEgt : σ.slicing.gtProp C cut E :=
        ObjectProperty.prop_of_iso (σ.slicing.gtProp C cut) (asIso f) hXgt
      have hgt := σ.slicing.phiMinus_gt_of_gtProp C hE hEgt
      linarith
    have hslope : W.slope X ≤ W.slope Y :=
      hss.2 hXheart hYheart hX hY f g d hdist
    have hYplus : σ.slicing.phiPlus C Y hY ≤ cut :=
      σ.slicing.phiPlus_le_of_leProp C hY hYle
    have hYplus_one : σ.slicing.phiPlus C Y hY < 1 := hYplus.trans_lt hcut_one
    obtain ⟨hYupper, hYarg⟩ :=
      σ.charge_mem_upperHalfPlane_and_arg_le_phiPlus Y hYheart hY hYplus_one
    have hYim : 0 < (σ.weakStabilityFunctionOnHeart.charge Y).im := by
      rcases hYupper with him | ⟨him, hre⟩
      · exact him
      · have harg_pi :
            Complex.arg (σ.weakStabilityFunctionOnHeart.charge Y) = Real.pi := by
          rw [show σ.weakStabilityFunctionOnHeart.charge Y =
              ((σ.weakStabilityFunctionOnHeart.charge Y).re : ℂ) from
            Complex.ext rfl (by
              change (σ.weakStabilityFunctionOnHeart.charge Y).im = 0
              exact him), Complex.arg_ofReal_of_neg hre]
        have harg_lt :
            Complex.arg (σ.weakStabilityFunctionOnHeart.charge Y) < Real.pi := by
          calc
            Complex.arg (σ.weakStabilityFunctionOnHeart.charge Y) ≤
                Real.pi * σ.slicing.phiPlus C Y hY := hYarg
            _ < Real.pi * 1 :=
              mul_lt_mul_of_pos_left hYplus_one Real.pi_pos
            _ = Real.pi := mul_one _
        linarith
    by_cases hXim : 0 < (W.charge X).im
    · have hXarg :=
        σ.pi_mul_phiMinus_le_charge_arg_of_im_pos X hXheart hX hXim
      have hXminus : cut < σ.slicing.phiMinus C X hX :=
        σ.slicing.phiMinus_gt_of_gtProp C hX hXgt
      have harg_lt : Complex.arg (W.charge Y) < Complex.arg (W.charge X) := by
        calc
          Complex.arg (W.charge Y) ≤ Real.pi * σ.slicing.phiPlus C Y hY := hYarg
          _ ≤ Real.pi * cut := mul_le_mul_of_nonneg_left hYplus Real.pi_pos.le
          _ < Real.pi * σ.slicing.phiMinus C X hX :=
            mul_lt_mul_of_pos_left hXminus Real.pi_pos
          _ ≤ Complex.arg (W.charge X) := hXarg
      have hcross :
          0 < (W.charge Y).re * (W.charge X).im -
            (W.charge Y).im * (W.charge X).re :=
        cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hYupper)
          (semiClosedUpperHalfPlane_ne_zero hYupper)
          (ne_of_apply_ne Complex.im (ne_of_gt hXim)) harg_lt
      rw [W.slope_of_im_pos hXim, W.slope_of_im_pos hYim] at hslope
      have hreal :
          -(W.charge X).re / (W.charge X).im ≤
            -(W.charge Y).re / (W.charge Y).im := by
        exact_mod_cast hslope
      have hmul := (div_le_div_iff₀ hXim hYim).1 hreal
      nlinarith
    · have hXim_zero : (W.charge X).im = 0 := by
        rcases W.upper X hXheart hX with him | ⟨him, -⟩
        · exact absurd him hXim
        · exact him
      rw [W.slope_of_im_nonpos hXim, W.slope_of_im_pos hYim] at hslope
      exact WithTop.not_top_le_coe _ hslope
  · exact σ.slicing.phiMinus_le_phiPlus C E hE

/-- For nonzero heart objects, slicing semistability and semistability for the
induced weak stability function are equivalent. -/
theorem weakStabilityFunctionOnHeart_isSemistable_iff
    (σ : WeakPreStabilityCondition v) (E : C)
    (hheart : σ.slicing.toTStructure.heart E) (hE : ¬IsZero E) :
    σ.weakStabilityFunctionOnHeart.IsSemistable E ↔
      σ.slicing.P (σ.slicing.phiPlus C E hE) E := by
  constructor
  · exact σ.mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable E hE
  · intro hP
    have hbounds := (σ.slicing.toTStructure_heart_iff C E).mp hheart
    have hphase : σ.slicing.phiPlus C E hE ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · exact lt_of_lt_of_le (σ.slicing.phiMinus_gt_of_gtProp C hE hbounds.1)
          (σ.slicing.phiMinus_le_phiPlus C E hE)
      · exact σ.slicing.phiPlus_le_of_leProp C hE hbounds.2
    exact σ.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
      hphase E hP hE

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition
