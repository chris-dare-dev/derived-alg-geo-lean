/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CoreConsequences
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.FiltrationOperations
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhaseBounds

/-!
# The top slice of the heart `𝒫((φ - 1, φ])` is closed under subobjects and quotients

For a pre-stability condition `σ = (Z, 𝒫)` and `φ : ℝ`, the heart `𝒜 = 𝒫((φ - 1, φ])` is the
bounded t-structure heart of the slicing, and its top slice `𝒫(φ)` consists of the semistable
objects of the largest phase the heart contains.  A short exact sequence `0 → A → E → B → 0` in
`𝒜` is a distinguished triangle `A → E → B → A⟦1⟧` whose three vertices lie in `𝒜`.

* `mem_P_of_triangle_of_mem_P_top`: if `E ∈ 𝒫(φ)`, then `A ∈ 𝒫(φ)` and `B ∈ 𝒫(φ)`.
* `mem_P_of_filtration_top`: the graded pieces of a finite filtration of `E ∈ 𝒫(φ)` inside `𝒜`
  lie in `𝒫(φ)`.

## Proof

*Quotient.*  A morphism from `B` to an object of phases below `φ` precomposes with `E → B` to a
morphism from `E ∈ 𝒫(φ)` to such an object, which vanishes.  So it factors through
`B → A⟦1⟧`; but `A⟦1⟧` has phases above `φ`, so it also has no map to phases at most `φ`.
Hence `B` has all phases at least `φ`, and at most `φ` because it lies in `𝒜`.

*Subobject.*  The charge `Z(A) = Z(E) - Z(B)` is a real multiple of `e^{iπφ}`, since `E` and `B`
are semistable of phase `φ`.  Summing over the HN factors of `A`, whose phases `ψ_i` lie in
`(φ - 1, φ]`, the imaginary part of `e^{-iπφ} Z(A)` is `∑ |Z(A_i)| sin (π (ψ_i - φ))`.  Every
term is nonpositive, and a nonzero factor contributes a strictly negative term unless
`ψ_i = φ`.  So the nonzero extreme factors have phase `φ`, which makes both intrinsic phases of
`A` equal to `φ`.

## Hypotheses that cannot be dropped

* Strict positivity `|Z(F)| > 0` of nonzero semistable objects, built into `PreStabilityCondition`,
  is used.  For a weak stability condition the statement is false: on a polarized smooth
  projective surface `X` take `Z = i·p₂ - p₁` on `Coh X` (a weak stability condition whose
  zero-dimensional sheaves have `Z = 0` at phase `1`).  For a line bundle `L` of phase
  `φ ∈ (0, 1)` and a point `x`, the sequence `0 → k_x[-1] → I_x ⊗ L → L → 0` is short exact in the
  rotated heart `𝒫((φ - 1, φ])`, with `I_x ⊗ L` and `L` in `𝒫(φ)`, but its subobject `k_x[-1]`
  has `Z = 0` and phase `0 ≠ φ`.
* That `φ` is the top phase of the heart is used.  On a smooth projective curve with
  `Z = -deg + i·rk`, the structure sheaf `𝒪` lies in `𝒫(1/2)` and in the heart
  `Coh = 𝒫((0, 1])`, whose top phase is `1`; its subobject `𝒪(-p)` has phase `1/4`.  So `𝒫(φ)`
  is not a Serre subcategory of a heart in which `φ` is interior.

Neither the support property nor local finiteness is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}
  (σ : PreStabilityCondition.WithClassMap C v) (φ : ℝ)

/-- The quotient case: a quotient of an object of `𝒫(φ)` in `𝒫((φ - 1, φ])` is in `𝒫(φ)`. -/
private theorem P_quotient_of_mem_P_top {A E B : C} {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦1⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) (hA : σ.slicing.gtProp C (φ - 1) A)
    (hB : σ.slicing.leProp C φ B) (hE : σ.slicing.P φ E) : σ.slicing.P φ B := by
  rw [σ.slicing.semistable_iff_geProp_ltProp C]
  refine ⟨?_, fun ψ hψ => σ.slicing.ltProp_of_leProp_of_lt C hψ B hB⟩
  refine σ.slicing.geProp_of_forall_hom_eq_zero C φ fun G hG u => ?_
  have hcomp : g ≫ u = 0 :=
    σ.slicing.zero_of_geProp_ltProp_general C φ (σ.slicing.geProp_of_semistable C hE) hG _
  obtain ⟨w, hw⟩ := Triangle.yoneda_exact₃ _ hT u hcomp
  have hA' : σ.slicing.gtProp C φ (A⟦(1 : ℤ)⟧) := by
    simpa using σ.slicing.gtProp_shift C (φ - 1) A 1 hA
  have hw0 : w = 0 :=
    σ.slicing.zero_of_gtProp_leProp_general C φ hA' (σ.slicing.leProp_of_ltProp C G hG) w
  rw [hw, hw0, comp_zero]

/-- A semistable object of phase `φ` has charge a real multiple of `e^{iπφ}`. -/
private theorem charge_eq_real_mul_of_P {X : C} (hX : σ.slicing.P φ X) :
    ∃ r : ℝ, σ.charge X = (r : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) := by
  by_cases h : IsZero X
  · exact ⟨0, by simp [h]⟩
  · obtain ⟨m, -, hm⟩ := σ.compat φ X hX h
    exact ⟨m, hm⟩

/-- The contribution of a semistable factor of phase `ψ ≤ φ`, `φ - 1 < ψ`, to the imaginary part
of `e^{-iπφ} Z`: it is nonpositive, and vanishes only for a zero factor or when `ψ = φ`. -/
private theorem factor_term {X : C} {ψ : ℝ} (hX : σ.slicing.P ψ X) (h₁ : φ - 1 < ψ) (h₂ : ψ ≤ φ) :
    (Complex.exp ((-(Real.pi * φ) : ℝ) * Complex.I) * σ.charge X).im ≤ 0 ∧
      ((Complex.exp ((-(Real.pi * φ) : ℝ) * Complex.I) * σ.charge X).im = 0 →
        IsZero X ∨ ψ = φ) := by
  by_cases hz : IsZero X
  · simp [hz]
  obtain ⟨m, hm, hmeq⟩ := σ.compat ψ X hX hz
  have key : (Complex.exp ((-(Real.pi * φ) : ℝ) * Complex.I) * σ.charge X).im =
      m * Real.sin (Real.pi * ψ - Real.pi * φ) := by
    rw [hmeq, Complex.mul_im]
    simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      Real.cos_neg, Real.sin_neg, Real.sin_sub]
    ring
  have hπ := Real.pi_pos
  have hneg : Real.pi * ψ - Real.pi * φ ≤ 0 := by nlinarith
  have hlow : -Real.pi < Real.pi * ψ - Real.pi * φ := by nlinarith
  rw [key]
  refine ⟨mul_nonpos_of_nonneg_of_nonpos hm.le
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg hlow.le), fun h0 => Or.inr ?_⟩
  have hs : Real.sin (Real.pi * ψ - Real.pi * φ) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact (hm.ne' h).elim
    · exact h
  have := (Real.sin_eq_zero_iff_of_lt_of_lt hlow (by linarith)).mp hs
  nlinarith

/-- The subobject case. -/
private theorem P_sub_of_mem_P_top {A E B : C} {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦1⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) (hA : σ.slicing.gtProp C (φ - 1) A)
    (hA' : σ.slicing.leProp C φ A) (hE : σ.slicing.P φ E) (hB : σ.slicing.P φ B) :
    σ.slicing.P φ A := by
  by_cases hA0 : IsZero A
  · exact σ.slicing.zero_mem_of_isZero C φ A hA0
  obtain ⟨F, hn, hfirst, hlast⟩ := σ.slicing.exists_hn_nonzero_boundaries C hA0
  have hplus : F.phiPlus C hn ≤ φ := by
    rw [← σ.slicing.phiPlus_eq C A hA0 F hn hfirst]
    exact σ.slicing.phiPlus_le_of_leProp C hA0 hA'
  have hminus : φ - 1 < F.phiMinus C hn := by
    rw [← σ.slicing.phiMinus_eq C A hA0 F hn hlast]
    exact σ.slicing.phiMinus_gt_of_gtProp C hA0 hA
  have hbounds : ∀ i, φ - 1 < F.φ i ∧ F.φ i ≤ φ := fun i =>
    ⟨hminus.trans_le (F.phase_mem_range C hn i).1, (F.phase_mem_range C hn i).2.trans hplus⟩
  -- the charge of `A` is a real multiple of `e^{iπφ}`
  obtain ⟨rE, hrE⟩ := charge_eq_real_mul_of_P σ φ hE
  obtain ⟨rB, hrB⟩ := charge_eq_real_mul_of_P σ φ hB
  have hcharge : σ.charge E = σ.charge A + σ.charge B := by
    rw [WithClassMap.charge_def, WithClassMap.charge_def, WithClassMap.charge_def, ← map_add]
    exact congrArg σ.Z (classOf_triangle C v (Triangle.mk f g h) hT)
  have hA_charge : σ.charge A =
      ((rE - rB : ℝ) : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) := by
    have : σ.charge A = σ.charge E - σ.charge B := by rw [hcharge]; ring
    rw [this, hrE, hrB]
    push_cast
    ring
  have hsum : σ.charge A = ∑ i, σ.charge (F.factor i) :=
    σ.charge_postnikovTower_eq_sum F.toPostnikovTower
  set u : ℂ := Complex.exp ((-(Real.pi * φ) : ℝ) * Complex.I) with hu
  have hrot : (u * σ.charge A).im = 0 := by
    rw [hA_charge, ← mul_assoc, mul_comm u, mul_assoc, hu, ← Complex.exp_add]
    simp
  have hterms : ∑ i, (u * σ.charge (F.factor i)).im = 0 := by
    rw [← hrot, hsum, Finset.mul_sum, Complex.im_sum]
  have hnonpos : ∀ i ∈ Finset.univ, (u * σ.charge (F.factor i)).im ≤ 0 := fun i _ =>
    (factor_term σ φ (F.semistable i) (hbounds i).1 (hbounds i).2).1
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hterms
  have hphase : ∀ i, ¬IsZero (F.factor i) → F.φ i = φ := fun i hi =>
    ((factor_term σ φ (F.semistable i) (hbounds i).1 (hbounds i).2).2
      (hall i (Finset.mem_univ i))).resolve_left hi
  have hfirstφ : F.phiPlus C hn = φ := hphase _ hfirst
  have hlastφ : F.phiMinus C hn = φ := hphase _ hlast
  have heq : σ.slicing.phiPlus C A hA0 = σ.slicing.phiMinus C A hA0 := by
    rw [σ.slicing.phiPlus_eq C A hA0 F hn hfirst, σ.slicing.phiMinus_eq C A hA0 F hn hlast,
      hfirstφ, hlastφ]
  have hsemi := σ.slicing.semistable_of_phiPlus_eq_phiMinus C hA0 heq
  rwa [σ.slicing.phiPlus_eq C A hA0 F hn hfirst, hfirstφ] at hsemi

local notation "𝒜" => σ.slicing.gtProp C (φ - 1) ⊓ σ.slicing.leProp C φ

/-- The top slice `P(φ)` of the heart `P((φ - 1, φ])` is closed under subobjects and quotients. -/
theorem mem_P_of_triangle_of_mem_P_top {A E B : C} {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦1⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) (hA : 𝒜 A) (hB : 𝒜 B) (hE : σ.slicing.P φ E) :
    σ.slicing.P φ A ∧ σ.slicing.P φ B := by
  have hBP := P_quotient_of_mem_P_top σ φ hT hA.1 hB.2 hE
  exact ⟨P_sub_of_mem_P_top σ φ hT hA.1 hA.2 hE hBP, hBP⟩

/-- Graded pieces of a finite filtration of `E ∈ P(φ)` inside `P((φ - 1, φ])` lie in `P(φ)`. -/
theorem mem_P_of_filtration_top {n : ℕ} (E : Fin (n + 1) → C)
    (ι : ∀ i : Fin n, E i.castSucc ⟶ E i.succ) (gr : Fin n → C) (π : ∀ i : Fin n, E i.succ ⟶ gr i)
    (δ : ∀ i : Fin n, gr i ⟶ (E i.castSucc)⟦(1 : ℤ)⟧)
    (hT : ∀ i, Triangle.mk (ι i) (π i) (δ i) ∈ distTriang C)
    (hgr : ∀ i, 𝒜 (gr i)) (h0 : IsZero (E 0)) (hE : σ.slicing.P φ (E (Fin.last n))) :
    ∀ i, σ.slicing.P φ (gr i) := by
  -- Every stage of the filtration lies in the heart, by extension closure.
  have hheart : ∀ j : Fin (n + 1), 𝒜 (E j) := by
    intro j
    induction j using Fin.induction with
    | zero =>
        exact ⟨σ.slicing.gtProp_of_isZero C h0 _, σ.slicing.leProp_of_isZero C h0 _⟩
    | succ i ih =>
        exact ⟨σ.slicing.gtProp_of_triangle C _ ih.1 (hgr i).1 (hT i),
          σ.slicing.leProp_of_triangle C _ ih.2 (hgr i).2 (hT i)⟩
  -- Every stage lies in `𝒫(φ)`, by downward induction from the top.
  have hP : ∀ j : Fin (n + 1), σ.slicing.P φ (E j) := by
    intro j
    induction j using Fin.reverseInduction with
    | last => exact hE
    | cast i ih =>
        exact (mem_P_of_triangle_of_mem_P_top σ φ (hT i) (hheart _) (hgr i) ih).1
  intro i
  exact (mem_P_of_triangle_of_mem_P_top σ φ (hT i) (hheart _) (hgr i) (hP i.succ)).2

end CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
