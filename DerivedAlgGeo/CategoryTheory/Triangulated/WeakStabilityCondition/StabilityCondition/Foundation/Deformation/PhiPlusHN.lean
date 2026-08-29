/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.PhiPlusMDQ

/-!
# Owner HN existence by highest-phase reduction

The strict MDQ construction is iterated on its kernels.  A bound on the
highest old phase is preserved by the kernel triangles and supplies the
upper skewed-phase estimate required at every recursive call.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

omit [IsTriangulated C] in
/-- A `φ⁺ < b - 4ε` bound forces the midpoint-branch skewed phase below
`b - 3ε`. -/
theorem skewedPhase_lt_of_phiPlus_lt
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hwide : 6 * ε ≤ b - a)
    {E : C} (hE : ¬IsZero E) (hI : σ.slicing.intervalProp C a b E)
    (hplus : σ.slicing.phiPlus C E hE < b - 4 * ε) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E <
      b - 3 * ε := by
  apply σ.skewedPhase_lt_of_leProp C W hr0 hr1 hW hab
    hε hε2 hthin hsin
  · linarith
  · linarith
  · exact hI
  · exact hE
  · have hend : b - 3 * ε - ε = b - 4 * ε := by ring
    rw [hend]
    exact σ.slicing.leProp_of_phiPlus_le C hE hplus.le

/-- A nonzero strict quotient of an object in the inner strip has skewed
phase above the lower enveloping boundary. -/
theorem skewedPhase_gt_of_strictQuotient_inner
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {X B : σ.slicing.IntervalCat C a b}
    (hInner : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) X.obj)
    (q : X ⟶ B) (hq : IsStrictEpi q) (hB : ¬IsZero B.obj) :
    a + ε <
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase B.obj := by
  have hX : ¬IsZero X.obj := by
    intro hzero
    have hXI : IsZero X :=
      ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero
    letI : Epi q := hq.epi
    have hq0 : q = 0 := zero_of_source_iso_zero _ hXI.isoZero
    exact hB ((σ.slicing.intervalProp C a b).ι.map_isZero
      (IsZero.of_epi_eq_zero q hq0))
  have hInnerNonempty : a + 2 * ε < b - 4 * ε := by
    linarith [σ.slicing.phiMinus_gt_of_intervalProp C hX hInner,
      σ.slicing.phiPlus_lt_of_intervalProp C hX hInner,
      σ.slicing.phiMinus_le_phiPlus C X.obj hX]
  let K : Subobject X := kernelSubobject q
  have hKgt : σ.slicing.gtProp C a (K : σ.slicing.IntervalCat C a b).obj :=
    σ.slicing.gtProp_of_intervalProp C (K : σ.slicing.IntervalCat C a b).property
  let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
  have hSQ : StrictShortExact SQ :=
    Slicing.IntervalCat.strictShortExact_kernelSubobject C q hq
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_strictShortExact C σ.slicing hSQ
  have hBminus : a + 2 * ε < σ.slicing.phiMinus C B.obj hB := by
    apply σ.slicing.phiMinus_gt_of_triangle_with_gtProp C hB
      (fun _ => σ.slicing.phiMinus_gt_of_intervalProp C hX hInner)
      hKgt (by linarith) hT
  have hBge : σ.slicing.geProp C ((a + ε) + ε) B.obj := by
    have := σ.slicing.geProp_of_phiMinus_ge C hB hBminus.le
    convert this using 1 <;> ring
  exact σ.skewedPhase_gt_of_geProp C W hr0 hr1 hW hab hε hε2
    hthin hsin le_rfl (by linarith) B.property hB hBge

/-- Iterating the owner two-branch MDQ construction produces an HN
filtration above the explicit quotient lower bound. -/
theorem hn_exists_with_phiPlus_reduction
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFinite : ThinStrictFiniteLength C σ a b)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj ∧
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj < U)
    (hWidth : U - L < 1)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hL_a : a ≤ L + ε) (hwide : 6 * ε ≤ b - a)
    (t : ℝ) (ht : a + ε ≤ t)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot : ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
      t < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
        (cokernel A.arrow).obj)
    (hplusX : ∀ hXobj : ¬IsZero X.obj,
      σ.slicing.phiPlus C X.obj hXobj < b - 4 * ε) :
    let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
    let Psem : ℝ → ObjectProperty C := fun ψ E => F.IsSemistable E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  let Psem : ℝ → ObjectProperty C := fun ψ E => F.IsSemistable E ψ
  have hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E := by
    intro E hI hE
    exact σ.charge_ne_of_interval C W hr0 hr1 hW hab hε hε2
      hthin hsin hI hE
  letI : IsStrictArtinianObject X := (hFinite X).1
  let S0 : StrictSubobject X := ⟨⊤, isStrictMono_of_isIso⟩
  let Psub : StrictSubobject X → Prop := fun S =>
    ¬IsZero (S.1 : σ.slicing.IntervalCat C a b) →
      ∀ t : ℝ, a + ε ≤ t →
        (∀ A : Subobject (S.1 : σ.slicing.IntervalCat C a b),
          A ≠ ⊤ → IsStrictMono A.arrow →
          t < F.phase (cokernel A.arrow).obj) →
        (∀ hY : ¬IsZero (S.1 : σ.slicing.IntervalCat C a b).obj,
          σ.slicing.phiPlus C (S.1 : σ.slicing.IntervalCat C a b).obj hY <
            b - 4 * ε) →
        ∃ G : HNFiltration C Psem
            (S.1 : σ.slicing.IntervalCat C a b).obj,
          ∀ j, t < G.φ j ∧ G.φ j < U
  have recurse : ∀ S : StrictSubobject X, Psub S := by
    intro S
    refine (show WellFounded
      ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
        wellFounded_lt).induction S ?_
    intro S ih hS t htS hquotS hplusY
    let Y : σ.slicing.IntervalCat C a b := S.1
    have hYobj : ¬IsZero Y.obj := fun hzero =>
      hS (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
    let ψY := F.phase Y.obj
    by_cases hss : F.IsSemistable Y.obj ψY
    · let G : HNFiltration C Psem Y.obj := HNFiltration.single C Y.obj ψY hss
      refine ⟨G, ?_⟩
      intro j
      have hbotTop : (⊥ : Subobject Y) ≠ ⊤ := by
        intro hEq
        have hzero : IsZero Y := by
          have hbot : IsZero ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) :=
            (isZero_zero (σ.slicing.IntervalCat C a b)).of_iso
              Subobject.botCoeIsoZero
          have htop : IsZero ((⊤ : Subobject Y) : σ.slicing.IntervalCat C a b) :=
            hbot.of_iso (eqToIso (congrArg Subobject.underlying.obj hEq)).symm
          exact htop.of_iso (asIso (⊤ : Subobject Y).arrow).symm
        exact hS hzero
      have hbotPhase := hquotS ⊥ hbotTop
        (Slicing.IntervalCat.bot_arrow_strictMono C)
      let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
        rw [show ((⊥ : Subobject Y).arrow) = 0 by simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
      have hψ : t < ψY := hbotPhase.trans_eq (F.phase_iso eC)
      have hψU : ψY < U := (hWindow Y hYobj).2
      have hj0 : j.val = 0 := by
        have : j.val < 1 := by simp [G, HNFiltration.single] at j ⊢
        omega
      have hj : j = ⟨0, by simp [G, HNFiltration.single]⟩ := Fin.ext hj0
      subst j
      simpa [G, HNFiltration.single] using And.intro hψ hψU
    · letI : IsStrictArtinianObject Y := (hFinite Y).1
      letI : IsStrictNoetherianObject Y := (hFinite Y).2
      have hUpper : F.phase Y.obj < b - 3 * ε :=
        σ.skewedPhase_lt_of_phiPlus_lt C W hr0 hr1 hW hab hε hε2
          hthin hsin hwide hYobj Y.property (hplusY hYobj)
      have hQuotLo : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : Y ⟶ B'),
          IsStrictEpi q' → ¬IsZero B'.obj →
          F.IsSemistable B'.obj (F.phase B'.obj) → t < F.phase B'.obj := by
        intro B' q' hq' hB' _
        let K' : Subobject Y := kernelSubobject q'
        have hK'top : K' ≠ ⊤ :=
          Slicing.IntervalCat.kernelSubobject_ne_top_of_strictEpi_nonzero C
            hq' hB'
        have hK'strict : IsStrictMono K'.arrow := by
          simpa [K'] using Slicing.IntervalCat.subobject_arrow_strictMono C
            (kernel.ι q') (isStrictMono_kernel q')
        exact (hquotS K' hK'top hK'strict).trans_eq
          (F.phase_cokernel_kernelSubobject C q' hq')
      obtain ⟨B, q, hq⟩ :=
        σ.exists_strictMDQ_with_quotient_bound C W hr0 hr1 hW hab
          hFinite hWindow hWidth hε hε2 hε8 hthin hsin hL_a htS
          hS hQuotLo hUpper
      let K : Subobject Y := kernelSubobject q
      have hKbot : K ≠ ⊥ := hq.kernelSubobject_ne_bot_of_not_semistable C hss
      have hKtop : K ≠ ⊤ :=
        Slicing.IntervalCat.kernelSubobject_ne_top_of_strictEpi_nonzero C
          hq.strictEpi hq.nonzero
      have hKstrict : IsStrictMono K.arrow := by
        simpa [K] using Slicing.IntervalCat.subobject_arrow_strictMono C
          (kernel.ι q) (isStrictMono_kernel q)
      let T : Subobject X := Slicing.IntervalCat.liftSub C S.1 K
      have hTbot : T ≠ ⊥ := Slicing.IntervalCat.liftSub_ne_bot C S.1 hKbot
      have hTstrict : IsStrictMono T.arrow :=
        Slicing.IntervalCat.liftSub_arrow_strictMono C S.2 hKstrict
      let Tstr : StrictSubobject X := ⟨T, hTstrict⟩
      have hTlt : Tstr < S := by
        change T < S.1
        exact Slicing.IntervalCat.liftSub_lt C S.1 hKtop
      have hTne : ¬IsZero (T : σ.slicing.IntervalCat C a b) :=
        Slicing.IntervalCat.subobject_not_isZero_of_ne_bot C hTbot
      let ψB := F.phase B.obj
      have hψB : t < ψB := by
        have hgt := hquotS K hKtop hKstrict
        exact hgt.trans_eq (F.phase_cokernel_kernelSubobject C q hq.strictEpi)
      have hψBU : ψB < U := (hWindow B hq.nonzero).2
      let eK : (T : σ.slicing.IntervalCat C a b) ≅
          (K : σ.slicing.IntervalCat C a b) := by
        dsimp [T, Slicing.IntervalCat.liftSub]
        exact Subobject.underlyingIso (K.arrow ≫ S.1.arrow)
      have hquotT : ∀ A : Subobject (T : σ.slicing.IntervalCat C a b),
          A ≠ ⊤ → IsStrictMono A.arrow →
          ψB < F.phase (cokernel A.arrow).obj := by
        intro A hAtop hAstrict
        let A' : Subobject (K : σ.slicing.IntervalCat C a b) :=
          (Subobject.map eK.hom).obj A
        have hA'top : A' ≠ ⊤ := by
          intro htop
          apply hAtop
          apply (Subobject.map_obj_injective eK.hom)
          calc
            (Subobject.map eK.hom).obj A = A' := rfl
            _ = ⊤ := htop
            _ = (Subobject.map eK.hom).obj
                (⊤ : Subobject (T : σ.slicing.IntervalCat C a b)) := by
              rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso eK.hom]
        have hA'strict : IsStrictMono A'.arrow := by
          have hcomp : IsStrictMono (A.arrow ≫ eK.hom) :=
            Slicing.IntervalCat.comp_strictMono C σ.slicing A.arrow eK.hom
              hAstrict isStrictMono_of_isIso
          have hEq : A' = Subobject.mk (A.arrow ≫ eK.hom) := by
            simpa [A'] using Subobject.map_eq_mk_comp eK A
          rw [hEq]
          exact Slicing.IntervalCat.subobject_arrow_strictMono C
            (A.arrow ≫ eK.hom) hcomp
        have hphase : F.phase (cokernel A.arrow).obj =
            F.phase (cokernel A'.arrow).obj := by
          let eA : (A : σ.slicing.IntervalCat C a b) ≅
              (A' : σ.slicing.IntervalCat C a b) :=
            (Subobject.mapUnderlyingIso eK A).symm
          have hw : A.arrow ≫ eK.hom = eA.hom ≫ A'.arrow := by
            simp [eA, A', Subobject.mapUnderlyingIso]
          let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
            cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA eK hw
          exact F.phase_iso
            ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC)
        rw [hphase]
        exact hq.phase_lt_of_strictQuotient_of_kernel C hFinite hCharge
          hWindow hWidth hA'top hA'strict
      have hKobj : ¬IsZero (K : σ.slicing.IntervalCat C a b).obj := fun hzero =>
        (Slicing.IntervalCat.subobject_not_isZero_of_ne_bot C hKbot)
          (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
      have hplusK : σ.slicing.phiPlus C
          (K : σ.slicing.IntervalCat C a b).obj hKobj < b - 4 * ε := by
        let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
          ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
        have hSQ : StrictShortExact SQ :=
          Slicing.IntervalCat.strictShortExact_kernelSubobject C q hq.strictEpi
        obtain ⟨δ, hT⟩ :=
          Slicing.IntervalCat.exists_distinguished_of_strictShortExact
            C σ.slicing hSQ
        have hle := σ.slicing.phiPlus_triangle_le C hKobj hYobj
          (by linarith [Fact.out (p := b - a ≤ 1)])
          (K : σ.slicing.IntervalCat C a b).property B.property hT
        exact hle.trans_lt (hplusY hYobj)
      have hplusT : ∀ hTobj : ¬IsZero
          (T : σ.slicing.IntervalCat C a b).obj,
          σ.slicing.phiPlus C (T : σ.slicing.IntervalCat C a b).obj hTobj <
            b - 4 * ε := by
        intro hTobj
        let eC := (σ.slicing.intervalProp C a b).ι.mapIso eK
        have heq := σ.slicing.phiPlus_iso C eC hTobj hKobj
        exact heq.trans_lt hplusK
      obtain ⟨GT, hGT⟩ := ih Tstr hTlt hTne ψB
        (by linarith [htS, hψB]) hquotT hplusT
      let GK : HNFiltration C Psem
          (K : σ.slicing.IntervalCat C a b).obj :=
        GT.ofIso C ((Slicing.IntervalCat.ι
          (C := C) (s := σ.slicing) a b).mapIso eK)
      have hGK : ∀ j, ψB < GK.φ j ∧ GK.φ j < U := by
        change ∀ j : Fin GT.n, ψB < GT.φ j ∧ GT.φ j < U
        exact hGT
      let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
        ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
      have hSQ : StrictShortExact SQ :=
        Slicing.IntervalCat.strictShortExact_kernelSubobject C q hq.strictEpi
      let H : HNFiltration C Psem Y.obj :=
        HNFiltration.appendStrictFactor C GK hSQ ψB hq.semistable
          (fun j => (hGK j).1)
      refine ⟨H, ?_⟩
      intro j
      by_cases hj : j.val < GK.n
      · have hGj := hGK ⟨j.val, hj⟩
        have hGj' : t < GK.φ ⟨j.val, hj⟩ ∧
            GK.φ ⟨j.val, hj⟩ < U := ⟨hψB.trans hGj.1, hGj.2⟩
        simpa [H, GK, HNFiltration.appendStrictFactor,
          HNFiltration.appendFactor, hj] using hGj'
      · have hjlt : j.val < GK.n + 1 := by
          simpa [H, GK, HNFiltration.appendStrictFactor,
            HNFiltration.appendFactor] using j.is_lt
        have hjEq : j.val = GK.n := by omega
        have hlast : GK.n < H.n := by
          simp [H, GK, HNFiltration.appendStrictFactor,
            HNFiltration.appendFactor]
        have hjLast : j = ⟨GK.n, hlast⟩ := Fin.ext hjEq
        subst j
        have hfalse : ¬GK.n < GK.n := lt_irrefl _
        simpa [H, GK, HNFiltration.appendStrictFactor,
          HNFiltration.appendFactor, hfalse, ψB] using And.intro hψB hψBU
  have hS0 : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b) := by
    intro hzero
    exact hX (hzero.of_iso (asIso S0.1.arrow).symm)
  let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X := asIso S0.1.arrow
  have hquot0 : ∀ A : Subobject (S0.1 : σ.slicing.IntervalCat C a b),
      A ≠ ⊤ → IsStrictMono A.arrow →
      t < F.phase (cokernel A.arrow).obj := by
    intro A hAtop hAstrict
    let A' : Subobject X := (Subobject.map e0.hom).obj A
    have hA'top : A' ≠ ⊤ := by
      intro htop
      apply hAtop
      apply (Subobject.map_obj_injective e0.hom)
      calc
        (Subobject.map e0.hom).obj A = A' := rfl
        _ = ⊤ := htop
        _ = (Subobject.map e0.hom).obj
            (⊤ : Subobject (S0.1 : σ.slicing.IntervalCat C a b)) := by
          rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso e0.hom]
    have hA'strict : IsStrictMono A'.arrow := by
      have hcomp : IsStrictMono (A.arrow ≫ e0.hom) :=
        Slicing.IntervalCat.comp_strictMono C σ.slicing A.arrow e0.hom
          hAstrict isStrictMono_of_isIso
      have hEq : A' = Subobject.mk (A.arrow ≫ e0.hom) := by
        simpa [A'] using Subobject.map_eq_mk_comp e0 A
      rw [hEq]
      exact Slicing.IntervalCat.subobject_arrow_strictMono C
        (A.arrow ≫ e0.hom) hcomp
    have hphase : F.phase (cokernel A.arrow).obj =
        F.phase (cokernel A'.arrow).obj := by
      let eA : (A : σ.slicing.IntervalCat C a b) ≅
          (A' : σ.slicing.IntervalCat C a b) :=
        (Subobject.mapUnderlyingIso e0 A).symm
      have hw : A.arrow ≫ e0.hom = eA.hom ≫ A'.arrow := by
        simp [eA, A', Subobject.mapUnderlyingIso]
      let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
        cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA e0 hw
      exact F.phase_iso
        ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC)
    rw [hphase]
    exact hquot A' hA'top hA'strict
  have hS0obj : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b).obj := fun hzero =>
    hS0 (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
  have hXobj : ¬IsZero X.obj := fun hzero =>
    hX (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
  have hplus0 : ∀ h : ¬IsZero
      (S0.1 : σ.slicing.IntervalCat C a b).obj,
      σ.slicing.phiPlus C (S0.1 : σ.slicing.IntervalCat C a b).obj h <
        b - 4 * ε := by
    intro h
    let eC := (σ.slicing.intervalProp C a b).ι.mapIso e0
    have heq := σ.slicing.phiPlus_iso C eC h hXobj
    exact heq.trans_lt (hplusX hXobj)
  obtain ⟨G0, hG0⟩ := recurse S0 hS0 t ht hquot0 hplus0
  let eTop : (S0.1 : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso e0
  refine ⟨G0.ofIso C eTop, ?_⟩
  intro j
  change t < G0.φ j ∧ G0.φ j < U
  exact hG0 j

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
