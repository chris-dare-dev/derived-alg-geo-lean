/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.HarderNarasimhan.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Noetherian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Harder--Narasimhan reduction after phase tilting

This file isolates the cohomological quotient step used in Proposition 19.5
and in the weak-HN part of Proposition 14.16.  If the last original HN factor
of `F` is `U`, then quotienting an extension of `F[1]` by the shifted prefix
first produces an extension of `U[1]` by a zero-charge object.  Saturating
that extension gives the last tilted semistable quotient.  The kernel of the
composite quotient is again an extension of the shifted prefix by a
zero-charge object, which is the recursive state for the shorter original
HN filtration.

Boundary-phase saturation is performed inside the quotient step: no
right-orthogonality hypothesis on the shifted last factor is required.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open CategoryTheory.Triangulated.Tilting
open scoped ZeroObject

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

namespace WeakPreStabilityCondition

/-- **The `H⁻¹` last-factor reduction.**

Suppose `G ⟶ F ⟶ U` is the last step of an original HN filtration,
and `F[1] ⟶ E ⟶ V` is an extension by a tilted zero-charge object.
Then `E` has a
semistable quotient `B` with the charge of `U[1]`.  Its kernel `K` fits into
an extension `G[1] ⟶ K ⟶ A` with `A` zero-charge.

Thus the first triangle removes the last original HN factor, while the
second triangle is exactly the recursive input attached to the prefix. -/
theorem phaseTilt_hnLastQuotient
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1))
    {G F U V E : C}
    (hGfree : phaseFree sigma.slicing beta G)
    (hFfree : phaseFree sigma.slicing beta F)
    (hUfree : phaseFree sigma.slicing beta U)
    (hUss : sigma.weakStabilityFunctionOnHeart.IsSemistable U)
    (hUcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
        (U⟦(1 : ℤ)⟧) ≠ 0)
    (hV : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    {f : G ⟶ F} {g : F ⟶ U} {d : U ⟶ G⟦(1 : ℤ)⟧}
    (hGFU : Triangle.mk f g d ∈ distTriang C)
    {i : F⟦(1 : ℤ)⟧ ⟶ E} {p : E ⟶ V}
    {delta : V ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hFEV : Triangle.mk i p delta ∈ distTriang C) :
    ∃ (K A B : C)
      (_ : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart K)
      (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
      (_ : rightOrthogonal
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge B)
      (k : K ⟶ E) (q : E ⟶ B) (dk : B ⟶ K⟦(1 : ℤ)⟧),
        Triangle.mk k q dk ∈ distTriang C ∧
          ∃ (u : G⟦(1 : ℤ)⟧ ⟶ K) (r : K ⟶ A)
            (du : A ⟶ G⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
              Triangle.mk u r du ∈ distTriang C ∧
                (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable B ∧
                (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge B =
                  (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
                    (U⟦(1 : ℤ)⟧) := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  have hGshift : P.tilt.heart (G⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hGfree
  have hFshift : P.tilt.heart (F⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hFfree
  have hUshift : P.tilt.heart (U⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hUfree
  let GH : H := ⟨G⟦(1 : ℤ)⟧, hGshift⟩
  let FH : H := ⟨F⟦(1 : ℤ)⟧, hFshift⟩
  let UH : H := ⟨U⟦(1 : ℤ)⟧, hUshift⟩
  let EH : H := ⟨E, hE⟩
  let VH : H := ⟨V, hV.1⟩
  let Tshift := (shiftFunctor (Triangle C) (1 : ℤ)).obj (Triangle.mk f g d)
  have hTshift : Tshift ∈ distTriang C :=
    Triangle.shift_distinguished (Triangle.mk f g d) hGFU 1
  let fH : GH ⟶ FH := ObjectProperty.homMk Tshift.mor₁
  let gH : FH ⟶ UH := ObjectProperty.homMk Tshift.mor₂
  have hfg : fH ≫ gH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hTshift
  have hPrefix : (ShortComplex.mk fH gH hfg).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := GH) (B := FH) (Q := UH)
        (f := fH) (g := gH) (δ := Tshift.mor₃) hTshift
  let iH : FH ⟶ EH := ObjectProperty.homMk i
  let pH : EH ⟶ VH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hFEV
  have hOuter : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := FH) (B := EH) (Q := VH)
        (f := iH) (g := pH) (δ := delta) hFEV
  letI : Mono fH := hPrefix.mono_f
  letI : Mono iH := hOuter.mono_f
  let Rseq := cokernelCompShortComplex fH iH
  have hRseq : Rseq.ShortExact := cokernelCompShortComplex_shortExact fH iH
  let eU : Rseq.X₁ ≅ UH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel fH)
      hPrefix.gIsCokernel
  let eV : Rseq.X₃ ≅ VH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel iH)
      hOuter.gIsCokernel
  let jR : UH ⟶ Rseq.X₂ := eU.inv ≫ Rseq.f
  let pR : Rseq.X₂ ⟶ VH := Rseq.g ≫ eV.hom
  have hjp : jR ≫ pR = 0 := by
    simp [jR, pR, Rseq]
  let Sred : ShortComplex H := ShortComplex.mk jR pR hjp
  let eRed : Rseq ≅ Sred :=
    ShortComplex.isoMk eU (Iso.refl _) eV
  have hSred : Sred.ShortExact :=
    ShortComplex.shortExact_of_iso eRed hRseq
  letI : Mono jR := hSred.mono_f
  letI : Epi pR := hSred.epi_g
  obtain ⟨dR, hdR⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt jR pR hjp (fun {X} x hx => by
      exact ⟨hSred.fIsKernel.lift (KernelFork.ofι x hx),
        hSred.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  obtain ⟨A, B, hA, hB, a, qR, dA, hAB, hBss, hBcharge⟩ :=
    sigma.phaseTilt_semistableQuotient_of_extension
      beta hbeta0 hbeta1 hdec hUfree hUss hUcharge hV
        Rseq.X₂.property hdR
  let AH : H := ⟨A, hA.1⟩
  let BH : H := ⟨B, hB.1⟩
  let aH : AH ⟶ Rseq.X₂ := ObjectProperty.homMk a
  let qRH : Rseq.X₂ ⟶ BH := ObjectProperty.homMk qR
  have haq : aH ≫ qRH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hAB
  have hSat : (ShortComplex.mk aH qRH haq).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := AH) (B := Rseq.X₂) (Q := BH)
        (f := aH) (g := qRH) (δ := dA) hAB
  let e : EH ⟶ Rseq.X₂ := cokernel.π (fH ≫ iH)
  have hfe : (fH ≫ iH) ≫ e = 0 := cokernel.condition (fH ≫ iH)
  haveI : Epi e := by
    change Epi (coequalizer.π (fH ≫ iH) 0)
    infer_instance
  let qTotal : EH ⟶ BH := e ≫ qRH
  haveI : Epi qRH := hSat.epi_g
  haveI : Epi qTotal := by
    dsimp [qTotal]
    infer_instance
  let KH : H := kernel qTotal
  let kH : KH ⟶ EH := kernel.ι qTotal
  have hkq : kH ≫ qTotal = 0 := kernel.condition qTotal
  have hFinal : (ShortComplex.mk kH qTotal hkq).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel qTotal)
      inferInstance inferInstance
  obtain ⟨dk, hdk⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt kH qTotal hkq (fun {X} x hx => by
      exact ⟨hFinal.fIsKernel.lift (KernelFork.ofι x hx),
        hFinal.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  let Direct : ShortComplex H := ShortComplex.mk (fH ≫ iH) e hfe
  have hDirect : Direct.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (fH ≫ iH))
      inferInstance inferInstance
  let Kseq := kernelCompShortComplex e qRH
  have hKseq : Kseq.ShortExact := kernelCompShortComplex_shortExact e qRH
  let eG : Kseq.X₁ ≅ GH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel e) hDirect.fIsKernel
  let eK : Kseq.X₂ ≅ KH := by
    dsimp [Kseq, kernelCompShortComplex, qTotal, KH]
    exact Iso.refl _
  let eA : Kseq.X₃ ≅ AH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel qRH) hSat.fIsKernel
  let uK : GH ⟶ KH := eG.inv ≫ Kseq.f ≫ eK.hom
  let rK : KH ⟶ AH := eK.inv ≫ Kseq.g ≫ eA.hom
  have hur : uK ≫ rK = 0 := by
    simp [uK, rK, Kseq]
  let Sker : ShortComplex H := ShortComplex.mk uK rK hur
  let eKer : Kseq ≅ Sker := ShortComplex.isoMk eG eK eA
    (by
      change eG.hom ≫ (eG.inv ≫ Kseq.f ≫ eK.hom) =
        Kseq.f ≫ eK.hom
      simp)
    (by
      change eK.hom ≫ (eK.inv ≫ Kseq.g ≫ eA.hom) =
        Kseq.g ≫ eA.hom
      simp)
  have hSker : Sker.ShortExact :=
    ShortComplex.shortExact_of_iso eKer hKseq
  letI : Mono uK := hSker.mono_f
  letI : Epi rK := hSker.epi_g
  obtain ⟨du, hdu⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt uK rK hur (fun {X} x hx => by
      exact ⟨hSker.fIsKernel.lift (KernelFork.ofι x hx),
        hSker.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  exact ⟨KH.obj, A, B, KH.property, hA, hB,
    kH.hom, qTotal.hom, dk, hdk,
    uK.hom, rK.hom, du, hdu, hBss, hBcharge⟩

/-- Iterating the strengthened last-factor reduction constructs a weak HN
filtration for every extension of `F[1]` by a tilted zero-charge object, when
`F` belongs to the phase-cut torsion-free class.

The induction discards zero terminal factors in the chosen slicing HN tower.
For every nonzero factor it applies `phaseTilt_hnLastQuotient`; the recursive
kernel is the same kind of extension for the prefix.  The returned last-slope
identity records the last surviving original factor and turns strict phase
separation into the strict tilted-slope inequality required by
`append_hn_filtration_of_mono`. -/
theorem phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1))
    {F V E : C} (hFfree : phaseFree sigma.slicing beta F)
    (hV : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hE0 : ¬IsZero E)
    {i : F⟦(1 : ℤ)⟧ ⟶ E} {p : E ⟶ V}
    {d : V ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hd : Triangle.mk i p d ∈ distTriang C) :
    ∃ G : WeakAbelianHNFiltration
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) ⟨E, hE⟩,
      G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = ⊤ ∨
        ∃ L : C, phaseFree sigma.slicing beta L ∧ ¬IsZero L ∧
          G.μ ⟨G.n - 1, by have := G.hn; lia⟩ =
            (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).slope
              (L⟦(1 : ℤ)⟧) := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  have hFheart : t.heart F :=
    mem_heart_of_bounds sigma.slicing hFfree.1
      (sigma.slicing.leProp_mono C hbeta1.le F hFfree.2)
  by_cases hF0 : IsZero F
  · have hEcharge : W.charge E = 0 := by
      have hsum := W.charge_triangle' hd
      rw [W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hF0),
        hV.2, zero_add] at hsum
      exact hsum
    have hEzero : W.zeroCharge E := ⟨hE, hEcharge⟩
    obtain ⟨G, hG⟩ := W.exists_hn_with_last_slope_of_semistable
      (show ¬IsZero (⟨E, hE⟩ : H) from fun hzero =>
        hE0 (P.tilt.heart.ι.map_isZero hzero))
      (W.isSemistable_of_zeroCharge hEzero)
    refine ⟨G, Or.inl ?_⟩
    rw [hG]
    change W.slope E = ⊤
    exact W.slope_of_im_nonpos (by rw [hEcharge]; simp)
  suffices hmain :
      ∀ (m : ℕ) {X Z Q : C} (hX0 : ¬IsZero X)
        (hXfree : phaseFree sigma.slicing beta X)
        (FX : HNFiltration C sigma.slicing.P X) (hnFX : 0 < FX.n)
        (hFXm : FX.n ≤ m)
        (hfirst : ¬IsZero (FX.triangle ⟨0, hnFX⟩).obj₃)
        (hZ : P.tilt.heart Z) (hZ0 : ¬IsZero Z) (hQ : W.zeroCharge Q)
        {j : X⟦(1 : ℤ)⟧ ⟶ Z} {q : Z ⟶ Q}
        {delta : Q ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
        (hXZQ : Triangle.mk j q delta ∈ distTriang C),
        ∃ G : WeakAbelianHNFiltration W ⟨Z, hZ⟩, ∃ L : C,
          sigma.slicing.P (sigma.slicing.phiMinus C X hX0) L ∧
            ¬IsZero L ∧
              G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = W.slope (L⟦(1 : ℤ)⟧) by
    obtain ⟨FX, hnFX, hfirst, -⟩ :=
      sigma.slicing.exists_hn_nonzero_boundaries C hF0
    obtain ⟨G, L, hPL, hL0, hlast⟩ :=
      hmain FX.n hF0 hFfree FX hnFX le_rfl hfirst
      hE hE0 hV hd
    have hphaseL : sigma.slicing.phiMinus C F hF0 ∈ Set.Ioc (0 : ℝ) beta := by
      constructor
      · exact sigma.slicing.phiMinus_gt_of_gtProp C hF0 hFfree.1
      · exact (sigma.slicing.phiMinus_le_phiPlus C F hF0).trans
          (sigma.slicing.phiPlus_le_of_leProp C hF0 hFfree.2)
    have hLfree : phaseFree sigma.slicing beta L := ⟨
      sigma.slicing.gtProp_of_semistable C hPL hphaseL.1,
      sigma.slicing.leProp_of_semistable C hPL hphaseL.2⟩
    exact ⟨G, Or.inr ⟨L, hLfree, hL0, hlast⟩⟩
  intro m
  induction m with
  | zero =>
      intro X Z Q hX0 hXfree FX hnFX hFXm
      lia
  | succ m ih =>
      intro X Z Q hX0 hXfree FX hnFX hFXm hfirst hZ hZ0 hQ j q delta hXZQ
      have hXheart : t.heart X :=
        mem_heart_of_bounds sigma.slicing hXfree.1
          (sigma.slicing.leProp_mono C hbeta1.le X hXfree.2)
      by_cases h1 : FX.n = 1
      · let phi := FX.φ ⟨0, hnFX⟩
        have hlast : ¬IsZero (FX.triangle ⟨FX.n - 1, by lia⟩).obj₃ := by
          have hidx : (⟨FX.n - 1, by lia⟩ : Fin FX.n) = ⟨0, hnFX⟩ :=
            Fin.ext (by lia)
          simpa [hidx] using hfirst
        have hall : ∀ k : Fin FX.n, FX.φ k = phi := by
          intro k
          have hk : k = ⟨0, hnFX⟩ := Fin.ext (by lia)
          subst hk
          rfl
        have hP : sigma.slicing.P phi X :=
          sigma.slicing.semistable_of_HN_all_eq C FX hall
        have hphiMinus : sigma.slicing.phiMinus C X hX0 = phi := by
          rw [sigma.slicing.phiMinus_eq C X hX0 FX hnFX hlast]
          have hidx : (⟨FX.n - 1, by lia⟩ : Fin FX.n) = ⟨0, hnFX⟩ :=
            Fin.ext (by lia)
          simp [phi, hidx, CategoryTheory.Triangulated.HNFiltration.phiMinus]
        have hphi : phi ∈ Set.Ioc (0 : ℝ) beta := by
          constructor
          · rw [← hphiMinus]
            exact sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXfree.1
          · have hphiPlus : sigma.slicing.phiPlus C X hX0 = phi := by
              simpa [phi, CategoryTheory.Triangulated.HNFiltration.phiPlus] using
                sigma.slicing.phiPlus_eq C X hX0 FX hnFX hfirst
            rw [← hphiPlus]
            exact sigma.slicing.phiPlus_le_of_leProp C hX0 hXfree.2
        have hphi01 : phi ∈ Set.Ioc (0 : ℝ) 1 :=
          ⟨hphi.1, hphi.2.trans hbeta1.le⟩
        have hXss : W0.IsSemistable X :=
          sigma.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
            hphi01 X hP hX0
        have himX : 0 < (W0.charge X).im :=
          sigma.charge_im_pos_of_mem_P_phi_lt_one
            ⟨hphi.1, hphi.2.trans_lt hbeta1⟩ X hP hX0
        have hXcharge : W.charge (X⟦(1 : ℤ)⟧) ≠ 0 := by
          have hW0 : W0.charge X ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt himX)
          simpa [W, W0, WeakStabilityFunction.charge, phaseTiltRotation,
            K₀.of_shift_one] using
              mul_ne_zero (neg_ne_zero.mpr hW0)
                (Complex.exp_ne_zero (-(Real.pi * beta : ℂ) * Complex.I))
        have hZcharge : W.charge Z = W.charge (X⟦(1 : ℤ)⟧) := by
          have hsum := W.charge_triangle' hXZQ
          rw [hQ.2, add_zero] at hsum
          exact hsum
        by_cases himZ : 0 < (W.charge Z).im
        · obtain ⟨A, B, hA, hB, a, b, db, hAZB, hBss, hBcharge⟩ :=
            sigma.phaseTilt_semistableQuotient_of_extension beta hbeta0 hbeta1
              hdec hXfree hXss hXcharge hQ hZ hXZQ
          let AH : H := ⟨A, hA.1⟩
          let ZH : H := ⟨Z, hZ⟩
          let BH : H := ⟨B, hB.1⟩
          let aH : AH ⟶ ZH := ObjectProperty.homMk a
          let bH : ZH ⟶ BH := ObjectProperty.homMk b
          have hab : aH ≫ bH = 0 := by
            ext
            exact comp_distTriang_mor_zero₁₂ _ hAZB
          have hAB : (ShortComplex.mk aH bH hab).ShortExact :=
            TStructure.heartFullSubcategory_shortExact_of_distTriang
              (C := C) P.tilt (A := AH) (B := ZH) (Q := BH)
                (f := aH) (g := bH) (δ := db) hAZB
          have hB0 : ¬IsZero BH := fun hzero =>
            hXcharge (hBcharge.symm.trans (W.charge_isZero
              (P.tilt.heart.ι.map_isZero hzero)))
          by_cases hA0 : IsZero AH
          · haveI : IsIso bH := (hAB.isIso_g_iff).2 hA0
            let eZB : Z ≅ B := P.tilt.heart.ι.mapIso (asIso bH)
            have hZss : W.IsSemistable Z :=
              W.isSemistable_of_iso eZB.symm hBss
            obtain ⟨G, hG⟩ := W.exists_hn_with_last_slope_of_semistable
              (show ¬IsZero (⟨Z, hZ⟩ : H) from fun hzero =>
                hZ0 (P.tilt.heart.ι.map_isZero hzero)) hZss
            refine ⟨G, X, hphiMinus.symm ▸ hP, hX0, ?_⟩
            rw [hG]
            change W.slope Z = W.slope (X⟦(1 : ℤ)⟧)
            unfold WeakStabilityFunction.slope
            rw [hZcharge]
          · have hAss : W.IsSemistable A := W.isSemistable_of_zeroCharge hA
            obtain ⟨GA, hGA⟩ := W.exists_hn_with_last_slope_of_semistable
              hA0 hAss
            letI : Mono aH := hAB.mono_f
            let eB : cokernel aH ≅ BH :=
              IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel aH)
                hAB.gIsCokernel
            have hslopeB : W.heartSlope BH <
                GA.μ ⟨GA.n - 1, by have := GA.hn; lia⟩ := by
              rw [hGA]
              change W.slope B < W.slope A
              have himB : 0 < (W.charge B).im := by
                rw [hBcharge, ← hZcharge]
                exact himZ
              rw [W.slope_of_im_pos himB]
              have hAtop : W.slope A = ⊤ := by
                have himA : (W.charge A).im ≤ 0 := by rw [hA.2]; simp
                exact W.slope_of_im_nonpos (not_lt_of_ge himA)
              rw [hAtop]
              exact WithTop.coe_lt_top _
            obtain ⟨G, hG⟩ := W.append_hn_filtration_of_mono
              aH GA eB hB0 hBss hslopeB
            refine ⟨G, X, hphiMinus.symm ▸ hP, hX0, ?_⟩
            rw [hG]
            change W.slope B = W.slope (X⟦(1 : ℤ)⟧)
            unfold WeakStabilityFunction.slope
            rw [hBcharge]
        · have hQOld : sigma.zeroCharge Q :=
            (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
              beta hbeta0 hbeta1 Q).mp hQ
          have hTypeTwo : sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 Z := by
            refine ⟨X, Q, hXfree, hXss, hQOld, j, q, delta, hXZQ, ?_⟩
            intro hpos
            exact (not_lt_of_ge (le_of_not_gt himZ) hpos).elim
          have hZss : W.IsSemistable Z :=
            sigma.isSemistable_of_isPhaseTiltTypeTwo beta hbeta0 hbeta1
              hZ (hZcharge.symm ▸ hXcharge) hTypeTwo
          obtain ⟨G, hG⟩ := W.exists_hn_with_last_slope_of_semistable
            (show ¬IsZero (⟨Z, hZ⟩ : H) from fun hzero =>
              hZ0 (P.tilt.heart.ι.map_isZero hzero)) hZss
          refine ⟨G, X, hphiMinus.symm ▸ hP, hX0, ?_⟩
          rw [hG]
          change W.slope Z = W.slope (X⟦(1 : ℤ)⟧)
          unfold WeakStabilityFunction.slope
          rw [hZcharge]
      · have htwo : 2 ≤ FX.n := by lia
        by_cases hlast : IsZero (FX.triangle ⟨FX.n - 1, by lia⟩).obj₃
        · let FX' := CategoryTheory.Triangulated.HNFiltration.dropLast
            C FX (by lia) hlast
          have hnFX' : 0 < FX'.n := FX'.n_pos C hX0
          have hFX'm : FX'.n ≤ m := by
            change FX.n - 1 ≤ m
            lia
          have hfirst' : ¬IsZero (FX'.triangle ⟨0, hnFX'⟩).obj₃ := by
            simpa [FX', CategoryTheory.Triangulated.HNFiltration.dropLast,
              CategoryTheory.Triangulated.HNFiltration.prefix] using hfirst
          exact ih hX0 hXfree FX' hnFX' hFX'm hfirst' hZ hZ0 hQ hXZQ
        · have hall : ∀ k : Fin FX.n, FX.φ k ∈ Set.Ioc (0 : ℝ) beta := by
            intro k
            constructor
            · calc
                0 < sigma.slicing.phiMinus C X hX0 :=
                  sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXfree.1
                _ = FX.φ ⟨FX.n - 1, by lia⟩ :=
                  sigma.slicing.phiMinus_eq C X hX0 FX hnFX hlast
                _ ≤ FX.φ k := FX.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
            · calc
                FX.φ k ≤ FX.φ ⟨0, hnFX⟩ :=
                  FX.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le k.val))
                _ = sigma.slicing.phiPlus C X hX0 := by
                  symm
                  exact sigma.slicing.phiPlus_eq C X hX0 FX hnFX hfirst
                _ ≤ beta := sigma.slicing.phiPlus_le_of_leProp C hX0 hXfree.2
          let jLast : Fin FX.n := ⟨FX.n - 1, by lia⟩
          let Gobj : C := FX.chain.obj ⟨FX.n - 1, by lia⟩
          let U : C := (FX.triangle jLast).obj₃
          let FG : HNFiltration C sigma.slicing.P Gobj :=
            CategoryTheory.Triangulated.HNFiltration.prefix
              C FX (FX.n - 1) (by lia)
          have hnFG : 0 < FG.n := by change 0 < FX.n - 1; lia
          have hGfree : phaseFree sigma.slicing beta Gobj := by
            constructor
            · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
                C sigma.slicing FX
                (FX.n - 1) (by lia) (by lia) 0
                (fun k => (hall ⟨k, by lia⟩).1)
            · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
                C sigma.slicing FX
                (FX.n - 1) (by lia) (by lia) beta
                (fun k => (hall ⟨k, by lia⟩).2)
          have hG0 : ¬IsZero Gobj := by
            intro hzero
            have hzeroMap :
                ∀ f : (FG.triangle ⟨0, hnFG⟩).obj₃ ⟶ Gobj, f = 0 :=
              fun f => hzero.eq_of_tgt _ _
            exact hfirst <| by
              simpa [FG, CategoryTheory.Triangulated.HNFiltration.prefix,
                CategoryTheory.Triangulated.PostnikovTower.factor] using
                CategoryTheory.Triangulated.HNFiltration.isZero_factor_zero_of_hom_eq_zero
                  C sigma.slicing FG hnFG hzeroMap
          have hUfree : phaseFree sigma.slicing beta U := by
            exact ⟨
              sigma.slicing.gtProp_of_semistable C
                (FX.semistable jLast) (hall jLast).1,
              sigma.slicing.leProp_of_semistable C
                (FX.semistable jLast) (hall jLast).2⟩
          have hUheart : t.heart U :=
            mem_heart_of_bounds sigma.slicing hUfree.1
              (sigma.slicing.leProp_mono C hbeta1.le U hUfree.2)
          have hUss : W0.IsSemistable U :=
            sigma.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
              ⟨(hall jLast).1, (hall jLast).2.trans hbeta1.le⟩ U
              (FX.semistable jLast) hlast
          have hUoldcharge : W0.charge U ≠ 0 := by
            have him := sigma.charge_im_pos_of_mem_P_phi_lt_one
              ⟨(hall jLast).1, (hall jLast).2.trans_lt hbeta1⟩ U
                (FX.semistable jLast) hlast
            exact ne_of_apply_ne Complex.im (ne_of_gt him)
          have hUcharge : W.charge (U⟦(1 : ℤ)⟧) ≠ 0 := by
            simpa [W, W0, WeakStabilityFunction.charge, phaseTiltRotation,
              K₀.of_shift_one] using
                mul_ne_zero (neg_ne_zero.mpr hUoldcharge)
                  (Complex.exp_ne_zero (-(Real.pi * beta : ℂ) * Complex.I))
          let Tlast := FX.triangle jLast
          let e1 := Classical.choice (FX.triangle_obj₁ jLast)
          let e2 := Classical.choice (FX.triangle_obj₂ jLast)
          have hobj2 : FX.chain.obj' (FX.n - 1 + 1) (by lia) = FX.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            lia
          let e2X : Tlast.obj₂ ≅ X :=
            e2.trans ((eqToIso hobj2).trans (Classical.choice FX.top_iso))
          let f : Gobj ⟶ X := e1.inv ≫ Tlast.mor₁ ≫ e2X.hom
          let g : X ⟶ U := e2X.inv ≫ Tlast.mor₂
          let dd : U ⟶ Gobj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e1.hom⟦(1 : ℤ)⟧'
          have hGXU : Triangle.mk f g dd ∈ distTriang C := by
            refine isomorphic_distinguished _ (FX.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e1.symm e2X.symm (Iso.refl _)
              (by simp [Tlast, f, e2X]) (by simp [Tlast, g, e2X])
              (by simp [Tlast, dd])
          obtain ⟨K, A, B, hK, hA, hB, k, b, dk, hKZB,
            u, r, du, hGKA, hBss, hBcharge⟩ :=
              sigma.phaseTilt_hnLastQuotient beta hbeta0 hbeta1 hdec
                hGfree hXfree hUfree hUss hUcharge hQ hZ hGXU hXZQ
          have hK0 : ¬IsZero K := by
            intro hzero
            let GH : H := ⟨Gobj⟦(1 : ℤ)⟧, P.free_shift_mem_tilt_heart hGfree⟩
            let KH : H := ⟨K, hK⟩
            let AH : H := ⟨A, hA.1⟩
            let uH : GH ⟶ KH := ObjectProperty.homMk u
            let rH : KH ⟶ AH := ObjectProperty.homMk r
            have hur : uH ≫ rH = 0 := by
              ext
              exact comp_distTriang_mor_zero₁₂ _ hGKA
            have hshort : (ShortComplex.mk uH rH hur).ShortExact :=
              TStructure.heartFullSubcategory_shortExact_of_distTriang
                (C := C) P.tilt (A := GH) (B := KH) (Q := AH)
                  (f := uH) (g := rH) (δ := du) hGKA
            haveI : Mono uH := hshort.mono_f
            have hGHzero : IsZero GH := IsZero.of_mono_eq_zero uH (by
              ext
              exact hzero.eq_of_tgt _ _)
            have hGshiftzero := P.tilt.heart.ι.map_isZero hGHzero
            apply hG0
            rw [IsZero.iff_id_eq_zero] at hGshiftzero ⊢
            exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp
              (by simpa using hGshiftzero)
          have hfirstG : ¬IsZero (FG.triangle ⟨0, hnFG⟩).obj₃ := by
            simpa [FG, CategoryTheory.Triangulated.HNFiltration.prefix] using hfirst
          obtain ⟨GK, L, hPL, hL0, hGKlast⟩ :=
            ih hG0 hGfree FG hnFG (by change FX.n - 1 ≤ m; lia)
              hfirstG hK hK0 hA hGKA
          have hLheart : t.heart L := by
            have hphaseL : sigma.slicing.phiMinus C Gobj hG0 ∈ Set.Ioc (0 : ℝ) 1 := by
              constructor
              · exact sigma.slicing.phiMinus_gt_of_gtProp C hG0 hGfree.1
              · exact (sigma.slicing.phiMinus_le_phiPlus C Gobj hG0).trans
                  ((sigma.slicing.phiPlus_le_of_leProp C hG0 hGfree.2).trans
                    hbeta1.le)
            exact mem_heart_of_bounds sigma.slicing
              (sigma.slicing.gtProp_of_semistable C hPL hphaseL.1)
              (sigma.slicing.leProp_of_semistable C hPL hphaseL.2)
          have hLfree : phaseFree sigma.slicing beta L := by
            have hphaseLe : sigma.slicing.phiMinus C Gobj hG0 ≤ beta :=
              (sigma.slicing.phiMinus_le_phiPlus C Gobj hG0).trans
                (sigma.slicing.phiPlus_le_of_leProp C hG0 hGfree.2)
            exact ⟨
              sigma.slicing.gtProp_of_semistable C hPL
                (sigma.slicing.phiMinus_gt_of_gtProp C hG0 hGfree.1),
              sigma.slicing.leProp_of_semistable C hPL hphaseLe⟩
          have hphaseSep : FX.φ jLast < sigma.slicing.phiMinus C Gobj hG0 := by
            have hGgt : sigma.slicing.gtProp C (FX.φ jLast) Gobj :=
              CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
                C sigma.slicing FX
                (FX.n - 1) (by lia) (by lia) (FX.φ jLast) (fun a => by
                  exact FX.hφ (Fin.mk_lt_mk.mpr (by have := a.isLt; lia)))
            exact sigma.slicing.phiMinus_gt_of_gtProp C hG0 hGgt
          have hUplus : sigma.slicing.phiPlus C U hlast = FX.φ jLast :=
            (sigma.slicing.phiPlus_eq_phiMinus_of_semistable C
              (FX.semistable jLast) hlast).1
          have hLminus : sigma.slicing.phiMinus C L hL0 =
              sigma.slicing.phiMinus C Gobj hG0 :=
            (sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hPL hL0).2
          have hLcharge : W0.charge L ≠ 0 := by
            have hphaseL : sigma.slicing.phiMinus C Gobj hG0 ∈ Set.Ioo (0 : ℝ) 1 :=
              ⟨sigma.slicing.phiMinus_gt_of_gtProp C hG0 hGfree.1,
                (sigma.slicing.phiMinus_le_phiPlus C Gobj hG0).trans_lt
                  ((sigma.slicing.phiPlus_le_of_leProp C hG0 hGfree.2).trans_lt
                    hbeta1)⟩
            exact ne_of_apply_ne Complex.im (ne_of_gt
              (sigma.charge_im_pos_of_mem_P_phi_lt_one hphaseL L hPL hL0))
          have hWU : W.charge (U⟦(1 : ℤ)⟧) =
              phaseTiltRotation beta (-(W0.charge U)) := by
            simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation,
              K₀.of_shift_one]
          have hWL : W.charge (L⟦(1 : ℤ)⟧) =
              phaseTiltRotation beta (-(W0.charge L)) := by
            simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation,
              K₀.of_shift_one]
          have hslope : W.slope B < W.slope (L⟦(1 : ℤ)⟧) := by
            have hraw := phaseTilt_slope_shift_lt_shift_of_phase_separated
              sigma W hUheart hLheart
                (P.free_shift_mem_tilt_heart hUfree)
                (P.free_shift_mem_tilt_heart hLfree)
                hWU hWL hlast hL0 (by
                  calc
                    sigma.slicing.phiPlus C U hlast = FX.φ jLast := hUplus
                    _ < sigma.slicing.phiMinus C Gobj hG0 := hphaseSep
                    _ = sigma.slicing.phiMinus C L hL0 := hLminus.symm)
                (hUplus.trans_lt ((hall jLast).2.trans_lt hbeta1)) hLcharge
            unfold WeakStabilityFunction.slope at hraw ⊢
            rwa [hBcharge]
          let KH : H := ⟨K, hK⟩
          let ZH : H := ⟨Z, hZ⟩
          let BH : H := ⟨B, hB.1⟩
          let kH : KH ⟶ ZH := ObjectProperty.homMk k
          let bH : ZH ⟶ BH := ObjectProperty.homMk b
          have hkb : kH ≫ bH = 0 := by
            ext
            exact comp_distTriang_mor_zero₁₂ _ hKZB
          have hshort : (ShortComplex.mk kH bH hkb).ShortExact :=
            TStructure.heartFullSubcategory_shortExact_of_distTriang
              (C := C) P.tilt (A := KH) (B := ZH) (Q := BH)
                (f := kH) (g := bH) (δ := dk) hKZB
          letI : Mono kH := hshort.mono_f
          let eB : cokernel kH ≅ BH :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel kH)
              hshort.gIsCokernel
          have hBlast : W.heartSlope BH <
              GK.μ ⟨GK.n - 1, by have := GK.hn; lia⟩ := by
            rw [hGKlast]
            exact hslope
          have hBH0 : ¬IsZero BH := fun hzero =>
            hUcharge (hBcharge.symm.trans
              (W.charge_isZero (P.tilt.heart.ι.map_isZero hzero)))
          obtain ⟨GZ, hGZ⟩ := W.append_hn_filtration_of_mono
            kH GK eB hBH0 hBss hBlast
          refine ⟨GZ, U, ?_, hlast, ?_⟩
          · rw [sigma.slicing.phiMinus_eq C X hX0 FX hnFX hlast]
            exact FX.semistable jLast
          · rw [hGZ]
            change W.slope B = W.slope (U⟦(1 : ℤ)⟧)
            unfold WeakStabilityFunction.slope
            rw [hBcharge]

/-- Every free-shift/zero-charge extension has a weak HN filtration. -/
theorem phaseTilt_hasHN_of_freeShift_zeroCharge_extension
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1))
    {F V E : C} (hFfree : phaseFree sigma.slicing beta F)
    (hV : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hE0 : ¬IsZero E)
    {i : F⟦(1 : ℤ)⟧ ⟶ E} {p : E ⟶ V}
    {d : V ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hd : Triangle.mk i p d ∈ distTriang C) :
    Nonempty (WeakAbelianHNFiltration
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
      ⟨E, hE⟩) := by
  obtain ⟨G, -⟩ :=
    sigma.phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
      beta hbeta0 hbeta1 hdec hFfree hV hE hE0 hd
  exact ⟨G⟩

/-- **The `H⁰` last-factor kernel calculation.**

Given short exact sequences `F[1] ⟶ E ⟶ N` and `G ⟶ N ⟶ U` in the
tilted heart, the kernel of the composite quotient `E ⟶ U` fits into
`F[1] ⟶ K ⟶ G`.  This is the dual kernel-of-composite diagram used to
iterate the original `H⁰` HN filtration. -/
theorem phaseTilt_hZeroLastQuotient
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {F E N G U : C}
    (hFfree : phaseFree sigma.slicing beta F)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hN : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart N)
    (hG : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart G)
    (hU : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart U)
    {i : F⟦(1 : ℤ)⟧ ⟶ E} {p : E ⟶ N}
    {d : N ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hFEN : Triangle.mk i p d ∈ distTriang C)
    {a : G ⟶ N} {q : N ⟶ U} {delta : U ⟶ G⟦(1 : ℤ)⟧}
    (hGNU : Triangle.mk a q delta ∈ distTriang C) :
    ∃ (K : C)
      (_ : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart K)
      (k : K ⟶ E) (b : E ⟶ U) (dk : U ⟶ K⟦(1 : ℤ)⟧),
        Triangle.mk k b dk ∈ distTriang C ∧
          ∃ (u : F⟦(1 : ℤ)⟧ ⟶ K) (r : K ⟶ G)
            (du : G ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
              Triangle.mk u r du ∈ distTriang C := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  let FH : H := ⟨F⟦(1 : ℤ)⟧, P.free_shift_mem_tilt_heart hFfree⟩
  let EH : H := ⟨E, hE⟩
  let NH : H := ⟨N, hN⟩
  let GH : H := ⟨G, hG⟩
  let UH : H := ⟨U, hU⟩
  let iH : FH ⟶ EH := ObjectProperty.homMk i
  let pH : EH ⟶ NH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hFEN
  have hOuter : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := FH) (B := EH) (Q := NH)
        (f := iH) (g := pH) (δ := d) hFEN
  let aH : GH ⟶ NH := ObjectProperty.homMk a
  let qH : NH ⟶ UH := ObjectProperty.homMk q
  have haq : aH ≫ qH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hGNU
  have hLast : (ShortComplex.mk aH qH haq).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := GH) (B := NH) (Q := UH)
        (f := aH) (g := qH) (δ := delta) hGNU
  letI : Epi pH := hOuter.epi_g
  letI : Epi qH := hLast.epi_g
  let total : EH ⟶ UH := pH ≫ qH
  letI : Epi total := by dsimp [total]; infer_instance
  let KH : H := kernel total
  let kH : KH ⟶ EH := kernel.ι total
  have hkt : kH ≫ total = 0 := kernel.condition total
  have hFinal : (ShortComplex.mk kH total hkt).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel total)
      inferInstance inferInstance
  obtain ⟨dk, hdk⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt kH total hkt (fun {X} x hx => by
      exact ⟨hFinal.fIsKernel.lift (KernelFork.ofι x hx),
        hFinal.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  let Kseq := kernelCompShortComplex pH qH
  have hKseq : Kseq.ShortExact := kernelCompShortComplex_shortExact pH qH
  let eF : Kseq.X₁ ≅ FH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel pH) hOuter.fIsKernel
  let eK : Kseq.X₂ ≅ KH := by
    dsimp [Kseq, kernelCompShortComplex, total, KH]
    exact Iso.refl _
  let eG : Kseq.X₃ ≅ GH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel qH) hLast.fIsKernel
  let uK : FH ⟶ KH := eF.inv ≫ Kseq.f ≫ eK.hom
  let rK : KH ⟶ GH := eK.inv ≫ Kseq.g ≫ eG.hom
  have hur : uK ≫ rK = 0 := by
    simp [uK, rK, Kseq]
  let Sker : ShortComplex H := ShortComplex.mk uK rK hur
  let eKer : Kseq ≅ Sker := ShortComplex.isoMk eF eK eG
    (by
      change eF.hom ≫ (eF.inv ≫ Kseq.f ≫ eK.hom) = Kseq.f ≫ eK.hom
      simp)
    (by
      change eK.hom ≫ (eK.inv ≫ Kseq.g ≫ eG.hom) = Kseq.g ≫ eG.hom
      simp)
  have hSker : Sker.ShortExact :=
    ShortComplex.shortExact_of_iso eKer hKseq
  letI : Mono uK := hSker.mono_f
  letI : Epi rK := hSker.epi_g
  obtain ⟨du, hdu⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt uK rK hur (fun {X} x hx => by
      exact ⟨hSker.fIsKernel.lift (KernelFork.ofι x hx),
        hSker.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  exact ⟨KH.obj, KH.property, kH.hom, total.hom, dk, hdk,
    uK.hom, rK.hom, du, hdu⟩

/-- Iterating the original `H⁰` HN filtration, with the `H⁻¹` induction as
its base case, proves the weak HN property for the phase-tilted heart.

Charged terminal `H⁰` factors below phase `1` are directly of phase-tilt type
one.  At the boundary phase, the original zero-charge torsion pair first
saturates the factor; its zero-charge kernel is absorbed by the already
formalized `H⁻¹` induction. -/
theorem phaseTilt_hasHNProperty_of_zeroChargeDecompositions
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1)) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).HasHNProperty := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  intro E hE0
  have hEobj : ¬IsZero E.obj := fun hzero =>
    hE0 (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
  let F : C := (P.originalHMinusOne E.property).obj
  let N : C := (P.originalHZero E.property).obj
  have hFfree : phaseFree sigma.slicing beta F := P.originalHMinusOne_free E.property
  have hNtors : phaseTors sigma.slicing beta N := P.originalHZero_tors E.property
  let Scoh := P.originalCohomologyShortComplex E.property
  have hScoh : Scoh.ShortExact := P.originalCohomologyShortComplex_shortExact E.property
  letI : Mono Scoh.f := hScoh.mono_f
  letI : Epi Scoh.g := hScoh.epi_g
  obtain ⟨dCoh, hdCoh⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt Scoh.f Scoh.g Scoh.zero (fun {X} x hx => by
      exact ⟨hScoh.fIsKernel.lift (KernelFork.ofι x hx),
        hScoh.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  by_cases hNzero : IsZero N
  · have hNnew : W.zeroCharge N := ⟨Scoh.X₃.property, W.charge_isZero hNzero⟩
    obtain ⟨G, -⟩ :=
      sigma.phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
        beta hbeta0.le hbeta1 hdec hFfree hNnew E.property hEobj hdCoh
    exact ⟨G⟩
  obtain ⟨FN, hnFN, hfirst, -⟩ :=
    sigma.slicing.exists_hn_nonzero_boundaries C hNzero
  suffices hmain :
      ∀ (m : ℕ) {X Z : C} (hX0 : ¬IsZero X)
        (hXtors : phaseTors sigma.slicing beta X)
        (FX : HNFiltration C sigma.slicing.P X) (hnFX : 0 < FX.n)
        (hFXm : FX.n ≤ m)
        (hfirstX : ¬IsZero (FX.triangle ⟨0, hnFX⟩).obj₃)
        (hZ : P.tilt.heart Z) (hZ0 : ¬IsZero Z)
        {i : F⟦(1 : ℤ)⟧ ⟶ Z} {p : Z ⟶ X}
        {d : X ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
        (hFZX : Triangle.mk i p d ∈ distTriang C),
        ∃ G : WeakAbelianHNFiltration W ⟨Z, hZ⟩,
          G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = ⊤ ∨
            (∃ L : C, phaseFree sigma.slicing beta L ∧ ¬IsZero L ∧
              G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = W.slope (L⟦(1 : ℤ)⟧)) ∨
            ∃ L : C, sigma.slicing.P (sigma.slicing.phiMinus C X hX0) L ∧
              ¬IsZero L ∧ W0.charge L ≠ 0 ∧
                G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = W.slope L by
    obtain ⟨G, -⟩ := hmain FN.n hNzero hNtors FN hnFN le_rfl hfirst
      E.property hEobj hdCoh
    exact ⟨G⟩
  intro m
  induction m with
  | zero =>
      intro X Z hX0 hXtors FX hnFX hFXm
      lia
  | succ m ih =>
      intro X Z hX0 hXtors FX hnFX hFXm hfirstX hZ hZ0 i p d hFZX
      have hXheart : t.heart X :=
        mem_heart_of_bounds sigma.slicing
          (sigma.slicing.gtProp_anti C hbeta0.le X hXtors.1) hXtors.2
      by_cases h1 : FX.n = 1
      · let phi := FX.φ ⟨0, hnFX⟩
        have hlast : ¬IsZero (FX.triangle ⟨FX.n - 1, by lia⟩).obj₃ := by
          have hidx : (⟨FX.n - 1, by lia⟩ : Fin FX.n) = ⟨0, hnFX⟩ :=
            Fin.ext (by lia)
          simpa [hidx] using hfirstX
        have hall : ∀ k : Fin FX.n, FX.φ k = phi := by
          intro k
          have hk : k = ⟨0, hnFX⟩ := Fin.ext (by lia)
          subst hk
          rfl
        have hPX : sigma.slicing.P phi X :=
          sigma.slicing.semistable_of_HN_all_eq C FX hall
        have hphiMinus : sigma.slicing.phiMinus C X hX0 = phi := by
          rw [sigma.slicing.phiMinus_eq C X hX0 FX hnFX hlast]
          have hidx : (⟨FX.n - 1, by lia⟩ : Fin FX.n) = ⟨0, hnFX⟩ :=
            Fin.ext (by lia)
          simp [phi, hidx, CategoryTheory.Triangulated.HNFiltration.phiMinus]
        have hphi : phi ∈ Set.Ioc beta 1 := by
          constructor
          · rw [← hphiMinus]
            exact sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXtors.1
          · have hp : sigma.slicing.phiPlus C X hX0 = phi := by
              simpa [phi, CategoryTheory.Triangulated.HNFiltration.phiPlus] using
                sigma.slicing.phiPlus_eq C X hX0 FX hnFX hfirstX
            rw [← hp]
            exact sigma.slicing.phiPlus_le_of_leProp C hX0 hXtors.2
        have hXss : W0.IsSemistable X :=
          sigma.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
            ⟨hbeta0.trans hphi.1, hphi.2⟩ X hPX hX0
        by_cases hXcharge0 : W0.charge X = 0
        · have hXoldZero : sigma.zeroCharge X := ⟨hXheart, hXcharge0⟩
          have hXnewZero : W.zeroCharge X :=
            (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
              beta hbeta0.le hbeta1 X).mpr hXoldZero
          obtain ⟨G, hsource⟩ :=
            sigma.phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
              beta hbeta0.le hbeta1 hdec hFfree hXnewZero hZ hZ0 hFZX
          exact ⟨G, hsource.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
        · obtain ⟨A, B, hAtors, hBfree, a, b, db, hAXB⟩ :=
            N0.pair.exists_triangle X
              ((t.mem_heart_iff X).mp hXheart).1
              ((t.mem_heart_iff X).mp hXheart).2
          have hAold : sigma.zeroCharge A := by rw [← hN0]; exact hAtors
          have hAnew : W.zeroCharge A :=
            (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
              beta hbeta0.le hbeta1 A).mpr hAold
          have hBheart : t.heart B :=
            (t.mem_heart_iff B).mpr
              ⟨N0.pair.free_isLE B hBfree, N0.pair.free_isGE B hBfree⟩
          have hAphase : phaseTors sigma.slicing beta A :=
            sigma.zeroCharge_phaseTors beta hbeta1 hAold
          have hAshift : sigma.slicing.gtProp C beta (A⟦(1 : ℤ)⟧) := by
            have hs := sigma.slicing.gtProp_shift C beta A 1 hAphase.1
            exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hs
          have hBphase : phaseTors sigma.slicing beta B := by
            constructor
            · exact sigma.slicing.gtProp_of_triangle C beta hXtors.1 hAshift
                (rot_of_distTriang _ hAXB)
            · exact ((sigma.slicing.toTStructure_heart_iff C B).mp hBheart).2
          have hBtilt : P.tilt.heart B := P.tors_mem_tilt_heart hBphase
          have hBssOld : W0.IsSemistable B :=
            sigma.weakStabilityFunctionOnHeart.isSemistable_quotient_of_zeroCharge_subobject
              (t := t) hAold hXss hBheart hAXB
          have hBorth : ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ B, f = 0 := by
            intro A0 hA0 f
            exact N0.pair.hom_eq_zero (by rw [hN0]; exact hA0) hBfree f
          have hBtype : sigma.IsPhaseTiltTypeOne B := ⟨hBssOld, hBorth⟩
          have hXnewcharge : W.charge X ≠ 0 := by
            simpa [W, W0, WeakStabilityFunction.charge, phaseTiltRotation] using
              mul_ne_zero hXcharge0
                (Complex.exp_ne_zero (-(Real.pi * beta : ℂ) * Complex.I))
          have hBcharge : W.charge B = W.charge X := by
            have hsum := W.charge_triangle' hAXB
            rw [hAnew.2, zero_add] at hsum
            exact hsum.symm
          have hBss : W.IsSemistable B :=
            sigma.isSemistable_of_isPhaseTiltTypeOne beta hbeta0.le hbeta1
              hBtilt (hBcharge.symm ▸ hXnewcharge) hBtype
          obtain ⟨K, hK, k, qB, dk, hKZB, u, r, du, hFKA⟩ :=
            sigma.phaseTilt_hZeroLastQuotient beta hbeta0.le hbeta1 hFfree
              hZ (P.tors_mem_tilt_heart hXtors) hAnew.1 hBtilt hFZX hAXB
          let KH : H := ⟨K, hK⟩
          let ZH : H := ⟨Z, hZ⟩
          let BH : H := ⟨B, hBtilt⟩
          let kH : KH ⟶ ZH := ObjectProperty.homMk k
          let qBH : ZH ⟶ BH := ObjectProperty.homMk qB
          have hkq : kH ≫ qBH = 0 := by
            ext
            exact comp_distTriang_mor_zero₁₂ _ hKZB
          have hshort : (ShortComplex.mk kH qBH hkq).ShortExact :=
            TStructure.heartFullSubcategory_shortExact_of_distTriang
              (C := C) P.tilt (A := KH) (B := ZH) (Q := BH)
                (f := kH) (g := qBH) (δ := dk) hKZB
          have hBH0 : ¬IsZero BH := fun hzero =>
            hXnewcharge (hBcharge.symm.trans
              (W.charge_isZero (P.tilt.heart.ι.map_isZero hzero)))
          by_cases hK0 : IsZero KH
          · haveI : IsIso qBH := (hshort.isIso_g_iff).2 hK0
            let eZB : Z ≅ B := P.tilt.heart.ι.mapIso (asIso qBH)
            have hZss : W.IsSemistable Z := W.isSemistable_of_iso eZB.symm hBss
            obtain ⟨G, hG⟩ := W.exists_hn_with_last_slope_of_semistable
              (show ¬IsZero ZH from fun hz => hZ0 (P.tilt.heart.ι.map_isZero hz)) hZss
            refine ⟨G, Or.inr (Or.inr
              ⟨X, hphiMinus.symm ▸ hPX, hX0, hXcharge0, ?_⟩)⟩
            rw [hG]
            change W.slope Z = W.slope X
            unfold WeakStabilityFunction.slope
            rw [show W.charge Z = W.charge B from W.charge_eq_of_iso eZB,
              hBcharge]
          · obtain ⟨GK, hsource⟩ :=
              sigma.phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
                beta hbeta0.le hbeta1 hdec hFfree hAnew hK
                  (fun hz => hK0 (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hz))
                  hFKA
            have himB : 0 < (W.charge B).im := by
              rw [hBcharge]
              exact phaseTiltCharge_im_pos_of_phaseTors sigma hbeta0 hXtors (by
                simpa [W, W0, WeakStabilityFunction.charge, phaseTiltRotation] using
                  mul_ne_zero hXcharge0
                    (Complex.exp_ne_zero (-(Real.pi * beta : ℂ) * Complex.I)))
            have hslope : W.heartSlope BH <
                GK.μ ⟨GK.n - 1, by have := GK.hn; lia⟩ := by
              rcases hsource with htop | ⟨L, hLfree, hL0, hlastL⟩
              · rw [htop]
                change W.slope B < ⊤
                rw [W.slope_of_im_pos himB]
                exact WithTop.coe_lt_top _
              · rw [hlastL]
                have hLheart : t.heart L :=
                  mem_heart_of_bounds sigma.slicing hLfree.1
                    (sigma.slicing.leProp_mono C hbeta1.le L hLfree.2)
                have hsep : sigma.slicing.phiPlus C L hL0 <
                    sigma.slicing.phiMinus C X hX0 :=
                  (sigma.slicing.phiPlus_le_of_leProp C hL0 hLfree.2).trans_lt
                    (sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXtors.1)
                have hWL : W.charge (L⟦(1 : ℤ)⟧) =
                    phaseTiltRotation beta (-(W0.charge L)) := by
                  simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation,
                    K₀.of_shift_one]
                have hWX : W.charge X = phaseTiltRotation beta (W0.charge X) := by
                  rfl
                have hraw := phaseTilt_slope_unshifted_lt_shifted_of_phase_separated
                  sigma W hLheart hXheart
                    (P.free_shift_mem_tilt_heart hLfree)
                    (P.tors_mem_tilt_heart hXtors) hWL hWX hL0 hX0 hsep
                    ((sigma.slicing.phiPlus_le_of_leProp C hL0 hLfree.2).trans_lt
                      hbeta1) hXcharge0
                change W.slope B < W.slope (L⟦(1 : ℤ)⟧)
                unfold WeakStabilityFunction.slope at hraw ⊢
                rwa [hBcharge]
            letI : Mono kH := hshort.mono_f
            let eB : cokernel kH ≅ BH :=
              IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel kH)
                hshort.gIsCokernel
            obtain ⟨G, hG⟩ := W.append_hn_filtration_of_mono
              kH GK eB hBH0 hBss hslope
            refine ⟨G, Or.inr (Or.inr
              ⟨X, hphiMinus.symm ▸ hPX, hX0, hXcharge0, ?_⟩)⟩
            rw [hG]
            change W.slope B = W.slope X
            unfold WeakStabilityFunction.slope
            rw [hBcharge]
      · have htwo : 2 ≤ FX.n := by lia
        by_cases hlast : IsZero (FX.triangle ⟨FX.n - 1, by lia⟩).obj₃
        · let FX' := CategoryTheory.Triangulated.HNFiltration.dropLast
            C FX (by lia) hlast
          have hnFX' : 0 < FX'.n := FX'.n_pos C hX0
          have hfirst' : ¬IsZero (FX'.triangle ⟨0, hnFX'⟩).obj₃ := by
            simpa [FX', CategoryTheory.Triangulated.HNFiltration.dropLast,
              CategoryTheory.Triangulated.HNFiltration.prefix] using hfirstX
          exact ih hX0 hXtors FX' hnFX' (by change FX.n - 1 ≤ m; lia)
            hfirst' hZ hZ0 hFZX
        · have hall : ∀ k : Fin FX.n, FX.φ k ∈ Set.Ioc beta 1 := by
            intro k
            constructor
            · calc
                beta < sigma.slicing.phiMinus C X hX0 :=
                  sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXtors.1
                _ = FX.φ ⟨FX.n - 1, by lia⟩ :=
                  sigma.slicing.phiMinus_eq C X hX0 FX hnFX hlast
                _ ≤ FX.φ k := FX.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
            · calc
                FX.φ k ≤ FX.φ ⟨0, hnFX⟩ :=
                  FX.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le k.val))
                _ = sigma.slicing.phiPlus C X hX0 := by
                  symm
                  exact sigma.slicing.phiPlus_eq C X hX0 FX hnFX hfirstX
                _ ≤ 1 := sigma.slicing.phiPlus_le_of_leProp C hX0 hXtors.2
          let jLast : Fin FX.n := ⟨FX.n - 1, by lia⟩
          let Gobj : C := FX.chain.obj ⟨FX.n - 1, by lia⟩
          let U : C := (FX.triangle jLast).obj₃
          let FG : HNFiltration C sigma.slicing.P Gobj :=
            CategoryTheory.Triangulated.HNFiltration.prefix
              C FX (FX.n - 1) (by lia)
          have hnFG : 0 < FG.n := by change 0 < FX.n - 1; lia
          have hGtors : phaseTors sigma.slicing beta Gobj := ⟨
            CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
              C sigma.slicing FX
              (FX.n - 1) (by lia) (by lia) beta
                (fun k => (hall ⟨k, by lia⟩).1),
            CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
              C sigma.slicing FX
              (FX.n - 1) (by lia) (by lia) 1
                (fun k => (hall ⟨k, by lia⟩).2)⟩
          have hG0 : ¬IsZero Gobj := by
            intro hzero
            exact hfirstX <| by
              simpa [FG, CategoryTheory.Triangulated.HNFiltration.prefix,
                CategoryTheory.Triangulated.PostnikovTower.factor] using
                CategoryTheory.Triangulated.HNFiltration.isZero_factor_zero_of_hom_eq_zero
                  C sigma.slicing FG hnFG (fun f => hzero.eq_of_tgt _ _)
          have hUphase : phaseTors sigma.slicing beta U := ⟨
            sigma.slicing.gtProp_of_semistable C
              (FX.semistable jLast) (hall jLast).1,
            sigma.slicing.leProp_of_semistable C
              (FX.semistable jLast) (hall jLast).2⟩
          have hUheart : t.heart U :=
            mem_heart_of_bounds sigma.slicing
              (sigma.slicing.gtProp_anti C hbeta0.le U hUphase.1) hUphase.2
          have hUssOld : W0.IsSemistable U :=
            sigma.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
              ⟨hbeta0.trans (hall jLast).1, (hall jLast).2⟩ U
              (FX.semistable jLast) hlast
          have hUphiLt : FX.φ jLast < 1 := by
            let jPrev : Fin FX.n := ⟨FX.n - 2, by lia⟩
            have hj : jPrev < jLast := Fin.mk_lt_mk.mpr (by
              lia)
            exact (FX.hφ hj).trans_le (hall jPrev).2
          have hUchargeOld : W0.charge U ≠ 0 :=
            ne_of_apply_ne Complex.im (ne_of_gt
              (sigma.charge_im_pos_of_mem_P_phi_lt_one
                ⟨hbeta0.trans (hall jLast).1, hUphiLt⟩ U
                  (FX.semistable jLast) hlast))
          have hUorth : ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ U, f = 0 := by
            intro A0 hA0 f
            exact sigma.slicing.zero_of_gtProp_leProp_general C (FX.φ jLast)
              (sigma.zeroCharge_phaseTors (FX.φ jLast) hUphiLt hA0).1
              (sigma.slicing.leProp_of_semistable C
                (FX.semistable jLast) le_rfl) f
          have hUtilt : P.tilt.heart U := P.tors_mem_tilt_heart hUphase
          have hUcharge : W.charge U ≠ 0 := by
            simpa [W, W0, WeakStabilityFunction.charge, phaseTiltRotation] using
              mul_ne_zero hUchargeOld
                (Complex.exp_ne_zero (-(Real.pi * beta : ℂ) * Complex.I))
          have hUss : W.IsSemistable U :=
            sigma.isSemistable_of_isPhaseTiltTypeOne beta hbeta0.le hbeta1
              hUtilt hUcharge ⟨hUssOld, hUorth⟩
          let Tlast := FX.triangle jLast
          let e1 := Classical.choice (FX.triangle_obj₁ jLast)
          let e2 := Classical.choice (FX.triangle_obj₂ jLast)
          have hobj2 : FX.chain.obj' (FX.n - 1 + 1) (by lia) = FX.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            lia
          let e2X : Tlast.obj₂ ≅ X :=
            e2.trans ((eqToIso hobj2).trans (Classical.choice FX.top_iso))
          let a : Gobj ⟶ X := e1.inv ≫ Tlast.mor₁ ≫ e2X.hom
          let qU : X ⟶ U := e2X.inv ≫ Tlast.mor₂
          let du : U ⟶ Gobj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e1.hom⟦(1 : ℤ)⟧'
          have hGXU : Triangle.mk a qU du ∈ distTriang C := by
            refine isomorphic_distinguished _ (FX.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e1.symm e2X.symm (Iso.refl _)
              (by simp [Tlast, a, e2X]) (by simp [Tlast, qU, e2X])
              (by simp [Tlast, du])
          obtain ⟨K, hK, k, qK, dk, hKZU, u, r, dr, hFKG⟩ :=
            sigma.phaseTilt_hZeroLastQuotient beta hbeta0.le hbeta1 hFfree
              hZ (P.tors_mem_tilt_heart hXtors)
                (P.tors_mem_tilt_heart hGtors) hUtilt hFZX hGXU
          have hK0 : ¬IsZero K := by
            intro hz
            let KH : H := ⟨K, hK⟩
            let GH : H := ⟨Gobj, P.tors_mem_tilt_heart hGtors⟩
            let rH : KH ⟶ GH := ObjectProperty.homMk r
            haveI : Epi rH := by
              let FH : H := ⟨F⟦(1 : ℤ)⟧, P.free_shift_mem_tilt_heart hFfree⟩
              let uH : FH ⟶ KH := ObjectProperty.homMk u
              have hur : uH ≫ rH = 0 := by
                ext
                exact comp_distTriang_mor_zero₁₂ _ hFKG
              exact (TStructure.heartFullSubcategory_shortExact_of_distTriang
                (C := C) P.tilt (A := FH) (B := KH) (Q := GH)
                  (f := uH) (g := rH) (δ := dr) hFKG).epi_g
            exact hG0 (P.tilt.heart.ι.map_isZero
              (IsZero.of_epi rH (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hz)))
          have hfirstG : ¬IsZero (FG.triangle ⟨0, hnFG⟩).obj₃ := by
            simpa [FG, CategoryTheory.Triangulated.HNFiltration.prefix] using hfirstX
          obtain ⟨GK, hsource⟩ := ih hG0 hGtors FG hnFG
            (by change FX.n - 1 ≤ m; lia) hfirstG hK hK0 hFKG
          let KH : H := ⟨K, hK⟩
          let ZH : H := ⟨Z, hZ⟩
          let UH : H := ⟨U, hUtilt⟩
          let kH : KH ⟶ ZH := ObjectProperty.homMk k
          let qH : ZH ⟶ UH := ObjectProperty.homMk qK
          have hkq : kH ≫ qH = 0 := by
            ext
            exact comp_distTriang_mor_zero₁₂ _ hKZU
          have hshort : (ShortComplex.mk kH qH hkq).ShortExact :=
            TStructure.heartFullSubcategory_shortExact_of_distTriang
              (C := C) P.tilt (A := KH) (B := ZH) (Q := UH)
                (f := kH) (g := qH) (δ := dk) hKZU
          have hUH0 : ¬IsZero UH := fun hz =>
            hUcharge (W.charge_isZero (P.tilt.heart.ι.map_isZero hz))
          have himU : 0 < (W.charge U).im :=
            phaseTiltCharge_im_pos_of_phaseTors sigma hbeta0 hUphase (by
              simpa [W, W0, WeakStabilityFunction.charge, phaseTiltRotation] using
                mul_ne_zero hUchargeOld
                  (Complex.exp_ne_zero (-(Real.pi * beta : ℂ) * Complex.I)))
          have hslope : W.heartSlope UH <
              GK.μ ⟨GK.n - 1, by have := GK.hn; lia⟩ := by
            rcases hsource with htop | hrest
            · rw [htop]
              change W.slope U < ⊤
              rw [W.slope_of_im_pos himU]
              exact WithTop.coe_lt_top _
            · rcases hrest with ⟨L, hLfree, hL0, hlastL⟩ |
                ⟨L, hPL, hL0, hLcharge, hlastL⟩
              · rw [hlastL]
                have hLheart : t.heart L := mem_heart_of_bounds sigma.slicing
                  hLfree.1 (sigma.slicing.leProp_mono C hbeta1.le L hLfree.2)
                have hsep : sigma.slicing.phiPlus C L hL0 <
                    sigma.slicing.phiMinus C U hlast :=
                  (sigma.slicing.phiPlus_le_of_leProp C hL0 hLfree.2).trans_lt
                    (sigma.slicing.phiMinus_gt_of_gtProp C hlast hUphase.1)
                have hWL : W.charge (L⟦(1 : ℤ)⟧) =
                    phaseTiltRotation beta (-(W0.charge L)) := by
                  simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation,
                    K₀.of_shift_one]
                have hWU : W.charge U = phaseTiltRotation beta (W0.charge U) := rfl
                exact phaseTilt_slope_unshifted_lt_shifted_of_phase_separated
                  sigma W hLheart hUheart
                    (P.free_shift_mem_tilt_heart hLfree) hUtilt hWL hWU
                    hL0 hlast hsep
                    ((sigma.slicing.phiPlus_le_of_leProp C hL0 hLfree.2).trans_lt
                      hbeta1) hUchargeOld
              · rw [hlastL]
                have hLheart : t.heart L := by
                  have hp : sigma.slicing.phiMinus C Gobj hG0 ∈ Set.Ioc beta 1 :=
                    ⟨sigma.slicing.phiMinus_gt_of_gtProp C hG0 hGtors.1,
                      (sigma.slicing.phiMinus_le_phiPlus C Gobj hG0).trans
                        (sigma.slicing.phiPlus_le_of_leProp C hG0 hGtors.2)⟩
                  exact mem_heart_of_bounds sigma.slicing
                    (sigma.slicing.gtProp_of_semistable C hPL
                      (hbeta0.trans hp.1))
                    (sigma.slicing.leProp_of_semistable C hPL hp.2)
                have hsep : sigma.slicing.phiPlus C U hlast <
                    sigma.slicing.phiMinus C L hL0 := by
                  have hUplus :=
                    (sigma.slicing.phiPlus_eq_phiMinus_of_semistable C
                      (FX.semistable jLast) hlast).1
                  have hLminus :=
                    (sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hPL hL0).2
                  calc
                    sigma.slicing.phiPlus C U hlast = FX.φ jLast := hUplus
                    _ < sigma.slicing.phiMinus C Gobj hG0 := by
                      exact sigma.slicing.phiMinus_gt_of_gtProp C hG0 <|
                        CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
                          C sigma.slicing FX
                          (FX.n - 1) (by lia) (by lia) (FX.φ jLast)
                            (fun a => FX.hφ (Fin.mk_lt_mk.mpr (by
                              have := a.isLt; lia)))
                    _ = sigma.slicing.phiMinus C L hL0 := hLminus.symm
                have hWU : W.charge U = phaseTiltRotation beta (W0.charge U) := rfl
                have hWL : W.charge L = phaseTiltRotation beta (W0.charge L) := rfl
                exact phaseTilt_slope_lt_of_phase_separated sigma W hUheart hLheart
                  hUtilt (P.tors_mem_tilt_heart (by
                    exact ⟨sigma.slicing.gtProp_of_semistable C hPL
                      (sigma.slicing.phiMinus_gt_of_gtProp C hG0 hGtors.1),
                      sigma.slicing.leProp_of_semistable C hPL
                        ((sigma.slicing.phiMinus_le_phiPlus C Gobj hG0).trans
                          (sigma.slicing.phiPlus_le_of_leProp C hG0 hGtors.2))⟩))
                  hWU hWL hlast hL0 hsep (by
                    calc
                      sigma.slicing.phiPlus C U hlast = FX.φ jLast := by
                        simpa [U, CategoryTheory.Triangulated.PostnikovTower.factor] using
                          (sigma.slicing.phiPlus_eq_phiMinus_of_semistable C
                            (FX.semistable jLast) hlast).1
                      _ < 1 := hUphiLt) hLcharge
          letI : Mono kH := hshort.mono_f
          let eU : cokernel kH ≅ UH :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel kH)
              hshort.gIsCokernel
          obtain ⟨GZ, hGZ⟩ := W.append_hn_filtration_of_mono
            kH GK eU hUH0 hUss hslope
          refine ⟨GZ, Or.inr (Or.inr ⟨U, ?_, hlast, hUchargeOld, ?_⟩)⟩
          · rw [sigma.slicing.phiMinus_eq C X hX0 FX hnFX hlast]
            exact FX.semistable jLast
          · rw [hGZ]

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition
