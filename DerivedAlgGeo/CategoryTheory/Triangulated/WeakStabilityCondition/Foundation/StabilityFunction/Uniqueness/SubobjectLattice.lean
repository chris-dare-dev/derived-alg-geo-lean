/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Uniqueness.MonoDescent

/-!
# The subobject lattice of an HN filtration

This file owns the lattice bookkeeping of the uniqueness argument: an HN
filtration has one factor exactly when its object is semistable, pullback along
a cokernel projection is compatible with the chain and with charge, and the
canonical comparison `cokernelPullbackIso` identifies the cokernel of a
pullback with the pullback of a cokernel.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

/-- A semistable object can only have a one-factor HN filtration. -/
theorem n_eq_one_of_semistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hE : Z.IsSemistable E) : F.n = 1 := by
  by_contra hn
  have hn_ge : 1 < F.n := by
    have := F.nonempty
    lia
  have hchain1_ne_bot : F.chain ⟨1, by lia⟩ ≠ ⊥ := by
    intro heq
    have h01 : F.chain ⟨0, by lia⟩ < F.chain ⟨1, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    rw [F.chain_bot, heq] at h01
    exact lt_irrefl _ h01
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have hfirst :
      Z.phase (F.chain ⟨1, by lia⟩ : A) = F.phase ⟨0, F.nonempty⟩ := by
    rw [← F.factor_phase ⟨0, F.nonempty⟩]
    exact ((Z.phase_cokernel_ofLE_congr hzero rfl).trans
      (Z.phase_eq_of_iso
        (StabilityFunction.subobjectCokernelBotIso
          (F.chain ⟨1, by lia⟩) bot_le))).symm
  have hfirst_le : F.phase ⟨0, F.nonempty⟩ ≤ Z.phase E := by
    rw [← hfirst]
    exact hE.2 _
      (StabilityFunction.subobject_not_isZero_of_ne_bot hchain1_ne_bot)
  let last : Fin F.n := ⟨F.n - 1, by lia⟩
  have hpenultimate_ne_top : F.chain ⟨F.n - 1, by lia⟩ ≠ ⊤ := by
    intro heq
    have hlt : F.chain ⟨F.n - 1, by lia⟩ < F.chain ⟨F.n, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    rw [heq, F.chain_top] at hlt
    exact lt_irrefl _ hlt
  have hlast_top : F.chain last.succ = ⊤ := by
    have hindex : last.succ = ⟨F.n, by lia⟩ := Fin.ext (by simp [last]; lia)
    rw [hindex, F.chain_top]
  have hE_le_last : Z.phase E ≤ F.phase last := by
    have hquot := Z.phase_le_of_epi
      (cokernel.π (F.chain ⟨F.n - 1, by lia⟩).arrow) hE
      (StabilityFunction.cokernel_not_isZero_of_ne_top hpenultimate_ne_top)
    suffices Z.phase (cokernel (F.chain ⟨F.n - 1, by lia⟩).arrow) =
        F.phase last by linarith
    let S := F.chain ⟨F.n - 1, by lia⟩
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    calc
      Z.phase (cokernel S.arrow) =
          Z.phase (cokernel (Subobject.ofLE S ⊤ le_top)) :=
        Z.phase_eq_of_iso
          (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫
            cokernelCompIsIso _ _)
      _ = Z.phase (cokernel (Subobject.ofLE
          (F.chain last.castSucc) (F.chain last.succ)
          (le_of_lt (F.chain_strictMono last.castSucc_lt_succ)))) :=
        Z.phase_cokernel_ofLE_congr rfl hlast_top.symm
      _ = F.phase last := F.factor_phase last
  have hlast_lt : F.phase last < F.phase ⟨0, F.nonempty⟩ :=
    F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
  linarith

/-- A one-factor HN filtration identifies its ambient object as semistable. -/
theorem isSemistable_of_n_eq_one {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn : F.n = 1) : Z.IsSemistable E := by
  have hfactor := F.factor_semistable ⟨0, F.nonempty⟩
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have htop : F.chain (⟨0, F.nonempty⟩ : Fin F.n).succ = ⊤ := by
    have hindex : (⟨0, F.nonempty⟩ : Fin F.n).succ = ⟨F.n, by lia⟩ :=
      Fin.ext (by simp; lia)
    rw [hindex, F.chain_top]
  have hnormalized :
      Z.IsSemistable (cokernel (Subobject.ofLE (⊥ : Subobject E) ⊤ bot_le)) :=
    Z.isSemistable_cokernel_ofLE_congr hzero.symm htop.symm hfactor
  exact Z.isSemistable_of_iso
    (StabilityFunction.subobjectCokernelBotIso ⊤ bot_le ≪≫
      asIso (⊤ : Subobject E).arrow)
    hnormalized

/-- A one-factor HN filtration is equivalent to semistability of its ambient
object. -/
theorem n_eq_one_iff_isSemistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) : F.n = 1 ↔ Z.IsSemistable E :=
  ⟨F.isSemistable_of_n_eq_one, F.n_eq_one_of_semistable⟩

/-- A non-semistable object has at least two HN factors. -/
theorem two_le_n_of_not_isSemistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hE : ¬Z.IsSemistable E) : 2 ≤ F.n := by
  by_contra hlt
  apply hE
  apply F.isSemistable_of_n_eq_one
  have := F.nonempty
  lia

/-- If a subobject maps trivially to the quotient by another subobject, it is
contained in that subobject. -/
theorem le_of_arrow_comp_cokernel_zero {E : A} {B M : Subobject E}
    (h : B.arrow ≫ cokernel.π M.arrow = 0) : B ≤ M := by
  have hkernel : kernelSubobject (cokernel.π M.arrow) = M := by
    simpa [imageSubobject_mono, Subobject.mk_arrow] using
      ((ShortComplex.mk M.arrow (cokernel.π M.arrow)
        (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
        (ShortComplex.exact_cokernel M.arrow)).symm
  rw [← hkernel]
  exact Subobject.le_of_comm
    (factorThruKernelSubobject _ B.arrow h)
    (factorThruKernelSubobject_comp_arrow _ _ _)

/-- The relative form of `le_of_arrow_comp_cokernel_zero`: a subobject of `S`
that maps trivially to the quotient `S / M` is contained in `M`. -/
theorem le_of_ofLE_comp_cokernel_zero {E : A} {B M S : Subobject E}
    (hBS : B ≤ S) (hMS : M ≤ S)
    (h : Subobject.ofLE B S hBS ≫
      cokernel.π (Subobject.ofLE M S hMS) = 0) : B ≤ M := by
  have hse : (ShortComplex.mk (Subobject.ofLE M S hMS)
      (cokernel.π (Subobject.ofLE M S hMS))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
      inferInstance inferInstance
  set g := hse.fIsKernel.lift (KernelFork.ofι (Subobject.ofLE B S hBS) h)
  have hg : g ≫ Subobject.ofLE M S hMS = Subobject.ofLE B S hBS :=
    hse.fIsKernel.fac (KernelFork.ofι (Subobject.ofLE B S hBS) h)
      WalkingParallelPair.zero
  apply Subobject.le_of_comm g
  calc
    g ≫ M.arrow = g ≫ (Subobject.ofLE M S hMS ≫ S.arrow) := by
      congr 1
      exact (Subobject.ofLE_arrow hMS).symm
    _ = (g ≫ Subobject.ofLE M S hMS) ≫ S.arrow :=
      (Category.assoc _ _ _).symm
    _ = Subobject.ofLE B S hBS ≫ S.arrow := by congr 1
    _ = B.arrow := Subobject.ofLE_arrow hBS

/-- Pulling bottom back along the quotient by a subobject recovers the
subobject. -/
theorem pullback_cokernel_bot_eq {E : A} (M : Subobject E) :
    (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ = M := by
  apply le_antisymm
  · let P := (Subobject.pullback (cokernel.π M.arrow)).obj ⊥
    have hP : P.arrow ≫ cokernel.π M.arrow = 0 := by
      have h := (Subobject.isPullback (cokernel.π M.arrow)
        (⊥ : Subobject (cokernel M.arrow))).w
      simp only [Subobject.bot_arrow, comp_zero] at h
      exact h.symm
    exact le_of_arrow_comp_cokernel_zero hP
  · exact Subobject.le_of_comm
      ((Subobject.isPullback (cokernel.π M.arrow) (⊥ : Subobject _)).isLimit.lift
        (PullbackCone.mk 0 M.arrow (by simp [cokernel.condition])))
      ((Subobject.isPullback (cokernel.π M.arrow) (⊥ : Subobject _)).isLimit.fac _
        WalkingCospan.right)

/-- Quotienting by a nonzero subobject strictly decreases a finite subobject
lattice. -/
theorem card_subobject_cokernel_lt {E : A} {M : Subobject E}
    (hM : M ≠ ⊥) [Finite (Subobject E)] :
    Nat.card (Subobject (cokernel M.arrow)) < Nat.card (Subobject E) := by
  haveI := Fintype.ofFinite (Subobject E)
  haveI : Finite (Subobject (cokernel M.arrow)) :=
    Finite.of_injective _ (StabilityFunction.pullback_obj_injective_of_epi
      (cokernel.π M.arrow))
  haveI := Fintype.ofFinite (Subobject (cokernel M.arrow))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem
    (Subobject.pullback (cokernel.π M.arrow)).obj
    (StabilityFunction.pullback_obj_injective_of_epi _)
    (by
      simp only [Set.mem_range, not_exists]
      intro B hB
      apply hM
      apply le_bot_iff.mp
      calc
        M = (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ :=
          (pullback_cokernel_bot_eq M).symm
        _ ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
          Functor.monotone _ bot_le
        _ = ⊥ := hB)

/-- Every subobject of a quotient pulls back to a subobject containing the
kernel of the quotient map. -/
theorem le_pullback_cokernel {E : A} (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
  (pullback_cokernel_bot_eq M).symm.le.trans
    (Functor.monotone _ bot_le)

/-- The kernel inclusion followed by the restricted quotient map is zero. -/
theorem ofLE_pullbackπ_cokernel_eq_zero {E : A} (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
      Subobject.pullbackπ (cokernel.π M.arrow) B = 0 := by
  apply (cancel_mono B.arrow).mp
  simp only [zero_comp, Category.assoc]
  have hw := (Subobject.isPullback (cokernel.π M.arrow) B).w
  calc
    Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
        (Subobject.pullbackπ (cokernel.π M.arrow) B ≫ B.arrow) =
        Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
          (((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow ≫
            cokernel.π M.arrow) := by rw [hw]
    _ = (Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
          ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow) ≫
            cokernel.π M.arrow := by rw [Category.assoc]
    _ = M.arrow ≫ cokernel.π M.arrow := by rw [Subobject.ofLE_arrow]
    _ = 0 := cokernel.condition M.arrow

/-- Pulling a subobject of a quotient back gives a canonical short exact
sequence with the quotient kernel. -/
theorem shortExact_ofLE_pullbackπ_cokernel {E : A} (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    (ShortComplex.mk
      (Subobject.ofLE M _ (le_pullback_cokernel M B))
      (Subobject.pullbackπ (cokernel.π M.arrow) B)
      (ofLE_pullbackπ_cokernel_eq_zero M B)).ShortExact := by
  let p := cokernel.π M.arrow
  let pbB := (Subobject.pullback p).obj B
  let hle := le_pullback_cokernel M B
  let hcomp := ofLE_pullbackπ_cokernel_eq_zero M B
  have hquotient :
      (ShortComplex.mk M.arrow p (cokernel.condition M.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel M.arrow)
      inferInstance inferInstance
  have hkernel := hquotient.fIsKernel
  haveI : Epi (Subobject.pullbackπ p B) := by
    rw [← (Subobject.isPullback p B).isoPullback_hom_fst]
    infer_instance
  apply ShortComplex.ShortExact.mk' _ inferInstance inferInstance
  apply ShortComplex.exact_of_f_is_kernel
  have hw := (Subobject.isPullback p B).w
  have key : ∀ {W : A} (g : W ⟶ (pbB : A)),
      g ≫ Subobject.pullbackπ p B = 0 → (g ≫ pbB.arrow) ≫ p = 0 := by
    intro W g hg
    calc
      (g ≫ pbB.arrow) ≫ p = g ≫ (pbB.arrow ≫ p) := by rw [Category.assoc]
      _ = g ≫ (Subobject.pullbackπ p B ≫ B.arrow) := by rw [hw]
      _ = (g ≫ Subobject.pullbackπ p B) ≫ B.arrow := by rw [← Category.assoc]
      _ = 0 := by rw [hg, zero_comp]
  exact KernelFork.IsLimit.ofι' (Subobject.ofLE M pbB hle) hcomp
    (fun g hg => ⟨hkernel.lift (KernelFork.ofι (g ≫ pbB.arrow) (key g hg)), by
      apply (cancel_mono pbB.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact hkernel.fac (KernelFork.ofι (g ≫ pbB.arrow) (key g hg))
        WalkingParallelPair.zero⟩)

/-- The charge of a pulled-back quotient subobject is the sum of the kernel
charge and the subobject charge. -/
theorem charge_pullback_eq_add (Z : StabilityFunction A) {E : A}
    (M : Subobject E) (B : Subobject (cokernel M.arrow)) :
    Z.charge (((Subobject.pullback (cokernel.π M.arrow)).obj B) : A) =
      Z.charge (M : A) + Z.charge (B : A) :=
  Z.additive _ (shortExact_ofLE_pullbackπ_cokernel M B)

/-- Pulling the image of a subobject containing the quotient kernel back along
the quotient projection recovers the original subobject. -/
theorem pullback_imageSubobject_eq (Z : StabilityFunction A) {E : A}
    {M S : Subobject E} (hMS : M ≤ S) :
    (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) = S := by
  let p := cokernel.π M.arrow
  let I := imageSubobject (S.arrow ≫ p)
  let pbI := (Subobject.pullback p).obj I
  change pbI = S
  have hle : S ≤ pbI := Subobject.le_of_comm
    ((Subobject.isPullback p I).isLimit.lift
      (PullbackCone.mk (factorThruImageSubobject (S.arrow ≫ p)) S.arrow
        (imageSubobject_arrow_comp (f := S.arrow ≫ p))))
    ((Subobject.isPullback p I).isLimit.fac _ WalkingCospan.right)
  have hpb := charge_pullback_eq_add Z M I
  have hS := Z.additive _
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE M S hMS))
      inferInstance inferInstance)
  have hI : Z.charge (I : A) =
      Z.charge (cokernel (Subobject.ofLE M S hMS)) := by
    have hses := Z.additive _
      (ShortComplex.ShortExact.mk'
        (ShortComplex.exact_cokernel (kernel.ι (S.arrow ≫ p)))
        inferInstance inferInstance)
    have hcondition : Subobject.ofLE M S hMS ≫ (S.arrow ≫ p) = 0 := by
      rw [← Category.assoc, Subobject.ofLE_arrow]
      exact cokernel.condition M.arrow
    have hkernelCondition :
        (kernel.ι (S.arrow ≫ p) ≫ S.arrow) ≫ cokernel.π M.arrow = 0 := by
      rw [Category.assoc]
      exact kernel.condition (S.arrow ≫ p)
    let k := kernel.lift (S.arrow ≫ p) (Subobject.ofLE M S hMS) hcondition
    let l := Abelian.monoLift M.arrow
      (kernel.ι (S.arrow ≫ p) ≫ S.arrow) hkernelCondition
    have hk : k ≫ kernel.ι (S.arrow ≫ p) = Subobject.ofLE M S hMS :=
      kernel.lift_ι _ _ _
    have hl : l ≫ M.arrow = kernel.ι (S.arrow ≫ p) ≫ S.arrow :=
      Abelian.monoLift_comp _ _ _
    have hkl : k ≫ l = 𝟙 _ := by
      apply (cancel_mono M.arrow).mp
      rw [Category.assoc, hl, ← Category.assoc, hk, Subobject.ofLE_arrow,
        Category.id_comp]
    have hlk : l ≫ k = 𝟙 _ := by
      apply (cancel_mono (kernel.ι (S.arrow ≫ p))).mp
      rw [Category.assoc, hk, Category.id_comp]
      apply (cancel_mono S.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow, hl]
    have hchargeKernel : Z.charge (M : A) = Z.charge (kernel (S.arrow ≫ p)) :=
      Z.charge_eq_of_iso ⟨k, l, hkl, hlk⟩
    have hchargeCoimage := Z.charge_eq_of_iso (Abelian.coimageIsoImage' (S.arrow ≫ p))
    have hchargeImage := Z.charge_eq_of_iso (imageSubobjectIso (S.arrow ≫ p))
    rw [← hchargeKernel] at hses
    exact (hchargeImage.trans hchargeCoimage.symm).trans
      (add_left_cancel (hses.symm.trans hS))
  have hcharge : Z.charge (pbI : A) = Z.charge (S : A) := by
    rw [hpb, hI]
    exact hS.symm
  rcases hle.eq_or_lt with heq | hlt
  · exact heq.symm
  · exfalso
    have hshort := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE S pbI hle))
      inferInstance inferInstance
    have hadd := Z.additive _ hshort
    have hcokernel :
        Z.charge (cokernel (Subobject.ofLE S pbI hle)) = 0 := by
      have h : Z.charge (S : A) + 0 = Z.charge (S : A) +
          Z.charge (cokernel (Subobject.ofLE S pbI hle)) := by
        rw [add_zero]
        exact hcharge.symm.trans hadd
      exact (add_left_cancel h).symm
    have hnonzero : ¬IsZero (cokernel (Subobject.ofLE S pbI hle)) := by
      intro hzero
      haveI : Epi (Subobject.ofLE S pbI hle) :=
        Preadditive.epi_of_isZero_cokernel _ hzero
      haveI : IsIso (Subobject.ofLE S pbI hle) := isIso_of_mono_of_epi _
      exact (ne_of_lt hlt) (Subobject.eq_of_comm (asIso (Subobject.ofLE S pbI hle))
        (Subobject.ofLE_arrow hle))
    exact semiClosedUpperHalfPlane_ne_zero
      (Z.nonzero_mem _ hnonzero) hcokernel

/-- Consecutive pulled-back quotient subobjects have the same charge as the
corresponding quotient factor. -/
theorem charge_cokernel_pullback_eq (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    Z.charge (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h))) =
      Z.charge (cokernel (Subobject.ofLE B₁ B₂ h)) := by
  let pbB₁ := (Subobject.pullback (cokernel.π M.arrow)).obj B₁
  let pbB₂ := (Subobject.pullback (cokernel.π M.arrow)).obj B₂
  let hpull : pbB₁ ≤ pbB₂ := Functor.monotone _ h
  have hshort₁ := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (Subobject.ofLE pbB₁ pbB₂ hpull))
    inferInstance inferInstance
  have hshort₂ := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (Subobject.ofLE B₁ B₂ h))
    inferInstance inferInstance
  have h₁ := Z.additive _ hshort₁
  have h₂ := Z.additive _ hshort₂
  have hB₁ := charge_pullback_eq_add Z M B₁
  have hB₂ := charge_pullback_eq_add Z M B₂
  linear_combination -h₁ + h₂ - hB₁ + hB₂

/-- Consecutive pulled-back quotient subobjects have the same phase as the
corresponding quotient factor. -/
theorem phase_cokernel_pullback_eq (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    Z.phase (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h))) =
      Z.phase (cokernel (Subobject.ofLE B₁ B₂ h)) := by
  simp only [StabilityFunction.phase, charge_cokernel_pullback_eq Z M h]

/-- Consecutive pulled-back quotient factors are canonically isomorphic. -/
noncomputable def cokernelPullbackIso (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ < B₂) :
    cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h.le)) ≅
      cokernel (Subobject.ofLE B₁ B₂ h.le) := by
  let p := cokernel.π M.arrow
  let pbB₁ := (Subobject.pullback p).obj B₁
  let pbB₂ := (Subobject.pullback p).obj B₂
  let hpull : pbB₁ ≤ pbB₂ := Functor.monotone _ h.le
  have hw₁ := (Subobject.isPullback p B₁).w
  have hw₂ := (Subobject.isPullback p B₂).w
  have hcomm : Subobject.ofLE pbB₁ pbB₂ hpull ≫
      Subobject.pullbackπ p B₂ =
      Subobject.pullbackπ p B₁ ≫ Subobject.ofLE B₁ B₂ h.le := by
    apply (cancel_mono B₂.arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow]
    calc
      Subobject.ofLE pbB₁ pbB₂ hpull ≫
          (Subobject.pullbackπ p B₂ ≫ B₂.arrow) =
          Subobject.ofLE pbB₁ pbB₂ hpull ≫ (pbB₂.arrow ≫ p) := by rw [hw₂]
      _ = (Subobject.ofLE pbB₁ pbB₂ hpull ≫ pbB₂.arrow) ≫ p := by
        rw [Category.assoc]
      _ = pbB₁.arrow ≫ p := by rw [Subobject.ofLE_arrow]
      _ = Subobject.pullbackπ p B₁ ≫ B₁.arrow := hw₁.symm
  have hfactor : Subobject.ofLE pbB₁ pbB₂ hpull ≫
      (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h.le)) = 0 := by
    rw [← Category.assoc, hcomm, Category.assoc, cokernel.condition, comp_zero]
  let f := cokernel.desc (Subobject.ofLE pbB₁ pbB₂ hpull)
    (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h.le)) hfactor
  haveI : Epi (Subobject.pullbackπ p B₂) := by
    rw [← (Subobject.isPullback p B₂).isoPullback_hom_fst]
    infer_instance
  haveI : Epi f := epi_of_epi_fac (cokernel.π_desc _ _ _)
  haveI : Mono f := by
    suffices hk : kernel.ι f = 0 from Preadditive.mono_of_kernel_zero hk
    have hshort := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_kernel f) inferInstance inferInstance
    have hadd := Z.additive _ hshort
    have hcharge : Z.charge (cokernel (Subobject.ofLE pbB₁ pbB₂ hpull)) =
        Z.charge (cokernel (Subobject.ofLE B₁ B₂ h.le)) :=
      charge_cokernel_pullback_eq Z M h.le
    rw [hcharge] at hadd
    have hkernelCharge : Z.charge (kernel f) = 0 :=
      add_eq_right.mp hadd.symm
    by_contra hk
    have hkernel : ¬IsZero (kernel f) := fun hzero =>
      hk (zero_of_source_iso_zero _ hzero.isoZero)
    exact semiClosedUpperHalfPlane_ne_zero
      (Z.nonzero_mem _ hkernel) hkernelCharge
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

end AbelianHNFiltration

end CategoryTheory.Triangulated
