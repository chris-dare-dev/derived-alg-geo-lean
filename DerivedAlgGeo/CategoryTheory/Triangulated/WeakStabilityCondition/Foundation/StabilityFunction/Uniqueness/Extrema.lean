/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Uniqueness.SubobjectLattice

/-!
# The extremal phases of an HN filtration

This file owns the identification of the first chain step as the maximal
semistable subobject of maximal phase, and the resulting formulas `phiPlus_eq`
and `phiMinus_eq` for the extremal phases.  These are the facts that pin an HN
filtration down at both ends.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

/-- A semistable object of phase above an HN factor has no morphisms to that
factor. -/
theorem hom_eq_zero_to_factor {Z : StabilityFunction A} {E B : A}
    (F : AbelianHNFiltration Z E) (hB : Z.IsSemistable B)
    (j : Fin F.n) (hphase : F.phase j < Z.phase B)
    (f : B ⟶ cokernel (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) : f = 0 :=
  Z.hom_eq_zero_of_semistable_phase_gt hB (F.factor_semistable j)
    (F.factor_phase j ▸ hphase) f

/-- A semistable subobject whose phase is above every factor from index `k`
onward lies in the `k`-th term of an HN filtration. -/
theorem le_chain_of_semistable_phase_gt {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) {k : ℕ} (hk : k ≤ F.n)
    (hphase : ∀ j : Fin F.n, k ≤ j.val →
      F.phase j < Z.phase (B : A)) :
    B ≤ F.chain ⟨k, by lia⟩ := by
  suffices descend : ∀ d m (hm : m < F.n + 1), F.n - m = d → k ≤ m →
      B ≤ F.chain ⟨m, hm⟩ from
    descend (F.n - k) k (by lia) rfl le_rfl
  intro d
  induction d with
  | zero =>
      intro m hm hd _
      have hmn : m = F.n := by lia
      subst hmn
      rw [F.chain_top]
      exact le_top
  | succ d ih =>
      intro m hm hd hkm
      have hnext : B ≤ F.chain ⟨m + 1, by lia⟩ :=
        ih (m + 1) (by lia) (by lia) (by lia)
      let j : Fin F.n := ⟨m, by lia⟩
      have hsucc : (j.succ : Fin (F.n + 1)) = ⟨m + 1, by lia⟩ :=
        Fin.ext (by simp [j])
      have hBnext : B ≤ F.chain j.succ := hsucc ▸ hnext
      have hzero : Subobject.ofLE B (F.chain j.succ) hBnext ≫
          cokernel.π (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) = 0 :=
        F.hom_eq_zero_to_factor hB j (hphase j (by simp [j]; lia)) _
      exact le_of_ofLE_comp_cokernel_zero hBnext
        (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hzero

/-- A semistable subobject whose phase is above the highest HN phase is zero. -/
theorem eq_bot_of_semistable_phase_gt_phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : F.phiPlus < Z.phase (B : A)) : B = ⊥ := by
  apply le_bot_iff.mp
  rw [← F.chain_bot]
  apply F.le_chain_of_semistable_phase_gt hB (Nat.zero_le _)
  intro j _
  exact lt_of_le_of_lt
    (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hphase

/-- The first nonzero term in an HN filtration is not bottom. -/
theorem chain_one_ne_bot {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) :
    F.chain ⟨1, by have := F.nonempty; lia⟩ ≠ ⊥ := by
  have hn := F.nonempty
  intro heq
  have hlt : F.chain ⟨0, by lia⟩ < F.chain ⟨1, by lia⟩ :=
    F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
  rw [F.chain_bot, heq] at hlt
  exact lt_irrefl _ hlt

/-- The phase of the first nonzero term is the highest HN phase. -/
theorem phase_chain_one {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) :
    Z.phase (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) = F.phiPlus := by
  have hn := F.nonempty
  change Z.phase (F.chain ⟨1, by lia⟩ : A) = F.phase ⟨0, F.nonempty⟩
  rw [← F.factor_phase ⟨0, F.nonempty⟩]
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  exact ((Z.phase_cokernel_ofLE_congr hzero rfl).trans
    (Z.phase_eq_of_iso
      (StabilityFunction.subobjectCokernelBotIso
        (F.chain ⟨1, by lia⟩) bot_le))).symm

/-- The first nonzero term in an HN filtration is semistable. -/
theorem chain_one_isSemistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) :
    Z.IsSemistable (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) := by
  have hn := F.nonempty
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have hfactor : Z.IsSemistable
      (cokernel (Subobject.ofLE (F.chain
        (⟨0, F.nonempty⟩ : Fin F.n).castSucc)
        (F.chain (⟨0, F.nonempty⟩ : Fin F.n).succ)
        (le_of_lt (F.chain_strictMono
          (⟨0, F.nonempty⟩ : Fin F.n).castSucc_lt_succ)))) :=
    F.factor_semistable ⟨0, F.nonempty⟩
  have hnormalized : Z.IsSemistable
      (cokernel (Subobject.ofLE (⊥ : Subobject E)
        (F.chain ⟨1, by lia⟩) bot_le)) :=
    Z.isSemistable_cokernel_ofLE_congr hzero.symm rfl hfactor
  exact Z.isSemistable_of_iso
    (StabilityFunction.subobjectCokernelBotIso
      (F.chain ⟨1, by lia⟩) bot_le) hnormalized

/-- The highest phase is intrinsic: any two owner HN filtrations of the same
object have the same first phase. -/
theorem phiPlus_eq {Z : StabilityFunction A} {E : A}
    (F G : AbelianHNFiltration Z E) : F.phiPlus = G.phiPlus := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hGF
    have hbot := G.eq_bot_of_semistable_phase_gt_phiPlus
      F.chain_one_isSemistable (F.phase_chain_one ▸ hGF)
    exact F.chain_one_ne_bot hbot
  · apply le_of_not_gt
    intro hFG
    have hbot := F.eq_bot_of_semistable_phase_gt_phiPlus
      G.chain_one_isSemistable (G.phase_chain_one ▸ hFG)
    exact G.chain_one_ne_bot hbot

/-- The first nonzero term is intrinsic: any two owner HN filtrations of the
same object have the same maximally destabilizing subobject. -/
theorem chain_one_eq {Z : StabilityFunction A} {E : A}
    (F G : AbelianHNFiltration Z E) :
    F.chain ⟨1, by have := F.nonempty; lia⟩ =
      G.chain ⟨1, by have := G.nonempty; lia⟩ := by
  apply le_antisymm
  · apply G.le_chain_of_semistable_phase_gt F.chain_one_isSemistable G.nonempty
    intro j hj
    calc
      G.phase j < G.phiPlus :=
        G.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
      _ = F.phiPlus := (F.phiPlus_eq G).symm
      _ = Z.phase (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) :=
        F.phase_chain_one.symm
  · apply F.le_chain_of_semistable_phase_gt G.chain_one_isSemistable F.nonempty
    intro j hj
    calc
      F.phase j < F.phiPlus :=
        F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
      _ = G.phiPlus := F.phiPlus_eq G
      _ = Z.phase (G.chain ⟨1, by have := G.nonempty; lia⟩ : A) :=
        G.phase_chain_one.symm

/-- No nonzero semistable subobject has phase above the first HN phase. -/
theorem semistable_phase_le_phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) : Z.phase (B : A) ≤ F.phiPlus := by
  apply le_of_not_gt
  intro hphase
  have hbot := F.eq_bot_of_semistable_phase_gt_phiPlus hB hphase
  exact hB.1 ((StabilityFunction.subobject_isZero_iff_eq_bot B).2 hbot)

/-- A semistable subobject at the highest HN phase is contained in the
intrinsic first HN term. -/
theorem le_chain_one_of_semistable_phase_eq_phiPlus
    {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = F.phiPlus) :
    B ≤ F.chain ⟨1, by have := F.nonempty; lia⟩ := by
  apply F.le_chain_of_semistable_phase_gt hB F.nonempty
  intro j hj
  calc
    F.phase j < F.phiPlus :=
      F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
    _ = Z.phase (B : A) := hphase.symm

/-- The first HN term contains every semistable subobject having the highest
HN phase. -/
theorem chain_one_maximal_semistable_phase {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = F.phiPlus) :
    B ≤ F.chain ⟨1, by have := F.nonempty; lia⟩ :=
  F.le_chain_one_of_semistable_phase_eq_phiPlus hB hphase

/-- Every morphism from an HN-filtered object to a semistable object whose
phase is below the lowest HN phase is zero. -/
theorem hom_eq_zero_to_semistable_of_phase_lt_phiMinus
    {Z : StabilityFunction A} {E B : A} (F : AbelianHNFiltration Z E)
    (hB : Z.IsSemistable B) (hphase : Z.phase B < F.phiMinus)
    (f : E ⟶ B) : f = 0 := by
  have hrestrict : ∀ m : ℕ, (hm : m ≤ F.n) →
      (F.chain ⟨m, by lia⟩).arrow ≫ f = 0 := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [F.chain_bot]
        simp
    | succ m ih =>
        intro hm
        let j : Fin F.n := ⟨m, by lia⟩
        have hprevious : (F.chain j.castSucc).arrow ≫ f = 0 := by
          change (F.chain ⟨m, by lia⟩).arrow ≫ f = 0
          exact ih (by lia)
        have hcomp : Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
              (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) ≫
            ((F.chain j.succ).arrow ≫ f) = 0 := by
          calc
            Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
                  (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) ≫
                ((F.chain j.succ).arrow ≫ f) =
                (F.chain j.castSucc).arrow ≫ f := by
              rw [← Category.assoc, Subobject.ofLE_arrow]
            _ = 0 := hprevious
        let descended := cokernel.desc
          (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))
          ((F.chain j.succ).arrow ≫ f) hcomp
        have hfactor_phase : Z.phase B <
            Z.phase (cokernel (Subobject.ofLE (F.chain j.castSucc)
              (F.chain j.succ)
              (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) := by
          rw [F.factor_phase j]
          exact lt_of_lt_of_le hphase (F.phase_mem_range j).1
        have hdescended : descended = 0 :=
          Z.hom_eq_zero_of_semistable_phase_gt (F.factor_semistable j) hB
            hfactor_phase descended
        change (F.chain j.succ).arrow ≫ f = 0
        calc
          (F.chain j.succ).arrow ≫ f =
              cokernel.π (Subobject.ofLE (F.chain j.castSucc)
                (F.chain j.succ)
                (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) ≫
                descended := (cokernel.π_desc _ _ _).symm
          _ = 0 := by rw [hdescended, comp_zero]
  have htop : (⊤ : Subobject E).arrow ≫ f = 0 := by
    rw [← F.chain_top]
    exact hrestrict F.n le_rfl
  apply (cancel_epi (⊤ : Subobject E).arrow).mp
  simpa using htop

/-- The lowest phase is intrinsic: any two owner HN filtrations of the same
object have the same last phase. -/
theorem phiMinus_eq {Z : StabilityFunction A} {E : A}
    (F G : AbelianHNFiltration Z E) : F.phiMinus = G.phiMinus := by
  have no_strict_order : ∀ (H K : AbelianHNFiltration Z E),
      ¬H.phiMinus < K.phiMinus := by
    intro H K hHK
    have hn := H.nonempty
    let last : Fin H.n := ⟨H.n - 1, by have := H.nonempty; lia⟩
    have hlast : H.chain last.succ = ⊤ := by
      have hindex : last.succ = ⟨H.n, by lia⟩ :=
        Fin.ext (by simp [last]; lia)
      rw [hindex, H.chain_top]
    haveI : IsIso (H.chain last.succ).arrow := by
      rw [hlast]
      infer_instance
    let q : E ⟶ cokernel (Subobject.ofLE (H.chain last.castSucc)
        (H.chain last.succ)
        (le_of_lt (H.chain_strictMono last.castSucc_lt_succ))) :=
      inv (H.chain last.succ).arrow ≫
        cokernel.π (Subobject.ofLE (H.chain last.castSucc)
          (H.chain last.succ)
          (le_of_lt (H.chain_strictMono last.castSucc_lt_succ)))
    haveI : Epi q := inferInstance
    have hq : q = 0 := K.hom_eq_zero_to_semistable_of_phase_lt_phiMinus
      (H.factor_semistable last) (by
        rw [H.factor_phase last]
        exact hHK) q
    exact (H.factor_semistable last).1 (IsZero.of_epi_eq_zero q hq)
  exact le_antisymm (le_of_not_gt (no_strict_order G F))
    (le_of_not_gt (no_strict_order F G))

end AbelianHNFiltration

end CategoryTheory.Triangulated
