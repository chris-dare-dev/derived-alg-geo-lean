/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.PhaseGeometry

/-!
# Descent of HN filtrations along a monomorphism

This file owns the normalization lemmas of the owner-native uniqueness
argument: phase and semistability are invariant under propositional rewriting
of a successive quotient, a subobject of the domain of a monomorphism is
carried isomorphically to its image, and an HN filtration of a subobject can be
extended by the mono.  It closes with the semistable base case that produces an
HN filtration whose last phase is prescribed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- Phase equality after propositionally rewriting both subobjects in a
successive quotient. -/
theorem phase_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    Z.phase (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
      Z.phase (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst A₂
  subst B₂
  rfl

/-- Semistability is preserved after propositionally rewriting both
subobjects in a successive quotient. -/
theorem isSemistable_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : Z.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    Z.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst A₂
  subst B₂
  exact hs

namespace Subobject

omit [Abelian A] in
/-- Mapping a subobject along a monomorphism agrees with the subobject
represented by the composite arrow. -/
theorem map_eq_mk_mono {X Y : A} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) := by
      simpa using Subobject.map_mk S.arrow f

/-- A subobject and its image under a monomorphism have canonically
isomorphic underlying objects. -/
noncomputable def mapMonoIso {X Y : A} (f : X ⟶ Y) [Mono f]
    (S : Subobject X) : ((Subobject.map f).obj S : A) ≅ (S : A) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (map_eq_mk_mono f S)

omit [Abelian A] in
theorem ofLE_map_comp_mapMonoIso_hom {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (mapMonoIso f T).hom =
      (mapMonoIso f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [mapMonoIso, Category.assoc]

/-- Successive quotients are unchanged when a subobject chain is mapped
along a monomorphism. -/
noncomputable def cokernelMapMonoIso {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (mapMonoIso f S) (mapMonoIso f T)
    (by simpa [Category.assoc] using ofLE_map_comp_mapMonoIso_hom f h)

end Subobject

theorem phase_cokernel_mapMono_eq (Z : StabilityFunction A) {X Y : A}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.phase (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE S T h)) :=
  Z.phase_eq_of_iso (Subobject.cokernelMapMonoIso f h)

theorem isSemistable_cokernel_mapMono_iff (Z : StabilityFunction A)
    {X Y : A} (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      Z.IsSemistable (cokernel (Subobject.ofLE S T h)) := by
  constructor
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso f h)
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso f h).symm

/-- Append a lower-phase semistable quotient to an owner abelian HN
filtration along a monomorphism. -/
theorem append_hn_filtration_of_mono (Z : StabilityFunction A) {X Y B : A}
    (i : X ⟶ Y) [Mono i] (F : AbelianHNFiltration Z X)
    (eB : cokernel i ≅ B) (hB : Z.IsSemistable B)
    (hlast : Z.phase B < F.phase ⟨F.n - 1, by have := F.nonempty; omega⟩) :
    ∃ G : AbelianHNFiltration Z Y,
      G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ = Z.phase B := by
  let K : Subobject Y := Subobject.mk i
  let eK : cokernel K.arrow ≅ B := by
    let eKi : cokernel K.arrow ≅ cokernel i := by
      refine cokernel.mapIso (f := K.arrow) (f' := i)
        (Subobject.underlyingIso i) (Iso.refl _) ?_
      calc
        K.arrow ≫ (Iso.refl Y).hom = K.arrow := by simp
        _ = (Subobject.underlyingIso i).hom ≫ i := by
          exact (Subobject.underlyingIso_hom_comp_eq_mk i).symm
    exact eKi ≪≫ eB
  have hK_ne_top : K ≠ ⊤ := by
    intro hK
    have hmk : Subobject.mk i = ⊤ := by simpa [K] using hK
    haveI : IsIso i := (Subobject.isIso_iff_mk_eq_top i).2 hmk
    exact hB.1 ((isZero_cokernel_of_epi i).of_iso eB.symm)
  have hK_lt_top : K < ⊤ := lt_of_le_of_ne le_top hK_ne_top
  let newChain : Fin (F.n + 2) → Subobject Y := fun j ↦
    if h : (j : ℕ) ≤ F.n then
      (Subobject.map i).obj (F.chain ⟨j, by omega⟩)
    else ⊤
  have hNewBot : newChain ⟨0, by omega⟩ = ⊥ := by
    change (Subobject.map i).obj (F.chain ⟨0, by omega⟩) = ⊥
    rw [F.chain_bot]
    exact Subobject.map_bot i
  have hNewK : newChain ⟨F.n, by omega⟩ = K := by
    simp [newChain, K, Subobject.map_top, F.chain_top]
  have hNewTop : newChain ⟨F.n + 1, by omega⟩ = ⊤ := by
    simp [newChain]
  have hNewMono : StrictMono newChain := by
    apply Fin.strictMono_iff_lt_succ.mpr
    rintro ⟨j, hj⟩
    change newChain ⟨j, by omega⟩ < newChain ⟨j + 1, by omega⟩
    by_cases hjn : j = F.n
    · subst hjn
      rw [hNewK, hNewTop]
      exact hK_lt_top
    · have hjle : j + 1 ≤ F.n := by omega
      simp [newChain, show j ≤ F.n by omega, hjle]
      apply (Subobject.map i).monotone.strictMono_of_injective
        (Subobject.map_obj_injective i)
      exact F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
  let phase : Fin (F.n + 1) → ℝ := fun j ↦
    if h : (j : ℕ) < F.n then F.phase ⟨j, h⟩ else Z.phase B
  refine ⟨{
    n := F.n + 1
    nonempty := Nat.succ_pos _
    chain := newChain
    chain_strictMono := hNewMono
    chain_bot := hNewBot
    chain_top := hNewTop
    phase := phase
    phase_strictAnti := ?_
    factor_phase := ?_
    factor_semistable := ?_
  }, ?_⟩
  · intro a b hab
    dsimp [phase]
    by_cases hb : (b : ℕ) < F.n
    · have ha : (a : ℕ) < F.n := (Fin.mk_lt_mk.mp hab).trans hb
      simp [ha, hb]
      exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hab))
    · have ha : (a : ℕ) < F.n := by omega
      have hlast_le : F.phase ⟨F.n - 1, by omega⟩ ≤ F.phase ⟨a, ha⟩ :=
        F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (by omega))
      simp [ha, hb]
      exact hlast.trans_le hlast_le
  · intro j
    by_cases hj : (j : ℕ) < F.n
    · let j' : Fin F.n := ⟨j, hj⟩
      have hcast : newChain j.castSucc =
          (Subobject.map i).obj (F.chain j'.castSucc) := by
        simp [newChain, j', show (j : ℕ) ≤ F.n by omega]
      have hsucc : newChain j.succ =
          (Subobject.map i).obj (F.chain j'.succ) := by
        simp [newChain, j', show (j : ℕ) + 1 ≤ F.n by omega]
      have hp := (Z.phase_cokernel_mapMono_eq i
        (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).trans
        (F.factor_phase j')
      exact ((Z.phase_cokernel_ofLE_congr hcast hsucc).trans hp).trans (by
        simp [phase, hj, j'])
    · have hj_eq : (j : ℕ) = F.n := by omega
      have hcast : j.castSucc = ⟨F.n, by omega⟩ := Fin.ext hj_eq
      have hsucc : j.succ = ⟨F.n + 1, by omega⟩ := Fin.ext (by simp [hj_eq])
      have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
      have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
      have htarget : Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
          Z.phase B := by
        calc
          Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
              Z.phase (cokernel K.arrow) :=
            Z.phase_eq_of_iso
              ((cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫
                cokernelCompIsIso _ _).symm)
          _ = Z.phase B := Z.phase_eq_of_iso eK
      exact ((Z.phase_cokernel_ofLE_congr hcast_obj hsucc_obj).trans htarget).trans (by
        simp [phase, hj])
  · intro j
    by_cases hj : (j : ℕ) < F.n
    · let j' : Fin F.n := ⟨j, hj⟩
      have hcast : newChain j.castSucc =
          (Subobject.map i).obj (F.chain j'.castSucc) := by
        simp [newChain, j', show (j : ℕ) ≤ F.n by omega]
      have hsucc : newChain j.succ =
          (Subobject.map i).obj (F.chain j'.succ) := by
        simp [newChain, j', show (j : ℕ) + 1 ≤ F.n by omega]
      have hs := (Z.isSemistable_cokernel_mapMono_iff i
        (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).2
        (F.factor_semistable j')
      exact Z.isSemistable_cokernel_ofLE_congr hcast hsucc hs
    · have hj_eq : (j : ℕ) = F.n := by omega
      have hcast : j.castSucc = ⟨F.n, by omega⟩ := Fin.ext hj_eq
      have hsucc : j.succ = ⟨F.n + 1, by omega⟩ := Fin.ext (by simp [hj_eq])
      have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
      have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
      let eTop : B ≅ cokernel (Subobject.ofLE K ⊤ le_top) :=
        eK.symm ≪≫
          (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
      exact Z.isSemistable_cokernel_ofLE_congr hcast_obj hsucc_obj
        (Z.isSemistable_of_iso eTop hB)
  · simp [phase]

/-- The one-factor owner HN filtration of a semistable abelian object. -/
theorem exists_hn_with_last_phase_of_semistable (Z : StabilityFunction A)
    {E : A} (hE : Z.IsSemistable E) :
    ∃ F : AbelianHNFiltration Z E,
      F.phase ⟨F.n - 1, by have := F.nonempty; omega⟩ = Z.phase E := by
  refine ⟨{
    n := 1
    nonempty := Nat.one_pos
    chain := fun i ↦ if i = 0 then ⊥ else ⊤
    chain_strictMono := ?_
    chain_bot := by simp
    chain_top := by simp
    phase := fun _ ↦ Z.phase E
    phase_strictAnti := fun a b hab ↦ (by omega)
    factor_phase := ?_
    factor_semistable := ?_
  }, by simp⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.lt_def] at hij
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst hi0
    subst hj1
    simp only [Fin.zero_eta, Fin.mk_one, one_ne_zero, if_false, if_true]
    exact lt_of_le_of_ne bot_le
      (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hE.1))
  · intro ⟨j, hj⟩
    have hj0 : j = 0 := by omega
    subst hj0
    change Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ _)) = Z.phase E
    rw [Z.phase_eq_of_iso (StabilityFunction.subobjectCokernelBotIso ⊤ bot_le)]
    exact Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow)
  · intro ⟨j, hj⟩
    have hj0 : j = 0 := by omega
    subst hj0
    change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
    exact Z.isSemistable_of_iso
      ((asIso (⊤ : Subobject E).arrow).symm ≪≫
        (StabilityFunction.subobjectCokernelBotIso ⊤ bot_le).symm) hE

end StabilityFunction

end CategoryTheory.Triangulated
