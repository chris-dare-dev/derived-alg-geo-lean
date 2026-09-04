/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.Equivalence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Harder--Narasimhan filtrations for weak stability functions

This file supplies the heart-level HN package needed for the weak
heart--slicing correspondence of Lemma 14.4 in arXiv:1902.08184v4.

Weak HN filtrations are finite strict chains of subobjects in the abelian full
heart.  Their successive quotients are weak-semistable and their
`WithTop ℝ` slopes strictly decrease.  The value `⊤` incorporates the
zero-charge boundary at phase `1` without assigning an argument to zero.

The main construction reads the slicing HN filtration of a heart object as a
weak abelian HN filtration.  It follows the ordinary heart-equivalence proof in
`WeakStabilityCondition/Heart/Equivalence.lean`, with phase comparisons
replaced by the weak phase--slope bridge proved here.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open scoped ZeroObject

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Λ : Type*} [AddCommGroup Λ]
variable {v : K₀ C →+ Λ}

/-! ## The weak abelian HN package -/

section WeakAbelian

variable {t : TStructure C}

/-- The abelian structure on the full heart, used for weak-slope comparisons. -/
@[nolint defsWithUnderscore]
local instance : Abelian t.heart.FullSubcategory :=
  t.heartFullSubcategoryAbelian

/-- The weak slope of an object of the abelian full heart. -/
abbrev WeakStabilityFunction.heartSlope
    (W : WeakStabilityFunction t) (E : t.heart.FullSubcategory) : WithTop ℝ :=
  W.slope E.obj

/-- Weak semistability for an object of the abelian full heart. -/
abbrev WeakStabilityFunction.HeartSemistable
    (W : WeakStabilityFunction t) (E : t.heart.FullSubcategory) : Prop :=
  W.IsSemistable E.obj

/-- A Harder--Narasimhan filtration in the abelian full heart for a weak
stability function.  Successive slopes, rather than arguments, are stored so
that a zero-charge phase-`1` factor is represented honestly by `⊤`. -/
structure WeakAbelianHNFiltration (W : WeakStabilityFunction t)
    (E : t.heart.FullSubcategory) where
  /-- The number of semistable factors. -/
  n : ℕ
  /-- A nonzero object has at least one factor. -/
  hn : 0 < n
  /-- The chain `0 = E₀ < ... < Eₙ = E`. -/
  chain : Fin (n + 1) → Subobject E
  /-- The chain is strict. -/
  chain_strictMono : StrictMono chain
  /-- The first term is zero. -/
  chain_bot : chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥
  /-- The last term is the whole object. -/
  chain_top : chain ⟨n, n.lt_succ_iff.mpr le_rfl⟩ = ⊤
  /-- Slopes of successive quotients. -/
  μ : Fin n → WithTop ℝ
  /-- Successive slopes strictly decrease. -/
  μ_anti : StrictAnti μ
  /-- The stored slope is the slope of the corresponding quotient. -/
  factor_slope : ∀ j : Fin n,
    W.heartSlope
      (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
        (le_of_lt (chain_strictMono j.castSucc_lt_succ)))) = μ j
  /-- Each successive quotient is weak-semistable. -/
  factor_semistable : ∀ j : Fin n,
    W.HeartSemistable
      (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
        (le_of_lt (chain_strictMono j.castSucc_lt_succ))))

/-- A weak stability function has the HN property when every nonzero object
of its abelian full heart admits a weak abelian HN filtration. -/
def WeakStabilityFunction.HasHNProperty (W : WeakStabilityFunction t) : Prop :=
  ∀ E : t.heart.FullSubcategory, ¬IsZero E →
    Nonempty (WeakAbelianHNFiltration W E)

/-- The `j`-th successive quotient of a weak abelian HN filtration. -/
abbrev WeakAbelianHNFiltration.factor {W : WeakStabilityFunction t}
    {E : t.heart.FullSubcategory} (F : WeakAbelianHNFiltration W E)
    (j : Fin F.n) : t.heart.FullSubcategory :=
  cokernel (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
    (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))

/-- Every factor of a weak abelian HN filtration is nonzero in the full
heart. -/
theorem WeakAbelianHNFiltration.factor_not_isZero
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) (j : Fin F.n) :
    ¬IsZero (F.factor j) := by
  intro hzero
  let f := Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
    (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))
  haveI : Epi f := Preadditive.epi_of_isZero_cokernel f hzero
  haveI : IsIso f := isIso_of_mono_of_epi f
  have hle : F.chain j.succ ≤ F.chain j.castSucc := by
    refine Subobject.le_of_comm (inv f) ?_
    simp [f]
  exact (not_le_of_gt (F.chain_strictMono j.castSucc_lt_succ)) hle

/-- Every factor is also nonzero after forgetting from the full heart to the
ambient triangulated category. -/
theorem WeakAbelianHNFiltration.factor_obj_not_isZero
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) (j : Fin F.n) :
    ¬IsZero (F.factor j).obj := fun hzero ↦
  F.factor_not_isZero j <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero

end WeakAbelian

/-! ## Singleton and append operations -/

section WeakAbelianOperations

variable {t : TStructure C}

/-- The abelian structure on the full heart, used for weak-HN subquotients. -/
local instance : Abelian t.heart.FullSubcategory :=
  t.heartFullSubcategoryAbelian

theorem heartSlope_cokernel_ofLE_congr
    (W : WeakStabilityFunction t) {E : t.heart.FullSubcategory}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    W.heartSlope (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
      W.heartSlope (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst hA
  subst hB
  rfl

theorem heartSemistable_cokernel_ofLE_congr
    (W : WeakStabilityFunction t) {E : t.heart.FullSubcategory}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : W.HeartSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    W.HeartSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst hA
  subst hB
  exact hs

theorem heartSlope_cokernel_mapMono_eq
    (W : WeakStabilityFunction t) {X Y : t.heart.FullSubcategory}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    W.heartSlope
        (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
          ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) =
      W.heartSlope (cokernel (Subobject.ofLE S T h)) :=
  W.slope_eq_of_iso <|
    (t.heart).ι.mapIso
      (CategoryTheory.Triangulated.StabilityFunction.Subobject.cokernelMapMonoIso
        f h)

theorem heartSemistable_cokernel_mapMono_iff
    (W : WeakStabilityFunction t) {X Y : t.heart.FullSubcategory}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    W.HeartSemistable
        (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
          ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      W.HeartSemistable (cokernel (Subobject.ofLE S T h)) := by
  let e := (t.heart).ι.mapIso
    (CategoryTheory.Triangulated.StabilityFunction.Subobject.cokernelMapMonoIso
      f h)
  exact W.isSemistable_iff_of_iso e

/-- A nonzero weak-semistable heart object has the one-factor weak HN
filtration. -/
theorem WeakStabilityFunction.exists_hn_with_last_slope_of_semistable
    (W : WeakStabilityFunction t) {E : t.heart.FullSubcategory}
    (hE : ¬IsZero E) (hss : W.HeartSemistable E) :
    ∃ F : WeakAbelianHNFiltration W E,
      F.μ ⟨F.n - 1, by have := F.hn; lia⟩ = W.heartSlope E := by
  let eFactor :
      cokernel (Subobject.ofLE (⊥ : Subobject E) ⊤ bot_le) ≅ E :=
    StabilityFunction.subobjectCokernelBotIso ⊤ bot_le ≪≫
      asIso (⊤ : Subobject E).arrow
  refine ⟨{
    n := 1
    hn := Nat.one_pos
    chain := fun i ↦ if i = 0 then ⊥ else ⊤
    chain_strictMono := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Fin.lt_def] at hij
      have hi0 : i = 0 := by lia
      have hj1 : j = 1 := by lia
      subst hi0
      subst hj1
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        Fin.mk_one, one_ne_zero, gt_iff_lt]
      exact lt_of_le_of_ne bot_le
        (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hE))
    chain_bot := by simp
    chain_top := by simp
    μ := fun _ ↦ W.heartSlope E
    μ_anti := fun a b hab ↦ by exfalso; exact absurd hab (by lia)
    factor_slope := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by lia
      subst hj0
      change W.heartSlope (cokernel (Subobject.ofLE ⊥ ⊤ _)) = W.heartSlope E
      exact W.slope_eq_of_iso ((t.heart).ι.mapIso eFactor)
    factor_semistable := by
      intro ⟨j, hj⟩
      have hj0 : j = 0 := by lia
      subst hj0
      change W.HeartSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
      exact W.isSemistable_of_iso ((t.heart).ι.mapIso eFactor).symm hss
  }, by simp⟩

/-- Append a lower-slope semistable quotient to a weak HN filtration along a
monomorphism. -/
theorem WeakStabilityFunction.append_hn_filtration_of_mono
    (W : WeakStabilityFunction t) {X Y B : t.heart.FullSubcategory}
    (i : X ⟶ Y) [Mono i] (F : WeakAbelianHNFiltration W X)
    (eB : cokernel i ≅ B) (hB0 : ¬IsZero B)
    (hBss : W.HeartSemistable B)
    (hlast : W.heartSlope B < F.μ ⟨F.n - 1, by have := F.hn; lia⟩) :
    ∃ G : WeakAbelianHNFiltration W Y,
      G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = W.heartSlope B := by
  let K : Subobject Y := Subobject.mk i
  let eK : cokernel K.arrow ≅ B := by
    let eKi : cokernel K.arrow ≅ cokernel i := by
      refine cokernel.mapIso (f := K.arrow) (f' := i)
        (Subobject.underlyingIso i) (Iso.refl _) ?_
      calc
        K.arrow ≫ (Iso.refl Y).hom = K.arrow := by simp
        _ = (Subobject.underlyingIso i).hom ≫ i := by
          change (Subobject.mk i).arrow = (Subobject.underlyingIso i).hom ≫ i
          exact (Subobject.underlyingIso_hom_comp_eq_mk i).symm
    exact eKi ≪≫ eB
  have hK_ne_top : K ≠ ⊤ := by
    intro hK
    have hmk : Subobject.mk i = ⊤ := by simpa [K] using hK
    haveI : IsIso i := (Subobject.isIso_iff_mk_eq_top i).2 hmk
    exact hB0 ((isZero_cokernel_of_epi i).of_iso eB.symm)
  have hK_lt_top : K < ⊤ := lt_of_le_of_ne le_top hK_ne_top
  let newChain : Fin (F.n + 2) → Subobject Y := fun j ↦
    if h : (j : ℕ) ≤ F.n then
      (Subobject.map i).obj (F.chain ⟨j, by lia⟩)
    else ⊤
  have hNewBot : newChain ⟨0, by lia⟩ = ⊥ := by
    change (Subobject.map i).obj (F.chain ⟨0, by lia⟩) = ⊥
    rw [F.chain_bot]
    exact Subobject.map_bot i
  have hNewK : newChain ⟨F.n, by lia⟩ = K := by
    simp [newChain, K, Subobject.map_top, F.chain_top]
  have hNewTop : newChain ⟨F.n + 1, by lia⟩ = ⊤ := by
    simp [newChain]
  have hNewMono : StrictMono newChain := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change newChain ⟨j, by lia⟩ < newChain ⟨j + 1, by lia⟩
    by_cases hjn : j = F.n
    · subst hjn
      rw [hNewK, hNewTop]
      exact hK_lt_top
    · have hjle : j + 1 ≤ F.n := by lia
      simp [newChain, show (j : ℕ) ≤ F.n by lia, hjle]
      apply (Subobject.map i).monotone.strictMono_of_injective
        (Subobject.map_obj_injective i)
      exact F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
  let μ : Fin (F.n + 1) → WithTop ℝ := fun j ↦
    if h : (j : ℕ) < F.n then F.μ ⟨j, h⟩ else W.heartSlope B
  let eLast : B ≅ cokernel (Subobject.ofLE K ⊤ le_top) :=
    eK.symm ≪≫
      (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
  refine ⟨{
    n := F.n + 1
    hn := Nat.succ_pos _
    chain := newChain
    chain_strictMono := hNewMono
    chain_bot := hNewBot
    chain_top := hNewTop
    μ := μ
    μ_anti := by
      intro a b hab
      dsimp [μ]
      by_cases hb : (b : ℕ) < F.n
      · have ha : (a : ℕ) < F.n := lt_trans (Fin.mk_lt_mk.mp hab) hb
        simp [ha, hb]
        exact F.μ_anti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hab))
      · have ha : (a : ℕ) < F.n := by lia
        have hlast_le :
            F.μ ⟨F.n - 1, by have := F.hn; lia⟩ ≤ F.μ ⟨a, ha⟩ :=
          F.μ_anti.antitone (Fin.mk_le_mk.mpr (by lia))
        simp [ha, hb]
        exact hlast.trans_le hlast_le
    factor_slope := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by lia
          simp [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by lia
          simp [newChain, j', hj1_le]
        have hslope :
            W.heartSlope
                (cokernel (Subobject.ofLE
                  ((Subobject.map i).obj (F.chain j'.castSucc))
                  ((Subobject.map i).obj (F.chain j'.succ))
                  ((Subobject.map i).monotone
                    (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) =
              F.μ j' :=
          (heartSlope_cokernel_mapMono_eq W i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).trans
              (F.factor_slope j')
        have hμj : μ j = F.μ j' := by simp [μ, hj, j']
        exact ((heartSlope_cokernel_ofLE_congr W hcast hsucc).trans hslope).trans hμj.symm
      · have hj_eq : (j : ℕ) = F.n := by lia
        have hcast : j.castSucc = ⟨F.n, by lia⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by lia⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        have hμj : μ j = W.heartSlope B := by simp [μ, hj]
        have htarget :
            W.heartSlope (cokernel (Subobject.ofLE K ⊤ le_top)) =
              W.heartSlope B :=
          W.slope_eq_of_iso ((t.heart).ι.mapIso eLast.symm)
        exact ((heartSlope_cokernel_ofLE_congr W hcast_obj hsucc_obj).trans htarget).trans
          hμj.symm
    factor_semistable := by
      intro j
      by_cases hj : (j : ℕ) < F.n
      · let j' : Fin F.n := ⟨j, hj⟩
        have hcast :
            newChain j.castSucc = (Subobject.map i).obj (F.chain j'.castSucc) := by
          have hj_le : (j : ℕ) ≤ F.n := by lia
          simp [newChain, j', hj_le]
        have hsucc :
            newChain j.succ = (Subobject.map i).obj (F.chain j'.succ) := by
          have hj1_le : (j : ℕ) + 1 ≤ F.n := by lia
          simp [newChain, j', hj1_le]
        have hsemistable :
            W.HeartSemistable
              (cokernel (Subobject.ofLE
                ((Subobject.map i).obj (F.chain j'.castSucc))
                ((Subobject.map i).obj (F.chain j'.succ))
                ((Subobject.map i).monotone
                  (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))))) :=
          (heartSemistable_cokernel_mapMono_iff W i
            (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).2
              (F.factor_semistable j')
        exact heartSemistable_cokernel_ofLE_congr W hcast hsucc hsemistable
      · have hj_eq : (j : ℕ) = F.n := by lia
        have hcast : j.castSucc = ⟨F.n, by lia⟩ := Fin.ext hj_eq
        have hsucc : j.succ = ⟨F.n + 1, by lia⟩ := Fin.ext (by simp [hj_eq])
        have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
        have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
        exact heartSemistable_cokernel_ofLE_congr W hcast_obj hsucc_obj <|
          W.isSemistable_of_iso ((t.heart).ι.mapIso eLast) hBss
  }, by simp [μ]⟩

end WeakAbelianOperations

/-! ## HN assembly by quotient induction -/

section WeakAbelianQuotientInduction

variable {t : TStructure C}

/-- The abelian full heart used for quotient-inductive HN assembly. -/
local instance : Abelian t.heart.FullSubcategory :=
  t.heartFullSubcategoryAbelian

/-- One recursive step for constructing an HN filtration from its last
semistable quotient.  The kernel has smaller rank, and the quotient slope is
strictly below the last slope of every HN filtration of that kernel.

The intended rank for Proposition 14.16 is the length of the original HN
filtration of `H⁻¹`; Proposition 19.5 describes exactly this step. -/
structure WeakStabilityFunction.HNQuotientStep
    (W : WeakStabilityFunction t)
    (rank : t.heart.FullSubcategory → ℕ)
    (E : t.heart.FullSubcategory) where
  /-- The recursive kernel. -/
  K : t.heart.FullSubcategory
  /-- The last semistable quotient. -/
  B : t.heart.FullSubcategory
  /-- Kernel inclusion. -/
  i : K ⟶ E
  /-- The inclusion is monic. -/
  mono_i : Mono i
  /-- Identification of its cokernel with the chosen quotient. -/
  cokernelIso : cokernel i ≅ B
  /-- The kernel is nonzero. -/
  kernel_not_isZero : ¬IsZero K
  /-- The quotient is nonzero. -/
  quotient_not_isZero : ¬IsZero B
  /-- The quotient is weak semistable. -/
  quotient_semistable : W.HeartSemistable B
  /-- The recursive measure decreases. -/
  rank_lt : rank K < rank E
  /-- The quotient belongs after every factor of the recursive HN
  filtration. -/
  slope_lt_last : ∀ F : WeakAbelianHNFiltration W K,
    W.heartSlope B < F.μ ⟨F.n - 1, by have := F.hn; omega⟩

/-- Quotient-induction data for all nonzero objects: each is already
semistable, or admits a rank-decreasing last-quotient step. -/
def WeakStabilityFunction.HasHNQuotientInduction
    (W : WeakStabilityFunction t)
    (rank : t.heart.FullSubcategory → ℕ) : Prop :=
  ∀ E : t.heart.FullSubcategory, ¬IsZero E →
    W.HeartSemistable E ∨ Nonempty (W.HNQuotientStep rank E)

/-- **Rank-decreasing semistable quotients assemble to the weak HN
property.**

This is the formal recursion used implicitly in Proposition 14.16 and
explicitly in Proposition 19.5. -/
theorem WeakStabilityFunction.hasHNProperty_of_quotientInduction
    (W : WeakStabilityFunction t)
    (rank : t.heart.FullSubcategory → ℕ)
    (hstep : W.HasHNQuotientInduction rank) : W.HasHNProperty := by
  suffices hmain : ∀ n : ℕ, ∀ E : t.heart.FullSubcategory,
      rank E = n → ¬IsZero E → Nonempty (WeakAbelianHNFiltration W E) by
    intro E hE
    exact hmain (rank E) E rfl hE
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro E hrank hE
      rcases hstep E hE with hsemistable | hrecursive
      · obtain ⟨F, -⟩ := W.exists_hn_with_last_slope_of_semistable hE hsemistable
        exact ⟨F⟩
      · let S := Classical.choice hrecursive
        letI : Mono S.i := S.mono_i
        have hKrank : rank S.K < n := by simpa [hrank] using S.rank_lt
        obtain ⟨F⟩ := ih (rank S.K) hKrank S.K rfl S.kernel_not_isZero
        obtain ⟨G, -⟩ := W.append_hn_filtration_of_mono S.i F
          S.cokernelIso S.quotient_not_isZero S.quotient_semistable
          (S.slope_lt_last F)
        exact ⟨G⟩

end WeakAbelianQuotientInduction

/-! ## Phase--slope comparison for the induced weak heart function -/

namespace WeakPreStabilityCondition

/-- A nonzero slicing-semistable heart object below phase `1` has positive
imaginary charge. -/
theorem charge_im_pos_of_mem_P_phi_lt_one
    (σ : WeakPreStabilityCondition v) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo (0 : ℝ) 1) (E : C)
    (hP : σ.slicing.P phi E) (hE : ¬IsZero E) :
    0 < (σ.weakStabilityFunctionOnHeart.charge E).im := by
  obtain ⟨m, -, hm_strict, hmZ⟩ := σ.compat' phi E hP hE
  have hnotint : ∀ n : ℤ, phi ≠ (n : ℝ) := by
    intro n hcast
    have hn0 : 0 < n := by exact_mod_cast (hcast ▸ hphi.1)
    have hn1 : n < 1 := by exact_mod_cast (hcast ▸ hphi.2)
    omega
  have hmpos : 0 < m := hm_strict hnotint
  rw [show σ.weakStabilityFunctionOnHeart.charge E =
      (m : ℂ) * Complex.exp ((Real.pi * phi : ℝ) * Complex.I) by
    rw [weakStabilityFunctionOnHeart_charge]
    simpa using hmZ]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, add_zero]
  simpa using mul_pos hmpos
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hphi.1)
      (by nlinarith [Real.pi_pos, hphi.2]))

/-- Below phase `1`, compatibility identifies the argument of the induced
weak heart charge with `π * phi`. -/
theorem charge_arg_eq_pi_mul_of_mem_P_phi_lt_one
    (σ : WeakPreStabilityCondition v) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo (0 : ℝ) 1) (E : C)
    (hP : σ.slicing.P phi E) (hE : ¬IsZero E) :
    Complex.arg (σ.weakStabilityFunctionOnHeart.charge E) = Real.pi * phi := by
  obtain ⟨m, -, hm_strict, hmZ⟩ := σ.compat' phi E hP hE
  have hnotint : ∀ n : ℤ, phi ≠ (n : ℝ) := by
    intro n hcast
    have hn0 : 0 < n := by exact_mod_cast (hcast ▸ hphi.1)
    have hn1 : n < 1 := by exact_mod_cast (hcast ▸ hphi.2)
    omega
  have hmpos : 0 < m := hm_strict hnotint
  rw [show σ.weakStabilityFunctionOnHeart.charge E =
      (m : ℂ) * Complex.exp ((Real.pi * phi : ℝ) * Complex.I) by
    rw [weakStabilityFunctionOnHeart_charge]
    simpa using hmZ]
  rw [Complex.arg_real_mul _ hmpos, Complex.arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> nlinarith [Real.pi_pos, hphi.1, hphi.2]

/-- A nonzero phase-`1` object has weak slope `+∞`, including when its charge
vanishes. -/
theorem slope_eq_top_of_mem_P_one
    (σ : WeakPreStabilityCondition v) (E : C)
    (hP : σ.slicing.P 1 E) (hE : ¬IsZero E) :
    σ.weakStabilityFunctionOnHeart.slope E = ⊤ := by
  let W := σ.weakStabilityFunctionOnHeart
  obtain ⟨m, -, -, hmZ⟩ := σ.compat' 1 E hP hE
  apply W.slope_of_im_nonpos
  rw [show W.charge E =
      (m : ℂ) * Complex.exp ((Real.pi * (1 : ℝ) : ℂ) * Complex.I) by
    rw [weakStabilityFunctionOnHeart_charge]
    simpa using hmZ]
  simp [Complex.exp_mul_I]

/-- On nonzero slicing-semistable objects in `(0,1]`, strict phase order is
strict weak-slope order.  The upper endpoint is the `⊤` boundary. -/
theorem slope_lt_of_mem_P_of_phase_lt
    (σ : WeakPreStabilityCondition v) {phi₁ phi₂ : ℝ}
    (hphi₁ : phi₁ ∈ Set.Ioc (0 : ℝ) 1)
    (hphi₂ : phi₂ ∈ Set.Ioc (0 : ℝ) 1) (hphi : phi₁ < phi₂)
    (E₁ E₂ : C) (hP₁ : σ.slicing.P phi₁ E₁)
    (hP₂ : σ.slicing.P phi₂ E₂) (hE₁ : ¬IsZero E₁)
    (hE₂ : ¬IsZero E₂) :
    σ.weakStabilityFunctionOnHeart.slope E₁ <
      σ.weakStabilityFunctionOnHeart.slope E₂ := by
  let W := σ.weakStabilityFunctionOnHeart
  by_cases htwo : phi₂ = 1
  · subst phi₂
    have hone : phi₁ < 1 := hphi
    have him₁ := σ.charge_im_pos_of_mem_P_phi_lt_one ⟨hphi₁.1, hone⟩ E₁ hP₁ hE₁
    rw [W.slope_of_im_pos him₁, σ.slope_eq_top_of_mem_P_one E₂ hP₂ hE₂]
    exact WithTop.coe_lt_top _
  · have htwo_lt : phi₂ < 1 := lt_of_le_of_ne hphi₂.2 htwo
    have hone_lt : phi₁ < 1 := hphi.trans htwo_lt
    have him₁ := σ.charge_im_pos_of_mem_P_phi_lt_one ⟨hphi₁.1, hone_lt⟩ E₁ hP₁ hE₁
    have him₂ := σ.charge_im_pos_of_mem_P_phi_lt_one ⟨hphi₂.1, htwo_lt⟩ E₂ hP₂ hE₂
    have harg₁ := σ.charge_arg_eq_pi_mul_of_mem_P_phi_lt_one
      ⟨hphi₁.1, hone_lt⟩ E₁ hP₁ hE₁
    have harg₂ := σ.charge_arg_eq_pi_mul_of_mem_P_phi_lt_one
      ⟨hphi₂.1, htwo_lt⟩ E₂ hP₂ hE₂
    have harg : Complex.arg (W.charge E₁) < Complex.arg (W.charge E₂) := by
      rw [harg₁, harg₂]
      exact mul_lt_mul_of_pos_left hphi Real.pi_pos
    have hcross :
        0 < (W.charge E₁).re * (W.charge E₂).im -
          (W.charge E₁).im * (W.charge E₂).re :=
      cross_pos_of_arg_lt (by
        rw [harg₁]
        exact mul_pos Real.pi_pos hphi₁.1)
        (ne_of_apply_ne Complex.im (ne_of_gt him₁))
        (ne_of_apply_ne Complex.im (ne_of_gt him₂)) harg
    rw [W.slope_of_im_pos him₁, W.slope_of_im_pos him₂]
    exact_mod_cast (div_lt_div_iff₀ him₁ him₂).2 (by nlinarith [hcross])

/-! ## Slicing HN filtrations induce weak abelian HN filtrations -/

/-- The weak stability function induced on the slicing heart has the
Harder--Narasimhan property.  Zero factors in an ambient slicing tower are
discarded; every remaining factor becomes a successive quotient in the
abelian full heart. -/
theorem weakStabilityFunctionOnHeart_hasHN
    (σ : WeakPreStabilityCondition v) :
    σ.weakStabilityFunctionOnHeart.HasHNProperty := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let W := σ.weakStabilityFunctionOnHeart
  intro E hE
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  suffices hmain :
      ∀ (m : ℕ) {X : t.heart.FullSubcategory} (hXobj : ¬IsZero X.obj)
        (F : HNFiltration C σ.slicing.P X.obj) (hnF : 0 < F.n)
        (hFm : F.n ≤ m)
        (hfirst : ¬IsZero (F.triangle ⟨0, hnF⟩).obj₃),
        ∃ G : WeakAbelianHNFiltration W X, ∃ L : C,
          σ.slicing.P (σ.slicing.phiMinus C X.obj hXobj) L ∧
            ¬IsZero L ∧
              G.μ ⟨G.n - 1, by have := G.hn; lia⟩ = W.slope L by
    obtain ⟨F, hnF, hfirst, _⟩ :=
      σ.slicing.exists_hn_nonzero_boundaries C hEobj
    obtain ⟨G, -, -, -, -⟩ := hmain F.n hEobj F hnF le_rfl hfirst
    exact ⟨G⟩
  intro m
  induction m with
  | zero =>
      intro X hXobj F hnF hFm
      lia
  | succ m ih =>
      intro X hXobj F hnF hFm hfirst
      have hX : ¬IsZero X := fun hZ ↦ hXobj ((t.heart).ι.map_isZero hZ)
      have hXheart := (σ.slicing.toTStructure_heart_iff C X.obj).mp X.property
      by_cases h1 : F.n = 1
      · let phi := F.φ ⟨0, hnF⟩
        have hlast : ¬IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃ := by
          have hidx : (⟨F.n - 1, by lia⟩ : Fin F.n) = ⟨0, hnF⟩ :=
            Fin.ext (by lia)
          simpa [hidx] using hfirst
        have hall : ∀ i : Fin F.n, F.φ i = phi := by
          intro i
          have hidx : i = ⟨0, hnF⟩ := Fin.ext (by lia)
          subst hidx
          rfl
        have hP : σ.slicing.P phi X.obj :=
          CategoryTheory.Triangulated.Slicing.semistable_of_HN_all_eq
            (C := C) σ.slicing F hall
        have hphiMinus : σ.slicing.phiMinus C X.obj hXobj = phi := by
          rw [σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast]
          have hidx : (⟨F.n - 1, by lia⟩ : Fin F.n) = ⟨0, hnF⟩ :=
            Fin.ext (by lia)
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus,
            hidx, phi]
        have hphiPlus : σ.slicing.phiPlus C X.obj hXobj = phi := by
          simpa only [phi,
            CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            (σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst)
        have hphi : phi ∈ Set.Ioc (0 : ℝ) 1 := by
          constructor
          · linarith [σ.slicing.phiMinus_gt_of_gtProp C hXobj hXheart.1,
              hphiMinus]
          · linarith [σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2, hphiPlus]
        have hss : W.HeartSemistable X :=
          σ.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
            hphi X.obj hP hXobj
        obtain ⟨G, hG⟩ := W.exists_hn_with_last_slope_of_semistable hX hss
        refine ⟨G, X.obj, ?_, hXobj, hG⟩
        rw [hphiMinus]
        exact hP
      · have htwo : 2 ≤ F.n := by lia
        by_cases hlast : IsZero (F.triangle ⟨F.n - 1, by lia⟩).obj₃
        · let F' := CategoryTheory.Triangulated.HNFiltration.dropLast
            C F (by lia) hlast
          have hnF' : 0 < F'.n := F'.n_pos C hXobj
          have hF'm : F'.n ≤ m := by
            change F.n - 1 ≤ m
            lia
          have hfirst' : ¬IsZero (F'.triangle ⟨0, hnF'⟩).obj₃ := by
            simpa [F', CategoryTheory.Triangulated.HNFiltration.dropLast,
              CategoryTheory.Triangulated.HNFiltration.prefix] using hfirst
          exact ih hXobj F' hnF' hF'm hfirst'
        · have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
            intro i
            constructor
            · calc
                0 < σ.slicing.phiMinus C X.obj hXobj :=
                  σ.slicing.phiMinus_gt_of_gtProp C hXobj hXheart.1
                _ = F.φ ⟨F.n - 1, by lia⟩ :=
                  σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast
                _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
            · calc
                F.φ i ≤ F.φ ⟨0, hnF⟩ :=
                  F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
                _ = σ.slicing.phiPlus C X.obj hXobj := by
                  symm
                  exact σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst
                _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
          let FX : HNFiltration C σ.slicing.P
              (F.chain.obj ⟨F.n - 1, by lia⟩) :=
            CategoryTheory.Triangulated.HNFiltration.prefix
              C F (F.n - 1) (by lia)
          have hFXn : 0 < FX.n := by
            change 0 < F.n - 1
            lia
          have hFXheart : t.heart (F.chain.obj ⟨F.n - 1, by lia⟩) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            constructor
            · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
                C σ.slicing F
                (F.n - 1) (by lia) (by lia) 0
                (fun j ↦ (hall_mem ⟨j, by lia⟩).1)
            · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
                C σ.slicing F
                (F.n - 1) (by lia) (by lia) 1
                (fun j ↦ (hall_mem ⟨j, by lia⟩).2)
          let X' : t.heart.FullSubcategory :=
            ⟨F.chain.obj ⟨F.n - 1, by lia⟩, hFXheart⟩
          have hfirstFX : ¬IsZero (FX.triangle ⟨0, hFXn⟩).obj₃ := by
            simpa [FX, CategoryTheory.Triangulated.HNFiltration.prefix] using hfirst
          have hX'obj : ¬IsZero X'.obj := by
            intro hZ
            have hzero :
                ∀ f : (FX.triangle ⟨0, hFXn⟩).obj₃ ⟶
                  F.chain.obj ⟨F.n - 1, by lia⟩, f = 0 :=
              fun f ↦ hZ.eq_of_tgt _ _
            exact hfirstFX <|
              CategoryTheory.Triangulated.HNFiltration.firstFactor_isZero_of_hom_eq_zero
                (C := C) σ.slicing FX hFXn hzero
          obtain ⟨GX, L, hPL, hL, hGX⟩ := ih hX'obj FX hFXn (by
            change F.n - 1 ≤ m
            lia) hfirstFX
          let jLast : Fin F.n := ⟨F.n - 1, by lia⟩
          have hBheart : t.heart (F.triangle jLast).obj₃ := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨
              σ.slicing.gtProp_of_semistable C
                (F.semistable jLast) (hall_mem jLast).1,
              σ.slicing.leProp_of_semistable C
                (F.semistable jLast) (hall_mem jLast).2⟩
          let B : t.heart.FullSubcategory :=
            ⟨(F.triangle jLast).obj₃, hBheart⟩
          have hB0 : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
          have hBss : W.HeartSemistable B :=
            σ.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
              (hall_mem jLast) B.obj (F.semistable jLast) hlast
          have hX'gt : σ.slicing.gtProp C (F.φ jLast) X'.obj :=
            CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp C σ.slicing F
              (F.n - 1) (by lia) (by lia) (F.φ jLast) <|
                fun j ↦ by
                  have hjlt : (⟨j.val, by grind⟩ : Fin F.n) < jLast :=
                    Fin.mk_lt_mk.mpr (by grind)
                  exact F.hφ hjlt
          have hphase_lt :
              F.φ jLast < σ.slicing.phiMinus C X'.obj hX'obj :=
            σ.slicing.phiMinus_gt_of_gtProp C hX'obj hX'gt
          have hX'bounds :=
            (σ.slicing.toTStructure_heart_iff C X'.obj).mp X'.property
          have hLphase :
              σ.slicing.phiMinus C X'.obj hX'obj ∈ Set.Ioc (0 : ℝ) 1 := by
            constructor
            · exact σ.slicing.phiMinus_gt_of_gtProp C hX'obj hX'bounds.1
            · exact (σ.slicing.phiMinus_le_phiPlus C X'.obj hX'obj).trans
                (σ.slicing.phiPlus_le_of_leProp C hX'obj hX'bounds.2)
          have hslope_lt : W.heartSlope B < W.slope L :=
            σ.slope_lt_of_mem_P_of_phase_lt (hall_mem jLast) hLphase
              hphase_lt B.obj L (F.semistable jLast) hPL hlast hL
          have hslope_last :
              W.heartSlope B < GX.μ ⟨GX.n - 1, by have := GX.hn; lia⟩ := by
            rw [hGX]
            exact hslope_lt
          let Tlast := F.triangle jLast
          let e₁ := Classical.choice (F.triangle_obj₁ jLast)
          let e₂ := Classical.choice (F.triangle_obj₂ jLast)
          have hobj₂_eq :
              F.chain.obj' (F.n - 1 + 1) (by lia) = F.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            lia
          let e₂X : Tlast.obj₂ ≅ X.obj :=
            e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
          let i : X' ⟶ X :=
            ObjectProperty.homMk (e₁.inv ≫ Tlast.mor₁ ≫ e₂X.hom)
          let q : X ⟶ B :=
            ObjectProperty.homMk (e₂X.inv ≫ Tlast.mor₂)
          let δ : B.obj ⟶ X'.obj⟦(1 : ℤ)⟧ :=
            Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
            refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm e₂X.symm (Iso.refl _)
              (by simp [Tlast, i, e₂X])
              (by simp [Tlast, q, e₂X])
              (by simp [Tlast, δ])
          have hiq_hom : i.hom ≫ q.hom = 0 := by
            have := comp_distTriang_mor_zero₁₂ _ hTlast
            simpa using this
          have hiq : i ≫ q = 0 := by
            ext
            exact hiq_hom
          have hKer : IsLimit (KernelFork.ofι i hiq) := by
            simpa [hiq] using
              Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
                (CategoryTheory.Triangulated.TStructure.heart_hι t)
                i q δ hTlast
          have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
            simpa [hiq] using
              Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
                (CategoryTheory.Triangulated.TStructure.heart_hι t)
                i q δ hTlast
          let eB : cokernel i ≅ B :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hCok
          haveI : Mono i := Fork.IsLimit.mono hKer
          obtain ⟨G, hG⟩ := W.append_hn_filtration_of_mono
            i GX eB hB0 hBss hslope_last
          refine ⟨G, B.obj, ?_, hlast, hG⟩
          rw [σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast]
          exact F.semistable jLast

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition
