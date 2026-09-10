/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.StrictDrop
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakHarderNarasimhan

/-!
# Lifting a filtration of a quotient back to the ambient object

The Harder–Narasimhan recursion removes the maximal destabilizing subobject `B ⊆ E`, filters the
quotient `E / B`, and splices the two together. This file supplies the lattice-level facts that
splice needs, all of them about the subobject correspondence and none of them about slopes.

* `pullback_bot` — the bottom subobject of `E / B` pulls back to `B` itself, so the spliced chain
  really does begin `⊥ < B < …`. It is `pullback_imageSubobject_eq` at `S = B`, where the image
  of `B.arrow ≫ cokernel.π B.arrow = 0` is `⊥`.
* `pullback_lt_of_lt` — strict inclusions pull back to strict inclusions. This is not formal
  monotonicity: it is proved from the fact that a chain step with a nonzero successive quotient
  cannot be an equality, using `cokernelPullbackIso` to identify that quotient with the one
  upstairs.
* `cokernelOfLEBotIso` — the first successive quotient of the spliced chain, `cokernel (⊥ ⟶ B)`,
  is `B` itself, which is what lets the first factor's slope and semistability be read off the
  maximal destabilizing subobject.

Nothing here mentions a polarization; it is the correspondence, specialised to what the splice
consumes.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- **The bottom of the quotient pulls back to the subobject itself.** -/
theorem pullback_bot {F : Coh X} (B : Subobject F) :
    (Subobject.pullback (cokernel.π B.arrow)).obj ⊥ = B := by
  have hzero : B.arrow ≫ cokernel.π B.arrow = 0 := cokernel.condition _
  have h := CategoryTheory.Abelian.pullback_imageSubobject_eq (le_refl B)
  rwa [hzero, imageSubobject_zero] at h

/-- The inclusion of the bottom subobject into any subobject is the zero morphism. -/
theorem ofLE_bot_eq_zero {F : Coh X} (B : Subobject F) (h : (⊥ : Subobject F) ≤ B) :
    Subobject.ofLE ⊥ B h = 0 := by
  have hz : IsZero ((⊥ : Subobject F) : Coh X) :=
    IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
  exact hz.eq_zero_of_src _

/-- **The first successive quotient of a spliced chain is the subobject itself.** -/
noncomputable def cokernelOfLEBotIso {F : Coh X} (B : Subobject F)
    (h : (⊥ : Subobject F) ≤ B) :
    cokernel (Subobject.ofLE ⊥ B h) ≅ (B : Coh X) := by
  refine (?_ : cokernel (Subobject.ofLE ⊥ B h) ≅ cokernel (0 : ((⊥ : Subobject F) : Coh X) ⟶
    (B : Coh X))).trans cokernelZeroIsoTarget
  exact cokernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp [ofLE_bot_eq_zero B h])

/-- A strict inclusion of subobjects has a nonzero successive quotient: a zero cokernel would
make the inclusion an isomorphism. This is `AbelianWeakHNFiltration.factor_not_isZero`'s
argument, stated for a bare pair of subobjects. -/
theorem cokernel_not_isZero_of_lt {Y : Coh X} {C₁ C₂ : Subobject Y} (hlt : C₁ < C₂) :
    ¬IsZero (cokernel (Subobject.ofLE C₁ C₂ hlt.le)) := fun hzero ↦ by
  haveI : Epi (Subobject.ofLE C₁ C₂ hlt.le) :=
    Preadditive.epi_of_isZero_cokernel _ hzero
  haveI : IsIso (Subobject.ofLE C₁ C₂ hlt.le) := isIso_of_mono_of_epi _
  have hle : C₂ ≤ C₁ :=
    Subobject.le_of_comm (inv (Subobject.ofLE C₁ C₂ hlt.le)) (by simp)
  exact absurd hle (not_le_of_gt hlt)

/-- **Strict inclusions pull back to strict inclusions.**

Monotonicity is formal; strictness is not. If the pullbacks agreed, the inclusion between them
would be an isomorphism and its cokernel zero, but `cokernelPullbackIso` identifies that cokernel
with the successive quotient upstairs, which a strict inclusion makes nonzero. -/
theorem pullback_lt_of_lt {F : Coh X} (B : Subobject F)
    {C₁ C₂ : Subobject (cokernel B.arrow)} (hlt : C₁ < C₂) :
    (Subobject.pullback (cokernel.π B.arrow)).obj C₁ <
      (Subobject.pullback (cokernel.π B.arrow)).obj C₂ := by
  have hle : C₁ ≤ C₂ := hlt.le
  have hne : ¬IsZero (cokernel (Subobject.ofLE C₁ C₂ hle)) := cokernel_not_isZero_of_lt hlt
  refine lt_of_le_of_ne (Functor.monotone _ hle) ?_
  intro heq
  apply hne
  set p := cokernel.π B.arrow with hp
  set pb₁ := (Subobject.pullback p).obj C₁ with hpb₁
  set pb₂ := (Subobject.pullback p).obj C₂ with hpb₂
  have hmono : pb₁ ≤ pb₂ := Functor.monotone _ hle
  have hback : pb₂ ≤ pb₁ := le_of_eq heq.symm
  haveI : IsIso (Subobject.ofLE pb₁ pb₂ hmono) :=
    ⟨⟨Subobject.ofLE pb₂ pb₁ hback,
      by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl],
      by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]⟩⟩
  have hcokzero : IsZero (cokernel (Subobject.ofLE pb₁ pb₂ hmono)) :=
    (Preadditive.epi_iff_isZero_cokernel _).mp inferInstance
  exact hcokzero.of_iso (CategoryTheory.Abelian.cokernelPullbackIso B hle).symm

/-- Transport of a successive quotient along equalities of its endpoints. The inclusion's
proof argument is irrelevant, so the two cokernels agree once the endpoints do. -/
noncomputable def cokernelOfLECongr {Y : Coh X} {C₁ C₂ C₁' C₂' : Subobject Y}
    (hle : C₁ ≤ C₂) (hle' : C₁' ≤ C₂') (e₁ : C₁ = C₁') (e₂ : C₂ = C₂') :
    cokernel (Subobject.ofLE C₁ C₂ hle) ≅ cokernel (Subobject.ofLE C₁' C₂' hle') := by
  subst e₁
  subst e₂
  exact Iso.refl _

/-- The spliced chain: the bottom subobject, then the pullbacks of a chain in the quotient. -/
noncomputable def spliceChain {F : Coh X} (B : Subobject F) {m : ℕ}
    (c : Fin (m + 1) → Subobject (cokernel B.arrow)) : Fin (m + 1 + 1) → Subobject F :=
  Fin.cases ⊥ (fun j ↦ (Subobject.pullback (cokernel.π B.arrow)).obj (c j))

@[simp]
theorem spliceChain_zero {F : Coh X} (B : Subobject F) {m : ℕ}
    (c : Fin (m + 1) → Subobject (cokernel B.arrow)) :
    spliceChain B c 0 = ⊥ := rfl

@[simp]
theorem spliceChain_succ {F : Coh X} (B : Subobject F) {m : ℕ}
    (c : Fin (m + 1) → Subobject (cokernel B.arrow)) (j : Fin (m + 1)) :
    spliceChain B c j.succ = (Subobject.pullback (cokernel.π B.arrow)).obj (c j) := rfl

/-- The spliced chain is strictly monotone: the first step is `⊥ < B`, which needs `B` nonzero,
and every later step is a pullback of a strict step downstairs. -/
theorem spliceChain_strictMono {F : Coh X} {B : Subobject F} (hB : ¬IsZero (B : Coh X)) {m : ℕ}
    {c : Fin (m + 1) → Subobject (cokernel B.arrow)} (hc : StrictMono c) (hbot : c 0 = ⊥) :
    StrictMono (spliceChain B c) := by
  refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
  refine Fin.cases ?_ ?_ i
  · -- the first step is `⊥ < B`
    have hb : (Subobject.pullback (cokernel.π B.arrow)).obj (c 0) = B := by
      rw [hbot, pullback_bot]
    have hBne : (⊥ : Subobject F) ≠ B := by
      intro hEq
      exact hB (IsZero.of_iso (isZero_zero _)
        ((Subobject.isoOfEq _ _ hEq).symm ≪≫ Subobject.botCoeIsoZero))
    show spliceChain B c (Fin.castSucc 0) < spliceChain B c (Fin.succ 0)
    rw [show (Fin.castSucc (0 : Fin (m + 1))) = 0 from rfl, spliceChain_zero,
      spliceChain_succ, hb]
    exact lt_of_le_of_ne bot_le hBne
  · intro i'
    show spliceChain B c (Fin.castSucc i'.succ) < spliceChain B c (Fin.succ i'.succ)
    rw [← Fin.succ_castSucc, spliceChain_succ, spliceChain_succ]
    exact pullback_lt_of_lt B (hc i'.castSucc_lt_succ)

/-- The spliced chain ends at the top, because the pullback of the top subobject is the top. -/
theorem spliceChain_top {F : Coh X} (B : Subobject F) {m : ℕ}
    (c : Fin (m + 1) → Subobject (cokernel B.arrow))
    (htop : c (Fin.last m) = ⊤) :
    spliceChain B c (Fin.last (m + 1)) = ⊤ := by
  show spliceChain B c (Fin.succ (Fin.last m)) = ⊤
  rw [spliceChain_succ, htop, Subobject.pullback_top]

/-- **The first factor of a spliced chain is the subobject itself.** -/
noncomputable def spliceFactorZeroIso {F : Coh X} (B : Subobject F) {m : ℕ}
    (c : Fin (m + 1) → Subobject (cokernel B.arrow)) (hbot : c 0 = ⊥)
    (hle : spliceChain B c (Fin.castSucc 0) ≤ spliceChain B c (Fin.succ 0)) :
    cokernel (Subobject.ofLE _ _ hle) ≅ (B : Coh X) := by
  have hbotEq : spliceChain B c (Fin.castSucc (0 : Fin (m + 1))) = (⊥ : Subobject F) := rfl
  have hsuccEq : spliceChain B c (Fin.succ (0 : Fin (m + 1))) = B := by
    rw [spliceChain_succ, hbot, pullback_bot]
  exact (cokernelOfLECongr hle bot_le hbotEq hsuccEq).trans (cokernelOfLEBotIso B bot_le)

/-- **Every later factor of a spliced chain is the corresponding factor downstairs.** -/
noncomputable def spliceFactorSuccIso {F : Coh X} (B : Subobject F) {m : ℕ}
    (c : Fin (m + 1) → Subobject (cokernel B.arrow)) (j : Fin m)
    (hle : spliceChain B c (Fin.castSucc j.succ) ≤ spliceChain B c (Fin.succ j.succ))
    (hlec : c (Fin.castSucc j) ≤ c (Fin.succ j)) :
    cokernel (Subobject.ofLE _ _ hle) ≅ cokernel (Subobject.ofLE _ _ hlec) := by
  have h1 : spliceChain B c (Fin.castSucc j.succ) =
      (Subobject.pullback (cokernel.π B.arrow)).obj (c (Fin.castSucc j)) := by
    rw [← Fin.succ_castSucc, spliceChain_succ]
  have h2 : spliceChain B c (Fin.succ j.succ) =
      (Subobject.pullback (cokernel.π B.arrow)).obj (c (Fin.succ j)) := by
    rw [spliceChain_succ]
  exact (cokernelOfLECongr hle (Functor.monotone _ hlec) h1 h2).trans
    (CategoryTheory.Abelian.cokernelPullbackIso B hlec)

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-- **The first factor of a filtration is its first chain step.**

The opening successive quotient runs out of the bottom subobject, so it is the first chain step
itself. This is what turns a statement about the *subobjects* of a quotient into one about the
*factors* of a filtration of it. -/
noncomputable def firstFactorIso (h : MuPositivityData P) {Y : Coh X}
    (G : AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction Y) :
    G.factor ⟨0, G.nonempty⟩ ≅
      ((G.chain (Fin.succ ⟨0, G.nonempty⟩) : Subobject Y) : Coh X) := by
  have hbot : G.chain (Fin.castSucc ⟨0, G.nonempty⟩) = ⊥ := G.chain_bot
  exact (cokernelOfLECongr _ bot_le hbot rfl).trans
    (cokernelOfLEBotIso (G.chain (Fin.succ ⟨0, G.nonempty⟩)) bot_le)

/-- **The top slope of a filtration of the quotient lies strictly below the maximal slope.**

The first factor is a genuine nonzero subobject of the quotient, so the strict drop applies to
it. This is the inequality that makes the spliced slope vector strictly antitone at the splice
point, and it is the only place the drop is needed. -/
theorem muZero_lt_topSlope (h : MuPositivityData P) {F : Coh X} {B : Subobject F}
    (hB : IsMaximalDestabilizing h F B)
    (G : AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction
      (cokernel (B : Subobject F).arrow)) :
    G.μ ⟨0, G.nonempty⟩ <
      (P.weakSlopeData h).topSlope ((B : Subobject F) : Coh X) := by
  have hiso := firstFactorIso h G
  have hne : ¬IsZero ((G.chain (Fin.succ ⟨0, G.nonempty⟩) :
      Subobject (cokernel B.arrow)) : Coh X) := by
    intro hz
    exact G.factor_not_isZero ⟨0, G.nonempty⟩ (hz.of_iso hiso)
  have hslope : G.μ ⟨0, G.nonempty⟩ =
      (P.weakSlopeData h).topSlope
        ((G.chain (Fin.succ ⟨0, G.nonempty⟩) : Subobject (cokernel B.arrow)) : Coh X) := by
    rw [← G.factor_slope ⟨0, G.nonempty⟩]
    exact (P.weakSlopeData h).toWeakStabilityFunction.slope_eq_of_iso hiso
  rw [hslope]
  exact topSlope_lt_of_maximalDestabilizing h hB _ hne

/-- **The spliced Harder–Narasimhan filtration.**

Given the maximal destabilizing subobject `B ⊆ F` and a filtration of `F / B`, prepend `B`.
The chain is `spliceChain`, the slope vector is the slope of `B` followed by the quotient's,
and every field is one of the facts above:

* strict monotonicity is `spliceChain_strictMono`;
* strict antitonicity is `muZero_lt_topSlope` at the splice point and `G.μ_anti` above it. It is
  proved directly rather than through the adjacent-step criterion, because that criterion would
  index by `Fin G.n` with `G.n` opaque, which cannot be case-split;
* the factors are identified by `spliceFactorZeroIso` and `spliceFactorSuccIso`, and their slopes
  and semistability transported along those isomorphisms. -/
noncomputable def splice (h : MuPositivityData P) {F : Coh X} {B : Subobject F}
    (hB : IsMaximalDestabilizing h F B)
    (G : AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction
      (cokernel (B : Subobject F).arrow)) :
    AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F where
  n := G.n + 1
  nonempty := Nat.succ_pos _
  chain := spliceChain B G.chain
  chain_strictMono := spliceChain_strictMono hB.1 G.chain_strictMono G.chain_bot
  chain_bot := rfl
  chain_top := spliceChain_top B G.chain G.chain_top
  μ := Fin.cases ((P.weakSlopeData h).topSlope ((B : Subobject F) : Coh X)) G.μ
  μ_anti := by
    intro a b hab
    revert hab
    refine Fin.cases ?_ ?_ b
    · intro hab
      exact absurd hab (Fin.not_lt_zero a)
    · intro b' hab
      revert hab
      refine Fin.cases ?_ ?_ a
      · intro _
        show G.μ b' < (P.weakSlopeData h).topSlope ((B : Subobject F) : Coh X)
        exact lt_of_le_of_lt (G.μ_anti.antitone (Fin.le_def.mpr (Nat.zero_le _)))
          (muZero_lt_topSlope h hB G)
      · intro a' hab
        show G.μ b' < G.μ a'
        exact G.μ_anti (Fin.succ_lt_succ_iff.mp hab)
  factor_slope := by
    intro j
    refine Fin.cases ?_ ?_ j
    · exact (P.weakSlopeData h).toWeakStabilityFunction.slope_eq_of_iso
        (spliceFactorZeroIso B G.chain G.chain_bot _)
    · intro j'
      refine Eq.trans ((P.weakSlopeData h).toWeakStabilityFunction.slope_eq_of_iso
        (spliceFactorSuccIso B G.chain j' _
          (le_of_lt (G.chain_strictMono Fin.castSucc_lt_succ)))) ?_
      exact G.factor_slope j'
  factor_semistable := by
    intro j
    refine Fin.cases ?_ ?_ j
    · exact (P.weakSlopeData h).toWeakStabilityFunction.isSemistable_of_iso
        (spliceFactorZeroIso B G.chain G.chain_bot _).symm
        (maximalDestabilizing_isSemistable h hB)
    · intro j'
      exact (P.weakSlopeData h).toWeakStabilityFunction.isSemistable_of_iso
        (spliceFactorSuccIso B G.chain j' _
          (le_of_lt (G.chain_strictMono Fin.castSucc_lt_succ))).symm
        (G.factor_semistable j')

end PolarizedVarietyData
