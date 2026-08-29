/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.WeakHarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Uniqueness.SubobjectLattice

/-!
# The extremal slopes of a weak HN filtration

This is `Uniqueness/Extrema.lean` and `PhaseMonotone.lean` for the
slope-indexed weak filtration of `WeakHarderNarasimhan.lean`.

**Why the port is mechanical, recorded because it was the question this work
turned on.**  The strict development never performs arithmetic on phases.  It
compares them, and nothing else: across `Extrema.lean`, `PhaseMonotone.lean`,
`Uniqueness/Tail.lean` and `Uniqueness/Destabilizing.lean` there is not one
`linarith`, no subtraction, no `Real.pi`, no `arg`.  Every step is
`le_antisymm`, `le_of_not_gt`, `lt_of_le_of_lt` or `StrictAnti.antitone`, all of
which hold over `WithTop ℝ` exactly as over `ℝ`.  The one genuinely analytic
input is Hom-vanishing for semistable objects of decreasing value, and its weak
counterpart `hom_eq_zero_of_semistable_slope_gt` is proved in
`WeakSlopeGeometry.lean` from the slope see-saw.

The subobject-lattice primitives are shared rather than duplicated: they are
already charge-free, so `AbelianHNFiltration.le_of_ofLE_comp_cokernel_zero`,
`StabilityFunction.subobjectCokernelBotIso` and
`StabilityFunction.subobject_isZero_iff_eq_bot` are used here directly.  The
first of those sits in the *strict* filtration's namespace even though it
mentions no charge; moving it is a rename across the strict development and is
deliberately not done here.

## Contents

* `le_chain_of_semistable_μ_gt`, `eq_bot_of_semistable_μ_gt_μPlus` — a
  weak-semistable subobject of large slope is trapped in the filtration.
* `chain_one_isSemistable`, `μ_chain_one`, `chain_one_ne_bot` — the first chain
  step is the maximal destabilizing subobject.
* `μPlus_eq`, `μMinus_eq` — **the extrema are intrinsic**, so the cutoff
  classes of `WeakCutoff.lean` are well defined.
* `μPlus_le_of_mono`, `μMinus_le_of_epi` — the monotonicity that traps the
  image of a map between the two cutoff classes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianWeakHNFiltration

variable {W : WeakStabilityFunctionOn (abelianDatum A)}

/-- A weak-semistable object of slope above an HN factor has no morphisms to
that factor. -/
theorem hom_eq_zero_to_factor {E B : A} (F : AbelianWeakHNFiltration W E)
    (hB : W.IsSemistable B) (j : Fin F.n) (hslope : F.μ j < W.slope B)
    (f : B ⟶ F.factor j) : f = 0 :=
  W.hom_eq_zero_of_semistable_slope_gt hB (F.factor_semistable j)
    (F.factor_slope j ▸ hslope) f

/-- A weak-semistable subobject whose slope is above every factor from index
`k` onward lies in the `k`-th term of an HN filtration. -/
theorem le_chain_of_semistable_μ_gt {E : A} (F : AbelianWeakHNFiltration W E)
    {B : Subobject E} (hB : W.IsSemistable (B : A)) {k : ℕ} (hk : k ≤ F.n)
    (hslope : ∀ j : Fin F.n, k ≤ j.val → F.μ j < W.slope (B : A)) :
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
        F.hom_eq_zero_to_factor hB j (hslope j (by simp [j]; lia)) _
      exact AbelianHNFiltration.le_of_ofLE_comp_cokernel_zero hBnext
        (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hzero

/-- A weak-semistable subobject whose slope is above the highest HN slope is
zero. -/
theorem eq_bot_of_semistable_μ_gt_μPlus {E : A}
    (F : AbelianWeakHNFiltration W E) {B : Subobject E}
    (hB : W.IsSemistable (B : A)) (hslope : F.μPlus < W.slope (B : A)) :
    B = ⊥ := by
  apply le_bot_iff.mp
  rw [← F.chain_bot]
  apply F.le_chain_of_semistable_μ_gt hB (Nat.zero_le _)
  intro j _
  exact lt_of_le_of_lt
    (F.μ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hslope

/-- The first nonzero term in an HN filtration is not bottom. -/
theorem chain_one_ne_bot {E : A} (F : AbelianWeakHNFiltration W E) :
    F.chain ⟨1, by have := F.nonempty; lia⟩ ≠ ⊥ := by
  have hn := F.nonempty
  intro heq
  have hlt : F.chain ⟨0, by lia⟩ < F.chain ⟨1, by lia⟩ :=
    F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
  rw [F.chain_bot, heq] at hlt
  exact lt_irrefl _ hlt

/-- The slope of the first nonzero term is the highest HN slope. -/
theorem μ_chain_one {E : A} (F : AbelianWeakHNFiltration W E) :
    W.slope (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) = F.μPlus := by
  have hn := F.nonempty
  change W.slope (F.chain ⟨1, by lia⟩ : A) = F.μ ⟨0, F.nonempty⟩
  rw [← F.factor_slope ⟨0, F.nonempty⟩]
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  exact ((W.slope_cokernel_ofLE_congr hzero rfl).trans
    (W.slope_eq_of_iso
      (StabilityFunction.subobjectCokernelBotIso
        (F.chain ⟨1, by lia⟩) bot_le))).symm

/-- The first nonzero term in an HN filtration is weak-semistable. -/
theorem chain_one_isSemistable {E : A} (F : AbelianWeakHNFiltration W E) :
    W.IsSemistable (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) := by
  have hn := F.nonempty
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have hnormalized : W.IsSemistable
      (cokernel (Subobject.ofLE (⊥ : Subobject E)
        (F.chain ⟨1, by lia⟩) bot_le)) :=
    W.isSemistable_cokernel_ofLE_congr hzero.symm rfl
      (F.factor_semistable ⟨0, F.nonempty⟩)
  exact W.isSemistable_of_iso
    (StabilityFunction.subobjectCokernelBotIso
      (F.chain ⟨1, by lia⟩) bot_le) hnormalized

/-- **The highest slope is intrinsic**: any two weak HN filtrations of the same
object have the same first slope. -/
theorem μPlus_eq {E : A} (F G : AbelianWeakHNFiltration W E) :
    F.μPlus = G.μPlus := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hGF
    exact F.chain_one_ne_bot (G.eq_bot_of_semistable_μ_gt_μPlus
      F.chain_one_isSemistable (F.μ_chain_one ▸ hGF))
  · apply le_of_not_gt
    intro hFG
    exact G.chain_one_ne_bot (F.eq_bot_of_semistable_μ_gt_μPlus
      G.chain_one_isSemistable (G.μ_chain_one ▸ hFG))

/-- The first nonzero term is intrinsic: any two weak HN filtrations of the
same object have the same maximally destabilizing subobject. -/
theorem chain_one_eq {E : A} (F G : AbelianWeakHNFiltration W E) :
    F.chain ⟨1, by have := F.nonempty; lia⟩ =
      G.chain ⟨1, by have := G.nonempty; lia⟩ := by
  apply le_antisymm
  · apply G.le_chain_of_semistable_μ_gt F.chain_one_isSemistable G.nonempty
    intro j hj
    calc
      G.μ j < G.μPlus := G.μ_anti (Fin.mk_lt_mk.mpr (by lia))
      _ = F.μPlus := (F.μPlus_eq G).symm
      _ = W.slope (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) :=
        F.μ_chain_one.symm
  · apply F.le_chain_of_semistable_μ_gt G.chain_one_isSemistable F.nonempty
    intro j hj
    calc
      F.μ j < F.μPlus := F.μ_anti (Fin.mk_lt_mk.mpr (by lia))
      _ = G.μPlus := F.μPlus_eq G
      _ = W.slope (G.chain ⟨1, by have := G.nonempty; lia⟩ : A) :=
        G.μ_chain_one.symm

/-- No nonzero weak-semistable subobject has slope above the first HN slope. -/
theorem semistable_μ_le_μPlus {E : A} (F : AbelianWeakHNFiltration W E)
    {B : Subobject E} (hB : W.IsSemistable (B : A)) :
    W.slope (B : A) ≤ F.μPlus := by
  apply le_of_not_gt
  intro hslope
  exact hB.1 ((StabilityFunction.subobject_isZero_iff_eq_bot B).2
    (F.eq_bot_of_semistable_μ_gt_μPlus hB hslope))

/-- **Every morphism to a weak-semistable object of slope below the lowest HN
slope is zero.**  Induction along the chain: each step factors through a
successive quotient, which is semistable of slope above the target. -/
theorem hom_eq_zero_to_semistable_of_μ_lt_μMinus {E B : A}
    (F : AbelianWeakHNFiltration W E) (hB : W.IsSemistable B)
    (hslope : W.slope B < F.μMinus) (f : E ⟶ B) : f = 0 := by
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
        have hfactor_slope : W.slope B < W.slope (F.factor j) := by
          rw [F.factor_slope j]
          exact lt_of_lt_of_le hslope (F.μ_mem_range j).1
        have hdescended : descended = 0 :=
          W.hom_eq_zero_of_semistable_slope_gt (F.factor_semistable j) hB
            hfactor_slope descended
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

/-- The last HN factor, presented as a weak-semistable quotient of the filtered
object at the lowest HN slope. -/
theorem exists_epi_to_semistable_μ_μMinus {E : A}
    (F : AbelianWeakHNFiltration W E) :
    ∃ (Q : A) (q : E ⟶ Q), Epi q ∧ W.IsSemistable Q ∧ W.slope Q = F.μMinus := by
  have hn := F.nonempty
  let last : Fin F.n := ⟨F.n - 1, by lia⟩
  have hlast : F.chain last.succ = ⊤ := by
    have hindex : last.succ = ⟨F.n, by lia⟩ := Fin.ext (by simp [last]; lia)
    rw [hindex, F.chain_top]
  haveI : IsIso (F.chain last.succ).arrow := by
    rw [hlast]
    infer_instance
  exact ⟨F.factor last,
    inv (F.chain last.succ).arrow ≫
      cokernel.π (Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
        (le_of_lt (F.chain_strictMono last.castSucc_lt_succ))),
    inferInstance, F.factor_semistable last, F.factor_slope last⟩

/-- **The lowest slope is intrinsic**: any two weak HN filtrations of the same
object have the same last slope. -/
theorem μMinus_eq {E : A} (F G : AbelianWeakHNFiltration W E) :
    F.μMinus = G.μMinus := by
  have no_strict_order : ∀ (H K : AbelianWeakHNFiltration W E),
      ¬H.μMinus < K.μMinus := by
    intro H K hHK
    obtain ⟨Q, q, hq, hQ, hQslope⟩ := H.exists_epi_to_semistable_μ_μMinus
    haveI := hq
    have hzero : q = 0 :=
      K.hom_eq_zero_to_semistable_of_μ_lt_μMinus hQ (hQslope ▸ hHK) q
    exact hQ.1 (IsZero.of_epi_eq_zero q hzero)
  exact le_antisymm (le_of_not_gt (no_strict_order G F))
    (le_of_not_gt (no_strict_order F G))

/-- **`μPlus` is monotone along monomorphisms.**  The maximal destabilizing
subobject of the source maps to a weak-semistable subobject of the target of the
same slope, and no weak-semistable subobject exceeds `μPlus`. -/
theorem μPlus_le_of_mono {X Y : A} (F : AbelianWeakHNFiltration W X)
    (G : AbelianWeakHNFiltration W Y) (i : X ⟶ Y) [Mono i] :
    F.μPlus ≤ G.μPlus := by
  have hn := F.nonempty
  set M : Subobject X := F.chain ⟨1, by lia⟩ with hM
  have hmap : W.IsSemistable (((Subobject.map i).obj M : A)) :=
    W.isSemistable_of_iso (StabilityFunction.Subobject.mapMonoIso i M).symm
      F.chain_one_isSemistable
  have hle := G.semistable_μ_le_μPlus hmap
  rwa [W.slope_eq_of_iso (StabilityFunction.Subobject.mapMonoIso i M),
    F.μ_chain_one] at hle

/-- **`μMinus` is monotone along epimorphisms.**  A strict drop would make the
composite onto the last HN factor of the target a nonzero epimorphism that
`hom_eq_zero_to_semistable_of_μ_lt_μMinus` forces to vanish. -/
theorem μMinus_le_of_epi {X Y : A} (F : AbelianWeakHNFiltration W X)
    (G : AbelianWeakHNFiltration W Y) (p : X ⟶ Y) [Epi p] :
    F.μMinus ≤ G.μMinus := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨Q, q, hq, hQ, hQslope⟩ := G.exists_epi_to_semistable_μ_μMinus
  haveI := hq
  have hzero : p ≫ q = 0 :=
    F.hom_eq_zero_to_semistable_of_μ_lt_μMinus hQ (hQslope ▸ hlt) (p ≫ q)
  exact hQ.1 (IsZero.of_epi_eq_zero (p ≫ q) hzero)

end AbelianWeakHNFiltration

end CategoryTheory.Triangulated
