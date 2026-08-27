/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.WeakCutoff

/-!
# Truncating a weak HN filtration, and the cut at a slope

This is `Truncation.lean` for the slope-indexed weak filtration, together with
`Splitting.lean`'s crossing index and the **sub** half of the splitting.

## What ports and what does not, stated precisely

`Truncation.lean` has two truncations and they behave differently under
weakening.

* `restrict` — read the chain **below** an index as a filtration of the term at
  that index.  It travels along `Subobject.map` of a monomorphism, uses only
  `Subobject.map_obj_injective` and the successive-quotient congruences, and
  mentions no charge.  It ports verbatim, and is `restrict` below.
* `Uniqueness/Tail.lean`'s `tailAt` — push the chain **above** an index down to
  the quotient.  It did **not** port when this file was written: its two
  supporting lemmas, `pullback_imageSubobject_eq` and `cokernelPullbackIso`, were
  proved from `semiClosedUpperHalfPlane_ne_zero` — a nonzero object has nonzero
  charge — which is precisely the implication weak stability drops, and which
  fails on the skyscraper.

  **That obstruction is gone.**  Both statements are true in any abelian
  category, being the subobject correspondence for a quotient, and
  `CategoryTheory/SubobjectCorrespondence.lean` proves them with no charge
  anywhere.  `WeakTail.lean` ports `tailAt` on top of them.

`exists_subobject_hnTors` below gives the torsion **subobject** of the splitting.
It is kept because it is the weaker statement and needs no truncation of the
quotient, but it is **superseded** by
`WeakStabilityFunctionOn.exists_subobject_hnTors_cokernel_hnFree`
(`WeakSplitting.lean`), which supplies both halves — and hence by the weak
`TorsionPair` in `Weak/Tilting/TorsionPair/WeakStabilityFunction.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianWeakHNFiltration

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {E : A}

/-- The `j`-th term of a weak HN filtration read as a subobject of the `k`-th
term, for `j ≤ k`. -/
def restrictChain (F : AbelianWeakHNFiltration W E) (k : ℕ) (hkn : k ≤ F.n)
    (j : ℕ) (hjk : j ≤ k) : Subobject (F.chain ⟨k, by lia⟩ : A) :=
  Subobject.mk (Subobject.ofLE (F.chain ⟨j, by lia⟩) (F.chain ⟨k, _⟩)
    (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr hjk)))

/-- Mapping a restricted term back along the arrow of the `k`-th term recovers
the original term. -/
theorem map_restrictChain (F : AbelianWeakHNFiltration W E) (k : ℕ)
    (hkn : k ≤ F.n) (j : ℕ) (hjk : j ≤ k) :
    (Subobject.map (F.chain ⟨k, by lia⟩).arrow).obj
        (F.restrictChain k hkn j hjk) = F.chain ⟨j, by lia⟩ := by
  rw [restrictChain, Subobject.map_mk]
  simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]

/-- The restricted chain is monotone, by composing the inclusions. -/
theorem restrictChain_le (F : AbelianWeakHNFiltration W E) (k : ℕ)
    (hkn : k ≤ F.n) {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) (hjk : j₂ ≤ k) :
    F.restrictChain k hkn j₁ (hj.trans hjk) ≤ F.restrictChain k hkn j₂ hjk :=
  Subobject.mk_le_mk_of_comm
    (Subobject.ofLE (F.chain ⟨j₁, by lia⟩) (F.chain ⟨j₂, by lia⟩)
      (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr hj)))
    (Subobject.ofLE_comp_ofLE _ _ _ _ _)

/-- **The chain below an index is a weak HN filtration of the term at that
index.**  The factors are the original factors `0, …, k-1`, so the slopes are
the original slopes up to `k`. -/
def restrict (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) :
    AbelianWeakHNFiltration W (F.chain ⟨k, by lia⟩ : A) where
  n := k
  nonempty := hk
  chain := fun ⟨j, _⟩ => F.restrictChain k hkn j (by lia)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    show F.restrictChain k hkn j (by lia) < F.restrictChain k hkn (j + 1) (by lia)
    refine lt_of_le_of_ne (F.restrictChain_le k hkn (by lia) (by lia)) ?_
    intro heq
    have hmapped :=
      congrArg (Subobject.map (F.chain ⟨k, by lia⟩).arrow).obj heq
    rw [F.map_restrictChain k hkn j (by lia),
      F.map_restrictChain k hkn (j + 1) (by lia)] at hmapped
    exact absurd hmapped
      (ne_of_lt (F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))))
  chain_bot := by
    apply Subobject.map_obj_injective (F.chain ⟨k, by lia⟩).arrow
    rw [F.map_restrictChain k hkn 0 (by lia), Subobject.map_bot, F.chain_bot]
  chain_top := by
    apply Subobject.map_obj_injective (F.chain ⟨k, by lia⟩).arrow
    rw [F.map_restrictChain k hkn k le_rfl, Subobject.map_top, Subobject.mk_arrow]
  μ := fun ⟨j, _⟩ => F.μ ⟨j, by lia⟩
  μ_anti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    exact F.μ_anti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp h))
  factor_slope := by
    intro ⟨j, hj⟩
    exact ((W.slope_cokernel_mapMono_eq (F.chain ⟨k, by lia⟩).arrow _).symm.trans
      ((W.slope_cokernel_ofLE_congr
        (F.map_restrictChain k hkn j (by lia))
        (F.map_restrictChain k hkn (j + 1) (by lia))).trans
        (F.factor_slope ⟨j, by lia⟩)))
  factor_semistable := by
    intro ⟨j, hj⟩
    exact W.isSemistable_of_iso
      (StabilityFunction.Subobject.cokernelMapMonoIso (F.chain ⟨k, by lia⟩).arrow _)
      (W.isSemistable_cokernel_ofLE_congr
        (F.map_restrictChain k hkn j (by lia))
        (F.map_restrictChain k hkn (j + 1) (by lia))
        (F.factor_semistable ⟨j, by lia⟩))

@[simp]
theorem restrict_n (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) : (F.restrict k hk hkn).n = k :=
  rfl

/-- A restriction starts where the filtration it was cut from starts. -/
theorem restrict_μPlus (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) : (F.restrict k hk hkn).μPlus = F.μPlus :=
  rfl

/-- The lowest slope of a restriction is the last slope below the cut. -/
theorem restrict_μMinus (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) :
    (F.restrict k hk hkn).μMinus = F.μ ⟨k - 1, by lia⟩ :=
  rfl

/-- **Transport along an isomorphism.**  The chain is carried by
`Subobject.map` of the isomorphism, which leaves every successive quotient
isomorphic to the original, so the slopes are literally the same function. -/
def ofIso (F : AbelianWeakHNFiltration W E) {E' : A} (e : E ≅ E') :
    AbelianWeakHNFiltration W E' where
  n := F.n
  nonempty := F.nonempty
  chain := fun j => (Subobject.map e.hom).obj (F.chain j)
  chain_strictMono :=
    ((Subobject.map e.hom).monotone.strictMono_of_injective
      (Subobject.map_obj_injective e.hom)).comp F.chain_strictMono
  chain_bot := by
    rw [F.chain_bot]
    exact Subobject.map_bot e.hom
  chain_top := by
    rw [F.chain_top, Subobject.map_top]
    exact (Subobject.isIso_iff_mk_eq_top e.hom).1 inferInstance
  μ := F.μ
  μ_anti := F.μ_anti
  factor_slope := fun j =>
    (W.slope_cokernel_mapMono_eq e.hom _).trans (F.factor_slope j)
  factor_semistable := fun j =>
    (W.isSemistable_cokernel_mapMono_iff e.hom _).2 (F.factor_semistable j)

@[simp]
theorem ofIso_μPlus (F : AbelianWeakHNFiltration W E) {E' : A} (e : E ≅ E') :
    (F.ofIso e).μPlus = F.μPlus :=
  rfl

@[simp]
theorem ofIso_μMinus (F : AbelianWeakHNFiltration W E) {E' : A} (e : E ≅ E') :
    (F.ofIso e).μMinus = F.μMinus :=
  rfl

/-- **The crossing index.**  The HN slopes strictly decrease, so the indices
whose slope exceeds `μ₀` are an initial segment; this names its length.  The
argument is `Nat.find` on the order alone, so `WithTop ℝ` serves as well as
`ℝ`. -/
theorem exists_crossIndex (F : AbelianWeakHNFiltration W E) (μ₀ : WithTop ℝ) :
    ∃ k ≤ F.n, (∀ j : Fin F.n, j.val < k → μ₀ < F.μ j) ∧
      (∀ j : Fin F.n, k ≤ j.val → F.μ j ≤ μ₀) := by
  classical
  by_cases hex : ∃ m : ℕ, ∃ hm : m < F.n, F.μ ⟨m, hm⟩ ≤ μ₀
  · obtain ⟨hlt, hle⟩ := Nat.find_spec hex
    refine ⟨Nat.find hex, le_of_lt hlt, ?_, ?_⟩
    · intro j hj
      by_contra hcon
      exact Nat.find_min hex hj ⟨j.isLt, by simpa using not_lt.mp hcon⟩
    · intro j hj
      exact le_trans (F.μ_anti.antitone (Fin.le_def.mpr hj)) hle
  · refine ⟨F.n, le_rfl, ?_, ?_⟩
    · intro j _
      by_contra hcon
      exact hex ⟨j.val, j.isLt, by simpa using not_lt.mp hcon⟩
    · intro j hj
      exact absurd j.isLt (not_lt.mpr hj)

end AbelianWeakHNFiltration

namespace WeakStabilityFunctionOn

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {μ₀ : WithTop ℝ}

/-- The torsion class is closed under isomorphism. -/
theorem hnTors_of_iso {E E' : A} (e : E ≅ E') (h : E ∈ hnTors W μ₀) :
    E' ∈ hnTors W μ₀ := by
  rcases h with h0 | ⟨F, hF⟩
  · exact Or.inl (h0.of_iso e.symm)
  · exact Or.inr ⟨F.ofIso e, by simpa using hF⟩

/-- The torsion-free class is closed under isomorphism. -/
theorem hnFree_of_iso {E E' : A} (e : E ≅ E') (h : E ∈ hnFree W μ₀) :
    E' ∈ hnFree W μ₀ := by
  rcases h with h0 | ⟨F, hF⟩
  · exact Or.inl (h0.of_iso e.symm)
  · exact Or.inr ⟨F.ofIso e, by simpa using hF⟩

/-- **The torsion subobject of the splitting.**  Cutting an HN filtration at its
crossing index gives a subobject in `T μ₀`.

This is one half of `exists_subobject_hnTors_cokernel_hnFree`, and is superseded
by it: `WeakSplitting.lean` now supplies the torsion-free quotient too.  Kept
because it is the weaker statement and does not truncate the quotient. -/
theorem exists_subobject_hnTors (hHN : W.HasHNProperty) (E : A) :
    ∃ T : Subobject E, ((T : A) ∈ hnTors W μ₀) := by
  by_cases hE : IsZero E
  · exact ⟨⊥, Or.inl ((StabilityFunction.subobject_isZero_iff_eq_bot
      (⊥ : Subobject E)).2 rfl)⟩
  obtain ⟨F⟩ := hHN E hE
  obtain ⟨k, hkn, hlow, _⟩ := F.exists_crossIndex μ₀
  refine ⟨F.chain ⟨k, by lia⟩, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl ((StabilityFunction.subobject_isZero_iff_eq_bot _).2 F.chain_bot)
  · refine Or.inr ⟨F.restrict k hk hkn, ?_⟩
    rw [F.restrict_μMinus k hk hkn]
    exact hlow ⟨k - 1, by lia⟩ (by lia)

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
