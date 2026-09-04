/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Extrema

/-!
# The tail filtration and uniqueness of length

This file owns the induction step: removing the first factor of a nontrivial HN
filtration and pushing the remaining chain to the quotient by its first nonzero
term, together with the length bookkeeping that makes the number of factors an
invariant of the object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

/-- Cut an HN filtration above an index: push the chain from index `k` onward
down to the quotient by the `k`-th term.  The factors are the original factors
`k, …, n-1`, so the phases are the original phases from `k` on.

The chain index is written `k + j` rather than `j + k` so that the successor
step is definitionally `(k + j) + 1`, which is what `factor_phase` and
`factor_semistable` of the original filtration are stated at. -/
noncomputable def tailAt {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (k : ℕ) (hk : k < F.n) :
    AbelianHNFiltration Z (cokernel (F.chain ⟨k, by lia⟩).arrow) where
  n := F.n - k
  nonempty := by lia
  chain := fun ⟨j, _⟩ => imageSubobject
    ((F.chain ⟨k + j, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨k, by lia⟩).arrow)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change imageSubobject ((F.chain ⟨k + j, by lia⟩).arrow ≫
        cokernel.π (F.chain ⟨k, by lia⟩).arrow) <
      imageSubobject ((F.chain ⟨k + j + 1, by lia⟩).arrow ≫
        cokernel.π (F.chain ⟨k, by lia⟩).arrow)
    have hM₁ : F.chain ⟨k, by lia⟩ ≤ F.chain ⟨k + j, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hM₂ : F.chain ⟨k, by lia⟩ ≤ F.chain ⟨k + j + 1, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hstep : F.chain ⟨k + j, by lia⟩ < F.chain ⟨k + j + 1, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    have hle : imageSubobject ((F.chain ⟨k + j, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow) ≤
        imageSubobject ((F.chain ⟨k + j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow) := by
      rw [show (F.chain ⟨k + j, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow =
        Subobject.ofLE _ _ hstep.le ≫
          ((F.chain ⟨k + j + 1, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨k, by lia⟩).arrow) by
        rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact lt_of_le_of_ne hle (fun heq => (ne_of_lt hstep) <|
      (pullback_imageSubobject_eq Z hM₁).symm.trans
        (heq ▸ pullback_imageSubobject_eq Z hM₂))
  chain_bot := by
    change imageSubobject ((F.chain ⟨k, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨k, by lia⟩).arrow) = ⊥
    rw [cokernel.condition, imageSubobject_zero]
  chain_top := by
    change imageSubobject ((F.chain ⟨k + (F.n - k), by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨k, by lia⟩).arrow) = ⊤
    have htop : F.chain ⟨k + (F.n - k), by lia⟩ = ⊤ :=
      (congrArg F.chain (Fin.ext (Nat.add_sub_cancel' (by lia)))).trans F.chain_top
    rw [htop]
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    rw [imageSubobject_iso_comp]
    exact StabilityFunction.imageSubobject_eq_top_of_epi _
  phase := fun ⟨j, _⟩ => F.phase ⟨k + j, by lia⟩
  phase_strictAnti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by
      have h' := Fin.mk_lt_mk.mp h
      lia))
  factor_phase := by
    intro ⟨j, hj⟩
    exact (phase_cokernel_pullback_eq Z (F.chain ⟨k, by lia⟩) _).symm.trans
      ((Z.phase_cokernel_ofLE_congr
        (pullback_imageSubobject_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))
        (pullback_imageSubobject_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))).trans
        (F.factor_phase ⟨k + j, by lia⟩))
  factor_semistable := by
    intro ⟨j, hj⟩
    have hM₁ : F.chain ⟨k, by lia⟩ ≤ F.chain ⟨k + j, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hM₂ : F.chain ⟨k, by lia⟩ ≤ F.chain ⟨k + j + 1, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hstep : F.chain ⟨k + j, by lia⟩ < F.chain ⟨k + j + 1, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    have hle : imageSubobject ((F.chain ⟨k + j, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow) ≤
        imageSubobject ((F.chain ⟨k + j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow) := by
      rw [show (F.chain ⟨k + j, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow =
        Subobject.ofLE _ _ hstep.le ≫
          ((F.chain ⟨k + j + 1, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨k, by lia⟩).arrow) by
        rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    have hstrict : imageSubobject ((F.chain ⟨k + j, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow) <
        imageSubobject ((F.chain ⟨k + j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by lia⟩).arrow) :=
      lt_of_le_of_ne hle (fun heq => (ne_of_lt hstep) <|
        (pullback_imageSubobject_eq Z hM₁).symm.trans
          (heq ▸ pullback_imageSubobject_eq Z hM₂))
    exact Z.isSemistable_of_iso
      (cokernelPullbackIso Z (F.chain ⟨k, by lia⟩) hstrict)
      (Z.isSemistable_cokernel_ofLE_congr
        (pullback_imageSubobject_eq Z hM₁)
        (pullback_imageSubobject_eq Z hM₂)
        (F.factor_semistable ⟨k + j, by lia⟩))

@[simp]
theorem tailAt_n {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (k : ℕ) (hk : k < F.n) :
    (F.tailAt k hk).n = F.n - k :=
  rfl

@[simp]
theorem tailAt_phase {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (k : ℕ) (hk : k < F.n) (j : ℕ)
    (hj : j < F.n - k) :
    (F.tailAt k hk).phase ⟨j, hj⟩ = F.phase ⟨k + j, by lia⟩ :=
  rfl

/-- The highest phase of a tail is the phase at the index it was cut at. -/
theorem tailAt_phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (k : ℕ) (hk : k < F.n) :
    (F.tailAt k hk).phiPlus = F.phase ⟨k, hk⟩ :=
  rfl

/-- A tail ends where the filtration it was cut from ends. -/
theorem tailAt_phiMinus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (k : ℕ) (hk : k < F.n) :
    (F.tailAt k hk).phiMinus = F.phiMinus :=
  congrArg F.phase (Fin.ext (by
    show k + (F.n - k - 1) = F.n - 1
    lia))

/-- Remove the first factor of a nontrivial HN filtration and push the
remaining chain to the quotient by its first nonzero term. -/
noncomputable def tail {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn : 2 ≤ F.n) :
    AbelianHNFiltration Z (cokernel (F.chain ⟨1, by lia⟩).arrow) :=
  F.tailAt 1 (by lia)

@[simp]
theorem tail_n {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn : 2 ≤ F.n) :
    (F.tail hn).n = F.n - 1 :=
  rfl

/-- Transporting an owner HN filtration along equality of its ambient objects
preserves the number of factors. -/
theorem transport_n {Z : StabilityFunction A} {E₁ E₂ : A}
    (h : E₁ = E₂) (F : AbelianHNFiltration Z E₁) :
    (h ▸ F).n = F.n := by
  subst h
  rfl

/-- Owner HN filtrations have a unique length when every object has a finite
subobject lattice.  The proof recursively removes the intrinsic first HN term
and descends to its strictly smaller quotient subobject lattice. -/
theorem n_eq {Z : StabilityFunction A} {E : A} (hE : ¬IsZero E)
    (hFinite : ∀ X : A, Finite (Subobject X))
    (F G : AbelianHNFiltration Z E) : F.n = G.n := by
  suffices main : ∀ k : ℕ, ∀ X : A, ¬IsZero X →
      Nat.card (Subobject X) ≤ k →
      ∀ F₁ F₂ : AbelianHNFiltration Z X, F₁.n = F₂.n by
    exact main _ E hE le_rfl F G
  intro k
  induction k with
  | zero =>
      intro X hX hcard F₁ F₂
      haveI := hFinite X
      haveI := Fintype.ofFinite (Subobject X)
      have hpositive : 0 < Nat.card (Subobject X) := by
        rw [Nat.card_eq_fintype_card]
        haveI : Nonempty (Subobject X) := ⟨⊥⟩
        exact Fintype.card_pos
      lia
  | succ k ih =>
      intro X hX hcard F₁ F₂
      haveI := hFinite X
      by_cases hsemistable : Z.IsSemistable X
      · exact (F₁.n_eq_one_of_semistable hsemistable).trans
          (F₂.n_eq_one_of_semistable hsemistable).symm
      · have hn₁ : 2 ≤ F₁.n := F₁.two_le_n_of_not_isSemistable hsemistable
        have hn₂ : 2 ≤ F₂.n := F₂.two_le_n_of_not_isSemistable hsemistable
        let M := F₁.chain ⟨1, by lia⟩
        have hMnonzero : M ≠ ⊥ := F₁.chain_one_ne_bot
        have hMproper : M ≠ ⊤ := by
          intro htop
          have hlt : F₁.chain ⟨1, by lia⟩ < F₁.chain ⟨F₁.n, by lia⟩ :=
            F₁.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
          change F₁.chain ⟨1, by lia⟩ = ⊤ at htop
          rw [F₁.chain_top, htop] at hlt
          exact lt_irrefl _ hlt
        have hcardQuotient : Nat.card (Subobject (cokernel M.arrow)) <
            Nat.card (Subobject X) := card_subobject_cokernel_lt hMnonzero
        have hfirst : F₂.chain ⟨1, by lia⟩ = M :=
          (F₁.chain_one_eq F₂).symm
        have hquotient : cokernel (F₂.chain ⟨1, by lia⟩).arrow =
            cokernel M.arrow := congrArg (fun S => cokernel (Subobject.arrow S)) hfirst
        have htail : (F₁.tail hn₁).n = (hquotient ▸ F₂.tail hn₂).n :=
          ih (cokernel M.arrow)
            (StabilityFunction.cokernel_not_isZero_of_ne_top hMproper)
            (by lia) _ _
        rw [F₁.tail_n, transport_n, F₂.tail_n] at htail
        lia

end AbelianHNFiltration

end CategoryTheory.Triangulated
