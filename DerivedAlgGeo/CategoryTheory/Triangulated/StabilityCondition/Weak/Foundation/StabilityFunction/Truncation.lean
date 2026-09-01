/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Tail

/-!
# Carrying an HN filtration along a monomorphism

Both constructions here move a chain by `Subobject.map` of a mono.

`Uniqueness/Tail.lean` owns `tailAt`, which pushes the chain above an index
down to the quotient by that index.  This file owns the other half — `restrict`,
the chain below an index as an HN filtration of the term at that index — and
`ofIso`, the transport along an isomorphism that the two classes at a cutoff
need in order to be closed under isomorphism.

The two together cut a filtration in half at any index, and the halves keep the
original factors — so their phases are read off `F.phase` with no new
computation.  That is what makes a cut at the index where the phases cross a
number produce one object with all phases above it and one with all phases at
or below it.

The chain is carried across by `Subobject.map` along the arrow of the term:
`map_restrictChain` says the mapped-back chain is the original one, and
`MonoDescent.lean` then supplies the successive quotients unchanged.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E : A}

/-- The `j`-th term of an HN filtration read as a subobject of the `k`-th
term, for `j ≤ k`. -/
def restrictChain (F : AbelianHNFiltration Z E) (k : ℕ) (hkn : k ≤ F.n)
    (j : ℕ) (hjk : j ≤ k) : Subobject (F.chain ⟨k, by lia⟩ : A) :=
  Subobject.mk (Subobject.ofLE (F.chain ⟨j, by lia⟩) (F.chain ⟨k, _⟩)
    (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr hjk)))

/-- Mapping a restricted term back along the arrow of the `k`-th term recovers
the original term. -/
theorem map_restrictChain (F : AbelianHNFiltration Z E) (k : ℕ) (hkn : k ≤ F.n)
    (j : ℕ) (hjk : j ≤ k) :
    (Subobject.map (F.chain ⟨k, by lia⟩).arrow).obj (F.restrictChain k hkn j hjk) =
      F.chain ⟨j, by lia⟩ := by
  rw [restrictChain, Subobject.map_mk]
  simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]

/-- The restricted chain is monotone, by composing the inclusions. -/
theorem restrictChain_le (F : AbelianHNFiltration Z E) (k : ℕ) (hkn : k ≤ F.n)
    {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) (hjk : j₂ ≤ k) :
    F.restrictChain k hkn j₁ (hj.trans hjk) ≤ F.restrictChain k hkn j₂ hjk :=
  Subobject.mk_le_mk_of_comm
    (Subobject.ofLE (F.chain ⟨j₁, by lia⟩) (F.chain ⟨j₂, by lia⟩)
      (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr hj)))
    (Subobject.ofLE_comp_ofLE _ _ _ _ _)

/-- **The chain below an index is an HN filtration of the term at that
index.**  The factors are the original factors `0, …, k-1`, so the phases are
the original phases up to `k`. -/
def restrict (F : AbelianHNFiltration Z E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) : AbelianHNFiltration Z (F.chain ⟨k, by lia⟩ : A) where
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
  phase := fun ⟨j, _⟩ => F.phase ⟨j, by lia⟩
  phase_strictAnti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp h))
  factor_phase := by
    intro ⟨j, hj⟩
    exact ((Z.phase_cokernel_mapMono_eq (F.chain ⟨k, by lia⟩).arrow _).symm.trans
      ((Z.phase_cokernel_ofLE_congr
        (F.map_restrictChain k hkn j (by lia))
        (F.map_restrictChain k hkn (j + 1) (by lia))).trans
        (F.factor_phase ⟨j, by lia⟩)))
  factor_semistable := by
    intro ⟨j, hj⟩
    exact Z.isSemistable_of_iso
      (StabilityFunction.Subobject.cokernelMapMonoIso (F.chain ⟨k, by lia⟩).arrow _)
      (Z.isSemistable_cokernel_ofLE_congr
        (F.map_restrictChain k hkn j (by lia))
        (F.map_restrictChain k hkn (j + 1) (by lia))
        (F.factor_semistable ⟨j, by lia⟩))

@[simp]
theorem restrict_n (F : AbelianHNFiltration Z E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) : (F.restrict k hk hkn).n = k :=
  rfl

/-- A restriction starts where the filtration it was cut from starts. -/
theorem restrict_phiPlus (F : AbelianHNFiltration Z E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) : (F.restrict k hk hkn).phiPlus = F.phiPlus :=
  rfl

/-- The lowest phase of a restriction is the last phase below the cut. -/
theorem restrict_phiMinus (F : AbelianHNFiltration Z E) (k : ℕ) (hk : 0 < k)
    (hkn : k ≤ F.n) :
    (F.restrict k hk hkn).phiMinus = F.phase ⟨k - 1, by lia⟩ :=
  rfl

/-- **Transport along an isomorphism.**  The chain is carried by
`Subobject.map` of the isomorphism, which leaves every successive quotient
isomorphic to the original, so the phases are literally the same function. -/
def ofIso (F : AbelianHNFiltration Z E) {E' : A} (e : E ≅ E') :
    AbelianHNFiltration Z E' where
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
  phase := F.phase
  phase_strictAnti := F.phase_strictAnti
  factor_phase := fun j =>
    (Z.phase_cokernel_mapMono_eq e.hom _).trans (F.factor_phase j)
  factor_semistable := fun j =>
    (Z.isSemistable_cokernel_mapMono_iff e.hom _).2 (F.factor_semistable j)

@[simp]
theorem ofIso_phiPlus (F : AbelianHNFiltration Z E) {E' : A} (e : E ≅ E') :
    (F.ofIso e).phiPlus = F.phiPlus :=
  rfl

@[simp]
theorem ofIso_phiMinus (F : AbelianHNFiltration Z E) {E' : A} (e : E ≅ E') :
    (F.ofIso e).phiMinus = F.phiMinus :=
  rfl

end AbelianHNFiltration

end CategoryTheory.Triangulated
