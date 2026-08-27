/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SubobjectCorrespondence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.WeakTruncation

/-!
# Truncating a weak HN filtration above an index

`WeakTruncation.lean` ported `restrict`, the truncation **below** an index, and recorded that
`tailAt` — the truncation **above** it, pushed down to the quotient — did not port, because its
two supporting lemmas were proved from `semiClosedUpperHalfPlane_ne_zero`.

`CategoryTheory/SubobjectCorrespondence.lean` removed that obstruction by proving both without
any charge.  This file is the port those lemmas unblock.

## What changed, and what did not

The strict `tailAt` (`Uniqueness/Tail.lean:35`) reads four charge-dependent facts.  Two of them
are replaced here by their charge-free counterparts:

| strict | here |
|---|---|
| `pullback_imageSubobject_eq Z` | `Abelian.pullback_imageSubobject_eq` |
| `cokernelPullbackIso Z` | `Abelian.cokernelPullbackIso` |
| `phase_cokernel_pullback_eq Z` | `slope_cokernel_pullback_eq`, below |
| `Z.phase_cokernel_ofLE_congr` | `W.slope_cokernel_ofLE_congr` (#789) |

`slope_cokernel_pullback_eq` is *shorter* than the phase version it replaces.  The strict proof
computes both charges and cancels with `linear_combination`; here the correspondence already
supplies an isomorphism of the two quotients, so the slopes agree by
`slope_eq_of_iso` and additivity is never mentioned.

Everything else — the chain, its strictness, its endpoints, the index arithmetic — is the strict
proof with `phase` renamed to `μ`, and is order-generic exactly as the rest of this development
turned out to be.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakStabilityFunctionOn

variable (W : WeakStabilityFunctionOn (abelianDatum A))

/-- **Consecutive pulled-back quotient subobjects have the slope of the corresponding quotient
factor.**  The correspondence gives an isomorphism of the two quotients outright, so this is
`slope_eq_of_iso` and nothing else. -/
theorem slope_cokernel_pullback_eq {E : A} (M : Subobject E)
    {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    W.slope (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h))) =
      W.slope (cokernel (Subobject.ofLE B₁ B₂ h)) :=
  W.slope_eq_of_iso (Abelian.cokernelPullbackIso M h)

/-- Weak semistability likewise transfers across the correspondence. -/
theorem isSemistable_cokernel_pullback_iff {E : A} (M : Subobject E)
    {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    W.IsSemistable (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h))) ↔
      W.IsSemistable (cokernel (Subobject.ofLE B₁ B₂ h)) :=
  ⟨W.isSemistable_of_iso (Abelian.cokernelPullbackIso M h),
   W.isSemistable_of_iso (Abelian.cokernelPullbackIso M h).symm⟩

end WeakStabilityFunctionOn

namespace AbelianWeakHNFiltration

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {E : A}

/-- **Cut a weak HN filtration above an index**: push the chain from index `k` onward down to
the quotient by the `k`-th term.  The factors are the original factors `k, …, n-1`, so the
slopes are the original slopes from `k` on.

The chain index is written `k + j` rather than `j + k` so that the successor step is
definitionally `(k + j) + 1`, which is what `factor_slope` and `factor_semistable` of the
original filtration are stated at. -/
def tailAt (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : k < F.n) :
    AbelianWeakHNFiltration W (cokernel (F.chain ⟨k, by lia⟩).arrow) where
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
      (Abelian.pullback_imageSubobject_eq hM₁).symm.trans
        (heq ▸ Abelian.pullback_imageSubobject_eq hM₂))
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
  μ := fun ⟨j, _⟩ => F.μ ⟨k + j, by lia⟩
  μ_anti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    exact F.μ_anti (Fin.mk_lt_mk.mpr (by
      have h' := Fin.mk_lt_mk.mp h
      lia))
  factor_slope := by
    intro ⟨j, hj⟩
    exact (W.slope_cokernel_pullback_eq (F.chain ⟨k, by lia⟩) _).symm.trans
      ((W.slope_cokernel_ofLE_congr
        (Abelian.pullback_imageSubobject_eq
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))
        (Abelian.pullback_imageSubobject_eq
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))).trans
        (F.factor_slope ⟨k + j, by lia⟩))
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
    exact W.isSemistable_of_iso
      (Abelian.cokernelPullbackIso (F.chain ⟨k, by lia⟩) hle)
      (W.isSemistable_cokernel_ofLE_congr
        (Abelian.pullback_imageSubobject_eq hM₁)
        (Abelian.pullback_imageSubobject_eq hM₂)
        (F.factor_semistable ⟨k + j, by lia⟩))

@[simp]
theorem tailAt_n (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : k < F.n) :
    (F.tailAt k hk).n = F.n - k := rfl

@[simp]
theorem tailAt_μ (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : k < F.n) (j : ℕ)
    (hj : j < F.n - k) :
    (F.tailAt k hk).μ ⟨j, hj⟩ = F.μ ⟨k + j, by lia⟩ := rfl

/-- The highest slope of a tail is the slope at the index it was cut at. -/
theorem tailAt_μPlus (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : k < F.n) :
    (F.tailAt k hk).μPlus = F.μ ⟨k, hk⟩ := rfl

/-- A tail ends where the filtration it was cut from ends. -/
theorem tailAt_μMinus (F : AbelianWeakHNFiltration W E) (k : ℕ) (hk : k < F.n) :
    (F.tailAt k hk).μMinus = F.μMinus :=
  congrArg F.μ (Fin.ext (by
    show k + (F.n - k - 1) = F.n - 1
    lia))

end AbelianWeakHNFiltration

end CategoryTheory.Triangulated
