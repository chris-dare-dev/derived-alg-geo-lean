/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Pretriangulated.Basic
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Model.Complexes

/-!
# `C^dg A` is pretriangulated

The witness for `dg-enhancements-e5`. Nothing here is a new construction: the
shift is `CochainComplex.shiftFunctor`, the cone is
`CochainComplex.mappingCone`, and every clause is discharged by the Mathlib
lemma written for it.

| clause | supplied by |
|---|---|
| `IsShiftBy.hom` | `Cocycle.rightShift` of `Cocycle.ofHom (𝟙 K)` |
| `IsShiftBy.hom_closed` | `Cocycle.δ_eq_zero` |
| `IsShiftBy.bijective` | `Cochain.rightUnshift_comp` |
| `IsConeOf.inl`, `.inr` | `mappingCone.inl`, `mappingCone.inr` |
| `IsConeOf.δ_inl` | `mappingCone.δ_inl` |
| `IsConeOf.bijective` | `mappingCone.id` and `inl_fst`/`inl_snd`/`inr_fst`/`inr_snd` |

## The shift bijection is not proved by exhibiting an inverse

`Cochain.rightUnshift_comp` says that unshifting a composite with the canonical
cochain returns the cochain you started with. So right composition is a
*section* of `Cochain.rightUnshift`, and `rightUnshift` is itself injective by
`Cochain.rightShift_rightUnshift`. A section of an injection is a bijection, so
both round trips reduce to those two Mathlib lemmas and no sign bookkeeping.

## Why the type ascriptions are written out

`Cdg A` is a type synonym for `CochainComplex A ℤ` and `Cdg.of` is the
identity, so `dgHom K L` and `HomComplex (of A K) (of A L)` are the same term
definitionally — but only after unfolding the synonym and the instance
projection. Elaboration does not unfold either while it is *choosing* an
instance, so `(of A K)⟦n⟧` written at the ascribed type `Cdg A` looks for
`HasShift (Cdg A) ℤ` and fails. Every shift is therefore ascribed at
`CochainComplex A ℤ` and converted afterwards.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex Limits

variable {A : Type u} [Category.{v} A] [Preadditive A]

namespace Cdg

/-- The shift of an object of `C^dg A`, as an object of `C^dg A`. -/
def shiftObj (K : Cdg A) (n : ℤ) : Cdg A := ((of A K)⟦n⟧ : CochainComplex A ℤ)

lemma of_shiftObj (K : Cdg A) (n : ℤ) :
    of A (shiftObj K n) = ((of A K)⟦n⟧ : CochainComplex A ℤ) := rfl

/-- The identity of `K`, right-shifted: the canonical closed cochain of degree
`-n` from `K` to `K⟦n⟧`. Degree `-n` rather than `n` because
`Homᵈ(K, L) = ∏ₚ Hom(Kᵖ, L^{p+d})` and `(K⟦n⟧)^q = K^{q+n}`. -/
noncomputable def shiftCocycle (K : Cdg A) (n : ℤ) :
    Cocycle (of A K) ((of A K)⟦n⟧) (-n) :=
  (Cocycle.ofHom (𝟙 (of A K))).rightShift n (-n) (by omega)

/-- Unshifting the canonical cochain returns the identity. -/
lemma rightUnshift_shiftCocycle (K : Cdg A) (n : ℤ) :
    (shiftCocycle K n).1.rightUnshift 0 (neg_add_cancel n) =
      Cochain.ofHom (𝟙 (of A K)) := by
  simp [shiftCocycle]

/-- `K⟦n⟧` is a shift of `K` by `n` in `C^dg A`. -/
noncomputable def isShiftBy (K : Cdg A) (n : ℤ) : IsShiftBy K n (shiftObj K n) where
  hom := (shiftCocycle K n).1
  hom_closed := Cocycle.δ_eq_zero _ _
  bijective W p q h := by
    have hqp : q + n = p := by omega
    have hpn : p + -n = q := by omega
    -- Right composition with the canonical cochain, then unshifting, is the
    -- identity: `rightUnshift_comp` moves the unshift onto the second factor,
    -- where it is `𝟙`.
    have hsec : ∀ f : Cochain (of A W) (of A K) p,
        (f.comp (shiftCocycle K n).1 hpn).rightUnshift p hqp = f := fun f => by
      rw [Cochain.rightUnshift_comp (a := n) f (shiftCocycle K n).1 hpn p hqp 0
        (neg_add_cancel n), rightUnshift_shiftCocycle, Cochain.comp_id]
    -- `rightUnshift` is injective because `rightShift` undoes it.
    have huinj : Function.Injective
        (fun γ : Cochain (of A W) ((of A K)⟦n⟧) q => γ.rightUnshift p hqp) := by
      intro γ₁ γ₂ hγ
      have := congrArg (fun δ => Cochain.rightShift δ n q hqp) hγ
      simpa only [Cochain.rightShift_rightUnshift] using this
    refine ⟨fun a b hab => ?_, fun c => ⟨Cochain.rightUnshift c p hqp, huinj (hsec _)⟩⟩
    exact (hsec a).symm.trans
      ((congrArg (fun γ => Cochain.rightUnshift γ p hqp) hab).trans (hsec b))

/-- A closed degree-zero cochain of `C^dg A`, as one of Mathlib's cocycles.
`cocycles K L` and `HomComplex.cocycle (of A K) (of A L) 0` are the same
subgroup of the same group, but of two different subgroup *terms*, so the
crossing is written by hand exactly as in `Model/Seam.lean`. -/
def coneCocycle {K L : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) : Cocycle (of A K) (of A L) 0 :=
  ⟨f, hf⟩

/-- The morphism of complexes a closed degree-zero cochain presents. -/
noncomputable def coneHom {K L : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) : of A K ⟶ of A L :=
  Cocycle.homOf (coneCocycle f hf)

@[simp]
lemma cochain_ofHom_coneHom {K L : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) : Cochain.ofHom (coneHom f hf) = f :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

section Cone

variable [HasBinaryBiproducts A]

/-- The mapping cone of a closed degree-zero cochain, as an object of `C^dg A`. -/
noncomputable def coneObj {K L : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) : Cdg A :=
  (mappingCone (coneHom f hf) : CochainComplex A ℤ)

/-- Recovering the first component of a split map into the cone: compose with
`fst`. The `inr` term dies by `inr_fst`. -/
lemma comp_fst_of_split {K L W : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) (p q : ℤ) (hq : p + 1 = q) (h1 : q + (-1 : ℤ) = p)
    (a : Cochain (of A W) (of A K) q) (b : Cochain (of A W) (of A L) p) :
    (a.comp (mappingCone.inl (coneHom f hf)) h1 +
        b.comp (Cochain.ofHom (mappingCone.inr (coneHom f hf))) (add_zero p)).comp
      (mappingCone.fst (coneHom f hf)).1 hq = a := by
  subst hq
  simp

/-- And the second component: compose with `snd`, where the `inl` term dies by
`inl_snd`. -/
lemma comp_snd_of_split {K L W : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) (p q : ℤ) (h1 : q + (-1 : ℤ) = p)
    (a : Cochain (of A W) (of A K) q) (b : Cochain (of A W) (of A L) p) :
    (a.comp (mappingCone.inl (coneHom f hf)) h1 +
        b.comp (Cochain.ofHom (mappingCone.inr (coneHom f hf))) (add_zero p)).comp
      (mappingCone.snd (coneHom f hf)) (add_zero p) = b := by
  obtain rfl : q = p + 1 := by omega
  simp

/-- Mathlib's mapping cone is a cone in the dg sense. Every field is one of its
lemmas: the splitting is `mappingCone.id` read forwards and
`inl_fst`/`inl_snd`/`inr_fst`/`inr_snd` read backwards. -/
noncomputable def isConeOf {K L : Cdg A} (f : (DGCategoryStruct.dgHom K L).X 0)
    (hf : f ∈ cocycles K L) : IsConeOf f (coneObj f hf) where
  inr := Cochain.ofHom (mappingCone.inr (coneHom f hf))
  inr_closed := by
    show δ 0 1 (Cochain.ofHom (mappingCone.inr (coneHom f hf))) = 0
    exact δ_ofHom _
  inl := mappingCone.inl (coneHom f hf)
  δ_inl := by
    show δ (-1) 0 (mappingCone.inl (coneHom f hf)) =
      f.comp (Cochain.ofHom (mappingCone.inr (coneHom f hf))) (add_zero 0)
    rw [mappingCone.δ_inl, Cochain.ofHom_comp, cochain_ofHom_coneHom]
  bijective W p q hq := by
    have h1 : q + (-1 : ℤ) = p := by omega
    show Function.Bijective
      (fun ab : Cochain (of A W) (of A K) q × Cochain (of A W) (of A L) p =>
        ab.1.comp (mappingCone.inl (coneHom f hf)) h1 +
          ab.2.comp (Cochain.ofHom (mappingCone.inr (coneHom f hf))) (add_zero p))
    refine ⟨fun ab ab' hh => Prod.ext ?_ ?_,
      fun γ => ⟨⟨γ.comp (mappingCone.fst (coneHom f hf)).1 hq,
        γ.comp (mappingCone.snd (coneHom f hf)) (add_zero p)⟩, ?_⟩⟩
    · rw [← comp_fst_of_split f hf p q hq h1 ab.1 ab.2,
        ← comp_fst_of_split f hf p q hq h1 ab'.1 ab'.2]
      exact congrArg (fun z => Cochain.comp z (mappingCone.fst (coneHom f hf)).1 hq) hh
    · rw [← comp_snd_of_split f hf p q h1 ab.1 ab.2,
        ← comp_snd_of_split f hf p q h1 ab'.1 ab'.2]
      exact congrArg
        (fun z => Cochain.comp z (mappingCone.snd (coneHom f hf)) (add_zero p)) hh
    · dsimp only
      -- `comp_assoc_of_second_degree_eq_neg_third_degree` does not fire on the
      -- `fst`-then-`inl` term: it wants the second degree spelled `-(-1)`, and
      -- `fst` has degree `1`. The general `comp_assoc` takes it.
      rw [Cochain.comp_assoc _ _ _ hq (by omega : (1 : ℤ) + -1 = 0)
        (by omega : p + 1 + (-1 : ℤ) = p)]
      simp only [Cochain.comp_assoc_of_third_is_zero_cochain]
      rw [← Cochain.comp_add, mappingCone.id, Cochain.comp_id]

/-- `C^dg A` is pretriangulated whenever `A` has a zero object and binary
biproducts: the shift is `isShiftBy`, the cone is `isConeOf`, and the zero
object is `A`'s. -/
instance isPretriangulated [HasZeroObject A] : IsPretriangulated (Cdg A) where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := CochainComplex A ℤ)
    refine ⟨(Z : Cdg A), ?_⟩
    show Cochain.ofHom (𝟙 Z) = 0
    simp [hZ.eq_of_src (𝟙 Z) 0]
  exists_shift K n := ⟨shiftObj K n, ⟨isShiftBy K n⟩⟩
  exists_cone f hf := ⟨coneObj f hf, ⟨isConeOf f hf⟩⟩

end Cone

end Cdg

end CategoryTheory
