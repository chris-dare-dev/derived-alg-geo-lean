/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The induction principle for quasi-compact opens of a quasi-separated scheme

Mathlib's `compact_open_induction_on` proves a property of a quasi-compact open by adding one
affine open at a time. On a quasi-separated scheme the Mayer–Vietoris arguments of cohomology
need a stronger step, which also knows the property on the intersection: if `P` holds for every
affine open, and `P U`, `P V` and `P (U ⊓ V)` give `P (U ⊔ V)` whenever `U` is quasi-compact and
`V` is affine, then `P` holds for every quasi-compact open (Stacks, Lemma 30.4.1, Tag 08DR).

## Main results

* `AlgebraicGeometry.Scheme.induction_on_isCompact`: the induction principle for the
  quasi-compact opens of a quasi-separated scheme (Stacks, Tag 08DR).
* `AlgebraicGeometry.Scheme.induction_on_qcqs`: its value at `⊤` for a quasi-compact and
  quasi-separated scheme.

## Implementation notes

Stacks first proves the property for quasi-compact opens that are separated, and then for all
quasi-compact opens. The proof here first proves it for quasi-compact opens contained in an
affine open `V₀`. Such an open is a finite union of affine opens contained in `V₀`, and two of
these meet in an affine open, by `isAffineHom_diagonal_iff` applied to the identity of `X`. The
induction over a finite union `⨆ i ∈ s, i` is run for all the unions `⨆ i ∈ s, i ⊓ t`, `t` an
affine open in `V₀`, at once: the intersection needed by the step is the union for `s` and
another `t`. In the second induction, for an arbitrary finite union of affine opens, the
intersection with the new affine open `V` is quasi-compact, by quasi-separatedness, and is
contained in `V`, so the first induction applies to it.

## References

* [The Stacks project, Lemma 30.4.1](https://stacks.math.columbia.edu/tag/08DR)

## Tags

quasi-separated scheme, quasi-compact open, induction principle, Mayer–Vietoris
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- Two affine opens contained in a common affine open meet in an affine open. -/
private theorem isAffineOpen_inf_of_le {V₀ V₁ V₂ : X.Opens} (h₀ : IsAffineOpen V₀)
    (h₁ : IsAffineOpen V₁) (h₂ : IsAffineOpen V₂) (le₁ : V₁ ≤ V₀) (le₂ : V₂ ≤ V₀) :
    IsAffineOpen (V₁ ⊓ V₂) :=
  isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal (𝟙 X))) V₀ h₀
    V₁ le₁ V₂ le₂ h₁ h₂

/-- A finite union of affine opens is quasi-compact. -/
private theorem isCompact_biSup {s : Finset X.Opens} {g : X.Opens → X.Opens}
    (hs : ∀ i ∈ s, IsAffineOpen (g i)) : IsCompact ((⨆ i ∈ s, g i : X.Opens) : Set X) := by
  simp only [Opens.coe_iSup]
  exact s.isCompact_biUnion fun i hi ↦ (hs i hi).isCompact

section

variable (P : X.Opens → Prop) (affine : ∀ U, IsAffineOpen U → P U)
  (union : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V → P U → P V → P (U ⊓ V) →
    P (U ⊔ V))
include affine union

/-- The induction principle inside an affine open `V₀`, for the unions `⨆ i ∈ s, i ⊓ t` of a
finite family `s` of affine opens in `V₀` cut down by an affine open `t` in `V₀`. -/
private theorem induction_on_biSup_inf {V₀ : X.Opens} (h₀ : IsAffineOpen V₀) (s : Finset X.Opens)
    (hs : ∀ i ∈ s, IsAffineOpen i ∧ i ≤ V₀) (t : X.Opens) (ht : IsAffineOpen t) (htV : t ≤ V₀) :
    P (⨆ i ∈ s, i ⊓ t) := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simpa using affine ⊥ (isAffineOpen_bot X)
  | insert a s ha ih =>
    have hs' : ∀ i ∈ s, IsAffineOpen i ∧ i ≤ V₀ := fun i hi ↦ hs i (Finset.mem_insert_of_mem hi)
    have haff : IsAffineOpen (a ⊓ t) := isAffineOpen_inf_of_le h₀ (hs a (by simp)).1 ht
      (hs a (by simp)).2 htV
    have hinf : (⨆ i ∈ s, i ⊓ t) ⊓ (a ⊓ t) = ⨆ i ∈ s, i ⊓ (a ⊓ t) := by
      rw [iSup₂_inf_eq]
      refine iSup_congr fun i ↦ iSup_congr fun _ ↦ ?_
      rw [inf_assoc, inf_comm t, inf_assoc, inf_idem]
    rw [Finset.iSup_insert, sup_comm]
    refine union _ _ (isCompact_biSup fun i hi ↦ isAffineOpen_inf_of_le h₀ (hs' i hi).1 ht
      (hs' i hi).2 htV) haff (ih hs' t ht htV) (affine _ haff) ?_
    rw [hinf]
    exact ih hs' (a ⊓ t) haff (inf_le_right.trans htV)

/-- The induction principle for the quasi-compact opens contained in an affine open. -/
private theorem induction_on_isCompact_of_le {V₀ : X.Opens} (h₀ : IsAffineOpen V₀) (W : X.Opens)
    (hW : IsCompact (W : Set X)) (hWV : W ≤ V₀) : P W := by
  classical
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  have key := induction_on_biSup_inf P affine union h₀ (hs.toFinset.image Subtype.val)
    (fun i hi ↦ by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.2, (le_biSup (fun i : X.affineOpens ↦ (i : X.Opens))
        (hs.mem_toFinset.mp hj)).trans hWV⟩) V₀ h₀ le_rfl
  convert key using 1
  refine le_antisymm (iSup₂_le fun j hj ↦ ?_) (iSup₂_le fun i hi ↦ ?_)
  · refine le_trans ?_ (le_biSup _ (Finset.mem_image_of_mem Subtype.val (hs.mem_toFinset.mpr hj)))
    exact le_inf le_rfl ((le_biSup (fun i : X.affineOpens ↦ (i : X.Opens)) hj).trans hWV)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact inf_le_left.trans (le_biSup (fun i : X.affineOpens ↦ (i : X.Opens))
      (hs.mem_toFinset.mp hj))

/-- **The induction principle for quasi-separated schemes** (Stacks, Lemma 30.4.1, Tag 08DR).
Let `X` be quasi-separated and `P` a property of opens of `X`. Assume `P` holds for every affine
open, and that `P U`, `P V` and `P (U ⊓ V)` imply `P (U ⊔ V)` whenever `U` is quasi-compact and
`V` is affine. Then `P` holds for every quasi-compact open of `X`. -/
@[stacks 08DR]
theorem induction_on_isCompact [QuasiSeparatedSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) : P W := by
  classical
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  suffices key : ∀ s : Finset X.Opens, (∀ i ∈ s, IsAffineOpen i) → P (⨆ i ∈ s, i) by
    convert key (hs.toFinset.image Subtype.val) (fun i hi ↦ by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact j.2) using 1
    refine le_antisymm (iSup₂_le fun j hj ↦ ?_) (iSup₂_le fun i hi ↦ ?_)
    · exact le_biSup (fun i : X.Opens ↦ i)
        (Finset.mem_image_of_mem Subtype.val (hs.mem_toFinset.mpr hj))
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact le_biSup (fun i : X.affineOpens ↦ (i : X.Opens)) (hs.mem_toFinset.mp hj)
  intro s hs
  induction s using Finset.induction_on with
  | empty => simpa using affine ⊥ (isAffineOpen_bot X)
  | insert a s ha ih =>
    have hs' : ∀ i ∈ s, IsAffineOpen i := fun i hi ↦ hs i (Finset.mem_insert_of_mem hi)
    have ha' : IsAffineOpen a := hs a (by simp)
    have hU : IsCompact ((⨆ i ∈ s, i : X.Opens) : Set X) := isCompact_biSup hs'
    rw [Finset.iSup_insert, sup_comm]
    refine union _ _ hU ha' (ih hs') (affine a ha') ?_
    exact induction_on_isCompact_of_le P affine union ha' _
      (QuasiSeparatedSpace.inter_isCompact _ _ (Opens.isOpen _) hU a.isOpen ha'.isCompact)
      inf_le_right

end

/-- **The induction principle for quasi-compact and quasi-separated schemes** (Stacks,
Lemma 30.4.1, Tag 08DR): under the hypotheses of `Scheme.induction_on_isCompact`, the property
holds for `X` itself. -/
@[stacks 08DR]
theorem induction_on_qcqs (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : X.Opens → Prop) (affine : ∀ U, IsAffineOpen U → P U)
    (union : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V → P U → P V → P (U ⊓ V) →
      P (U ⊔ V)) :
    P ⊤ :=
  induction_on_isCompact P affine union ⊤ (by simpa using isCompact_univ)

end Scheme

end AlgebraicGeometry
