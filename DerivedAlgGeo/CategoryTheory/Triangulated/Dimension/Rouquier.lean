/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import Mathlib.Data.ENat.Lattice

/-!
# Rouquier dimension

`CategoryTheory.Triangulated.rouquierDim C` is the infimum of the generation times from
singleton object properties to the whole category. Thus the infimum ranges over individual
objects, not arbitrary object properties. It is a scalar definition and does
not choose a distinguished object attaining the infimum. Since a category with
a zero object is nonempty and `ℕ∞` is well ordered, a minimizing object does
exist existentially; the finite-witness results below state their witnesses
separately.

The indexing has no offset from Rouquier's `⟨G⟩_{n+1}` convention:
`CategoryTheory.ObjectProperty.triangEnvelopeIter_zero` identifies stage zero with the shifts,
finite binary products, and retracts of `G`, which is `⟨G⟩₁`;
`CategoryTheory.ObjectProperty.triangEnvelopeIter_succ`
adds one extension at the next stage. The equation
`CategoryTheory.ObjectProperty.triangEnvelopeIter_add` is a conditional decomposition of
envelope stages under `[IsTriangulated C]`. It is not a generation-time composition or
subadditivity law; that composition result is separate work in issue #920.

## Main definitions

* `CategoryTheory.Triangulated.rouquierDim C`: the infimum of generation times over singleton object
  properties.

## Main results

* `CategoryTheory.Triangulated.rouquierDim_le_coe_iff`: a finite bound is witnessed by one
  object whose envelope reaches the whole category at that stage.
* `CategoryTheory.Triangulated.rouquierDim_ne_top_iff_exists_strong` and
  `CategoryTheory.Triangulated.exists_isClassicalTriangulatedGenerator_of_rouquierDim_ne_top`:
  finite Rouquier dimension is equivalent to strong generation and implies
  classical generation.
* `CategoryTheory.Triangulated.rouquierDim_eq_zero_iff`: dimension zero is generation using shifts,
  finite binary products, and retracts, without extension steps.

## Implementation notes

The category's zero object makes the index type nonempty. Since `ℕ∞` is
well ordered, the infimum is attained by some object, although the scalar
definition does not select that object. The finite-bound and strong-generator
theorems extract a witness when one is needed.

## References

* Raphaël Rouquier, *Dimensions of triangulated categories*.

## Tags

Rouquier dimension, triangulated category, strong generator, classical generator
-/

universe v u

namespace CategoryTheory.Triangulated

open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The scalar invariant leaves the minimizing object out of the API; the zero-object
hypothesis makes the index nonempty, so the infimum is attained in `ℕ∞`. -/
noncomputable def rouquierDim : ℕ∞ :=
  ⨅ G : C, (ObjectProperty.singleton G).generationTime ⊤

/-- The zero object makes the indexing type nonempty, so the `ℕ∞` infimum attains its value;
this equivalence extracts a witness at the requested finite stage. -/
theorem rouquierDim_le_coe_iff (n : ℕ) :
    rouquierDim C ≤ (n : ℕ∞) ↔
      ∃ G : C, (ObjectProperty.singleton G).triangEnvelopeIter n = ⊤ := by
  constructor
  · intro h
    letI : Nonempty C := ⟨HasZeroObject.zero.choose⟩
    obtain ⟨G, hG⟩ :=
      ENat.exists_eq_iInf (fun G : C ↦ (ObjectProperty.singleton G).generationTime ⊤)
    refine ⟨G, ?_⟩
    have htime : (ObjectProperty.singleton G).generationTime ⊤ ≤ (n : ℕ∞) := by
      rw [rouquierDim, ← hG] at h
      exact h
    exact top_le_iff.mp
      ((ObjectProperty.generationTime_le_coe_iff (ObjectProperty.singleton G) ⊤ n).1 htime)
  · rintro ⟨G, hG⟩
    rw [rouquierDim]
    calc
      (⨅ G' : C, (ObjectProperty.singleton G').generationTime ⊤) ≤
          (ObjectProperty.singleton G).generationTime ⊤ := iInf_le _ _
      _ ≤ (n : ℕ∞) :=
        (ObjectProperty.generationTime_le_coe_iff (ObjectProperty.singleton G) ⊤ n).2
          (top_le_iff.mpr hG)

/-- Well-ordering of `ℕ∞` makes the infimum attainable; the generation-time bridge identifies
a finite value with strong generation. -/
theorem rouquierDim_ne_top_iff_exists_strong :
    rouquierDim C ≠ ⊤ ↔
      ∃ G : C, (ObjectProperty.singleton G).IsStrongTriangulatedGenerator := by
  constructor
  · intro h
    letI : Nonempty C := ⟨HasZeroObject.zero.choose⟩
    obtain ⟨G, hG⟩ :=
      ENat.exists_eq_iInf (fun G : C ↦ (ObjectProperty.singleton G).generationTime ⊤)
    have htime : (ObjectProperty.singleton G).generationTime ⊤ ≠ ⊤ := by
      intro htop
      apply h
      change (⨅ G' : C, (ObjectProperty.singleton G').generationTime ⊤) = ⊤
      rw [← hG, htop]
    exact ⟨G,
      (ObjectProperty.isStrongTriangulatedGenerator_iff_generationTime_ne_top
        (ObjectProperty.singleton G)).2 htime⟩
  · rintro ⟨G, hG⟩ hdim
    have htime : (ObjectProperty.singleton G).generationTime ⊤ ≠ ⊤ :=
      (ObjectProperty.isStrongTriangulatedGenerator_iff_generationTime_ne_top
        (ObjectProperty.singleton G)).1 hG
    apply htime
    have hle : rouquierDim C ≤ (ObjectProperty.singleton G).generationTime ⊤ := by
      rw [rouquierDim]
      exact iInf_le _ _
    rw [hdim] at hle
    exact top_le_iff.mp hle

/-- Mathlib's strong-to-classical implication turns the strong generator from the finite-dimension
characterization into a classical generator. -/
theorem exists_isClassicalTriangulatedGenerator_of_rouquierDim_ne_top
    (h : rouquierDim C ≠ ⊤) :
    ∃ G : C, (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator := by
  obtain ⟨G, hG⟩ := (rouquierDim_ne_top_iff_exists_strong C).mp h
  exact ⟨G, hG.isClassicalTriangulatedGenerator⟩

/-- Rouquier dimension is zero exactly when one object's zeroth envelope is the whole category.
By `CategoryTheory.ObjectProperty.triangEnvelopeIter_zero`, this is generation using only shifts,
finite binary products, and
retracts, without extension steps. -/
theorem rouquierDim_eq_zero_iff :
    rouquierDim C = 0 ↔
      ∃ G : C, (ObjectProperty.singleton G).triangEnvelopeIter 0 = ⊤ := by
  rw [rouquierDim, ENat.iInf_eq_zero]
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨G, top_le_iff.mp
      ((ObjectProperty.generationTime_eq_zero_iff (ObjectProperty.singleton G) ⊤).1 hG)⟩
  · rintro ⟨G, hG⟩
    exact ⟨G,
      (ObjectProperty.generationTime_eq_zero_iff (ObjectProperty.singleton G) ⊤).2
        (top_le_iff.mpr hG)⟩

end CategoryTheory.Triangulated
