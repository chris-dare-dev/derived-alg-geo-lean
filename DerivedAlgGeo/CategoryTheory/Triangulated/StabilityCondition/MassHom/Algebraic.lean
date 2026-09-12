/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Stable
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.SimpleCharge
import Mathlib.CategoryTheory.Noetherian
import Mathlib.Tactic

/-!
# Algebraic stability conditions and mass--Hom bounds

An algebraic stability condition has a finite-length heart with finitely many
simple objects.  The categorical content needed here is recorded operationally:
the slicing has Jordan--Hölder filtrations and its stable objects form finitely
many shift-orbits.  This avoids identifying the repository's free lattice of
simple charges with a categorical Grothendieck group before the missing
Jordan--Hölder bridge is constructed (GitHub issue #1203).

With the properness input `HomFiniteBounded`, a fixed source has only finitely
many nonzero shifted Hom-spaces into each simple representative.  Summing those
dimensions and dividing by the finitely many positive simple masses gives a
stable-target bound; the stable-object reduction then gives the global
mass--Hom bound.  This is the algebraic base case in
Halpern--Leistner--Robotis, arXiv:2501.00710v2, Example 2.9.

This proof deliberately does not use the tempting estimate
`dim Hom(Sⱼ⟦m⟧, F) ≤ length(F)`: finite length controls morphisms in the
heart, not arbitrary shifted Ext groups.  Finite Ext-amplitude is therefore
kept visible as `HomFiniteBounded` and all shifted Hom dimensions are summed
before the finite family of simple representatives is used.

The numerical lemma `exists_common_positive_functional` isolates the other
finite-heart estimate: finitely many charges in the semi-closed upper half
plane admit one strictly positive real linear functional, with a uniform
positive lower bound.  Its functional `(x,y) ↦ y - δx` is the unnormalised
form of taking real part after rotation; normalising does not affect strict
positivity.

No geometry is imported, and no stability condition is manufactured from the
finite-lattice charge model.  In particular, the concrete
`Kᵇ(FGModuleCat k)` properness witness does not by itself supply a heart,
slicing, or stability condition.  The nondegenerate concrete stability
witness is tracked separately by GitHub issue #1206.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.SerreFunctor
open scoped ENNReal ZeroObject BigOperators ComplexConjugate

namespace CategoryTheory.Triangulated

noncomputable section

namespace WeakStabilityCondition.FiniteLength

/-- A positive function on a nonempty finite type has a uniform positive
lower bound. -/
private theorem exists_uniform_pos_lower_bound
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.Nonempty := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact ⟨f i, by simp [s]⟩
  refine ⟨s.min' hs, ?_, fun i ↦ ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
    simpa [hi] using hf i
  · exact s.min'_le _ (by simp [s])

/-- The real functional used to tilt the boundary ray of the semi-closed
upper half plane into an open half plane. -/
def tiltedImaginaryPart (δ : ℝ) (z : ℂ) : ℝ := z.im - δ * z.re

/-- Finitely many vectors in the semi-closed upper half plane admit a common
strictly positive direction and a uniform positive lower bound.

The direction is the real functional `z.im - δ * z.re`, with `δ > 0`.
It is the dot product with `(-δ, 1)`; division by its positive norm gives the
equivalent unit-direction formulation. -/
theorem exists_common_positive_functional
    {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℂ)
    (hz : ∀ i, z i ∈ semiClosedUpperHalfPlane) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ i, c ≤ tiltedImaginaryPart δ (z i) := by
  let slopeCap : ι → ℝ := fun i ↦
    if 0 < (z i).re then (z i).im / (z i).re else 1
  have hslope : ∀ i, 0 < slopeCap i := by
    intro i
    simp only [slopeCap]
    split_ifs with hre
    · rcases hz i with him | ⟨_, hneg⟩
      · exact div_pos him hre
      · exact absurd hre (not_lt_of_ge hneg.le)
    · exact one_pos
  obtain ⟨d, hd, hdle⟩ := exists_uniform_pos_lower_bound slopeCap hslope
  let δ := d / 2
  have hδ : 0 < δ := div_pos hd (by norm_num)
  have hpositive : ∀ i, 0 < tiltedImaginaryPart δ (z i) := by
    intro i
    rcases hz i with him | ⟨him, hre⟩
    · by_cases hrei : 0 < (z i).re
      · have hlt : δ < (z i).im / (z i).re := by
          have hbound := hdle i
          simp only [slopeCap, if_pos hrei] at hbound
          dsimp [δ]
          linarith
        have hmul : δ * (z i).re < (z i).im :=
          (lt_div_iff₀ hrei).mp hlt
        dsimp [tiltedImaginaryPart]
        linarith
      · have hrele : (z i).re ≤ 0 := le_of_not_gt hrei
        have hmul : δ * (z i).re ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hδ.le hrele
        change 0 < (z i).im at him
        dsimp [tiltedImaginaryPart]
        linarith
    · dsimp [tiltedImaginaryPart]
      rw [him]
      simp only [zero_sub]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hδ hre)
  obtain ⟨c, hc, hcle⟩ := exists_uniform_pos_lower_bound
    (fun i ↦ tiltedImaginaryPart δ (z i)) hpositive
  exact ⟨δ, c, hδ, hc, hcle⟩

/-- Unit-vector form of `exists_common_positive_functional`: after one
rotation, the real parts of a finite family of upper-half-plane vectors have
a uniform positive lower bound. -/
theorem exists_common_unit_direction
    {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℂ)
    (hz : ∀ i, z i ∈ semiClosedUpperHalfPlane) :
    ∃ u : ℂ, ∃ c : ℝ, ‖u‖ = 1 ∧ 0 < c ∧
      ∀ i, c ≤ (z i * conj u).re := by
  obtain ⟨δ, c, hδ, hc, hcle⟩ := exists_common_positive_functional z hz
  let w : ℂ := ⟨-δ, 1⟩
  have hw : w ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [w] at him
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u : ℂ := (‖w‖⁻¹ : ℝ) • w
  let c' : ℝ := c / ‖w‖
  refine ⟨u, c', ?_, div_pos hc hwnorm, fun i ↦ ?_⟩
  · simp [u, hwnorm.ne']
  · have hre : (z i * conj u).re =
        tiltedImaginaryPart δ (z i) / ‖w‖ := by
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      simp [u, w, tiltedImaginaryPart]
      field_simp [hwnorm.ne']
      ring
    rw [hre]
    exact (div_le_div_iff_of_pos_right hwnorm).mpr (hcle i)

end WeakStabilityCondition.FiniteLength

universe w v u u'

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [Pretriangulated C] [IsTriangulated C]
  [HomFinite k C] [HomFiniteBounded k C]
variable {Λ : Type u'} [AddCommGroup Λ] {v₀ : K₀ C →+ Λ}
variable {σ : StabilityCondition.WithClassMap C v₀}
variable {A F : C}

namespace StabilityCondition.WithClassMap

/-- The literal finite-heart part of algebraicity: every object of the
canonical heart is Artinian and Noetherian, and a finite list exhausts its
simple objects up to isomorphism. -/
def HasFiniteLengthHeart (σ : StabilityCondition.WithClassMap C v₀) : Prop :=
  ∃ (n : ℕ)
      (S : Fin n → σ.slicing.toTStructure.heart.FullSubcategory),
    (∀ E : σ.slicing.toTStructure.heart.FullSubcategory,
      IsArtinianObject E ∧ IsNoetherianObject E) ∧
    (∀ i, Simple (S i)) ∧
    ∀ T : σ.slicing.toTStructure.heart.FullSubcategory, Simple T →
      ∃ i, Nonempty (T ≅ S i)

/-- The currently explicit categorical bridge from a finite-length heart to
the slicing: same-phase Jordan--Hölder filtrations exist, and stable objects
are shifts of finitely many representatives.  Deriving this bridge from
`HasFiniteLengthHeart` is the missing Jordan--Hölder lane (#1203). -/
def HasFiniteStableOrbits (σ : StabilityCondition.WithClassMap C v₀) : Prop :=
  ∃ (n : ℕ) (S : Fin n → C),
    0 < n ∧ σ.slicing.HasJordanHolderFiltrations ∧
      (∀ i, ∃ φ : ℝ, σ.slicing.IsStableAt φ (S i)) ∧
      ∀ (F : C) (φ : ℝ), σ.slicing.IsStableAt φ F →
        ∃ (i : Fin n) (m : ℤ), Nonempty (F ≅ (S i)⟦m⟧)

/-- An algebraic stability condition, with the unresolved heart-to-slicing
Jordan--Hölder bridge kept explicit rather than inferred from local
finiteness. -/
def IsAlgebraic (σ : StabilityCondition.WithClassMap C v₀) : Prop :=
  σ.HasFiniteLengthHeart ∧ σ.HasFiniteStableOrbits

namespace IsAlgebraic

/-- An algebraic stability condition has the explicit Jordan--Hölder input
required by stable-object reduction. -/
theorem hasJordanHolder (h : σ.IsAlgebraic) :
    σ.slicing.HasJordanHolderFiltrations := by
  obtain ⟨_, _, _, hJH, _, _⟩ := h.2
  exact hJH

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- The finite stable representatives of a nonzero algebraic stability
condition classically generate the ambient triangulated category.  This is
assembled from the explicit Jordan--Hölder bridge and the slicing's HN
towers. -/
theorem exists_classicalGenerator (h : σ.IsAlgebraic) :
    ∃ (n : ℕ) (S : Fin n → C),
      (∀ i, ∃ φ : ℝ, σ.slicing.IsStableAt φ (S i)) ∧
      ObjectProperty.IsClassicalTriangulatedGenerator
        (fun E : C ↦ ∃ i, Nonempty (E ≅ S i)) := by
  obtain ⟨n, S, hn, hJH, hSstable, hclassify⟩ := h.2
  let G : ObjectProperty C := fun E ↦ ∃ i, Nonempty (E ≅ S i)
  haveI : G.Nonempty := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨S i, i, ⟨Iso.refl _⟩⟩
  have hstable : ∀ φ : ℝ, σ.slicing.IsStableAt φ ≤ G.triangEnvelope := by
    intro φ F hF
    obtain ⟨i, m, ⟨e⟩⟩ := hclassify F φ hF
    have hSi : G.triangEnvelope (S i) :=
      G.le_triangEnvelope _ ⟨i, ⟨Iso.refl _⟩⟩
    have hshift : G.triangEnvelope ((S i)⟦m⟧) :=
      G.triangEnvelope.le_shift m _ hSi
    exact G.triangEnvelope.prop_of_iso e.symm hshift
  have hext : ExtensionClosure G.triangEnvelope ≤ G.triangEnvelope :=
    ExtensionClosure.le_of_closed
      (fun hzero ↦ G.triangEnvelope.prop_of_isZero hzero)
      (fun _ hE ↦ hE)
      (fun hT hX hY ↦
        G.triangEnvelope.ext_of_isTriangulatedClosed₂ _ hT hX hY)
  refine ⟨n, S, hSstable, ?_⟩
  apply le_antisymm le_top
  intro E _
  obtain ⟨P⟩ := σ.slicing.hn_exists E
  apply hext
  apply ExtensionClosure.ofPostnikovTower P.toPostnikovTower
  intro i
  apply hext
  exact ExtensionClosure.mono (hstable (P.φ i)) (P.factor i)
    (hJH (P.φ i) (P.factor i) (P.semistable i))

/-- The total dimension of all shifted Hom-spaces from `A` to `B`. -/
def totalShiftedHomRank (A B : C) : ℕ :=
  ∑ᶠ m : ℤ, Module.finrank k (A ⟶ B⟦m⟧)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear k] [Pretriangulated C]
    [IsTriangulated C] [HomFinite k C] in
private theorem finrank_le_totalShiftedHomRank (A B : C) (m : ℤ) :
    Module.finrank k (A ⟶ B⟦m⟧) ≤ totalShiftedHomRank (k := k) A B := by
  have hs : (Function.support fun j : ℤ ↦
      Module.finrank k (A ⟶ B⟦j⟧)).Finite := by
    refine (HomFiniteBounded.support_finite (k := k) A B).subset ?_
    intro j hj
    change Module.finrank k (A ⟶ B⟦j⟧) ≠ 0 at hj
    change (Module.finrank k (A ⟶ B⟦j⟧) : ℤ) ≠ 0
    exact_mod_cast hj
  exact single_le_finsum m hs fun _ ↦ Nat.zero_le _

private theorem stabilityMass_shift (E : C) (m : ℤ) :
    stabilityMass σ (E⟦m⟧) = stabilityMass σ E := by
  induction m using Int.induction_on with
  | zero =>
      exact stabilityMass_congr σ ((shiftFunctorZero C ℤ).app E)
  | succ m ih =>
      rw [stabilityMass_congr σ
        ((shiftFunctorAdd' C (m : ℤ) 1 ((m : ℤ) + 1) (by omega)).app E)]
      change stabilityMass σ ((E⟦(m : ℤ)⟧)⟦(1 : ℤ)⟧) = stabilityMass σ E
      rw [stabilityMass_shift_one, ih]
  | pred m ih =>
      rw [stabilityMass_congr σ
        ((shiftFunctorAdd' C (-(m : ℤ)) (-1 : ℤ)
          (-(m : ℤ) - 1) rfl).app E)]
      change stabilityMass σ ((E⟦(-(m : ℤ))⟧)⟦(-1 : ℤ)⟧) = stabilityMass σ E
      rw [stabilityMass_shift_neg_one, ih]

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- An algebraic stability condition on a proper category has a mass--Hom
bound.  Properness is the explicit `HomFiniteBounded` hypothesis; it is not
inferred from finite length of the heart. -/
theorem hasGlobalMassHomBound (h : σ.IsAlgebraic) :
    σ.HasGlobalMassHomBound (k := k) := by
  obtain ⟨n, S, _, hJH, hSstable, hclassify⟩ := h.2
  have hstableBound : σ.HasStableMassHomBound (k := k) ⊤ := by
    intro A _
    let q : Fin n → ℝ := fun i ↦
      (totalShiftedHomRank (k := k) A (S i) : ℝ) /
        (stabilityMass σ (S i)).toReal
    let K : ℝ := (∑ i, q i) + 1
    have hq : ∀ i, 0 ≤ q i := fun i ↦
      div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
    have hK : 0 < K := by
      dsimp [K]
      exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ ↦ hq i) one_pos
    refine ⟨K, hK, fun F φ hF ↦ ?_⟩
    obtain ⟨i, m, ⟨e⟩⟩ := hclassify F φ hF
    obtain ⟨φi, hSi⟩ := hSstable i
    have hmassPos : 0 < (stabilityMass σ (S i)).toReal :=
      stabilityMass_toReal_pos σ hSi.2.1
    have hdimNat := finrank_le_totalShiftedHomRank (k := k) A (S i) m
    have hdimIso := (Linear.homCongr k (Iso.refl A) e).finrank_eq
    have hmassIso := stabilityMass_congr σ e
    have hqi : q i ≤ ∑ j, q j :=
      Finset.single_le_sum (fun j _ ↦ hq j) (Finset.mem_univ i)
    calc
      (Module.finrank k (A ⟶ F) : ℝ) =
          (Module.finrank k (A ⟶ (S i)⟦m⟧) : ℝ) := by
        exact_mod_cast hdimIso
      _ ≤ (totalShiftedHomRank (k := k) A (S i) : ℝ) := by
        exact_mod_cast hdimNat
      _ = q i * (stabilityMass σ (S i)).toReal := by
        dsimp [q]
        field_simp [ne_of_gt hmassPos]
      _ ≤ K * (stabilityMass σ (S i)).toReal := by
        apply mul_le_mul_of_nonneg_right _ hmassPos.le
        dsimp [K]
        linarith
      _ = K * (stabilityMass σ F).toReal := by
        rw [hmassIso, stabilityMass_shift (C := C)]
  exact hstableBound.massHom hJH

end IsAlgebraic

end StabilityCondition.WithClassMap

end

end CategoryTheory.Triangulated
