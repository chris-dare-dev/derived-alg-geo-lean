/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealFormSignature
import Mathlib.Tactic

/-!
# Hodge-index data for a symmetric real pairing

`DivisorSpace` is the established name of a real vector space equipped with a
symmetric bilinear pairing.  `HodgeIndex` records the index inequality relative
to a positive vector, while `HodgeDefinite` records negative definiteness on its
orthogonal complement.  The latter determines the signature and nondegeneracy
of the pairing.

All declarations in this file are linear algebra.  No charge family, Chern
character, scheme, support predicate, or wall arrangement is imported.  The
existing namespace is preserved by the ownership cutover.
-/

open QuadraticMap

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

variable {D : Type w} [AddCommGroup D] [Module ℝ D]

/-- A real vector space with a symmetric bilinear pairing. -/
structure DivisorSpace (D : Type w) [AddCommGroup D] [Module ℝ D] where
  /-- The real intersection pairing. -/
  intersection : LinearMap.BilinForm ℝ D
  /-- The pairing is symmetric. -/
  intersection_symm : intersection.IsSymm

namespace DivisorSpace

variable (S : DivisorSpace D)

/-- Dot notation for the symmetric pairing. -/
def pair (x y : D) : ℝ := S.intersection x y

theorem pair_apply (x y : D) : S.pair x y = S.intersection x y := rfl

/-- Symmetry of the pairing. -/
theorem pair_comm (x y : D) : S.pair x y = S.pair y x :=
  S.intersection_symm.eq x y

@[simp]
theorem pair_zero_left (x : D) : S.pair 0 x = 0 := by
  simp [pair]

@[simp]
theorem pair_zero_right (x : D) : S.pair x 0 = 0 := by
  simp [pair]

/-- The Hodge index inequality relative to a vector `H` of positive square. -/
structure HodgeIndex (H : D) : Prop where
  /-- The reference vector has positive square. -/
  H_square_pos : 0 < S.pair H H
  /-- The index inequality at every vector. -/
  index_le : ∀ x : D, S.pair H H * S.pair x x ≤ S.pair H x ^ 2

namespace HodgeIndex

variable {S} {H : D}

/-- A vector orthogonal to `H` has nonpositive square. -/
theorem pair_self_nonpos_of_orthogonal (h : S.HodgeIndex H) {x : D}
    (hx : S.pair H x = 0) : S.pair x x ≤ 0 := by
  have hidx := h.index_le x
  rw [hx] at hidx
  nlinarith [h.H_square_pos, hidx]

/-- An orthogonal vector with nonzero square has negative square. -/
theorem pair_self_neg_of_orthogonal (h : S.HodgeIndex H) {x : D}
    (hx : S.pair H x = 0) (hne : S.pair x x ≠ 0) : S.pair x x < 0 :=
  lt_of_le_of_ne (h.pair_self_nonpos_of_orthogonal hx) hne

end HodgeIndex

/-- Negative definiteness on `H^⊥`, together with positivity of `H²`. -/
structure HodgeDefinite (H : D) : Prop where
  /-- The reference vector has positive square. -/
  H_square_pos : 0 < S.pair H H
  /-- The form is negative definite on the orthogonal complement of `H`. -/
  neg_definite : ∀ x : D, S.pair H x = 0 → x ≠ 0 → S.pair x x < 0

namespace HodgeDefinite

variable {S} {H : D}

/-- Definiteness on `H^⊥` implies the Hodge index inequality. -/
theorem toHodgeIndex (h : S.HodgeDefinite H) : S.HodgeIndex H where
  H_square_pos := h.H_square_pos
  index_le x := by
    have hH : S.pair H H ≠ 0 := ne_of_gt h.H_square_pos
    set t : ℝ := S.pair H x / S.pair H H with ht
    set x' : D := x - t • H with hx'
    have horth : S.pair H x' = 0 := by
      simp only [hx', DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
      change S.pair H x - t * S.pair H H = 0
      rw [ht, div_mul_cancel₀ _ hH, sub_self]
    have hsplit : x = t • H + x' := by
      simp only [hx']
      abel
    have hcomm : S.pair x' H = 0 := by rw [S.pair_comm]; exact horth
    have hxx : S.pair x x = t ^ 2 * S.pair H H + S.pair x' x' := by
      conv_lhs => rw [hsplit]
      simp only [DivisorSpace.pair, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul] at horth hcomm ⊢
      linear_combination t * horth + t * hcomm
    have hx'nonpos : S.pair x' x' ≤ 0 := by
      by_cases hz : x' = 0
      · rw [hz]
        simp [DivisorSpace.pair]
      · exact (h.neg_definite x' horth hz).le
    have hts : t ^ 2 * S.pair H H * S.pair H H = S.pair H x ^ 2 := by
      rw [ht]
      field_simp
    nlinarith [h.H_square_pos, hxx, hx'nonpos, hts]

end HodgeDefinite

/-- The self-pairing bundled as a quadratic form. -/
abbrev intersectionQuadratic : QuadraticForm ℝ D :=
  LinearMap.BilinMap.toQuadraticMap S.intersection

theorem intersectionQuadratic_apply (x : D) : S.intersectionQuadratic x = S.pair x x := rfl

theorem polar_intersectionQuadratic (x y : D) :
    polar (⇑S.intersectionQuadratic) x y = 2 * S.pair x y := by
  rw [intersectionQuadratic, LinearMap.BilinMap.polar_toQuadraticMap]
  have h : S.intersection y x = S.intersection x y := S.pair_comm y x
  simp only [DivisorSpace.pair] at h ⊢
  linarith

variable {S} {H : D}

private def hLine (H : D) : Submodule ℝ D := Submodule.span ℝ ({H} : Set D)

private def hPerp (S : DivisorSpace D) (H : D) : Submodule ℝ D :=
  LinearMap.ker (S.intersection H)

private theorem mem_hPerp_iff {x : D} : x ∈ hPerp S H ↔ S.pair H x = 0 := Iff.rfl

private theorem isCompl_hLine_hPerp (hpos : 0 < S.pair H H) :
    IsCompl (hLine H) (hPerp S H) := by
  have hH : S.intersection H H ≠ 0 := ne_of_gt hpos
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    have hzero : a * S.intersection H H = 0 := by
      have hker := mem_hPerp_iff.mp hx'
      rw [← ha] at hker
      simpa [DivisorSpace.pair, smul_eq_mul] using hker
    have hazero : a = 0 := (mul_eq_zero.mp hzero).resolve_right hH
    rw [← ha, hazero, zero_smul]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    refine Submodule.mem_sup.mpr ⟨(S.pair H x / S.pair H H) • H,
      Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
      x - (S.pair H x / S.pair H H) • H, ?_, by abel⟩
    show S.pair H (x - (S.pair H x / S.pair H H) • H) = 0
    simp only [DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
    field_simp
    ring

private theorem orth_hLine_hPerp (S : DivisorSpace D) (H : D) :
    ∀ w ∈ hLine H, ∀ w' ∈ hPerp S H, polar (⇑S.intersectionQuadratic) w w' = 0 := by
  intro w hw w' hw'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [polar_intersectionQuadratic]
  have hsmul : S.pair (a • H) w' = a * S.pair H w' := by
    simp [DivisorSpace.pair]
  rw [hsmul, mem_hPerp_iff.mp hw']
  ring

private theorem posDef_restrict_hLine (hpos : 0 < S.pair H H) :
    (S.intersectionQuadratic.restrict (hLine H)).PosDef := by
  intro x hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
  have hane : a ≠ 0 := by
    intro hc
    apply hx
    apply Subtype.ext
    simp [← ha, hc]
  have hval : S.intersectionQuadratic (x : D) = a ^ 2 * S.pair H H := by
    rw [← ha]
    simp only [intersectionQuadratic_apply, DivisorSpace.pair, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [restrict_apply, hval]
  have hsq : 0 < a ^ 2 := by positivity
  exact mul_pos hsq hpos

private theorem negDef_restrict_hPerp (h : S.HodgeDefinite H) :
    (-(S.intersectionQuadratic.restrict (hPerp S H))).PosDef := by
  intro x hx
  have hxne : (x : D) ≠ 0 := fun hc => hx (Subtype.ext hc)
  have hneg : S.pair (x : D) (x : D) < 0 := h.neg_definite _ (mem_hPerp_iff.mp x.2) hxne
  have hval : (-(S.intersectionQuadratic.restrict (hPerp S H))) x
      = -(S.pair (x : D) (x : D)) := rfl
  rw [hval]
  linarith

private theorem finrank_hLine (hpos : 0 < S.pair H H) :
    Module.finrank ℝ (hLine H) = 1 := by
  have hHne : H ≠ 0 := by
    intro hc
    have hsq := hpos
    rw [hc] at hsq
    simp [DivisorSpace.pair] at hsq
  rw [hLine, finrank_span_singleton hHne]

variable [FiniteDimensional ℝ D]

/-- The indices of inertia of a Hodge-definite pairing. -/
theorem sigPos_sigNeg_of_hodgeDefinite (h : S.HodgeDefinite H) :
    sigPos S.intersectionQuadratic = 1 ∧
      sigNeg S.intersectionQuadratic + 1 = Module.finrank ℝ D := by
  obtain ⟨hP₁, hN₁, hnd₁⟩ := sigPos_eq_finrank_of_posDef (posDef_restrict_hLine h.H_square_pos)
  obtain ⟨hN₂, hP₂, hnd₂⟩ := sigNeg_eq_finrank_of_negDef (negDef_restrict_hPerp h)
  obtain ⟨hsplitP, hsplitN⟩ :=
    QuadraticMap.sigPos_eq_add (Q := S.intersectionQuadratic)
      (isCompl_hLine_hPerp h.H_square_pos) (orth_hLine_hPerp S H) hnd₁ hnd₂
  have hdim := Submodule.finrank_add_eq_of_isCompl (isCompl_hLine_hPerp h.H_square_pos)
  rw [finrank_hLine h.H_square_pos] at hP₁ hdim
  refine ⟨by rw [hsplitP, hP₁, hP₂], ?_⟩
  rw [hsplitN, hN₁, hN₂]
  omega

/-- A Hodge-definite pairing is nondegenerate. -/
theorem nondegenerate_of_hodgeDefinite (h : S.HodgeDefinite H) :
    S.intersectionQuadratic.Nondegenerate := by
  obtain ⟨hP, hN⟩ := sigPos_sigNeg_of_hodgeDefinite h
  have htot := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := S.intersectionQuadratic)
  have hrad : Module.finrank ℝ S.intersectionQuadratic.radical = 0 := by omega
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  exact Submodule.finrank_eq_zero.mp hrad

/-- A Hodge-definite certificate can be transported to any positive vector. -/
theorem HodgeDefinite.of_pair_pos (h : S.HodgeDefinite H) {omega : D}
    (homega : 0 < S.pair omega omega) : S.HodgeDefinite omega := by
  obtain ⟨hP, hN⟩ := sigPos_sigNeg_of_hodgeDefinite h
  have hnd := nondegenerate_of_hodgeDefinite h
  have hcompl := isCompl_hLine_hPerp (S := S) (H := omega) homega
  have horth := orth_hLine_hPerp S omega
  obtain ⟨hP₁, hN₁, hnd₁⟩ :=
    sigPos_eq_finrank_of_posDef (posDef_restrict_hLine (S := S) (H := omega) homega)
  rw [finrank_hLine (S := S) (H := omega) homega] at hP₁
  have hle := QuadraticMap.sigPos_add_le (Q := S.intersectionQuadratic) hcompl horth
  rw [hP₁, hP] at hle
  have hPperp : sigPos (S.intersectionQuadratic.restrict (hPerp S omega)) = 0 := by omega
  have hnd₂ : (S.intersectionQuadratic.restrict (hPerp S omega)).Nondegenerate :=
    QuadraticMap.nondegenerate_restrict_of_isCompl hcompl horth hnd
  have htot := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := S.intersectionQuadratic.restrict (hPerp S omega))
  have hrad₂ : Module.finrank ℝ
      (S.intersectionQuadratic.restrict (hPerp S omega)).radical = 0 := by
    rw [hnd₂.radical_eq_bot]
    simp
  have hNperp : sigNeg (S.intersectionQuadratic.restrict (hPerp S omega))
      = Module.finrank ℝ (hPerp S omega) := by omega
  have hnegdef := QuadraticMap.negDef_of_sigNeg_eq_finrank hNperp
  refine ⟨homega, fun x hx hxne => ?_⟩
  have hmem : x ∈ hPerp S omega := hx
  have hpos := hnegdef ⟨x, hmem⟩ (fun hc => hxne (congrArg Subtype.val hc))
  have hval : (-(S.intersectionQuadratic.restrict (hPerp S omega))) ⟨x, hmem⟩
      = -(S.pair x x) := rfl
  rw [hval] at hpos
  linarith

/-- The real Mukai extension of a Hodge-definite pairing has signature two. -/
theorem hasSignatureTwo_of_hodgeDefinite (h : S.HodgeDefinite H) :
    PeriodDomain.HasSignatureTwo (Mukai.realForm S.intersection) := by
  obtain ⟨hP, hN⟩ := sigPos_sigNeg_of_hodgeDefinite h
  exact Mukai.hasSignatureTwo_realForm S.intersection
    (fun x y => S.pair_comm x y) hP hN

end DivisorSpace

end


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
