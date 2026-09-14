/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositivePlane

/-!
# Orthogonality loci among positive planes

This file owns the deleted-locus arrangement attached to a real quadratic
space. For a class `δ`, `orthogonalityLocus Q δ` consists of positive planes
orthogonal to `δ`. After choosing a positive frame, membership is the pair of
real equations saying that the associated complex functional kills `δ`.

This is not a determinant-alignment locus: alignment is one real equation and
also contains zero charges and opposite rays. It is not an actual
destabilization wall either; there is no category or semistable object here.
-/

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

section Defs

variable (Q : QuadraticForm ℝ M)

/-- A class of pairing square `-2`. -/
def IsSphericalClass (δ : M) : Prop := polar Q δ δ = -2

/-- The positive planes orthogonal to `δ`. -/
def orthogonalityLocus (δ : M) : Set (Submodule ℝ M) :=
  {W | IsPositivePlane Q W ∧ ∀ w ∈ W, polar Q δ w = 0}

/-- The spherical classes lying in a chosen set of classes. -/
def sphericalClasses (Λ : Set M) : Set M := {δ ∈ Λ | IsSphericalClass Q δ}

/-- Positive planes away from all orthogonality loci indexed by `Δ`. -/
def positivePlanesAway (Δ : Set M) : Set (Submodule ℝ M) :=
  {W ∈ positivePlanes Q | ∀ δ ∈ Δ, W ∉ orthogonalityLocus Q δ}

end Defs

variable {Q : QuadraticForm ℝ M}

/-- A spherical class has quadratic value `-1`; the factor two comes from the
polar form. -/
theorem isSphericalClass_iff_apply {δ : M} : IsSphericalClass Q δ ↔ Q δ = -1 := by
  rw [IsSphericalClass, polar_self, two_nsmul]
  constructor <;> intro h <;> linarith

/-- A positive plane is in the orthogonality locus of `δ` exactly when `δ`
lies in its orthogonal complement. -/
theorem mem_orthogonalityLocus_iff_mem_orthogonal {W : Submodule ℝ M} {δ : M}
    (hW : IsPositivePlane Q W) : W ∈ orthogonalityLocus Q δ ↔ δ ∈ orthogonal Q W := by
  rw [orthogonalityLocus, Set.mem_setOf_eq, mem_orthogonal_iff]
  refine ⟨fun h w hw => ?_, fun h => ⟨hW, fun w hw => ?_⟩⟩
  · exact (polar_comm (⇑Q) w δ).trans (h.2 w hw)
  · exact (polar_comm (⇑Q) δ w).trans (h w hw)

/-- A spherical class lies in no positive plane. -/
theorem notMem_of_isSphericalClass {W : Submodule ℝ M} {δ : M}
    (hW : IsPositivePlane Q W) (hδ : IsSphericalClass Q δ) : δ ∉ W := by
  intro hmem
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [isSphericalClass_iff_apply, h, map_zero] at hδ
    norm_num at hδ
  have hpos : 0 < (Q.restrict W) ⟨δ, hmem⟩ := hW.posDef _ (by simpa using hδ0)
  rw [restrict_apply, isSphericalClass_iff_apply.mp hδ] at hpos
  norm_num at hpos

section FiniteDimensional

variable [FiniteDimensional ℝ M]

/-- Cutting by every real spherical class empties the positive-plane locus in
dimension at least three. This is why a geometric application cuts by a
discrete lattice of classes instead. -/
theorem positivePlanesAway_sphericalClasses_univ_eq_empty (hsig : HasSignatureTwo Q)
    (hdim : 3 ≤ Module.finrank ℝ M) :
    positivePlanesAway Q (sphericalClasses Q Set.univ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro W ⟨hW, hcut⟩
  have hWpos : IsPositivePlane Q W := hW
  have hrank : Module.finrank ℝ (orthogonal Q W) + 2 = Module.finrank ℝ M :=
    finrank_orthogonal hWpos
  have hpos : 0 < Module.finrank ℝ (orthogonal Q W) := by omega
  haveI : Nontrivial (orthogonal Q W) := (Module.finrank_pos_iff).mp hpos
  obtain ⟨u, hu0⟩ := exists_ne (0 : orthogonal Q W)
  have humem : (u : M) ∈ orthogonal Q W := u.2
  have hune : (u : M) ≠ 0 := by simpa using hu0
  have hQu : Q (u : M) < 0 := neg_of_mem_orthogonal hsig hWpos humem hune
  have hQne : Q (u : M) ≠ 0 := ne_of_lt hQu
  have hfrac : 0 < -1 / Q (u : M) := div_pos_of_neg_of_neg (by norm_num) hQu
  set c : ℝ := Real.sqrt (-1 / Q (u : M)) with hc
  have hcsq : c * c = -1 / Q (u : M) := Real.mul_self_sqrt hfrac.le
  set δ : M := c • (u : M) with hδ
  have hQδ : Q δ = -1 := by
    rw [hδ, QuadraticMap.map_smul, smul_eq_mul, hcsq]
    field_simp
  have hsph : IsSphericalClass Q δ := by
    rw [isSphericalClass_iff_apply, hQδ]
  have hmem : δ ∈ orthogonal Q W := Submodule.smul_mem _ _ humem
  exact hcut δ ⟨Set.mem_univ δ, hsph⟩
    ((mem_orthogonalityLocus_iff_mem_orthogonal hWpos).mpr hmem)

end FiniteDimensional

end PeriodDomain
