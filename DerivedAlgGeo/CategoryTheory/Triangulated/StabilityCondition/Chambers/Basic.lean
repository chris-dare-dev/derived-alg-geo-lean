/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.LatticeAut
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.PeriodMap
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Family

/-!
# Charge-zero loci and their connected components in the stability space

For a stability condition `σ : StabilityCondition.WithClassMap C v` and a
class `δ : Λ`, this file defines the locus on which the central charge kills
`δ`. A regular locus avoids the zero loci indexed by a chosen set `Δ`, and a
`ChargeChamber` is a connected component of that regular-locus subtype.

## Distinction from the numerical loci

The locus here is the **charge-vanishing locus in the stability space**:
`chargeZeroLocus δ = {σ | σ.Z δ = 0}`.

It is not `Wall.Spherical.signedRayRegularLocus`, a subset of `V × V` in the
`exp(β + iω)` chart cut out by real half-spaces indexed by
`sphericalPlus`.  It is not the tilt-stability construction in
`Walls/Numerical/Basic.lean`, whose parameter space is the `(s, t)` half-plane
and whose walls are conics.  It is also not `PeriodDomain.orthogonalityLocus`, whose points
are submodules of a quadratic space and whose locus condition is orthogonality
to a class.

The comparison with the generic `ChargeFamily.zeroLocus` is explicit through
`stabilityChargeFamily`. No map from the stability space to either the
spherical chart or the positive-plane carrier is defined here.

## Topological boundary

Only the already-installed topology on `StabilityCondition.WithClassMap C v`
and the induced subtype topology are used to form `ConnectedComponents`.
Nothing here proves that `chargeZeroLocus` is closed or that `chargeRegularLocus` is open.
Until such a theorem is supplied, a `ChargeChamber` is the connected component
of a possibly non-open subspace and should not be read as a chamber in the
geometric sense.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Set

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

open GroupAction

/-! ## Charge-zero loci and their complement -/

/-- The central charges carried by the stability space, exposed through the
generic family API. This is the comparison map from stability conditions to
the upstream charge-zero-locus construction. -/
def stabilityChargeFamily :
    Wall.ChargeFamily (StabilityCondition.WithClassMap C v) Λ where
  charge σ := σ.Z

@[simp]
theorem stabilityChargeFamily_charge (σ : StabilityCondition.WithClassMap C v) (δ : Λ) :
    (stabilityChargeFamily (C := C) (v := v)).charge σ δ = σ.Z δ := rfl

/-- The locus of stability conditions whose central charge kills `δ`. -/
def chargeZeroLocus (δ : Λ) : Set (StabilityCondition.WithClassMap C v) :=
  (stabilityChargeFamily (C := C) (v := v)).zeroLocus δ

/-- The stability-space charge-zero locus is exactly the generic family zero
locus after applying `stabilityChargeFamily`. -/
theorem chargeZeroLocus_eq_family_zeroLocus (δ : Λ) :
    chargeZeroLocus (C := C) (v := v) δ =
      (stabilityChargeFamily (C := C) (v := v)).zeroLocus δ := rfl

/-- Membership in `chargeZeroLocus δ` is vanishing of the charge at `δ`. -/
theorem mem_chargeZeroLocus_iff (δ : Λ) (σ : StabilityCondition.WithClassMap C v) :
    σ ∈ chargeZeroLocus (C := C) (v := v) δ ↔ σ.Z δ = 0 :=
  Iff.rfl

/-- The stability conditions whose central charge is nonzero on every class
in `Δ`. -/
def chargeRegularLocus (Δ : Set Λ) : Set (StabilityCondition.WithClassMap C v) :=
  {σ | ∀ δ ∈ Δ, σ.Z δ ≠ 0}

/-- Membership in `chargeRegularLocus Δ` is nonvanishing on every class of `Δ`. -/
theorem mem_chargeRegularLocus_iff (Δ : Set Λ) (σ : StabilityCondition.WithClassMap C v) :
    σ ∈ chargeRegularLocus (C := C) (v := v) Δ ↔ ∀ δ ∈ Δ, σ.Z δ ≠ 0 :=
  Iff.rfl

/-- Enlarging the indexing set can only shrink the regular locus. -/
theorem chargeRegularLocus_antitone : Antitone (chargeRegularLocus (C := C) (v := v)) :=
  fun _ _ h _ hσ δ hδ ↦ hσ δ (h hδ)

/-- Avoiding the charge-zero loci of every lattice class is impossible because the zero
class has zero charge. -/
theorem chargeRegularLocus_univ : chargeRegularLocus (C := C) (v := v) Set.univ = ∅ := by
  ext σ
  simp only [mem_chargeRegularLocus_iff, Set.mem_univ, ne_eq, Set.mem_empty_iff_false,
    iff_false]
  intro h
  exact h 0 trivial (map_zero σ.Z)

/-- The regular locus is the complement of the union of its charge-zero loci. -/
theorem chargeRegularLocus_eq_compl_iUnion (Δ : Set Λ) :
    chargeRegularLocus (C := C) (v := v) Δ =
      (⋃ δ ∈ Δ, chargeZeroLocus (C := C) (v := v) δ)ᶜ := by
  ext σ
  simp [chargeRegularLocus, chargeZeroLocus]

/-! ## Equivariance -/

variable [IsTriangulated C]

/-- The combined symmetry sends the charge-zero locus indexed by `p.2.lam δ` to the locus
indexed by `δ`. -/
theorem combined_smul_mem_chargeZeroLocus_iff (p : GLTilde × AutPairQuot v)
    (σ : StabilityCondition.WithClassMap C v) (δ : Λ) :
    p • σ ∈ chargeZeroLocus (C := C) (v := v) δ ↔
      σ ∈ chargeZeroLocus (C := C) (v := v) (p.2.lam δ) := by
  rcases p with ⟨x, q⟩
  induction q using _root_.Quotient.inductionOn with
  | _ a =>
      change (((x, AutPairQuot.mk a) • σ).Z δ = 0 ↔
        σ.Z ((AutPairQuot.mk a).lam δ) = 0)
      rw [prod_mk_smul_Z, AutPairQuot.lam_mk, actC_eq_zero_iff]

/-- A combined symmetry maps the charge-zero locus indexed by the transformed
class exactly onto the original locus. -/
theorem image_chargeZeroLocus_smul (p : GLTilde × AutPairQuot v) (δ : Λ) :
    (fun σ : StabilityCondition.WithClassMap C v ↦ p • σ) ''
        chargeZeroLocus (C := C) (v := v) (p.2.lam δ) =
      chargeZeroLocus (C := C) (v := v) δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact (combined_smul_mem_chargeZeroLocus_iff p σ δ).2 hσ
  · intro σ hσ
    refine ⟨p⁻¹ • σ, ?_, by simp⟩
    apply (combined_smul_mem_chargeZeroLocus_iff p (p⁻¹ • σ) δ).1
    simpa using hσ

/-- The `GLTilde` action preserves every charge-zero locus setwise. -/
theorem image_chargeZeroLocus_gltilde (x : GLTilde) (δ : Λ) :
    (fun σ : StabilityCondition.WithClassMap C v ↦ x • σ) ''
        chargeZeroLocus (C := C) (v := v) δ =
      chargeZeroLocus (C := C) (v := v) δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [mem_chargeZeroLocus_iff, smul_stab_Z, actC_eq_zero_iff]
    exact hσ
  · intro σ hσ
    refine ⟨x⁻¹ • σ, ?_, by simp⟩
    rw [mem_chargeZeroLocus_iff, smul_stab_Z, actC_eq_zero_iff]
    exact hσ

/-- If the lattice part of a combined symmetry preserves `Δ`, membership in
the corresponding regular locus is invariant. -/
theorem combined_smul_mem_chargeRegularLocus_iff (p : GLTilde × AutPairQuot v)
    {Δ : Set Λ} (hΔ : p.2.lam '' Δ = Δ)
    (σ : StabilityCondition.WithClassMap C v) :
    p • σ ∈ chargeRegularLocus (C := C) (v := v) Δ ↔
      σ ∈ chargeRegularLocus (C := C) (v := v) Δ := by
  rw [mem_chargeRegularLocus_iff, mem_chargeRegularLocus_iff]
  constructor
  · intro hp δ hδ hzero
    have hmem : δ ∈ p.2.lam '' Δ := by simpa [hΔ] using hδ
    obtain ⟨ε, hε, rfl⟩ := hmem
    have hwall : σ ∈ chargeZeroLocus (C := C) (v := v) (p.2.lam ε) := hzero
    exact hp ε hε ((combined_smul_mem_chargeZeroLocus_iff p σ ε).2 hwall)
  · intro hσ δ hδ hzero
    have hlam : p.2.lam δ ∈ Δ := by
      rw [← hΔ]
      exact ⟨δ, hδ, rfl⟩
    have hwall : p • σ ∈ chargeZeroLocus (C := C) (v := v) δ := hzero
    exact hσ (p.2.lam δ) hlam
      ((combined_smul_mem_chargeZeroLocus_iff p σ δ).1 hwall)

/-- If the lattice part of a combined symmetry preserves `Δ`, the symmetry
preserves the regular locus setwise. -/
theorem image_chargeRegularLocus_smul (p : GLTilde × AutPairQuot v) {Δ : Set Λ}
    (hΔ : p.2.lam '' Δ = Δ) :
    (fun σ : StabilityCondition.WithClassMap C v ↦ p • σ) ''
        chargeRegularLocus (C := C) (v := v) Δ =
      chargeRegularLocus (C := C) (v := v) Δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact (combined_smul_mem_chargeRegularLocus_iff p hΔ σ).2 hσ
  · intro σ hσ
    refine ⟨p⁻¹ • σ, ?_, by simp⟩
    apply (combined_smul_mem_chargeRegularLocus_iff p hΔ (p⁻¹ • σ)).1
    simpa using hσ

/-! ## Chambers -/

/-- A chamber is a connected component of the regular-locus subtype.

No openness of that subtype is asserted here; see the module docstring. -/
def ChargeChamber (Δ : Set Λ) :=
  ConnectedComponents (chargeRegularLocus (C := C) (v := v) Δ)

/-- The chamber containing a point of the regular locus. -/
def chargeChamberOf {Δ : Set Λ} (σ : chargeRegularLocus (C := C) (v := v) Δ) :
    ChargeChamber (C := C) (v := v) Δ :=
  ConnectedComponents.mk σ

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero
