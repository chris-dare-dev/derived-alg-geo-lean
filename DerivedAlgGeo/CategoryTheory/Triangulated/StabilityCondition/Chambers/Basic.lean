/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.LatticeAut
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.PeriodMap

/-!
# Charge-vanishing walls and chambers in the stability space

For a stability condition `σ : StabilityCondition.WithClassMap C v` and a
class `δ : Λ`, this file defines the wall on which the central charge kills
`δ`.  A regular locus avoids the walls indexed by a chosen set `Δ`, and a
`StabChamber` is a connected component of that regular-locus subtype.

## Four different wall constructions

The wall here is the **charge-vanishing locus in the stability space**:
`stabWall δ = {σ | σ.Z δ = 0}`.

It is not `Wall.Spherical.chamber`, a subset of `V × V` in the
`exp(β + iω)` chart cut out by real half-spaces indexed by
`sphericalPlus`.  It is not the tilt-stability construction in
`Walls/Numerical/Basic.lean`, whose parameter space is the `(s, t)` half-plane
and whose walls are conics.  It is also not `PeriodDomain.wall`, whose points
are submodules of a quadratic space and whose wall condition is orthogonality
to a class.

No map from the stability space to any of those three parameter spaces is
defined in the repository, and constructing one is outside the scope of this
file.

## Topological boundary

Only the already-installed topology on `StabilityCondition.WithClassMap C v`
and the induced subtype topology are used to form `ConnectedComponents`.
Nothing here proves that `stabWall` is closed or that `stabRegular` is open.
Until such a theorem is supplied, a `StabChamber` is the connected component
of a possibly non-open subspace and should not be read as a chamber in the
geometric sense.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Set

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

open GroupAction

/-! ## Walls and their complement -/

/-- The locus of stability conditions whose central charge kills `δ`. -/
def stabWall (δ : Λ) : Set (StabilityCondition.WithClassMap C v) :=
  {σ | σ.Z δ = 0}

/-- Membership in `stabWall δ` is vanishing of the charge at `δ`. -/
theorem mem_stabWall_iff (δ : Λ) (σ : StabilityCondition.WithClassMap C v) :
    σ ∈ stabWall (C := C) (v := v) δ ↔ σ.Z δ = 0 :=
  Iff.rfl

/-- The stability conditions whose central charge is nonzero on every class
in `Δ`. -/
def stabRegular (Δ : Set Λ) : Set (StabilityCondition.WithClassMap C v) :=
  {σ | ∀ δ ∈ Δ, σ.Z δ ≠ 0}

/-- Membership in `stabRegular Δ` is nonvanishing on every class of `Δ`. -/
theorem mem_stabRegular_iff (Δ : Set Λ) (σ : StabilityCondition.WithClassMap C v) :
    σ ∈ stabRegular (C := C) (v := v) Δ ↔ ∀ δ ∈ Δ, σ.Z δ ≠ 0 :=
  Iff.rfl

/-- Enlarging the indexing set can only shrink the regular locus. -/
theorem stabRegular_antitone : Antitone (stabRegular (C := C) (v := v)) :=
  fun _ _ h _ hσ δ hδ ↦ hσ δ (h hδ)

/-- Avoiding the walls of every lattice class is impossible because the zero
class has zero charge. -/
theorem stabRegular_univ : stabRegular (C := C) (v := v) Set.univ = ∅ := by
  ext σ
  simp only [mem_stabRegular_iff, Set.mem_univ, ne_eq, Set.mem_empty_iff_false,
    iff_false]
  intro h
  exact h 0 trivial (map_zero σ.Z)

/-- The regular locus is the complement of the union of its walls. -/
theorem stabRegular_eq_compl_iUnion (Δ : Set Λ) :
    stabRegular (C := C) (v := v) Δ =
      (⋃ δ ∈ Δ, stabWall (C := C) (v := v) δ)ᶜ := by
  ext σ
  simp [stabRegular, stabWall]

/-! ## Equivariance -/

variable [IsTriangulated C]

/-- The combined symmetry sends the wall indexed by `p.2.lam δ` to the wall
indexed by `δ`. -/
theorem combined_smul_mem_stabWall_iff (p : GLTilde × AutPairQuot v)
    (σ : StabilityCondition.WithClassMap C v) (δ : Λ) :
    p • σ ∈ stabWall (C := C) (v := v) δ ↔
      σ ∈ stabWall (C := C) (v := v) (p.2.lam δ) := by
  rcases p with ⟨x, q⟩
  induction q using _root_.Quotient.inductionOn with
  | _ a =>
      change (((x, AutPairQuot.mk a) • σ).Z δ = 0 ↔
        σ.Z ((AutPairQuot.mk a).lam δ) = 0)
      rw [prod_mk_smul_Z, AutPairQuot.lam_mk, actC_eq_zero_iff]

/-- A combined symmetry maps the wall indexed by the transformed class
exactly onto the original wall. -/
theorem image_stabWall_smul (p : GLTilde × AutPairQuot v) (δ : Λ) :
    (fun σ : StabilityCondition.WithClassMap C v ↦ p • σ) ''
        stabWall (C := C) (v := v) (p.2.lam δ) =
      stabWall (C := C) (v := v) δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact (combined_smul_mem_stabWall_iff p σ δ).2 hσ
  · intro σ hσ
    refine ⟨p⁻¹ • σ, ?_, by simp⟩
    apply (combined_smul_mem_stabWall_iff p (p⁻¹ • σ) δ).1
    simpa using hσ

/-- The `GLTilde` action preserves every charge-vanishing wall setwise. -/
theorem image_stabWall_gltilde (x : GLTilde) (δ : Λ) :
    (fun σ : StabilityCondition.WithClassMap C v ↦ x • σ) ''
        stabWall (C := C) (v := v) δ =
      stabWall (C := C) (v := v) δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [mem_stabWall_iff, smul_stab_Z, actC_eq_zero_iff]
    exact hσ
  · intro σ hσ
    refine ⟨x⁻¹ • σ, ?_, by simp⟩
    rw [mem_stabWall_iff, smul_stab_Z, actC_eq_zero_iff]
    exact hσ

/-- If the lattice part of a combined symmetry preserves `Δ`, membership in
the corresponding regular locus is invariant. -/
theorem combined_smul_mem_stabRegular_iff (p : GLTilde × AutPairQuot v)
    {Δ : Set Λ} (hΔ : p.2.lam '' Δ = Δ)
    (σ : StabilityCondition.WithClassMap C v) :
    p • σ ∈ stabRegular (C := C) (v := v) Δ ↔
      σ ∈ stabRegular (C := C) (v := v) Δ := by
  rw [mem_stabRegular_iff, mem_stabRegular_iff]
  constructor
  · intro hp δ hδ hzero
    have hmem : δ ∈ p.2.lam '' Δ := by simpa [hΔ] using hδ
    obtain ⟨ε, hε, rfl⟩ := hmem
    have hwall : σ ∈ stabWall (C := C) (v := v) (p.2.lam ε) := hzero
    exact hp ε hε ((combined_smul_mem_stabWall_iff p σ ε).2 hwall)
  · intro hσ δ hδ hzero
    have hlam : p.2.lam δ ∈ Δ := by
      rw [← hΔ]
      exact ⟨δ, hδ, rfl⟩
    have hwall : p • σ ∈ stabWall (C := C) (v := v) δ := hzero
    exact hσ (p.2.lam δ) hlam
      ((combined_smul_mem_stabWall_iff p σ δ).1 hwall)

/-- If the lattice part of a combined symmetry preserves `Δ`, the symmetry
preserves the regular locus setwise. -/
theorem image_stabRegular_smul (p : GLTilde × AutPairQuot v) {Δ : Set Λ}
    (hΔ : p.2.lam '' Δ = Δ) :
    (fun σ : StabilityCondition.WithClassMap C v ↦ p • σ) ''
        stabRegular (C := C) (v := v) Δ =
      stabRegular (C := C) (v := v) Δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact (combined_smul_mem_stabRegular_iff p hΔ σ).2 hσ
  · intro σ hσ
    refine ⟨p⁻¹ • σ, ?_, by simp⟩
    apply (combined_smul_mem_stabRegular_iff p hΔ (p⁻¹ • σ)).1
    simpa using hσ

/-! ## Chambers -/

/-- A chamber is a connected component of the regular-locus subtype.

No openness of that subtype is asserted here; see the module docstring. -/
def StabChamber (Δ : Set Λ) :=
  ConnectedComponents (stabRegular (C := C) (v := v) Δ)

/-- The chamber containing a point of the regular locus. -/
def chamberOf {Δ : Set Λ} (σ : stabRegular (C := C) (v := v) Δ) :
    StabChamber (C := C) (v := v) Δ :=
  ConnectedComponents.mk σ

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall
