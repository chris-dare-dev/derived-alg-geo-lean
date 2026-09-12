/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Chambers.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Effective

/-!
# Symmetry actions on chambers

A set of lattice classes is `IsAutStable` when every compatible
autoequivalence preserves membership through its descended lattice
automorphism. For such a set, the combined `GLTilde × AutPairQuot v` action
restricts to the regular-locus subtype and hence, through the existing generic
connected-component machinery, acts on `StabChamber`.

The full kernel of the action on the stability space acts trivially on chamber
labels. Consequently the chamber action descends to
`EffectiveCombinedSymmetry v`.

No faithfulness is asserted for the descended chamber action: an effective
symmetry can move stability conditions inside a chamber while fixing its
component label. Nor does this file assert transitivity, nonemptiness of any
chamber, finiteness of a chamber stabilizer, an orbit-space construction, or
openness of the regular locus.
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

/-! ## Invariant class sets -/

/-- A set of lattice classes is stable under every lattice automorphism
carried by a compatible autoequivalence. -/
def IsAutStable (Δ : Set Λ) : Prop :=
  ∀ (q : AutPairQuot v) (δ : Λ), δ ∈ Δ ↔ q.lam δ ∈ Δ

/-- The full class lattice is stable under compatible autoequivalences. -/
@[simp]
theorem isAutStable_univ : IsAutStable (C := C) (v := v) Set.univ := by
  intro q δ
  simp

/-- An intersection of stable class sets is stable. -/
theorem IsAutStable.inter {Δ Γ : Set Λ}
    (hΔ : IsAutStable (C := C) (v := v) Δ)
    (hΓ : IsAutStable (C := C) (v := v) Γ) :
    IsAutStable (C := C) (v := v) (Δ ∩ Γ) := by
  intro q δ
  exact and_congr (hΔ q δ) (hΓ q δ)

/-- A stable class set is carried onto itself by each descended lattice
automorphism. -/
theorem IsAutStable.image_lam {Δ : Set Λ}
    (hΔ : IsAutStable (C := C) (v := v) Δ) (q : AutPairQuot v) :
    q.lam '' Δ = Δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨δ, hδ, rfl⟩
    exact (hΔ q δ).1 hδ
  · intro δ hδ
    refine ⟨q.lam.symm δ, ?_, by simp⟩
    exact (hΔ q (q.lam.symm δ)).2 (by simpa using hδ)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}
variable {Δ : Set Λ}

open StabWall
open scoped GroupAction

/-! ## The regular-locus action -/

/-- The combined symmetry action restricts to the regular locus of an
autoequivalence-stable class set. -/
noncomputable abbrev stabRegularMulAction
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ) :
    MulAction (GLTilde × AutPairQuot v) (stabRegular (C := C) (v := v) Δ) where
  smul p σ := ⟨p • σ.1, (combined_smul_mem_stabRegular_iff p
    (hΔ.image_lam p.2) σ.1).2 σ.2⟩
  one_smul σ := by
    apply Subtype.ext
    exact one_smul (GLTilde × AutPairQuot v) σ.1
  mul_smul p q σ := by
    apply Subtype.ext
    exact mul_smul p q σ.1

/-- The restricted action is continuous in the regular-locus variable for
each fixed combined symmetry. -/
noncomputable abbrev stabRegularContinuousConstSMul
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ) :
    letI := stabRegularMulAction hΔ
    ContinuousConstSMul (GLTilde × AutPairQuot v)
      (stabRegular (C := C) (v := v) Δ) := by
  letI := stabRegularMulAction hΔ
  exact
    { continuous_const_smul := fun p ↦
        ((continuous_const_smul p : Continuous fun σ :
          StabilityCondition.WithClassMap C v ↦ p • σ).comp
          continuous_subtype_val).subtype_mk _ }

/-! ## Chamber transport -/

/-- The named specialization of `componentSmul` to regular-locus chambers. -/
def chamberSmul (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ)
    (p : GLTilde × AutPairQuot v)
    (cc : StabChamber (C := C) (v := v) Δ) :
    StabChamber (C := C) (v := v) Δ :=
  letI := stabRegularMulAction hΔ
  letI := stabRegularContinuousConstSMul hΔ
  componentSmul p cc

/-- The named specialization of `componentHomeomorph` between chambers of
the regular locus. -/
def chamberHomeomorph
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ)
    (p : GLTilde × AutPairQuot v)
    (cc : StabChamber (C := C) (v := v) Δ) :
    {σ : stabRegular (C := C) (v := v) Δ // chamberOf σ = cc} ≃ₜ
      {σ : stabRegular (C := C) (v := v) Δ //
        chamberOf σ = chamberSmul hΔ p cc} :=
  letI := stabRegularMulAction hΔ
  letI := stabRegularContinuousConstSMul hΔ
  componentHomeomorph p cc

/-- The subgroup of combined symmetries preserving a chamber label. -/
abbrev chamberStabilizer
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ)
    (cc : StabChamber (C := C) (v := v) Δ) :
    Subgroup (GLTilde × AutPairQuot v) :=
  letI := stabRegularMulAction hΔ
  letI := stabRegularContinuousConstSMul hΔ
  componentStabilizer cc

/-! ## Descent to the effective quotient -/

/-- The permutation representation of the combined symmetry group on chamber
labels. -/
noncomputable def chamberActionHom
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ) :
    (GLTilde × AutPairQuot v) →*
      Equiv.Perm (StabChamber (C := C) (v := v) Δ) :=
  letI := stabRegularMulAction hΔ
  letI := stabRegularContinuousConstSMul hΔ
  letI : MulAction (GLTilde × AutPairQuot v)
      (StabChamber (C := C) (v := v) Δ) := componentMulAction
  MulAction.toPermHom _ _

/-- Every symmetry acting trivially on the full stability space also acts
trivially on chamber labels. -/
theorem combinedActionKernel_le_chamberActionHom_ker
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ) :
    combinedActionKernel v ≤
      (chamberActionHom (C := C) (v := v) hΔ).ker := by
  letI := stabRegularMulAction hΔ
  letI := stabRegularContinuousConstSMul hΔ
  intro p hp
  rw [MonoidHom.mem_ker] at hp ⊢
  apply Equiv.ext
  intro cc
  obtain ⟨σ, rfl⟩ := ConnectedComponents.surjective_coe cc
  simp only [chamberActionHom]
  change ConnectedComponents.mk (p • σ) = ConnectedComponents.mk σ
  apply congrArg ConnectedComponents.mk
  apply Subtype.ext
  change p • σ.1 = σ.1
  simpa [combinedActionHom] using congrArg
    (fun e : Equiv.Perm (StabilityCondition.WithClassMap C v) ↦ e σ.1) hp

/-- The chamber permutation representation descended through the full kernel
of the action on the stability space. -/
noncomputable def effectiveChamberActionHom
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ) :
    EffectiveCombinedSymmetry v →*
      Equiv.Perm (StabChamber (C := C) (v := v) Δ) :=
  QuotientGroup.lift (combinedActionKernel v)
    (chamberActionHom (C := C) (v := v) hΔ)
    (combinedActionKernel_le_chamberActionHom_ker hΔ)

/-- The effective combined symmetry group acts on chamber labels. This action
is deliberately not asserted faithful; see the module docstring. -/
noncomputable abbrev effectiveCombinedChamberMulAction
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ) :
    MulAction (EffectiveCombinedSymmetry v)
      (StabChamber (C := C) (v := v) Δ) :=
  MulAction.compHom _
    (effectiveChamberActionHom (C := C) (v := v) hΔ)

/-- On a representative of the effective quotient, the descended action is
the original combined action on chamber labels. -/
@[simp]
theorem effectiveCombinedChamber_smul_coe
    (hΔ : StabWall.IsAutStable (C := C) (v := v) Δ)
    (p : GLTilde × AutPairQuot v)
    (cc : StabChamber (C := C) (v := v) Δ) :
    letI := effectiveCombinedChamberMulAction hΔ
    (p : EffectiveCombinedSymmetry v) • cc = chamberSmul hΔ p cc :=
  rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
