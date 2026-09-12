/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Components
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Effective
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Topology
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Orbit spaces of stability conditions

This file packages the topological orbit spaces of the three symmetry groups
acting on a Bridgeland stability space: compatible autoequivalences, the
combined lifted-linear/autoequivalence group, and its effective quotient.

The topology on every orbit space is the ordinary coinduced topology on
`MulAction.orbitRel.Quotient`.  Mathlib's general theorem for continuous group
actions therefore makes each orbit projection a continuous open quotient map.
The connected-component labelling descends equivariantly to orbit spaces.

Finally, autoequivalence orbits map continuously and surjectively to combined
orbits, while the combined and effective actions have exactly the same orbits
and hence homeomorphic orbit spaces.  No separation, proper-discontinuity, or
covering-space property is asserted here.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

open scoped GroupAction

/-! ## Connected-component labels on orbit spaces -/

universe uG uX

variable {G : Type uG} {X : Type uX} [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

/-- The orbit space of connected-component labels induced by a continuous
group action on `X`. -/
abbrev ComponentOrbitSpace (G : Type uG) (X : Type uX) [Group G]
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] :=
  MulAction.orbitRel.Quotient G (ConnectedComponents X)

/-- The connected-component labelling carries point orbits to component-label
orbits. -/
private theorem componentOrbitMap_wellDefined (x y : X)
    (hxy : MulAction.orbitRel G X x y) :
    MulAction.orbitRel G (ConnectedComponents X)
      (ConnectedComponents.mk x) (ConnectedComponents.mk y) := by
  rw [MulAction.orbitRel_apply] at hxy ⊢
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, ?_⟩
  change g • y = x at hg
  change componentSmul g (ConnectedComponents.mk y) = ConnectedComponents.mk x
  rw [componentSmul_mk, hg]

/-- Connected-component labelling descends from points to their group orbits. -/
def componentOrbitMap :
    MulAction.orbitRel.Quotient G X → ComponentOrbitSpace G X :=
  Quotient.map ConnectedComponents.mk componentOrbitMap_wellDefined

@[simp]
theorem componentOrbitMap_mk (x : X) :
    componentOrbitMap (G := G) (Quotient.mk'' x) =
      (Quotient.mk'' (ConnectedComponents.mk x) : ComponentOrbitSpace G X) :=
  rfl

/-- The descended connected-component labelling is continuous for the quotient
topologies. -/
theorem continuous_componentOrbitMap :
    Continuous (componentOrbitMap (G := G) (X := X)) :=
  continuous_quot_map componentOrbitMap_wellDefined
    ConnectedComponents.continuous_coe

/-! ## Stability-condition orbit spaces -/

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Stability conditions modulo compatible autoequivalences. -/
abbrev AutPairOrbitSpace (v : K₀ C →+ Λ) :=
  MulAction.orbitRel.Quotient (AutPairQuot v)
    (StabilityCondition.WithClassMap C v)

/-- Stability conditions modulo the combined lifted-linear and
autoequivalence action. -/
abbrev CombinedOrbitSpace (v : K₀ C →+ Λ) :=
  MulAction.orbitRel.Quotient (GLTilde × AutPairQuot v)
    (StabilityCondition.WithClassMap C v)

/-- Stability conditions modulo the effective combined symmetry group. -/
abbrev EffectiveCombinedOrbitSpace (v : K₀ C →+ Λ) :=
  MulAction.orbitRel.Quotient (EffectiveCombinedSymmetry v)
    (StabilityCondition.WithClassMap C v)

/-- The projection to compatible-autoequivalence orbits. -/
def autPairOrbitMap :
    StabilityCondition.WithClassMap C v → AutPairOrbitSpace v :=
  fun σ ↦ _root_.Quotient.mk (MulAction.orbitRel (AutPairQuot v)
    (StabilityCondition.WithClassMap C v)) σ

/-- The projection to combined-symmetry orbits. -/
def combinedOrbitMap :
    StabilityCondition.WithClassMap C v → CombinedOrbitSpace v :=
  fun σ ↦ _root_.Quotient.mk (MulAction.orbitRel (GLTilde × AutPairQuot v)
    (StabilityCondition.WithClassMap C v)) σ

/-- The effective combined action is continuous in the stability-condition
variable for each fixed symmetry class. -/
noncomputable instance effectiveCombinedContinuousConstSMul :
    ContinuousConstSMul (EffectiveCombinedSymmetry v)
      (StabilityCondition.WithClassMap C v) where
  continuous_const_smul q := by
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    exact continuous_const_smul p

/-- The projection to effective-combined-symmetry orbits. -/
def effectiveCombinedOrbitMap :
    StabilityCondition.WithClassMap C v → EffectiveCombinedOrbitSpace v :=
  fun σ ↦ _root_.Quotient.mk (MulAction.orbitRel (EffectiveCombinedSymmetry v)
    (StabilityCondition.WithClassMap C v)) σ

/-- The compatible-autoequivalence orbit projection is a continuous open
quotient map. -/
theorem isOpenQuotientMap_autPairOrbitMap :
    IsOpenQuotientMap (autPairOrbitMap (C := C) (v := v)) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The combined-symmetry orbit projection is a continuous open quotient map. -/
theorem isOpenQuotientMap_combinedOrbitMap :
    IsOpenQuotientMap (combinedOrbitMap (C := C) (v := v)) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The effective-combined-symmetry orbit projection is a continuous open
quotient map. -/
theorem isOpenQuotientMap_effectiveCombinedOrbitMap :
    IsOpenQuotientMap (effectiveCombinedOrbitMap (C := C) (v := v)) :=
  MulAction.isOpenQuotientMap_quotientMk

/-! ## Comparison of the three orbit spaces -/

/-- The autoequivalence orbit relation is contained in the combined-symmetry
orbit relation. -/
private theorem autPairOrbitRel_le_combinedOrbitRel
    (σ τ : StabilityCondition.WithClassMap C v)
    (h : MulAction.orbitRel (AutPairQuot v)
      (StabilityCondition.WithClassMap C v) σ τ) :
    MulAction.orbitRel (GLTilde × AutPairQuot v)
      (StabilityCondition.WithClassMap C v) σ τ := by
  rw [MulAction.orbitRel_apply] at h ⊢
  obtain ⟨q, hq⟩ := h
  refine ⟨(1, q), ?_⟩
  change (1 : GLTilde) • q • τ = σ
  rw [one_smul]
  exact hq

/-- Forgetting that an orbit was generated only by compatible
autoequivalences gives its combined-symmetry orbit. -/
def autPairToCombinedOrbitMap : AutPairOrbitSpace v → CombinedOrbitSpace v :=
  Quotient.map id autPairOrbitRel_le_combinedOrbitRel

@[simp]
theorem autPairToCombinedOrbitMap_mk
    (σ : StabilityCondition.WithClassMap C v) :
    autPairToCombinedOrbitMap (C := C) (v := v) (Quotient.mk'' σ) =
      (Quotient.mk'' σ : CombinedOrbitSpace v) :=
  rfl

/-- The comparison from autoequivalence orbits to combined orbits is
continuous. -/
theorem continuous_autPairToCombinedOrbitMap :
    Continuous (autPairToCombinedOrbitMap (C := C) (v := v)) :=
  continuous_quot_map autPairOrbitRel_le_combinedOrbitRel continuous_id

/-- Every combined orbit is the image of an autoequivalence orbit. -/
theorem surjective_autPairToCombinedOrbitMap :
    Function.Surjective (autPairToCombinedOrbitMap (C := C) (v := v)) :=
  Quotient.map_surjective autPairOrbitRel_le_combinedOrbitRel
    Function.surjective_id

/-- Passing from the combined group to its quotient by the action kernel does
not change the orbit relation on the stability space. -/
theorem combinedOrbitRel_iff_effectiveCombinedOrbitRel
    (σ τ : StabilityCondition.WithClassMap C v) :
    MulAction.orbitRel (GLTilde × AutPairQuot v)
        (StabilityCondition.WithClassMap C v) σ τ ↔
      MulAction.orbitRel (EffectiveCombinedSymmetry v)
        (StabilityCondition.WithClassMap C v) σ τ := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨(p : EffectiveCombinedSymmetry v), hp⟩
  · rintro ⟨q, hq⟩
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨p, hq⟩

/-- Combined and effective symmetries have homeomorphic orbit spaces because
quotienting the group by the full action kernel leaves every orbit unchanged. -/
def combinedEffectiveOrbitHomeomorph :
    CombinedOrbitSpace v ≃ₜ EffectiveCombinedOrbitSpace v :=
  Homeomorph.Quotient.congrRight
    (combinedOrbitRel_iff_effectiveCombinedOrbitRel (C := C) (v := v))

@[simp]
theorem combinedEffectiveOrbitHomeomorph_mk
    (σ : StabilityCondition.WithClassMap C v) :
    combinedEffectiveOrbitHomeomorph (C := C) (v := v)
        (Quotient.mk'' σ) =
      (Quotient.mk'' σ : EffectiveCombinedOrbitSpace v) :=
  rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
