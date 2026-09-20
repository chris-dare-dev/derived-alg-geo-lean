/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.SLocal
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseTruncation

/-!
# S-local slicings over a family of base changes

The family-level S-local t-structure quantifier belongs to the Families layer.
This file adds the phase-level analogue in the geometric stability layer,
where the slicing and phase-truncation APIs are used. The target slicing,
t-exactness, and phase comparison remain explicit owner data: this module does
not manufacture geometric restriction or generation theorems from affineness.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]

namespace Slicing

/-- A slicing restriction along a functor.

The target slicing and its t-exactness are kept together. The phase
compatibility field is stronger than preservation of semistability alone: it
is the exact phase-level comparison needed by a local slicing, while the
t-exactness field is the bridge to the t-structure API. -/
structure Restriction (s : Slicing C) (F : C ⥤ D) where
  /-- The slicing on the target category. -/
  slicing : Slicing D
  /-- The ambient functor is t-exact for the t-structures owned by the two
  slicings. -/
  isTExact : F.IsTExact (s.toTStructure C) (slicing.toTStructure D)
  /-- The target phase slices are detected by the source phase slices. -/
  phase_iff : ∀ (φ : ℝ) (X : C), slicing.P φ (F.obj X) ↔ s.P φ X

namespace Restriction

variable {s : Slicing C} {F : C ⥤ D}

/-- Equality of target slicings from equality of all phase predicates. -/
theorem slicing_eq_of_phase_iff (r₁ r₂ : s.Restriction F)
    (h : ∀ (φ : ℝ) (Y : D), r₁.slicing.P φ Y ↔ r₂.slicing.P φ Y) :
    r₁.slicing = r₂.slicing := by
  apply Slicing.ext
  funext φ Y
  exact propext (h φ Y)

/-- The t-structure restriction carried by a slicing restriction. -/
def toTStructureRestriction (r : s.Restriction F) :
    (s.toTStructure C).Restriction F :=
  { tStructure := r.slicing.toTStructure D
    isTExact := r.isTExact }

end Restriction

end Slicing

end CategoryTheory.Triangulated

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory.Families

universe u

variable {S : Scheme.{u}}

namespace OpenRestrictionFamily

variable {X : SchemeBaseChange S} {P : ObjectProperty (SourceDqc X)}
  [P.ContainsZero] {DS : KFlatBaseChangeData X (identityBaseChange S)}

variable {R : OpenRestrictionFamily X P DS}
  {s : Slicing (DS.QuasicoherentCategory P)}

/-- **S-local slicing**: every quasi-compact open carries a slicing whose
phase predicates and associated t-structure are compatible with restriction.
The target slicings are chosen because downstream phase arguments need the
actual owner data, not only a proposition that some slicing exists. -/
structure SLocalSlicingData (R : OpenRestrictionFamily X P DS)
    (s : Slicing (DS.QuasicoherentCategory P)) where
  restriction (U : S.Opens) (hU : CompactSpace U.toScheme) :
    s.Restriction (R.restriction U hU)

/-- Propositional shadow of `SLocalSlicingData`. -/
def IsSLocalSlicing (R : OpenRestrictionFamily X P DS)
    (s : Slicing (DS.QuasicoherentCategory P)) : Prop :=
  ∀ (U : S.Opens) (hU : CompactSpace U.toScheme),
    Nonempty (s.Restriction (R.restriction U hU))

namespace SLocalSlicingData

variable {R : OpenRestrictionFamily X P DS}
  {s : Slicing (DS.QuasicoherentCategory P)}

/-- Chosen slicing restrictions witness the propositional S-local condition. -/
theorem isSLocal (L : SLocalSlicingData R s) : R.IsSLocalSlicing s :=
  fun U hU ↦ ⟨L.restriction U hU⟩

/-- Forget the phase data to obtain the associated S-local t-structure. -/
def toSLocalData (L : SLocalSlicingData R s) :
    SLocalData R (s.toTStructure _) where
  restriction U hU :=
    (L.restriction U hU).toTStructureRestriction

/-- Slicing restrictions agree once their complete phase predicates agree.
The phase comparison is left explicit because image-generation of a target
category is geometric, not a consequence of t-exactness alone. -/
theorem restriction_eq_of_phase_iff (_L : SLocalSlicingData R s)
    (U : S.Opens) (hU : CompactSpace U.toScheme)
    {r₁ r₂ : s.Restriction (R.restriction U hU)}
    (h : ∀ (φ : ℝ) (Y : (R.data U hU).QuasicoherentCategory P),
      r₁.slicing.P φ Y ↔ r₂.slicing.P φ Y) :
    r₁.slicing = r₂.slicing := by
  exact Slicing.Restriction.slicing_eq_of_phase_iff r₁ r₂ h

end SLocalSlicingData

/-- An affine-base package containing two distinct S-local t-structures.

Affineness alone does not create K-flat families or t-exactness. The two
chosen slicing-locality witnesses and the distinctness proof are therefore
explicit inputs to the adapter. -/
structure TwoDistinctAffineSLocalTStructures
    (R : OpenRestrictionFamily X P DS)
    (s₁ s₂ : Slicing (DS.QuasicoherentCategory P)) where
  affineBase : IsAffine S
  first : SLocalData R (s₁.toTStructure _)
  second : SLocalData R (s₂.toTStructure _)
  distinct : s₁.toTStructure _ ≠ s₂.toTStructure _

/-- Build the affine package from two actual slicing-locality witnesses. -/
def TwoDistinctAffineSLocalTStructures.ofSlicingData
    (hAffine : IsAffine S)
    {s₁ s₂ : Slicing (DS.QuasicoherentCategory P)}
    (L₁ : SLocalSlicingData R s₁) (L₂ : SLocalSlicingData R s₂)
    (hne : s₁.toTStructure _ ≠ s₂.toTStructure _) :
    TwoDistinctAffineSLocalTStructures R s₁ s₂ where
  affineBase := hAffine
  first := L₁.toSLocalData
  second := L₂.toSLocalData
  distinct := hne

end OpenRestrictionFamily

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
