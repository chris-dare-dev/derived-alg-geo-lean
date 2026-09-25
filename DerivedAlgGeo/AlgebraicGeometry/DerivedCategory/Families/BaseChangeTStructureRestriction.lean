/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeBoundedAmplitude
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Restriction

/-!
# Conditional restriction of a target t-structure to bounded-coherent Dqc

`TargetBoundedTStructure` supplies a t-structure on the target quasicoherent
derived category and identifies its bounded locus with ambient cohomological
boundedness. On a locally Noetherian target, finite presentation of cohomology
is triangulated. Consequently, if nonpositive truncations of bounded-coherent
objects retain finite-presentation cohomology, then the t-structure restricts
to the intrinsic bounded-coherent full subcategory, and the restriction is
bounded. The complementary truncation condition follows from the truncation
triangle; it is not a second geometric premise.

Neither the supplied t-structure nor the finite-presentation preservation
premise is constructed here. In particular, `TargetBoundedTStructure` is not
identified with a paper-defined base-changed t-structure.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
namespace TargetBoundedTStructure

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  [IsLocallyNoetherian (X ⨯ T).left]
  (τ : TargetBoundedTStructure X T)
  (hfpLE : ∀ (E : TargetDqc X T),
    Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left E →
    ∀ n : ℤ,
      Dqc.schemeFinitePresentationCohomology (X ⨯ T).left
        ((τ.tStructure.truncLE n).obj E))

include hfpLE in
/-- One-sided finite-presentation preservation suffices for the target
t-structure to induce a t-structure on bounded-coherent Dqc. -/
theorem hasInducedBoundedCoherent :
    (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).HasInducedTStructure
      τ.tStructure := by
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated :=
    inferInstance
  apply ObjectProperty.HasInducedTStructure.mk'
  intro E hE n
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (τ.bounded_iff E).2 hE.1
  letI : τ.tStructure.IsGE E a := ha
  letI : τ.tStructure.IsLE E b := hb
  have hfpGE : Dqc.schemeFinitePresentationCohomology (X ⨯ T).left
      ((τ.tStructure.truncGE n).obj E) := by
    let P := Dqc.schemeFinitePresentationCohomology (X ⨯ T).left
    let Z := (τ.tStructure.triangleLEGE (n - 1) n (by omega)).obj E
    have hZ : Z ∈ distTriang _ :=
      τ.tStructure.triangleLEGE_distinguished (n - 1) n (by omega) E
    have hfpE : P E := hE.2
    apply P.ext_of_isTriangulatedClosed₃ Z hZ
    · simpa only [Z, TStructure.triangleLEGE_obj_obj₁] using
        hfpLE E hE (n - 1)
    · simpa only [Z, TStructure.triangleLEGE_obj_obj₂] using hfpE
  constructor
  · have hBound : τ.tStructure.bounded ((τ.tStructure.truncLE n).obj E) :=
      ⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩
    exact ⟨(τ.bounded_iff _).1 hBound, hfpLE E hE n⟩
  · have hBound : τ.tStructure.bounded ((τ.tStructure.truncGE n).obj E) :=
      ⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩
    exact ⟨(τ.bounded_iff _).1 hBound, hfpGE⟩

include hfpLE in
/-- The t-structure induced by `τ` on the intrinsic bounded-coherent Dqc
category, conditional on finite-presentation preservation by truncation. -/
noncomputable def boundedCoherentTStructure :
    TStructure (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) := by
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated :=
    inferInstance
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).HasInducedTStructure
    τ.tStructure := τ.hasInducedBoundedCoherent hfpLE
  exact (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).tStructure τ.tStructure

include hfpLE in
/-- The induced bounded-coherent t-structure is bounded. This does not
construct `τ` or prove the truncation-coherence premise. -/
theorem boundedCoherentTStructureIsBounded :
    TStructure.IsBounded (τ.boundedCoherentTStructure hfpLE) := by
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated :=
    inferInstance
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).HasInducedTStructure
    τ.tStructure := τ.hasInducedBoundedCoherent hfpLE
  change TStructure.IsBounded
    ((Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).tStructure τ.tStructure)
  apply (ObjectProperty.tStructure_isBounded_iff_le_bounded).2
  intro E hE
  exact (τ.bounded_iff E).2 hE.1

include hfpLE in
/-- The nonpositive half of the named restriction is inherited from `τ`. -/
theorem boundedCoherentTStructureIsLE
    (E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) (n : ℤ) :
    (τ.boundedCoherentTStructure hfpLE).IsLE E n ↔
      τ.tStructure.IsLE E.obj n := by
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated :=
    inferInstance
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).HasInducedTStructure
    τ.tStructure := τ.hasInducedBoundedCoherent hfpLE
  change ((Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).tStructure
    τ.tStructure).IsLE E n ↔ τ.tStructure.IsLE E.obj n
  exact (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).tStructure_isLE_iff
    τ.tStructure E n

include hfpLE in
/-- The nonnegative half of the named restriction is inherited from `τ`. -/
theorem boundedCoherentTStructureIsGE
    (E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) (n : ℤ) :
    (τ.boundedCoherentTStructure hfpLE).IsGE E n ↔
      τ.tStructure.IsGE E.obj n := by
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated :=
    inferInstance
  letI : (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).HasInducedTStructure
    τ.tStructure := τ.hasInducedBoundedCoherent hfpLE
  change ((Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).tStructure
    τ.tStructure).IsGE E n ↔ τ.tStructure.IsGE E.obj n
  exact (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).tStructure_isGE_iff
    τ.tStructure E n

end

end TargetBoundedTStructure
end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
