import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeTStructureRestriction

/-! Axiom audit and direct client for conditional bounded-coherent t-structure restriction. -/

#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure.hasInducedBoundedCoherent
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure.boundedCoherentTStructure
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure.boundedCoherentTStructureIsBounded
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure.boundedCoherentTStructureIsLE
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure.boundedCoherentTStructureIsGE

noncomputable section

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure

universe u

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  [IsLocallyNoetherian (X ⨯ T).left]
  (τ : TargetBoundedTStructure X T)
  (hfpLE : ∀ (E : TargetDqc X T),
    Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left E →
    ∀ n : ℤ,
      Dqc.schemeFinitePresentationCohomology (X ⨯ T).left
        ((τ.tStructure.truncLE n).obj E))

-- The geometric truncation-coherence input is explicit at the client site.
example :
    (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).HasInducedTStructure
      τ.tStructure :=
  τ.hasInducedBoundedCoherent hfpLE

example : TStructure.IsBounded (τ.boundedCoherentTStructure hfpLE) :=
  τ.boundedCoherentTStructureIsBounded hfpLE

example (E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) (n : ℤ) :
    (τ.boundedCoherentTStructure hfpLE).IsLE E n ↔
      τ.tStructure.IsLE E.obj n :=
  τ.boundedCoherentTStructureIsLE hfpLE E n

example (E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) (n : ℤ) :
    (τ.boundedCoherentTStructure hfpLE).IsGE E n ↔
      τ.tStructure.IsGE E.obj n :=
  τ.boundedCoherentTStructureIsGE hfpLE E n

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.TargetBoundedTStructure
