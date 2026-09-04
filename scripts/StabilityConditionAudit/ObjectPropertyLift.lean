/-
ObjectPropertyLift slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

This slice owns `DerivedAlgGeo/CategoryTheory/ObjectProperty/`. The twelve
declarations below were audited in `TStructureCore.lean` while they lived in the t-structure
restriction file; they moved here with the block, so the sweep follows the declarations rather than
the theorem that first needed them.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty

/-! ## Restricting a functor to the subcategories cut out by a property -/

#print axioms CategoryTheory.ObjectProperty.liftOfLE
#print axioms CategoryTheory.ObjectProperty.instAdditiveLiftOfLE
#print axioms CategoryTheory.ObjectProperty.instCommShiftLiftOfLE
#print axioms CategoryTheory.ObjectProperty.instIsTriangulatedLiftOfLE
#print axioms CategoryTheory.ObjectProperty.preimageLift
#print axioms CategoryTheory.ObjectProperty.instAdditivePreimageLift
#print axioms CategoryTheory.ObjectProperty.instCommShiftPreimageLift
#print axioms CategoryTheory.ObjectProperty.instIsTriangulatedPreimageLift
#print axioms CategoryTheory.ObjectProperty.inverseImageLift
#print axioms CategoryTheory.ObjectProperty.liftToInverseImage

/-! ## Restricting an adjunction on either side of the functor -/

#print axioms CategoryTheory.Adjunction.restrictInverseImageLeft
#print axioms CategoryTheory.Adjunction.restrictInverseImageRight

/-! ## Left orthogonals are closed under colimits -/

#print axioms CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeLeftOrthogonal
