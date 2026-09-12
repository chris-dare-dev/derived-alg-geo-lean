/-
Chambers slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition

/-! ## Charge-vanishing walls, regular loci, and chambers -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.stabWall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.mem_stabWall_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.stabRegular
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.mem_stabRegular_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.stabRegular_antitone
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.stabRegular_univ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.stabRegular_eq_compl_iUnion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.combined_smul_mem_stabWall_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.image_stabWall_smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.image_stabWall_gltilde
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.combined_smul_mem_stabRegular_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.image_stabRegular_smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.StabChamber
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall.chamberOf
