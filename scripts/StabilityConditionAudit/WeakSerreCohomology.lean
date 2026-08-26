/-
Weak-Serre / cohomological-locus slice of the StabilityCondition audit, split out so
concurrent branches append to different files (#480). See the umbrella file for the
contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CohomologyObjectProperty

/-! ## The middle of a five-term exact sequence (#721)

A weak Serre subcategory — closed under kernels, cokernels and extensions, but not
under subobjects or quotients — contains the middle of a five-term exact sequence.
Mathlib has the three-term statement for full Serre classes only, and quasi-coherent
sheaves on a general scheme are not a Serre class.
-/

#print axioms CategoryTheory.ObjectProperty.prop_of_exact_of_epi
#print axioms CategoryTheory.ObjectProperty.prop_of_exact_of_mono
#print axioms CategoryTheory.ObjectProperty.prop_X₃_of_exact₅

/-! ## Cohomology in a subcategory cuts out a triangulated subcategory (#721)

`cohomologyIn P` is a triangulated subcategory of `DerivedCategory A` whenever `P` is
a weak Serre subcategory containing zero. Closure under cones is the five-term lemma
above applied to the long exact homology sequence; that is the only field with
mathematical content, and it is why no abelian structure on `P.FullSubcategory` is
needed.
-/

#print axioms DerivedCategory.cohomologyIn
#print axioms DerivedCategory.mem_cohomologyIn_iff
#print axioms DerivedCategory.instIsClosedUnderIsomorphismsCohomologyIn
#print axioms DerivedCategory.instContainsZeroCohomologyInOfIsClosedUnderIsomorphisms
#print axioms DerivedCategory.instIsStableUnderShiftCohomologyInIntOfIsClosedUnderIsomorphisms
#print axioms DerivedCategory.cohomologyIn_isTriangulatedClosed₂
#print axioms DerivedCategory.cohomologyIn_isTriangulated
