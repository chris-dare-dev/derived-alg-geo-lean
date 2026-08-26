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

/-! ## Closure under a coproduct that cohomology preserves (#721)

Stated relative to the coproduct existing and every `Hⁿ` preserving it. Neither is
available for `DerivedCategory A` at this Mathlib pin, so both are hypotheses rather
than instances, and nothing here asserts that the derived category has coproducts it
has not been shown to have.
-/

#print axioms DerivedCategory.cohomologyIn_coproduct
#print axioms DerivedCategory.cohomologyIn_prop_coproduct

/-! ## Two elaboration artifacts, audited rather than exempted

`ShortComplex.mk.congr_simp` and `ShortComplex.homologyData.congr_simp` are congruence
lemmas Lean generates on first use; `WeakSerreExact.lean` is the first module in the
build to trigger them, so the declaration sweep attributes them here and the
completeness ratchet counts them. They are recorded rather than filtered because the
alternative — adding `.congr_simp` to `autoSuffixes` in `scripts/EnumDecls.lean` — is a
trust-surface edit, and this slice is not the place to make one.
-/

#print axioms CategoryTheory.ShortComplex.mk.congr_simp
#print axioms CategoryTheory.ShortComplex.homologyData.congr_simp
