/-
Ext-along-an-adjunction slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and
reading guide.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicGenerators
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.Adjunction
import DerivedAlgGeo.CategoryTheory.Linear.Adjunction

/-! ## Ext along an adjunction with exact left adjoint (#572 step 3, slice 2)

`Sheaf.H` is `Ext` out of the constant sheaf, so cohomology invariance along a closed immersion
is an `Ext` transport across `ι⁻¹ ⊣ ι_*`. `ConstantPullback.lean` moved the constant sheaf;
these records cover the comparison map, its naturality, and the theorem that it is bijective in
every degree.
-/

#print axioms CategoryTheory.extAdjunctionMap
#print axioms CategoryTheory.extAdjunctionMap_zero
#print axioms CategoryTheory.extAdjunctionMap_add
#print axioms CategoryTheory.extAdjunctionAddHom
#print axioms CategoryTheory.extAdjunctionAddHom_apply
#print axioms CategoryTheory.extAdjunctionMap_mk₀
#print axioms CategoryTheory.preservesInjectiveObjects_of_adj
#print axioms CategoryTheory.subsingleton_ext_right_of_injective
#print axioms CategoryTheory.bijective_extAdjunctionMap_of_injective
#print axioms CategoryTheory.extAdjunctionMap_comp
#print axioms CategoryTheory.extAdjunctionMap_comp_mk₀
#print axioms CategoryTheory.extAdjunctionMap_comp_extClass
#print axioms CategoryTheory.bijective_extAdjunctionMap_zero
#print axioms CategoryTheory.surjective_extAdjunctionMap
#print axioms CategoryTheory.injective_extAdjunctionMap
#print axioms CategoryTheory.extAdjunctionAddEquiv
#print axioms CategoryTheory.extAdjunctionAddEquiv_apply
#print axioms CategoryTheory.extAdjunctionLinearMap
#print axioms CategoryTheory.extAdjunctionLinearMap_apply
#print axioms CategoryTheory.extAdjunctionLinearEquiv
#print axioms CategoryTheory.extAdjunctionLinearEquiv_apply
#print axioms CategoryTheory.Abelian.Ext.precompAddEquiv
#print axioms CategoryTheory.Abelian.Ext.precompLinearEquiv
#print axioms CategoryTheory.Adjunction.homLinearEquiv

/-! ## Ext comparison from acyclicity of images of injectives (#1070, affine lane, slice 2)

The root the adjunction comparison above is now a corollary of: the comparison along an exact
`R : D ⥤ C` from a fixed `u : A ⟶ R P` is bijective in every degree once it is bijective in
degree zero and `R` sends injectives to `A`-acyclic objects. -/

#print axioms CategoryTheory.extComparisonMap
#print axioms CategoryTheory.extComparisonMap_zero
#print axioms CategoryTheory.extComparisonMap_add
#print axioms CategoryTheory.extComparisonAddHom
#print axioms CategoryTheory.extComparisonAddHom_apply
#print axioms CategoryTheory.extComparisonMap_comp
#print axioms CategoryTheory.extComparisonMap_comp_mk₀
#print axioms CategoryTheory.extComparisonMap_comp_extClass
#print axioms CategoryTheory.surjective_extComparisonMap
#print axioms CategoryTheory.injective_extComparisonMap
#print axioms CategoryTheory.extComparisonAddEquiv
#print axioms CategoryTheory.extComparisonAddEquiv_apply
#print axioms CategoryTheory.extComparisonMap_mk₀
#print axioms CategoryTheory.bijective_extComparisonMap_zero_iff
#print axioms CategoryTheory.Ext.subsingleton_of_iso_left
#print axioms CategoryTheory.Ext.subsingleton_biproduct_left
#print axioms CategoryTheory.Ext.subsingleton_coproduct_left
#print axioms CategoryTheory.Functor.bijective_mapExtAddHom_zero_iff
#print axioms CategoryTheory.Functor.bijective_mapExtAddHom_zero
#print axioms CategoryTheory.Functor.surjective_mapExtAddHom_of_generators
#print axioms CategoryTheory.Functor.injective_mapExtAddHom_of_generators
#print axioms CategoryTheory.Functor.bijective_mapExtAddHom_of_generators
