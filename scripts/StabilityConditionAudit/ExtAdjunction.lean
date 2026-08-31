/-
Ext-along-an-adjunction slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and
reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Ext.Adjunction

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
#print axioms CategoryTheory.surjective_extAdjunctionMap
#print axioms CategoryTheory.injective_extAdjunctionMap
#print axioms CategoryTheory.extAdjunctionAddEquiv
#print axioms CategoryTheory.extAdjunctionAddEquiv_apply
#print axioms CategoryTheory.Abelian.Ext.precompAddEquiv
