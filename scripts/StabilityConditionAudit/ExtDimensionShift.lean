/-
Ext-dimension-shift slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and
reading guide.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.DimensionShift

/-! ## Dimension shifting for `Ext` (#572 step 3)

Composition with the `extClass` of an injective embedding is an isomorphism
`Ext^n(X, C) ≅ Ext^{n+1}(X, B)` above degree zero, and is surjective at degree zero.
This is the induction step of the Ext-adjunction transport that step 3 still needs.
-/

#print axioms CategoryTheory.Abelian.Ext.postcomp_extClass_surjective
#print axioms CategoryTheory.Abelian.Ext.postcomp_extClass_bijective
#print axioms CategoryTheory.Abelian.Ext.extClassAddEquiv
#print axioms CategoryTheory.Abelian.Ext.extClassAddEquiv_apply
