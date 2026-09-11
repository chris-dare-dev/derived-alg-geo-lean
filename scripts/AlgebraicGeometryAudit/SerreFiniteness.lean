import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Projective

/-!
# Serre finiteness on projective space (#571, #332 step 2)

## The middle of an exact pair between finite modules is finite (LinearAlgebra)

`Submodule.fg_of_fg_map_of_fg_inf_ker` at `s = ⊤`: the range of the second map is a submodule
of a finite module over a division ring, and the kernel is the range of the first map. The step
every degree of a dévissage takes. -/

#print axioms Function.Exact.module_finite_of_finite

/-! ## The connecting map is base-field linear (Cohomology/Finiteness/LinearConnecting.lean)

`coherentConnectingMap` is Mathlib's Ext connecting homomorphism; the scalar endomorphisms of the
three terms of a short exact sequence form a morphism of short exact sequences, and
`extClass_naturality` makes the connecting map commute with them. Hence the canonical linear
realization carries a LINEAR connecting map and an exact long sequence of k-vector spaces. Nothing
is supplied: Additivity.lean's `LinearConnectingMaps` is data for an arbitrary realization; this is
the theorem for the canonical one. -/

#print axioms AlgebraicGeometry.Cohomology.coherentScalarShortComplexHom
#print axioms AlgebraicGeometry.Cohomology.coherentConnectingMap_smul
#print axioms AlgebraicGeometry.Cohomology.linearCoherentConnectingMap
#print axioms AlgebraicGeometry.Cohomology.linearCoherentH_exact₂
#print axioms AlgebraicGeometry.Cohomology.linearCoherentH_exact₃
#print axioms AlgebraicGeometry.Cohomology.linearCoherentH_exact₁
#print axioms AlgebraicGeometry.Cohomology.linearCoherentH_additive

/-! ## Dévissage (Cohomology/Finiteness/Devissage.lean)

Descending induction from the finite-affine-cover vanishing bound along the linear exact
sequence `Hⁱ(G) → Hⁱ(F) → Hⁱ⁺¹(K)`, for any supply of generators with finite-dimensional
cohomology. Cohomology of a finite coproduct is a finite product of vector spaces because the
realization is additive. -/

#print axioms AlgebraicGeometry.Cohomology.module_finite_linearCoherentH_coproduct
#print axioms AlgebraicGeometry.Cohomology.module_finite_linearCoherentH_of_devissage

/-! ## Projective space (Cohomology/Finiteness/Projective.lean)

Serre's surjection `∐ O(-N) ↠ F` with `N ≥ 1`, lifted to `Coh Pⁿ` along the fully faithful,
finite-colimit-preserving `Coh.ι`; `H⁰(O(-N)) = 0` and `Hⁿ⁺¹(O(d))` finite (S1) feed the
dévissage. `projectiveSpaceFiniteDimensionalCohomology` inhabits `FiniteDimensionalCohomology`
for `Pⁿ` by theorem: its `finite` field is `module_finite_linearCoherentH_projectiveSpace`, not a
hypothesis. Closed subvarieties (#332 step 3) are not here. -/

#print axioms AlgebraicGeometry.Proj.module_finite_linearCoherentH_projectiveSpaceTwist_of_neg
#print axioms AlgebraicGeometry.Proj.exists_shortExact_coproduct_twist
#print axioms AlgebraicGeometry.Proj.module_finite_linearCoherentH_projectiveSpace
#print axioms AlgebraicGeometry.Proj.projectiveSpaceFiniteDimensionalCohomology
#print axioms AlgebraicGeometry.Proj.projectiveSpaceFiniteCohomology
#print axioms AlgebraicGeometry.Proj.isProper_projectiveSpaceToSpec

/-! ## The exponent above a threshold (Proj/Modules)

`exists_globalSection_twistBy_uniform_ge`, `exists_epi_free_tensorTwist_ge` and
`exists_epi_coproduct_twistingSheaf_ge` push Serre's exponent above any `N₀`; the dévissage takes
`N ≥ 1` so that the twist is negative and its degree-zero cohomology vanishes. -/

#print axioms AlgebraicGeometry.Proj.exists_globalSection_twistBy_uniform_ge
#print axioms AlgebraicGeometry.Proj.exists_epi_free_tensorTwist_ge
#print axioms AlgebraicGeometry.Proj.exists_epi_coproduct_twistingSheaf_ge
