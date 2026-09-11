import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInverse

/-!
# The tensor inverse of `O(N)`, and Serre's surjection `⊕ O(-N) ↠ F` (#806, #586)

## Tensoring by an invertible sheaf, two more consequences (Modules/Tensor/Invertible.lean)

`tensorLeftFunctor L` preserves finite colimits, hence pushouts, hence epimorphisms
(`epi_tensorHom_id_of_invertible`, the companion of `mono_tensorHom_id_of_invertible`); and it
preserves finite coproducts, so `L ⊗ free I` is a finite direct sum of copies of `L`
(`tensorLeftFreeIso`). Generic in the scheme and the invertible sheaf. -/

#print axioms AlgebraicGeometry.Scheme.Modules.epi_tensorHom_id_of_invertible
#print axioms AlgebraicGeometry.Scheme.Modules.tensorLeftFreeIso

/-! ## `O(-N)` inverts `O(N)`, and untwists an arbitrary `F` (Proj/Modules/TwistInverse.lean)

`twistingSheafTensorNegIso` is the composite #806 predicted at `L = O(N)`: twist addition at
`N + -N = 0`, then `O(0) ≅ Ã ≅ unit`. `tensorTwistNegIso` is `(F ⊗ O(N)) ⊗ O(-N) ≅ F` for an
ARBITRARY `F`, from the hypothesis-free associator; the obstruction `TensorTwist.lean` recorded was
an associator that then carried invertibility hypotheses, and both outer factors here are
invertible anyway. The general `IsInvertible L → ∃ L'` and the hom-equivalence of #806 are NOT
here; #806 stays open for them. -/

#print axioms AlgebraicGeometry.Proj.twistingSheafTensorNegIso
#print axioms AlgebraicGeometry.Proj.tensorTwistNegIso

/-! ## Serre's theorem in the `⊕ O(-N) ↠ F` form

`exists_epi_free_tensorTwist`'s `free I ↠ F ⊗ O(N)`, tensored by `O(-N)`, untwisted, and read on
the coproduct through `tensorLeftFreeIso`. This is #586's literal deliverable and the input S3
(#571) consumes: every coherent `F` on `Proj 𝒜` is a quotient of a finite direct sum of copies of
one `O(-N)`. -/

#print axioms AlgebraicGeometry.Proj.exists_epi_coproduct_twistingSheaf
