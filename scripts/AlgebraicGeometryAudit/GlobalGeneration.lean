import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.GlobalGeneration

/-!
# Serre's global generation audit (#586)

Every declaration on the road from the section-extension lemma to Serre's theorem proper:
`F(N)` is a quotient of a finite free sheaf for `F` coherent on `Proj 𝒜` and `N` large.

## The pure-tensor calculus (Modules/Tensor/Picard.lean)

`tmulSection` was a map INTO the sections of the sheafified tensor, with one lemma about it. The
chart-local half of Serre needs to FOLLOW a pure tensor: restrict it, split it over a sum, and move
a scalar onto the `F` factor where the generators live. `res_tmulSection` is naturality of the
sheafification unit; the other three are bilinearity read through the unit's component. Each is
proved by `congrArg`/`Eq.trans` on an explicitly typed `have`, because the tensor-product lemmas
infer their scalar ring from the expected type and land on the presheaf's ring otherwise. -/

#print axioms AlgebraicGeometry.Scheme.Modules.res_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.tmulSection_add_left
#print axioms AlgebraicGeometry.Scheme.Modules.smul_tmulSection_left
#print axioms AlgebraicGeometry.Scheme.Modules.tmulSection_finset_sum_left

/-! ## The chart scalar is a unit on `D₊(g) ⊓ D₊(f)` (Proj/Modules/FracSection.lean)

`(a / b) (b / a) = 1` over an open inside both basic opens. The extension lemma produces
`(f / gᵉ)ⁿ • u` as a restriction of a global section; this is what recovers `u` itself. -/

#print axioms AlgebraicGeometry.Proj.fracSection_mul_fracSection_symm

/-! ## Two spellings of one section, and a generator read as an equation of sections

`exists_globalSection_twistBy_uniform` twists by `g ^ N` at degree `1 * N`, and `1 * N` is not
`N` definitionally, so the twisting element arrives as `g ^ N` where the generator lemmas carry
`g ^ (1 * N)`. `sectionOfMem_congr` and `twistBy_congr` are the two `subst`s that reconcile them.
`res_sectionOfMem` says `m / 1` restricts to `m / 1`, and `exists_smul_sectionOfMem_eq_res` is
`exists_smul_sectionOfMem_eq` read as an equation of sections of `O(N)` rather than pointwise. -/

#print axioms AlgebraicGeometry.Proj.sectionOfMem_congr
#print axioms AlgebraicGeometry.Proj.res_sectionOfMem
#print axioms AlgebraicGeometry.Proj.twistBy_congr
#print axioms AlgebraicGeometry.Proj.exists_smul_sectionOfMem_eq_res

/-! ## Local combinations of a family of global sections (Modules/LocalCombination.lean)

A section is a local combination of `σ` when near every point it is a structure-sheaf
combination of the restrictions of `σ`. Closed under zero, sums and restriction, and the family
classifies an epimorphism `free I ⟶ G` when every section is one. Generic in the scheme; the
Serre assembly consumes it with `G = F(N)`. -/

#print axioms AlgebraicGeometry.Scheme.Modules.sectionsOfTop
#print axioms AlgebraicGeometry.Scheme.Modules.sectionsOfTop_val
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalCombination
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalCombination.zero
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalCombination.add
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalCombination.finset_sum
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalCombination.res
#print axioms AlgebraicGeometry.Scheme.Modules.freeHomEquiv_symm_sectionsOfTop_ιFree_app_one
#print axioms AlgebraicGeometry.Scheme.Modules.epi_freeHomEquiv_symm_of_isLocalCombination

/-! ## Finitely many generators on a chart (Proj/Modules/ChartGeneration.lean)

Step 2 of #586. Coherence makes the chart's module of sections finitely generated with no
Noetherian hypothesis; the affine extension lemma plus the unit `(f / gᵉ)ⁿ` on the positive-degree
basic open `D₊(g) ⊓ D₊(f)` around the point turns a spanning set of the chart's sections into a
family that generates locally on every open of the chart. `exists_mem_basicOpen_le` is the
neighbourhood: a basic open of a homogeneous component, multiplied by `g` to make the degree
positive. -/

#print axioms AlgebraicGeometry.Proj.exists_mem_basicOpen_le
#print axioms AlgebraicGeometry.Proj.exists_finite_generators_of_isCoherent

/-! ## Serre's theorem (Proj/Modules/GlobalGeneration.lean)

Hartshorne II.5.17 / EGA II 2.7.9 in the global-generation form: `free I ↠ F ⊗ O(N)` for `F`
coherent on `Proj 𝒜`, `𝒜` generated in degree one by finitely many elements, and `N` large.
The pure-tensor lemma is the chart-local half; the theorem joins it to the uniform exponent of
GlueUniform.lean through the local-combination calculus. No global-generation hypothesis, no
resolution property, no instance supplying the surjection. The `⊕ O(-N) ↠ F` form waits on the
tensor inverse of `O(N)` (#806) and is one tensor away. -/

#print axioms AlgebraicGeometry.Proj.exists_res_tmulSection_eq_sum
#print axioms AlgebraicGeometry.Proj.exists_epi_free_tensorTwist
#print axioms AlgebraicGeometry.Proj.exists_generatingSections_tensorTwist
