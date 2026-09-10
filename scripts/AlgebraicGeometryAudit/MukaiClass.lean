/-
MukaiClass slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

Kept separate from MukaiWitness.lean on purpose: tm-1 and tm-2 are the two
parallel entry points of the Mukai lane and must not contend for one file.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai

/-! ## The square root of a normalized graded class, and sqrt-td

sqrtComp is the coefficient family of sqrt(1+x), written out rather than
recursed, so it STOPS at codimension four. That ceiling is stated rather than
hidden: sqrtComp is zero above four and sqrtComp_convolution carries an explicit
i <= 4 hypothesis instead of burying the bound in a decide. Same ceiling and
same reason as CharacteristicClasses.lean's toddComponent.

sqrtComp_convolution is the only mathematical content: it is what makes the name
"square root" a theorem rather than a label. Its proof turns every coefficient
into a power of algebraMap (1/2), leaving ONE scalar atom and the single
relation h + h = 1, because writing the coefficients as distinct algebraMap
values leaves ring with five unrelated atoms and no way to relate them.

K3.sqrtToddComp_one and K3.degree_sqrtToddComp_two are together the formal
content of "sqrt td(X) = 1 + [pt]", which RiemannRoch/K3.lean states in prose. -/

#print axioms AlgebraicGeometry.Numerical.sqrtComp
#print axioms AlgebraicGeometry.Numerical.sqrtComp_zero
#print axioms AlgebraicGeometry.Numerical.sqrtComp_one
#print axioms AlgebraicGeometry.Numerical.sqrtComp_eq_zero_of_four_lt
#print axioms AlgebraicGeometry.Numerical.sqrtComp_convolution
#print axioms AlgebraicGeometry.Numerical.sqrtComp_mem
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.sqrtToddComp
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.sqrtToddComp_zero
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.sqrtToddComp_mem
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.sqrtToddComp_convolution
#print axioms AlgebraicGeometry.Numerical.K3.sqrtToddComp_one
#print axioms AlgebraicGeometry.Numerical.K3.degree_sqrtToddComp_two

/-! ## The Mukai vector as a class in the intersection ring (#908)

Until now the Mukai vector existed only as a FORMULA: `IntegralMukaiData` asserts the triple
`(rank, c₁, s)` by fiat, and `RiemannRoch/K3.lean` explained in a docstring that the triple is what
`ch(E)·√td(X)` comes to on a K3. `mukaiComp` computes that class, and the three comparison theorems
turn the docstring into theorems.

`mukaiComp` is defined for ARBITRARY dimension; the K3 statements are a section, not the
definition, because the Fourier-Mukai and higher-dimensional lanes want `v(E)` on a threefold.

`mukaiS` is deliberately NOT redefined as the degree of the top component -- `degree_mukaiComp_two`
is the comparison theorem instead. Redefining it would ripple through the Euler pairing, the Mukai
vector, the transfer and the realization files.

The middle coordinate is compared THROUGH THE FORM `b` rather than by an equation in the lattice:
in `IntegralMukaiData` the class `c₁` is a bare function with no additivity and no relation to the
intersection ring, so no equation in the lattice is available to state. -/

#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.mukaiComp
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.mukaiClass
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.mukaiComp_mem
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.mukaiComp_add
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.mukaiClass_add
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.mukaiComp_zero
#print axioms AlgebraicGeometry.Numerical.NumericalVarietyData.degree_mukaiComp_mul_mukaiComp_eq_zero
#print axioms AlgebraicGeometry.Numerical.K3.mukaiComp_one
#print axioms AlgebraicGeometry.Numerical.K3.mukaiComp_two
#print axioms AlgebraicGeometry.Numerical.K3.degree_mukaiComp_two
#print axioms AlgebraicGeometry.Numerical.K3.mukaiVector_fst_eq
#print axioms AlgebraicGeometry.Numerical.K3.b_mukaiVector_snd_eq_degree
#print axioms AlgebraicGeometry.Numerical.K3.mukaiVector_thd_eq_degree
