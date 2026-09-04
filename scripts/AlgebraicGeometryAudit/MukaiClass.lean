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
