/-
NumericalDivisorialDiscriminant slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## Through a numerical realization

The intrinsic discriminant of a realized character is the integrated
numerical discriminant, so BogomolovGiesekerData (supplied, never proved)
transports to 0 <= Delta. A Hodge index on the realized divisor space yields
the numerical HodgeIndexStatement; the converse yields the inequality on
realized first Chern classes ONLY, not DivisorSpace.HodgeIndex, because the
numerical statement quantifies over classes E : N and not over real divisors.
On the rank-one slice the bar discriminant is t^2 . discrH, equivalently t^2
times the wall-plane discriminant of the transported class, and its
nonnegativity for a semistable class needs only the numerical data. For
arbitrary (B, omega) the nonnegativity needs a supplied Hodge index at
omega. -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.barDiscriminant_nonneg_of_semistable
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.barDiscriminant_rankOneParameters
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.barDiscriminant_rankOneParameters_eq_discr_toNumClass
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.barDiscriminant_rankOneParameters_nonneg
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.discriminant_chernCharacter
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.discriminant_nonneg_of_semistable
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.hodgeIndexStatement_of_hodgeIndex
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.index_le_chOne_of_hodgeIndexStatement
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.pair_chOne_self
