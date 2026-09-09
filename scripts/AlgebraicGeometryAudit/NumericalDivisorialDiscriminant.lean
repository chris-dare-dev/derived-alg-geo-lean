/-
NumericalDivisorialDiscriminant slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## The Hodge index inequality on a real divisor space

DivisorSpace.HodgeIndex S H is the certificate H^2 > 0 together with
H^2 . x^2 <= (H . x)^2 for EVERY real class x. It is proposition-valued and
NOT proved for any geometric surface. Its consequences are: nonpositive
square on H-orthogonal classes, negative square given nondegeneracy, and the
IsHodge certificate of an orthogonal slice from the inequality plus
nondegeneracy of the transverse pairing. The rank-one slice is Hodge from
H^2 > 0 alone. IsHodge.index_le_B recovers the inequality on the B-fields a
slice reaches; it does not recover it on all of D. -/

#print axioms AlgebraicGeometry.Numerical.Surface.DivisorSpace.HodgeIndex
#print axioms AlgebraicGeometry.Numerical.Surface.DivisorSpace.HodgeIndex.H_square_pos
#print axioms AlgebraicGeometry.Numerical.Surface.DivisorSpace.HodgeIndex.index_le
#print axioms AlgebraicGeometry.Numerical.Surface.DivisorSpace.HodgeIndex.pair_self_neg_of_orthogonal
#print axioms AlgebraicGeometry.Numerical.Surface.DivisorSpace.HodgeIndex.pair_self_nonpos_of_orthogonal
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.H_pair_B
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.IsHodge.index_le_B
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.isHodge_of_hodgeIndex
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.rankOne_isHodge
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.transverse_square_nonpos_of_hodgeIndex

/-! ## The three discriminants of Macri--Schmidt Definition 6.12

discriminant is (ch_1)^2 - 2 ch_0 ch_2 with the square taken in the divisor
space; discriminant_twist says it does not see B. barDiscriminant is
(omega . ch_1^B)^2 - 2 omega^2 ch_0^B ch_2^B and discriminantC is
Delta + C (omega . ch_1^B)^2. omega_square_mul_discriminant_le_barDiscriminant
is omega^2 Delta <= bar Delta under the Hodge index inequality at omega; it is
the step from Bogomolov's Delta >= 0 to the (alpha, beta)-plane support form.
barDiscriminant_rankOne shows the bar form on B = beta H, omega = alpha H is
alpha^2 times the compressed discriminant and independent of beta.
ChargeCoordinates.discr is that compressed form, the shape of Surface.discrH
and of the wall-plane discriminant. No Bogomolov inequality is proved. -/

#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.discr
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.barDiscriminant
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.barDiscriminant_nonneg_of_discriminant_nonneg
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.barDiscriminant_rankOne
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.discriminant
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.discriminantC
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.discriminant_le_discriminantC
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.discriminant_twist
#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.omega_square_mul_discriminant_le_barDiscriminant

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
