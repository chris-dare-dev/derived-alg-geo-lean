/-
CalabiYauWalls slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Threefold

/-! ## The threefold wall transport, on the quintic

ProjectiveSpaceWalls connected the transport to the P3 model. The quintic
Calabi-Yau was in the same position: referenced only inside its own file, with
no polarization defined for it. quinticPolarization is that class and the four
quintic_toNumClass_deg lemmas evaluate the transport.

THE SECOND THREEFOLD IS NOT A COPY OF THE FIRST. It differs in the two places
the transport touches. The degree is int H^3 = 5 rather than 1, so every degree
carries a factor the P3 computation could not see; a transport that silently
assumed unit degree would pass on P3 and fail here. And the Todd class has
td_1 = 0 and int td_3 = chi(O) = 0 where P3 has every coefficient nonzero -- the
transport does not read the Todd class, and these records are the check that it
does not, since the four degrees depend on the Chern coefficients and the degree
alone. In deg3 the degree cancels the /5 that threefoldChCoeff 5 puts on the
point coordinate, which is the one place the answer is not the P3 one times
five.

NO SECOND SANITY WITNESS. ProjectiveSpaceWalls.p3BMTSanity already shows BMTData
is inhabitable, so quintic_Q_toNumClass_nonneg takes a supplied BMTData as a
HYPOTHESIS instead. The Bayer-Macri-Toda inequality is not proved here for the
quintic or for anything else, and it is false for some threefolds.

No scheme, sheaf, heart, or tilt-stable object appears. -/

#print axioms AlgebraicGeometry.Numerical.Examples.quinticPolarization
#print axioms AlgebraicGeometry.Numerical.Examples.quinticPolarization_cls
#print axioms AlgebraicGeometry.Numerical.Examples.quinticWallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.quinticWallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_Q_toNumClass_nonneg
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_degree_H_pow_three
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_imZ
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_reZ
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_toNumClass_deg0
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_toNumClass_deg1
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_toNumClass_deg2
#print axioms AlgebraicGeometry.Numerical.Examples.quintic_toNumClass_deg3
