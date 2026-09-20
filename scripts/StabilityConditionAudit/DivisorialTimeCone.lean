/-
Time-cone slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the
contract and reading guide.

Everything recorded here is linear algebra over a real vector space with a
symmetric bilinear pairing. There is NO scheme, sheaf, numerical intersection
ring, heart, slicing, charge, wall, or stability condition anywhere below it,
and no Bogomolov inequality and no Hodge index theorem are proved: negative
definiteness on the orthogonal complement is the caller's `HodgeDefinite`
certificate, exactly as it is for the Divisorial slice.

Two boundaries worth stating, because the names invite the opposite reading.

`IsFuture` is a predicate on two vectors of a real quadratic space -- positive
square together with positive pairing against the reference vector. It is NOT
asserted to be an ample cone, a positive cone, a cone of a surface, or the
image of anything geometric. No surface appears in this slice.

Unit normalization `e^2 = 1` is a per-theorem hypothesis, not a structure
field. The theorems that need it say so; `pair_mul_pair_le_sq`,
`pair_pos_of_isFuture` and both inequalities do not need it and do not carry
it. Nothing here introduces a Lorentzian structure or certificate.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.Lorentzian

/-! ## The orthogonal splitting

`timeCoord e x` is the pairing of `x` against the reference vector and
`spacePart e x = x - timeCoord e x • e` its complement.
`timeCoord_smul_add_spacePart` recovers `x`, `pair_spacePart_eq_zero` proves
the space part orthogonal to a unit `e`, and `pair_self_eq_timeCoord_sq_add`
is the splitting identity `x^2 = t(x)^2 + s(x)^2`. The space part has
nonpositive square under the caller's certificate, so the coordinate along `e`
dominates. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.timeCoord
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.spacePart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.timeCoord_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.spacePart_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.timeCoord_smul_add_spacePart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_spacePart_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_self_eq_timeCoord_sq_add
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.spacePart_self_nonpos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_self_le_timeCoord_sq

/-! ## Reverse Cauchy-Schwarz

`pair_mul_pair_le_sq` is the Cauchy-Schwarz inequality with the sense reversed,
for a vector of positive square. It needs no new input: `HodgeDefinite.of_pair_pos`
transports the caller's certificate from the reference vector to that vector,
and `HodgeIndex.index_le` there is the statement. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_mul_pair_le_sq

/-! ## The future cone

`IsFuture e x` is positive square together with positive pairing against `e` --
a predicate on vectors, not a geometric cone (see the header). It is closed
under positive scaling and, by `pair_pos_of_isFuture`, under addition. The
positivity theorem is proved WITHOUT Cauchy-Schwarz on the orthogonal
complement: the explicit combination `t(y) • x - t(x) • y` is orthogonal to
`e`, so the certificate makes its square nonpositive, and expanding that square
is the inequality. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.IsFuture
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.isFuture_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.isFuture_smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_pos_of_isFuture
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.isFuture_add

/-! ## The reverse triangle inequality

`sqrt_mul_sqrt_le_pair` bounds the product of the two lengths by the pairing,
and `sqrt_add_sqrt_le_sqrt_pair_add` is the reverse triangle inequality it
yields: on a Hodge-definite pairing the length of a sum of future vectors is at
least the sum of the lengths, opposite to the Euclidean inequality. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.sqrt_mul_sqrt_le_pair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.sqrt_add_sqrt_le_sqrt_pair_add
