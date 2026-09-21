/-
Diagonal-model slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the
contract and reading guide.

Everything recorded here is linear algebra on `R x (Fin k -> R)` with the
symmetric form `diag(1, -1, ..., -1)`. There is NO scheme, sheaf, numerical
intersection ring, heart, slicing, charge, wall or stability condition anywhere
below it.

THE ONE BOUNDARY THAT MATTERS. There is no surface. `DiagonalDivisor k` is a
real vector space with a symmetric bilinear form; it is NOT asserted to be
`N^1(X)` tensor R for any X. `(1, 0, ..., 0)` is not a hyperplane class,
`(3, -1, ..., -1)` is not an anticanonical class, and no ample cone,
(-1)-class or (-2)-class appears anywhere in this slice. The identification of
this model with the numerical divisor lattice of an iterated blow-up of the
projective plane is geometry, is not made here, and is not implied by the word
"diagonal".

UNLIKE the rest of the Divisorial lane, `hodgeDefinite_diagonal` is PROVED
rather than supplied. Negative definiteness on the orthogonal complement is
normally the caller's certificate; here it is a theorem about this particular
form, at every rank k and with no case split. The one inequality it rests on is
`Finset.sum_mul_sq_le_sq_mul_sq`, Mathlib's Cauchy-Schwarz for finsets.
`Examples/Surface/BlowUpPlane.lean` proves the k = 2 case separately by
destructuring three coordinates; that declaration is untouched by this slice
and the comparison between the two cannot be stated in `LinearAlgebra/`, which
may not import `AlgebraicGeometry/`.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.Lorentzian

/-! ## The model

`DiagonalDivisor k` is the carrier, `diagonalForm k` the bilinear form built by
`LinearMap.mk₂`, and `diagonalSpace k` the `DivisorSpace` packaging it with its
symmetry proof. The two `_apply` records are the definitional unfoldings a
consumer computes with. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DiagonalDivisor
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.diagonalForm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.diagonalForm_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.diagonalSpace
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.diagonalSpace_pair

/-! ## The Hodge index inequality at every rank

`hodgeDefinite_diagonal` is the reverse Cauchy-Schwarz inequality for
`diag(1, -1, ..., -1)`: a vector of positive square has negative-definite
orthogonal complement. Proved, not supplied, and proved uniformly in k.

`hodgeDefinite_of_equiv_diagonal` is what makes that reusable: a `DivisorSpace`
on any carrier admitting a form-preserving linear equivalence onto the model
inherits the certificate. It is the intended route for a concrete surface model
to stop proving its own Hodge index inequality, and it carries the equivalence
and the form-preservation as explicit hypotheses rather than as fields of a new
structure. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.hodgeDefinite_diagonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.hodgeDefinite_of_equiv_diagonal
