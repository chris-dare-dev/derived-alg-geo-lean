/-
LinearAlgebra slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the
contract and reading guide.
-/
import DerivedAlgGeo.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The middle of an exact pair between finite modules is finite

`Function.Exact.module_finite_of_finite` is consumed by Serre finiteness, whose
other records are in `AlgebraicGeometryAudit/SerreFiniteness.lean`.  It is
audited here and not there because the sweep routes a declaration by the module
that declares it, and this one is declared in
`DerivedAlgGeo/LinearAlgebra/FiniteDimensional/Lemmas.lean`:
`EnumDecls.libraryOf` sends `DerivedAlgGeo.LinearAlgebra.*` to
`StabilityCondition`, alongside `CategoryTheory` and `Algebra.Homology`.

A record in the wrong audit is invisible to `check_audit_complete.py` in both
directions at once -- it does not cover the declaration, which then counts as
unaudited in its own library, and it counts as an unresolved record in the
library it was written into.  That is what this file fixes.
-/

#print axioms Function.Exact.module_finite_of_finite
