/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Termwise
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Quasi-coherent cohomology of termwise quasi-coherent complexes

The homology sheaves of a complex whose terms are quasi-coherent are
quasi-coherent on any scheme. This gives a concrete source of objects in the
honest `Dqc` locus of the derived category of all module sheaves.

## Main definitions

This file introduces no new carrier, class, or instance.

## Main results

* `AlgebraicGeometry.DerivedCategory.Dqc.quasicoherentCohomology_of_termwiseQuasicoherent`
  supplies the `Dqc` membership proof for an unbounded termwise
  quasi-coherent complex.

## Implementation notes

The generic termwise theorem uses kernel and cokernel closure to obtain
homology membership, then transports it through derived homology. The
quasi-coherent object property supplies those closure instances here.

## References

`DerivedCategory.cohomologyIn_Q_obj_of_termwise` is the generic proof;
`SheafOfModules.isQuasicoherent` specializes its property argument.

## Tags

scheme, quasi-coherent sheaves, derived category, homology
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open AlgebraicGeometry.DerivedCategory
open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

/-- Apply the generic termwise homology-closure theorem to the
quasi-coherent object property on module sheaves. -/
theorem quasicoherentCohomology_of_termwiseQuasicoherent
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    schemeQuasicoherentCohomology X ((SchemeDerivedCategory.Q X).obj K) :=
  DerivedCategory.cohomologyIn_Q_obj_of_termwise
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) K hK

end
end AlgebraicGeometry.DerivedCategory.Dqc
