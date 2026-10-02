/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
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

Cycles are kernels and homology is a cokernel of a map into cycles. The
existing quasi-coherence closure theorems and derived homology comparison
finish the proof.

## References

Pinned Mathlib's `HomologicalComplex.cyclesIsKernel`,
`HomologicalComplex.homologyIsCokernel`, and
`DerivedCategory.homologyFunctorFactors` are used directly.

## Tags

scheme, quasi-coherent sheaves, derived category, homology
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open AlgebraicGeometry.DerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

private theorem cycles_isQuasicoherent_of_termwise
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) (n : ℤ) :
    (K.cycles n).IsQuasicoherent := by
  let e : K.cycles n ≅ kernel (K.d n (n + 1)) :=
    IsLimit.conePointUniqueUpToIso (K.cyclesIsKernel n (n + 1) (by simp))
      (limit.isLimit _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
    (Scheme.Modules.isQuasicoherent_kernel (K.d n (n + 1))
      (hK n) (hK (n + 1)))

private theorem homology_isQuasicoherent_of_termwise
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) (n : ℤ) :
    (K.homology n).IsQuasicoherent := by
  let e : K.homology n ≅ cokernel (K.toCycles (n - 1) n) :=
    IsColimit.coconePointUniqueUpToIso
      (K.homologyIsCokernel (n - 1) n (by simp)) (colimit.isColimit _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
    (Scheme.Modules.isQuasicoherent_cokernel (K.toCycles (n - 1) n)
      (hK (n - 1)) (cycles_isQuasicoherent_of_termwise X K hK n))

/-- A complex of quasi-coherent module sheaves represents an object of `Dqc(X)`.
The statement holds for unbounded complexes on any scheme. -/
theorem quasicoherentCohomology_of_termwiseQuasicoherent
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    schemeQuasicoherentCohomology X ((SchemeDerivedCategory.Q X).obj K) := by
  intro n
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules n).app K).symm
    (homology_isQuasicoherent_of_termwise X K hK n)

end
end AlgebraicGeometry.DerivedCategory.Dqc
