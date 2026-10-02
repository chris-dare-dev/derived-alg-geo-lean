/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.TermwiseQuasicoherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Pullback

/-!
# Derived pullback on K-flat quasi-coherent representatives

For a complex with quasi-coherent terms whose right tensor functor inverts
quasi-isomorphisms, the canonical arbitrary left-derived pullback has
quasi-coherent cohomology. K-flatness supplies that inversion premise. The
theorems do not supply such a representative for every object of `Dqc`.

## Main definitions

This file introduces no new carrier, class, or instance.

## Main results

* Right-tensor inversion gives conditional preservation along any morphism.
* K-flatness is an immediate specialization.

## Implementation notes

The generic objectwise comparison from `KFlatPullback.lean` identifies
canonical derived pullback with ordinary pullback on the supplied acyclic
representative. Ordinary pullback preserves quasi-coherent terms.

## References

The proof uses the repository's
`AlgebraicGeometry.Scheme.Modules.quasiIso_pullback_of_tensorRight_inverts`,
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`, and canonical
K-flat resolution.

## Tags

scheme base change, derived pullback, K-flat, quasi-coherence
-/

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

/-- Right-tensor inversion makes the pulled-back resolution comparison
invertible, so ordinary pullback computes the canonical derived pullback on
this representative. The theorem does not construct such a representative
for an arbitrary derived object. -/
theorem quasicoherentCohomology_arbitraryLeftDerivedPullback_of_tensorRightInverts_of_termwiseQC
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    (K : CochainComplex U.left.Modules ℤ)
    (hRight :
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)).IsInvertedBy
        ((Scheme.Modules.totalTensor U.left).flip.obj K ⋙ DerivedCategory.Q))
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    schemeQuasicoherentCohomology T.left
      ((arbitraryLeftDerivedPullback f).functor.obj
        ((SchemeDerivedCategory.Q U.left).obj K)) := by
  apply (schemeQuasicoherentCohomology T.left).prop_of_iso
    (derivedPullbackObjIsoOfTensorRightInverts f K hRight).symm
  apply quasicoherentCohomology_of_termwiseQuasicoherent
  intro n
  exact Scheme.Modules.isQuasicoherent_pullback f.left (K.X n) (hK n)

/-- K-flatness supplies the right-tensor inversion used to compare the
canonical derived pullback with ordinary pullback on the given complex. This
does not supply a quasi-coherent K-flat representative for every `Dqc` object. -/
theorem quasicoherentCohomology_arbitraryLeftDerivedPullback_of_isKFlat_of_termwiseQuasicoherent
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    (K : CochainComplex U.left.Modules ℤ)
    (hflat : CochainComplex.IsKFlat (Scheme.Modules.totalTensor U.left) K)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    schemeQuasicoherentCohomology T.left
      ((arbitraryLeftDerivedPullback f).functor.obj
        ((SchemeDerivedCategory.Q U.left).obj K)) :=
  quasicoherentCohomology_arbitraryLeftDerivedPullback_of_tensorRightInverts_of_termwiseQC
    f K hflat.2 hK

end
end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
