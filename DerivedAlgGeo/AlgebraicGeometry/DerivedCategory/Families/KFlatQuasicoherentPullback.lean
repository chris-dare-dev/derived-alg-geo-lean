/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.TermwiseQuasicoherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Pullback

/-!
# Derived pullback on K-flat quasi-coherent representatives

For a K-flat complex with quasi-coherent terms, the canonical arbitrary
left-derived pullback has quasi-coherent cohomology. The theorem uses ordinary
pullback on the given K-flat representative, so it does not assert that every
object of `Dqc` has such a representative.

## Main definitions

This file introduces no new carrier, class, or instance.

## Main results

* The theorem on arbitrary left-derived pullback proves conditional
  quasi-coherent cohomology preservation for any morphism.

## Implementation notes

Pullback preserves quasi-isomorphisms between K-flat complexes, so the
canonical resolved derived pullback agrees with ordinary pullback on the
given representative. Ordinary pullback preserves quasi-coherent terms.

## References

The proof uses the repository's
`AlgebraicGeometry.Scheme.Modules.quasiIso_pullback_of_isKFlat`,
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

/-- The caller-free arbitrary left-derived pullback preserves the `Dqc` locus
on a given K-flat representative with quasi-coherent terms, for every scheme
morphism in `Over S`. No flatness assumption is made on the morphism. -/
theorem quasicoherentCohomology_arbitraryLeftDerivedPullback_of_kFlatTermwise
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    (K : CochainComplex U.left.Modules ℤ)
    (hflat : CochainComplex.IsKFlat (Scheme.Modules.totalTensor U.left) K)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    schemeQuasicoherentCohomology T.left
      ((arbitraryLeftDerivedPullback f).functor.obj
        ((SchemeDerivedCategory.Q U.left).obj K)) := by
  let R := freeYonedaSchemeKFlatResolution U.left
  let hR := kFlatPullbackAcyclic R f
  have hcomp : IsIso ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map (R.comparison.app K))) := by
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    exact Scheme.Modules.quasiIso_pullback_of_isKFlat f.left
      (R.comparison.app K) (R.comparison_quasiIso K) (R.isKFlat K) hflat
  letI : IsIso ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map (R.comparison.app K))) := hcomp
  let e : (arbitraryLeftDerivedPullback f).functor.obj
      ((SchemeDerivedCategory.Q U.left).obj K) ≅
        (SchemeDerivedCategory.Q T.left).obj ((complexPullback f).obj K) :=
    (kFlatPullbackAcyclicResolution R f hR).derivedFactors.app K ≪≫
      @asIso _ _ _ _ ((SchemeDerivedCategory.Q T.left).map
        ((complexPullback f).map (R.comparison.app K))) hcomp
  apply (schemeQuasicoherentCohomology T.left).prop_of_iso e.symm
  apply quasicoherentCohomology_of_termwiseQuasicoherent
  intro n
  exact Scheme.Modules.isQuasicoherent_pullback f.left (K.X n) (hK n)

end
end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
