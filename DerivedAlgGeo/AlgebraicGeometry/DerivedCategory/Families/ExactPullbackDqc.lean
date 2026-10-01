/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeCategory
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Pullback

/-!
# Quasi-coherent cohomology under exact scheme pullback

An exact pullback commutes with cohomology. Ordinary pullback preserves
quasi-coherent module sheaves along every scheme morphism, so the exact derived
pullback preserves the quasi-coherent-cohomology locus. Flat pullback is an
unconditional geometric specialization because flatness supplies exactness.

This proves the exact and flat cases of the derived preservation obligation.
Arbitrary nonexact pullback still needs a derived comparison; its cohomology
need not be the ordinary pullback of the source cohomology sheaf.

## Main definitions

* `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.exactDqcLeftDerivedPullback`
  constructs the Dqc refinement for exact pullback.
* `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.flatDqcLeftDerivedPullback`
  specializes it to flat pullback.

## Main results

* The theorem below proves quasi-coherent cohomology preservation in the
  exact case.

## Implementation notes

The generic exact-functor homology isomorphism compares target cohomology to
ordinary pullback of source cohomology. The scheme-module theorem supplies
quasi-coherence of the latter, and isomorphism closure supplies the former.

## References

The exact homology comparison is in the repository's
`Algebra/Homology/DerivedCategory/Homology.lean`; ordinary quasi-coherent
pullback is in `AlgebraicGeometry/Modules/Quasicoherent/Pullback.lean`.

## Tags

derived pullback, quasi-coherent cohomology, exact pullback, flat pullback
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

/-- Exact derived pullback preserves quasi-coherent cohomology. The exact
homology comparison reduces this to ordinary quasi-coherent pullback. -/
theorem derivedPullback_preservesQuasicoherentCohomology
    (f : T ⟶ U) [IsExactPullback f]
    (E : Dqc.SchemeQuasicoherentDerivedCategory U.left) :
    Dqc.schemeQuasicoherentCohomology T.left
      ((derivedPullback f).obj E.obj) := by
  intro n
  let M := (DerivedCategory.homologyFunctor U.left.Modules n).obj E.obj
  have hM : M.IsQuasicoherent := E.property n
  have hpull : ((modulePullback f).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback f.left M hM
  exact (SheafOfModules.isQuasicoherent T.left.ringCatSheaf).prop_of_iso
    (mapDerivedCategoryHomologyIso (modulePullback f) inferInstance
      inferInstance inferInstance E.obj n).symm hpull

/-- The proof-backed quasi-coherent left-derived pullback in the exact case. -/
def exactDqcLeftDerivedPullback (f : T ⟶ U) [IsExactPullback f] :
    DqcLeftDerivedPullback f :=
  DqcLeftDerivedPullback.ofExact
    (derivedPullback_preservesQuasicoherentCohomology f)

/-- Flat pullback preserves quasi-coherent cohomology without a caller-supplied
exactness or preservation witness. -/
def flatDqcLeftDerivedPullback (f : T ⟶ U) [Flat f.left] :
    DqcLeftDerivedPullback f :=
  exactDqcLeftDerivedPullback f

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
