import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback

/-!
# Scheme-module pullback audit

This slice checks the neutral pullback root independently of line-bundle, determinant, divisor,
and Picard-group consumers. In particular, intrinsic rank-one invertibility is inherited through
Mathlib's existing scheme-module pullback rather than stored in a parallel carrier.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTrivializationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_pullback
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackLocalGeneratorsData
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackLocalGeneratorsData_generators_I
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallyFreeData_pullbackLocalGeneratorsData
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback

/-! ## Pullback on slices, and the structure sheaf -/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardOverFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverAdjunction
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverFunctor_preservesColimits
#print axioms AlgebraicGeometry.Scheme.Modules.overEquivFunctorUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.overEquivInverseUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackRestrictUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverUnitIso
#print axioms AlgebraicGeometry.Scheme.Hom.coversTop_preimage

/-! ## Coherence is preserved by pullback

`Coh.pullback` with its exactness: right exact always, left exact when module-sheaf pullback is.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackPresentationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isFinite_pullbackPresentationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback
#print axioms AlgebraicGeometry.Scheme.Modules.isCoherent_pullback
#print axioms AlgebraicGeometry.Coh.pullback
#print axioms AlgebraicGeometry.Coh.pullbackCompι
#print axioms AlgebraicGeometry.Coh.pullback_preservesFiniteColimits
#print axioms AlgebraicGeometry.Coh.pullback_preservesFiniteLimits
#print axioms AlgebraicGeometry.Coh.pullback_additive

example [SheafOfModules.IsInvertible.{u, u, u}
    (show SheafOfModules Y.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj M) :=
  inferInstance

end AlgebraicGeometry.Scheme.Modules
