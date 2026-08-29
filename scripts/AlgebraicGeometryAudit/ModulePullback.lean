import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback

/-!
# Scheme-module pullback audit

This slice checks the neutral pullback root independently of line-bundle, determinant, divisor,
and Picard-group consumers. Intrinsic rank-one invertibility is inherited through Mathlib's
existing scheme-module pullback rather than stored in a parallel carrier. Strong monoidality is
likewise consumed through Mathlib's standard `Functor.Monoidal` class rather than a parallel
capability record.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTrivializationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_pullback
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackUnitIso

example [SheafOfModules.IsInvertible.{u, u, u}
    (show SheafOfModules Y.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj M) :=
  inferInstance

end AlgebraicGeometry.Scheme.Modules
