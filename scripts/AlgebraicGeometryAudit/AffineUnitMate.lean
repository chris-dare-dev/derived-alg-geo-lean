import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec

/-!
# Affine scheme-module pullback unit mate

This direct owner-leaf client checks the actual pullback-unit equation and its tensor-generator
specialization without importing a relative global-sections or derived category module.
-/

open CategoryTheory
open scoped TensorProduct

universe u

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeIso_unit
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeIso_unit_apply

-- The Γ-functor's action on the adjunction unit is literally its top-section map.
example {R S : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat.{u} R)
    (x : AlgebraicGeometry.moduleSpecΓFunctor.obj (AlgebraicGeometry.tilde M)) :
    ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).map
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Spec.map f)).unit.app (AlgebraicGeometry.tilde M))).hom x =
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Spec.map f)).unit.app (AlgebraicGeometry.tilde M)).app ⊤) x := by
  rfl

example {R S : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((AlgebraicGeometry.tilde.isoTop M).hom ≫
      (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).map
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.Spec.map f)).unit.app (AlgebraicGeometry.tilde M)) ≫
      (AlgebraicGeometry.gammaPushforwardNatIso f).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Spec.map f)).obj
          (AlgebraicGeometry.tilde M)) ≫
      (ModuleCat.restrictScalars f.hom).map
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := S)).map
          ((AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeIso f).hom.app M))).hom m =
    (AlgebraicGeometry.tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom
      ((1 : S) ⊗ₜ[R] m) := by
  exact AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeIso_unit_apply f M m
