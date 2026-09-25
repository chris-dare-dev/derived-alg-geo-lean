import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ScalarExtendedSections

/-! # SF11 actual pullback-unit map after scalar extension -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackTopAfterExtension
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackTopAfterExtension_one_tmul

-- No cartesian or affine hypothesis is needed to define this A-linear map.
-- Those hypotheses are needed later to prove that the map is invertible.
example {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))
    (compat : φ ≫ f.appTop = a ≫ ψ) :
    (ModuleCat.extendScalars a.hom).obj
        ((fixedBaseSectionsFunctor Y φ ⊤).obj M) ⟶
      (fixedBaseSectionsFunctor Z ψ ⊤).obj ((Scheme.Modules.pullback f).obj M) :=
  Scheme.Modules.fixedBasePullbackTopAfterExtension φ f M a ψ compat

-- The map is fixed by the actual adjunction unit on every pure generator.
example {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))
    (compat : φ ≫ f.appTop = a ≫ ψ) (x : Γ(M, ⊤)) :
    (Scheme.Modules.fixedBasePullbackTopAfterExtension φ f M a ψ compat).hom
        ((1 : A) ⊗ₜ[R,(a.hom)] x) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) x :=
  Scheme.Modules.fixedBasePullbackTopAfterExtension_one_tmul φ f M a ψ compat x

end
