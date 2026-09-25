import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ScalarExtendedOpenSections

/-! # Actual pullback unit on arbitrary open sections after scalar extension -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpenAfterExtension
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpenAfterExtension_one_tmul

-- The map is A-linear for an arbitrary scheme morphism and arbitrary open.
example {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))
    (U : Y.Opens) (compat : φ ≫ f.appTop = a ≫ ψ) :
    (ModuleCat.extendScalars a.hom).obj
        ((fixedBaseSectionsFunctor Y φ U).obj M) ⟶
      (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj
        ((Scheme.Modules.pullback f).obj M) :=
  Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M a ψ U compat

-- On the generator, this is the component of the actual adjunction unit.
example {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))
    (U : Y.Opens) (compat : φ ≫ f.appTop = a ≫ ψ) (x : Γ(M, U)) :
    (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M a ψ U compat).hom
        ((1 : A) ⊗ₜ[R,(a.hom)] x) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U) x :=
  Scheme.Modules.fixedBasePullbackOpenAfterExtension_one_tmul φ f M a ψ U compat x

end
