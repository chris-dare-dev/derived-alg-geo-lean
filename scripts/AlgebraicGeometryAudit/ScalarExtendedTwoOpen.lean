import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ScalarExtendedTwoOpen

/-! # Two-open gluing of the actual scalar-extended pullback unit -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpenAfterExtension_isIso_sup

-- This is conditional on the three actual open-section maps, not a chart theorem.
example {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u,u,u} a.hom)]
    (U V : Y.Opens) (compat : φ ≫ f.appTop = a ≫ ψ)
    [IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M a ψ U compat)]
    [IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M a ψ V compat)]
    [IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M a ψ (U ⊓ V) compat)] :
    IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M a ψ (U ⊔ V) compat) :=
  Scheme.Modules.fixedBasePullbackOpenAfterExtension_isIso_sup φ f M a ψ U V compat

-- Canonical localization supplies finite-limit preservation; the three
-- open-section map isomorphisms remain explicit assumptions.
example {R : CommRingCat.{u}} {Y Z : Scheme.{u}}
    (S : Submonoid R) (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (ψ : CommRingCat.of (Localization S) ⟶ Γ(Z, ⊤))
    (U V : Y.Opens)
    (compat : φ ≫ f.appTop =
      CommRingCat.ofHom (algebraMap R (Localization S)) ≫ ψ)
    [IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M
      (CommRingCat.ofHom (algebraMap R (Localization S))) ψ U compat)]
    [IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M
      (CommRingCat.ofHom (algebraMap R (Localization S))) ψ V compat)]
    [IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M
      (CommRingCat.ofHom (algebraMap R (Localization S))) ψ (U ⊓ V) compat)] :
    IsIso (Scheme.Modules.fixedBasePullbackOpenAfterExtension φ f M
      (CommRingCat.ofHom (algebraMap R (Localization S))) ψ (U ⊔ V) compat) := by
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u,u,u} (algebraMap R (Localization S))) :=
    preservesFiniteLimits_of_natIso (ModuleCat.extendScalarsLocalizationNatIso S).symm
  exact Scheme.Modules.fixedBasePullbackOpenAfterExtension_isIso_sup φ f M
    (CommRingCat.ofHom (algebraMap R (Localization S))) ψ U V compat

end
