import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseOpenSections

/-! # The actual pullback unit on sections of an arbitrary open -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpen
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpen_apply
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpenNat
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackOpen_restrict

-- The client needs no affine or quasi-coherence assumption.
example {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (x : Γ(M, U)) :
    (Scheme.Modules.fixedBasePullbackOpen φ f M U).hom x =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U) x :=
  Scheme.Modules.fixedBasePullbackOpen_apply φ f M U x

example {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) {M N : Y.Modules}
    (U : Y.Opens) (u : M ⟶ N) :
    (fixedBaseSectionsFunctor Y φ U).map u ≫
        Scheme.Modules.fixedBasePullbackOpen φ f N U =
      Scheme.Modules.fixedBasePullbackOpen φ f M U ≫
        (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).map
          ((Scheme.Modules.pullback f).map u) :=
  (Scheme.Modules.fixedBasePullbackOpenNat φ f U).naturality u

example {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : U ≤ V) :
    Scheme.Modules.fixedBasePullbackOpen φ f M V ≫
        ((modulesToFixedBaseSheaf Z (φ ≫ f.appTop)).obj
          ((Scheme.Modules.pullback f).obj M)).presheaf.map
          ((Opens.map f.base).map (homOfLE h)).op =
      ((modulesToFixedBaseSheaf Y φ).obj M).presheaf.map (homOfLE h).op ≫
        Scheme.Modules.fixedBasePullbackOpen φ f M U :=
  Scheme.Modules.fixedBasePullbackOpen_restrict φ f M h
