import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseSections

/-! # Actual pullback-unit map on fixed-base top sections -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackTop
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackTop_apply
#print axioms AlgebraicGeometry.Scheme.Modules.fixedBasePullbackTopNat

-- No affine or quasi-coherence hypothesis enters the linear map.
example {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
    (x : Γ(M, ⊤)) :
    (Scheme.Modules.fixedBasePullbackTop φ f M).hom x =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) x :=
  Scheme.Modules.fixedBasePullbackTop_apply φ f M x

-- The comparison is natural in the module sheaf, not a pointwise choice of
-- unrelated R-linear maps.
example {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
    (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) {M N : Y.Modules} (u : M ⟶ N) :
    (fixedBaseSectionsFunctor Y φ ⊤).map u ≫
        Scheme.Modules.fixedBasePullbackTop φ f N =
      Scheme.Modules.fixedBasePullbackTop φ f M ≫
        (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) ⊤).map
          ((Scheme.Modules.pullback f).map u) :=
  (Scheme.Modules.fixedBasePullbackTopNat φ f).naturality u
