/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.FixedBaseSheaf
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Action

/-!
# Pullback of top sections over a fixed base ring

The actual scheme-module pullback adjunction unit induces a map on top
sections. This file equips that map with its fixed-base-ring linearity for
an arbitrary scheme morphism. It does not assert that the map is a
localization, an isomorphism, or a derived global-sections comparison.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
  (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)

/-- The actual pullback unit on top sections, as a map of `R`-modules. -/
noncomputable def fixedBasePullbackTop :
    (fixedBaseSectionsFunctor Y φ ⊤).obj M ⟶
      (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) ⊤).obj ((pullback f).obj M) := by
  let η := (pullbackPushforwardAdjunction f).unit.app M
  let g := (fixedBaseSectionsFunctor Y φ ⊤).map η
  let N := (pullback f).obj M
  let X := (fixedBaseSectionsFunctor Y φ ⊤).obj ((pushforward f).obj N)
  let T := (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) ⊤).obj N
  letI : Module R X := X.isModule
  letI : Module R T := T.isModule
  let cmp :
      X ⟶ T :=
    ModuleCat.ofHom (X := X) (Y := T)
      { toFun := fun x => x
        map_add' := by intros; rfl
        map_smul' := by
          intro r x
          change (X.smul r).hom x = (T.smul r).hom x
          have hX := modulesToFixedBaseSheaf_smul Y φ ((pushforward f).obj N) ⊤ r x
          change (X.smul r).hom x = _ at hX
          have hT := modulesToFixedBaseSheaf_smul Z (φ ≫ f.appTop) N ⊤ r x
          change (T.smul r).hom x = _ at hT
          rw [hX, hT]
          have htopY : (⊤ : Y.Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
          have htopZ : (⊤ : Z.Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
          simp [htopY, htopZ] at *
          change (φ.hom r) • (show Γ((pushforward f).obj N, ⊤) from x) =
            f.appTop.hom (φ.hom r) • (show Γ(N, ⊤) from x)
          exact pushforward_smul_appTop f N (φ.hom r) x }
  exact g ≫ cmp

/-- On elements, the fixed-base linear map is exactly the top component of
the ordinary pullback adjunction unit. -/
@[simp] theorem fixedBasePullbackTop_apply (x : Γ(M, ⊤)) :
    (fixedBasePullbackTop φ f M).hom x =
      (((pullbackPushforwardAdjunction f).unit.app M).app ⊤) x :=
  rfl

/-- Naturality of the actual pullback-unit map on fixed-base top sections. -/
noncomputable def fixedBasePullbackTopNat :
    fixedBaseSectionsFunctor Y φ ⊤ ⟶
      pullback f ⋙ fixedBaseSectionsFunctor Z (φ ≫ f.appTop) ⊤ where
  app M := fixedBasePullbackTop φ f M
  naturality := by
    intro A B u
    ext x
    have ht := congrArg (fun g => (g.app ⊤) x)
      ((pullbackPushforwardAdjunction f).unit.naturality u)
    exact ht

end AlgebraicGeometry.Scheme.Modules
