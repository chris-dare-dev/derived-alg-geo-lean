/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseSections

/-!
# The pullback unit on sections over an arbitrary open

For a scheme morphism `f : Z ⟶ Y` and a base-ring map
`φ : R ⟶ Γ(Y, ⊤)`, the actual pullback adjunction unit gives an `R`-linear
map from sections of `M` on `U` to sections of `f⁺ M` on `f ⁻¹ᵁ U`.
The map is natural in `M` and commutes with restriction of opens.
No affine, quasi-coherent, localization, or derived hypothesis is used.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {Z Y : Scheme.{u}}
  (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)

private theorem pushforward_smul_open (N : Z.Modules) (U : Y.Opens)
    (a : Γ(Y, ⊤)) (x : Γ((pushforward f).obj N, U)) :
    (((pushforward f).obj N).smul (Y.presheaf.map U.leTop.op a)).hom x =
      (N.smul (Z.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop.hom a))).hom
        (show Γ(N, f ⁻¹ᵁ U) from x) := by
  change (f.app U).hom (Y.presheaf.map U.leTop.op a) •
      (show Γ(N, f ⁻¹ᵁ U) from x) =
    (Z.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop.hom a)) •
      (show Γ(N, f ⁻¹ᵁ U) from x)
  exact congrArg (fun s : Γ(Z, f ⁻¹ᵁ U) => s • (show Γ(N, f ⁻¹ᵁ U) from x))
    (ConcreteCategory.congr_hom (f.naturality U.leTop.op) a)

/-- The actual pullback adjunction unit on sections of `U`, linear over `R`. -/
noncomputable def fixedBasePullbackOpen (U : Y.Opens) :
    (fixedBaseSectionsFunctor Y φ U).obj M ⟶
      (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).obj ((pullback f).obj M) := by
  let η := (pullbackPushforwardAdjunction f).unit.app M
  let g := (fixedBaseSectionsFunctor Y φ U).map η
  let N := (pullback f).obj M
  let X := (fixedBaseSectionsFunctor Y φ U).obj ((pushforward f).obj N)
  let T := (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).obj N
  letI : Module R X := X.isModule
  letI : Module R T := T.isModule
  let cmp : X ⟶ T :=
    ModuleCat.ofHom (X := X) (Y := T)
      { toFun := fun x => x
        map_add' := by intros; rfl
        map_smul' := by
          intro r x
          change (X.smul r).hom x = (T.smul r).hom x
          have hX := modulesToFixedBaseSheaf_smul Y φ ((pushforward f).obj N) U r x
          change (X.smul r).hom x = _ at hX
          have hT := modulesToFixedBaseSheaf_smul Z (φ ≫ f.appTop) N
            (f ⁻¹ᵁ U) r x
          change (T.smul r).hom x = _ at hT
          rw [hX, hT]
          exact pushforward_smul_open f N U (φ.hom r) x }
  exact g ≫ cmp

/-- On elements the linear map is the component of the ordinary adjunction unit. -/
@[simp] theorem fixedBasePullbackOpen_apply (U : Y.Opens) (x : Γ(M, U)) :
    (fixedBasePullbackOpen φ f M U).hom x =
      (((pullbackPushforwardAdjunction f).unit.app M).app U) x :=
  rfl

/-- Naturality of the open-section pullback unit in the module sheaf. -/
noncomputable def fixedBasePullbackOpenNat (U : Y.Opens) :
    fixedBaseSectionsFunctor Y φ U ⟶
      pullback f ⋙ fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U) where
  app M := fixedBasePullbackOpen φ f M U
  naturality := by
    intro A B u
    ext x
    have ht := congrArg (fun g => (g.app U) x)
      ((pullbackPushforwardAdjunction f).unit.naturality u)
    exact ht

/-- The open-section pullback unit commutes with restriction from `V` to `U`. -/
theorem fixedBasePullbackOpen_restrict {U V : Y.Opens} (h : U ≤ V) :
    fixedBasePullbackOpen φ f M V ≫
        ((modulesToFixedBaseSheaf Z (φ ≫ f.appTop)).obj ((pullback f).obj M)).presheaf.map
          ((Opens.map f.base).map (homOfLE h)).op =
      ((modulesToFixedBaseSheaf Y φ).obj M).presheaf.map (homOfLE h).op ≫
        fixedBasePullbackOpen φ f M U := by
  ext x
  exact (NatTrans.naturality_apply
    ((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf (homOfLE h).op x).symm

end AlgebraicGeometry.Scheme.Modules
