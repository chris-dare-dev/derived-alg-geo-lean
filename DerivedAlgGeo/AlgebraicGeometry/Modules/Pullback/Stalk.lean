/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Module stalks and pullback

This file equips stalks of scheme-module sheaves with their canonical local-ring
module structure.  These stalk functors preserve finite limits and jointly
reflect isomorphisms.  Pullback followed by a module stalk is identified with
the source stalk followed by extension of scalars along the local-ring map.

The pullback comparison is first constructed for presheaves via a private
module-valued skyscraper adjunction, then transported through module
sheafification.  It assumes no flatness and does not assert that pullback along
an arbitrary scheme morphism is exact.

## Main results

* `moduleStalkFunctor` bundles a sheaf stalk over the local ring.
* `preservesFiniteLimits_of_stalkwise` reduces finite-limit preservation to
  module stalks.
* `presheafModulePullbackStalkIso` compares presheaf pullback with extension of
  scalars on stalks.
* `pullbackStalkIso` gives the corresponding comparison for module sheaves.
-/

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/-- The cocone of underlying rings whose point is the local ring of `X` at
`x`.  It is the image of the standard commutative-ring stalk cocone. -/
def moduleStalkRingCocone (X : Scheme.{u}) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf ⋙
      forget₂ CommRingCat RingCat) :=
  (forget₂ CommRingCat RingCat).mapCocone
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf))

/-- The underlying-ring stalk cocone is a colimit cocone. -/
def moduleStalkRingIsColimit (X : Scheme.{u}) (x : X) :
    IsColimit (moduleStalkRingCocone X x) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))

/-- The colimit over the neighborhood diagram of modules, bundled over the
local ring at `x`. -/
def neighborhoodModuleStalkFunctor (X : Scheme.{u}) (x : X) :
    _root_.PresheafOfModules.{u}
        ((OpenNhds.inclusion x).op ⋙ X.ringCatSheaf.obj) ⥤
      ModuleCat.{u} (X.presheaf.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  _root_.PresheafOfModules.colimitFunctor (moduleStalkRingIsColimit X x)

/-- The stalk of a presheaf of modules, bundled over the local ring. -/
def presheafModuleStalkFunctor (X : Scheme.{u}) (x : X) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      ModuleCat.{u} (X.presheaf.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  _root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
      X.ringCatSheaf.obj ⋙
    _root_.PresheafOfModules.colimitFunctor
      (moduleStalkRingIsColimit X x)

/-- The stalk of a sheaf of modules, bundled as a module over the local ring.

This refines the usual abelian-group-valued stalk functor with the canonical
local-ring module structure. -/
def moduleStalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  Scheme.Modules.toPresheafOfModules X ⋙
    presheafModuleStalkFunctor X x

/-- The module map on stalks induced by the unit from a presheaf of modules
to its module sheafification. -/
def presheafModuleStalkToSheafificationApp
    (X : Scheme.{u}) (x : X)
    (M : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (presheafModuleStalkFunctor X x).obj M ⟶
      (moduleStalkFunctor X x).obj
        ((_root_.PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj M) :=
  (presheafModuleStalkFunctor X x).map
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app M)

/-- Module sheafification induces an isomorphism on every module stalk. -/
theorem presheafModuleStalkToSheafificationApp_isIso
    (X : Scheme.{u}) (x : X)
    (M : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    IsIso (presheafModuleStalkToSheafificationApp X x M) := by
  rw [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})]
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) M.presheaf))
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x AddCommGrpCat M.presheaf

/-- Taking a module stalk commutes naturally with module sheafification. -/
def presheafModuleStalkSheafificationIso
    (X : Scheme.{u}) (x : X) :
    presheafModuleStalkFunctor X x ≅
      _root_.PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) ⋙
        moduleStalkFunctor X x :=
  NatIso.ofComponents
    (fun M ↦
      @asIso _ _ _ _ (presheafModuleStalkToSheafificationApp X x M)
        (presheafModuleStalkToSheafificationApp_isIso X x M))
    (fun {M N} f ↦ by
      rw [asIso_hom, asIso_hom]
      change (presheafModuleStalkFunctor X x).map f ≫
          (presheafModuleStalkFunctor X x).map
            ((_root_.PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app N) =
        (presheafModuleStalkFunctor X x).map
            ((_root_.PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app M) ≫
          (presheafModuleStalkFunctor X x).map
            (((_root_.PresheafOfModules.sheafification
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map f).val)
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congr_arg (presheafModuleStalkFunctor X x).map
        ((_root_.PresheafOfModules.sheafificationAdjunction
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.naturality f))

/-- Forgetting the local-ring action on `moduleStalkFunctor` recovers the
usual stalk of the underlying sheaf of abelian groups. -/
def moduleStalkForgetIso (X : Scheme.{u}) (x : X) :
    moduleStalkFunctor X x ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  CategoryTheory.Functor.associator _ _ _

/-- Taking the stalk of a sheaf of modules preserves finite limits. -/
theorem moduleStalkFunctor_preservesFiniteLimits
    (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor X x) := by
  let forgetModule :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hF : PreservesFiniteLimits F := inferInstance
  have hG : PreservesFiniteLimits G := inferInstance
  have hFG : PreservesFiniteLimits (F ⋙ G) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ F G hF hG
  have hComposite :
      PreservesFiniteLimits (moduleStalkFunctor X x ⋙ forgetModule) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (moduleStalkForgetIso X x).symm hFG
  letI := hComposite
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleStalkFunctor X x) forgetModule

/-- The family of module-stalk functors over all points detects
isomorphisms of sheaves of modules. -/
theorem moduleStalkFunctors_jointlyReflectIsomorphisms (X : Scheme.{u}) :
    JointlyReflectIsomorphisms (moduleStalkFunctor X) where
  isIso {M N} f := by
    intro
    let M' : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨M.presheaf, M.isSheaf⟩
    let N' : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨N.presheaf, N.isSheaf⟩
    let g : M' ⟶ N' := { hom := f.mapPresheaf }
    haveI : IsIso g := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      have : IsIso
          ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x))
            AddCommGrpCat.{u}).map ((moduleStalkFunctor X x).map f)) :=
        inferInstance
      exact this
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    change IsIso
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map g).app (op U))
    infer_instance

/-- A functor between categories of module sheaves preserves finite limits
as soon as all of its composites with module-stalk functors do. -/
theorem preservesFiniteLimits_of_stalkwise
    {X Y : Scheme.{u}} (F : Y.Modules ⥤ X.Modules)
    (hF : ∀ x : X,
      PreservesFiniteLimits (F ⋙ moduleStalkFunctor X x)) :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := by
    letI (x : X) : PreservesFiniteLimits (moduleStalkFunctor X x) :=
      moduleStalkFunctor_preservesFiniteLimits X x
    letI (x : X) : PreservesFiniteLimits
        (F ⋙ moduleStalkFunctor X x) :=
      hF x
    refine { preservesLimit := fun {K} ↦
      { preserves := fun {c} hc ↦ ⟨?_⟩ } }
    exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).jointlyReflectsLimit
      (fun x ↦ by
        change IsLimit ((F ⋙ moduleStalkFunctor X x).mapCone c)
        exact isLimitOfPreserves (F ⋙ moduleStalkFunctor X x) hc)

/-- The ring map on neighborhood diagrams induced by a scheme morphism at a
point. Its component over `V ∋ f(x)` is the restriction of the scheme map
from `Γ(V, 𝒪_Y)` to `Γ(f⁻¹(V), 𝒪_X)`. -/
def neighborhoodRingHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (OpenNhds.inclusion (f x)).op ⋙ Y.ringCatSheaf.obj ⟶
      (OpenNhds.map f.base x).op ⋙
        ((OpenNhds.inclusion x).op ⋙ X.ringCatSheaf.obj) where
  app V := (forget₂ CommRingCat RingCat).map (f.app V.unop.1)
  naturality V W g := by
    exact f.toRingCatSheafHom.hom.naturality
      ((OpenNhds.inclusion (f x)).op.map g)

/-- Pullback of modules along the induced map between the two neighborhood
ring diagrams. -/
abbrev neighborhoodModulePullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :=
  _root_.PresheafOfModules.pullback (neighborhoodRingHom f x)

/-- The neighborhood ring map commutes with the two stalk cocones through the
scheme morphism's map on local rings. -/
lemma neighborhoodRingHom_comp_stalkCocone {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (V : (OpenNhds (f x))ᵒᵖ) :
    (moduleStalkRingCocone Y (f x)).ι.app V ≫
        (forget₂ CommRingCat RingCat).map (f.stalkMap x) =
      (neighborhoodRingHom f x).app V ≫
        (moduleStalkRingCocone X x).ι.app
          ((OpenNhds.map f.base x).op.obj V) := by
  obtain ⟨⟨V, hxV⟩⟩ := V
  exact congr_arg (forget₂ CommRingCat RingCat).map
    (Scheme.Hom.germ_stalkMap f V x hxV)

/-- Objectwise comparison between the two right adjoints used to compute
pullback followed by the neighborhood colimit. -/
def constNeighborhoodPushforwardIsoApp {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (_root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x) ⋙
      _root_.PresheafOfModules.pushforward (neighborhoodRingHom f x)).obj N ≅
    (ModuleCat.restrictScalars (f.stalkMap x).hom ⋙
      _root_.PresheafOfModules.constFunctor
        (moduleStalkRingCocone Y (f x))).obj N :=
  _root_.PresheafOfModules.isoMk
    (fun V ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ by
      ext m
      exact congrArg (fun s : X.presheaf.stalk x ↦ s • (show N from m))
        (CategoryTheory.congr_fun
          (neighborhoodRingHom_comp_stalkCocone f x V) r)))
    (fun {V W} g ↦ by ext m; rfl)

/-- Natural comparison between constant neighborhood modules followed by
pushforward and restriction of scalars followed by constant modules. -/
def constNeighborhoodPushforwardIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    _root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x) ⋙
        _root_.PresheafOfModules.pushforward (neighborhoodRingHom f x) ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙
        _root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone Y (f x)) :=
  NatIso.ofComponents (constNeighborhoodPushforwardIsoApp f x)
    (fun {M N} g ↦ by ext V m; rfl)

/-- Pulling a module diagram back from neighborhoods of `f(x)` and taking its
neighborhood colimit agrees with first taking the stalk at `f(x)` and then
extending scalars along the local-ring map at `x`. -/
def neighborhoodModulePullbackStalkIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    neighborhoodModulePullback f x ⋙ neighborhoodModuleStalkFunctor X x ≅
      neighborhoodModuleStalkFunctor Y (f x) ⋙
        ModuleCat.extendScalars (f.stalkMap x).hom := by
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  letI : InitiallySmall.{u} (OpenNhds (f x)) :=
    initiallySmall_of_essentiallySmall _
  letI : CommRing (moduleStalkRingCocone X x).pt :=
    inferInstanceAs (CommRing (X.presheaf.stalk x))
  letI : CommRing (moduleStalkRingCocone Y (f x)).pt :=
    inferInstanceAs (CommRing (Y.presheaf.stalk (f x)))
  change neighborhoodModulePullback f x ⋙
      _root_.PresheafOfModules.colimitFunctor (moduleStalkRingIsColimit X x) ≅
    _root_.PresheafOfModules.colimitFunctor
        (moduleStalkRingIsColimit Y (f x)) ⋙
      ModuleCat.extendScalars (f.stalkMap x).hom
  exact Adjunction.leftAdjointCompIso
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction
      (neighborhoodRingHom f x))
    (_root_.PresheafOfModules.colimitAdjunction (moduleStalkRingIsColimit X x))
    ((_root_.PresheafOfModules.colimitAdjunction
      (moduleStalkRingIsColimit Y (f x))).comp
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
    (constNeighborhoodPushforwardIso f x)

/-- After taking a stalk, module-sheaf pullback reduces canonically to
presheaf-module pullback.  The sheafification step disappears because it
induces an isomorphism on every module stalk. -/
def pullbackStalkPresheafIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    pullback f ⋙ moduleStalkFunctor X x ≅
      toPresheafOfModules Y ⋙
        _root_.PresheafOfModules.pullback f.toRingCatSheafHom.hom ⋙
          presheafModuleStalkFunctor X x :=
  CategoryTheory.Functor.isoWhiskerRight
        (SheafOfModules.pullbackIso f.toRingCatSheafHom)
        (moduleStalkFunctor X x) ≪≫
    CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft
      (toPresheafOfModules Y ⋙
        _root_.PresheafOfModules.pullback f.toRingCatSheafHom.hom)
      (presheafModuleStalkSheafificationIso X x).symm

/-! ### The presheaf pullback-to-stalk comparison

The implementation constructs the module-valued skyscraper presheaf at a
point, proves that it is right adjoint to the module stalk functor, and uses
uniqueness of left adjoints to identify pullback followed by a stalk with
extension of scalars along the induced local-ring map. The construction is
kept private; the resulting canonical comparison is exposed below.
-/

@[reducible] private def subsingletonModule (R M : Type u) [Ring R]
    [AddCommGroup M] [Subsingleton M] : Module R M := by
  letI : SMul R M := ⟨fun _ _ ↦ 0⟩
  letI : MulAction R M := {
    one_smul := fun _ ↦ Subsingleton.elim _ _
    mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _ }
  letI : DistribMulAction R M := {
    smul_zero := fun _ ↦ Subsingleton.elim _ _
    smul_add := fun _ _ _ ↦ Subsingleton.elim _ _ }
  exact {
    add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
    zero_smul := fun _ ↦ Subsingleton.elim _ _ }

private theorem terminalAddCommGrpSubsingleton :
    Subsingleton (terminal AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero
    ((isZero_zero AddCommGrpCat).of_iso
      (HasZeroObject.zeroIsoTerminal (C := AddCommGrpCat)).symm)

private def moduleSkyscraperUnderlying (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := by
  classical
  exact skyscraperPresheaf x
    ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).obj N)

private def moduleSkyscraperPositiveEquiv (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ)
    (hU : x ∈ U.unop) :
    ((moduleSkyscraperUnderlying X x N).obj U : Type u) ≃+ N := by
  classical
  exact (eqToIso (if_pos hU)).addCommGroupIsoToAddEquiv

@[reducible] private def moduleSkyscraperModule (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U)
      ((moduleSkyscraperUnderlying X x N).obj U) := by
  classical
  by_cases hU : x ∈ U.unop
  · letI : Module (X.ringCatSheaf.obj.obj U) N :=
      Module.compHom N (X.presheaf.germ U.unop x hU).hom
    exact (moduleSkyscraperPositiveEquiv X x N U hU).module _
  · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
      terminalAddCommGrpSubsingleton
    letI : Module (X.ringCatSheaf.obj.obj U)
        (terminal AddCommGrpCat.{u}) :=
      subsingletonModule _ _
    exact (eqToIso (if_neg hU)).addCommGroupIsoToAddEquiv.module _

private def moduleSkyscraperPresheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.PresheafOfModules := by
  classical
  let G := moduleSkyscraperUnderlying X x N
  letI (U : (Opens X)ᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) (G.obj U) :=
    moduleSkyscraperModule X x N U
  exact _root_.PresheafOfModules.ofPresheaf G (fun {U V} i r m ↦ by
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := i.unop.le hV
      let eU := moduleSkyscraperPositiveEquiv X x N U hU
      let eV := moduleSkyscraperPositiveEquiv X x N V hV
      letI : Module (X.ringCatSheaf.obj.obj U) N :=
        Module.compHom N (X.presheaf.germ U.unop x hU).hom
      letI : Module (X.ringCatSheaf.obj.obj V) N :=
        Module.compHom N (X.presheaf.germ V.unop x hV).hom
      have map_compat (z : G.obj U) : eV (G.map i z) = eU z := by
        have hmap : G.map i ≫
              (eqToIso (if_pos hV) : G.obj V ≅
                (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N).hom =
            (eqToIso (if_pos hU) : G.obj U ≅
                (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N).hom := by
          simp [G, moduleSkyscraperUnderlying, skyscraperPresheaf, hU, hV]
        exact CategoryTheory.congr_fun hmap z
      apply eV.injective
      calc
        eV (G.map i (r • m)) = eU (r • m) := map_compat _
        _ = r • eU m := by
          let smulActual (a : X.ringCatSheaf.obj.obj U) (z : G.obj U) : G.obj U :=
            letI : Module (X.ringCatSheaf.obj.obj U) (G.obj U) :=
              moduleSkyscraperModule X x N U
            a • z
          let smulTransfer (a : X.ringCatSheaf.obj.obj U) (z : G.obj U) : G.obj U :=
            letI : Module (X.ringCatSheaf.obj.obj U) (G.obj U) := eU.module _
            a • z
          have hmodule : moduleSkyscraperModule X x N U = eU.module _ := by
            simp [moduleSkyscraperModule, eU, hU]
          have hsmul : smulActual = smulTransfer := by
            unfold smulActual smulTransfer
            rw [hmodule]
          change eU (smulActual r m) = r • eU m
          rw [hsmul]
          simp [smulTransfer, Equiv.smul_def]
        _ = (X.ringCatSheaf.obj.map i).hom r • eU m := by
          change (X.presheaf.germ U.unop x hU).hom r • eU m =
            (X.presheaf.germ V.unop x hV).hom
              ((X.ringCatSheaf.obj.map i).hom r) • eU m
          exact congrArg (fun s : X.presheaf.stalk x ↦ s • eU m)
            (CategoryTheory.congr_fun (X.presheaf.germ_res' i x hV) r).symm
        _ = (X.ringCatSheaf.obj.map i).hom r • eV (G.map i m) := by
          rw [map_compat]
        _ = eV ((X.ringCatSheaf.obj.map i).hom r • G.map i m) := by
          let smulActual (a : X.ringCatSheaf.obj.obj V) (z : G.obj V) : G.obj V :=
            letI : Module (X.ringCatSheaf.obj.obj V) (G.obj V) :=
              moduleSkyscraperModule X x N V
            a • z
          let smulTransfer (a : X.ringCatSheaf.obj.obj V) (z : G.obj V) : G.obj V :=
            letI : Module (X.ringCatSheaf.obj.obj V) (G.obj V) := eV.module _
            a • z
          have hmodule : moduleSkyscraperModule X x N V = eV.module _ := by
            simp [moduleSkyscraperModule, eV, hV]
          have hsmul : smulActual = smulTransfer := by
            unfold smulActual smulTransfer
            rw [hmodule]
          change (X.ringCatSheaf.obj.map i).hom r • eV (G.map i m) =
            eV (smulActual ((X.ringCatSheaf.obj.map i).hom r) (G.map i m))
          rw [hsmul]
          simp [smulTransfer, Equiv.smul_def]
    · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
        terminalAddCommGrpSubsingleton
      apply (eqToIso (if_neg hV) : G.obj V ≅
        terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
      exact Subsingleton.elim _ _)

private def moduleSkyscraperPresheafAppIso (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ)
    (hU : x ∈ U.unop) :
    (moduleSkyscraperPresheaf X x N).obj U ≅
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hU).hom).obj N := by
  classical
  let e := moduleSkyscraperPositiveEquiv X x N U hU
  letI : Module (X.ringCatSheaf.obj.obj U) N :=
    Module.compHom N (X.presheaf.germ U.unop x hU).hom
  apply ModuleCat.isoMk
    (eqToIso (if_pos hU))
  intro r
  ext m
  let smulActual (a : X.ringCatSheaf.obj.obj U)
      (z : (moduleSkyscraperUnderlying X x N).obj U) :=
    letI : Module (X.ringCatSheaf.obj.obj U)
        ((moduleSkyscraperUnderlying X x N).obj U) :=
      moduleSkyscraperModule X x N U
    a • z
  let smulTransfer (a : X.ringCatSheaf.obj.obj U)
      (z : (moduleSkyscraperUnderlying X x N).obj U) :=
    letI : Module (X.ringCatSheaf.obj.obj U)
        ((moduleSkyscraperUnderlying X x N).obj U) := e.module _
    a • z
  have hmodule : moduleSkyscraperModule X x N U = e.module _ := by
    simp [moduleSkyscraperModule, e, hU]
  have hsmul : smulActual = smulTransfer := by
    unfold smulActual smulTransfer
    rw [hmodule]
  change (X.presheaf.germ U.unop x hU).hom r • e m = e (smulActual r m)
  rw [hsmul]
  simp [smulTransfer, Equiv.smul_def]
  rfl

@[simp] private theorem moduleSkyscraperPresheafAppIso_hom_apply
    (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ)
    (hU : x ∈ U.unop) (m : (moduleSkyscraperPresheaf X x N).obj U) :
    (moduleSkyscraperPresheafAppIso X x N U hU).hom m =
      moduleSkyscraperPositiveEquiv X x N U hU m := by
  rfl

@[simp] private theorem moduleSkyscraperPresheafAppIso_inv_apply
    (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ)
    (hU : x ∈ U.unop)
    (m : (ModuleCat.restrictScalars
      (X.presheaf.germ U.unop x hU).hom).obj N) :
    (moduleSkyscraperPresheafAppIso X x N U hU).inv m =
      (moduleSkyscraperPositiveEquiv X x N U hU).symm m := by
  rfl

private theorem moduleSkyscraperPositiveEquiv_map
    (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (hV : x ∈ V.unop)
    (m : (moduleSkyscraperUnderlying X x N).obj U) :
    moduleSkyscraperPositiveEquiv X x N V hV
        ((moduleSkyscraperUnderlying X x N).map i m) =
      moduleSkyscraperPositiveEquiv X x N U (i.unop.le hV) m := by
  classical
  have hmap : (moduleSkyscraperUnderlying X x N).map i ≫
        (eqToIso (if_pos hV) :
          (moduleSkyscraperUnderlying X x N).obj V ≅
            (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N).hom =
      (eqToIso (if_pos (i.unop.le hV)) :
          (moduleSkyscraperUnderlying X x N).obj U ≅
            (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N).hom := by
    simp [moduleSkyscraperUnderlying, skyscraperPresheaf, hV, i.unop.le hV]
  exact CategoryTheory.congr_fun hmap m

private def moduleSkyscraperMapApp (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) :
    ∀ U, (moduleSkyscraperPresheaf X x M).obj U ⟶
      (moduleSkyscraperPresheaf X x N).obj U := fun U ↦ by
  classical
  by_cases hU : x ∈ U.unop
  · exact (moduleSkyscraperPresheafAppIso X x M U hU).hom ≫
      (ModuleCat.restrictScalars
        (X.presheaf.germ U.unop x hU).hom).map g ≫
      (moduleSkyscraperPresheafAppIso X x N U hU).inv
  · exact 0

private def moduleSkyscraperUnderlyingMap (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) :
    moduleSkyscraperUnderlying X x M ⟶
      moduleSkyscraperUnderlying X x N := by
  classical
  exact SkyscraperPresheafFunctor.map' x
    ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map g)

private theorem moduleSkyscraperMapApp_apply (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N)
    (U : (Opens X)ᵒᵖ) (m : (moduleSkyscraperPresheaf X x M).obj U) :
    moduleSkyscraperMapApp X x g U m =
      (moduleSkyscraperUnderlyingMap X x g).app U m := by
  classical
  by_cases hU : x ∈ U.unop
  · let eN := moduleSkyscraperPositiveEquiv X x N U hU
    apply eN.injective
    simp [eN, moduleSkyscraperMapApp,
      moduleSkyscraperPresheafAppIso,
      moduleSkyscraperUnderlyingMap, moduleSkyscraperPositiveEquiv,
      moduleSkyscraperPresheaf, moduleSkyscraperUnderlying, hU]
    rfl
  · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
      terminalAddCommGrpSubsingleton
    apply (eqToIso (if_neg hU) :
      (moduleSkyscraperUnderlying X x N).obj U ≅
        terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
    exact Subsingleton.elim _ _

private def moduleSkyscraperMap (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) :
    moduleSkyscraperPresheaf X x M ⟶
      moduleSkyscraperPresheaf X x N where
  app := moduleSkyscraperMapApp X x g
  naturality {U V} i := by
    classical
    ext m
    change moduleSkyscraperMapApp X x g V
        ((moduleSkyscraperPresheaf X x M).map i m) =
      (moduleSkyscraperPresheaf X x N).map i
        (moduleSkyscraperMapApp X x g U m)
    let g' := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map g
    have h := CategoryTheory.congr_fun
      ((SkyscraperPresheafFunctor.map' x g').naturality i) m
    rw [moduleSkyscraperMapApp_apply, moduleSkyscraperMapApp_apply]
    change (moduleSkyscraperUnderlyingMap X x g).app V
        ((moduleSkyscraperUnderlying X x M).map i m) =
      (moduleSkyscraperUnderlying X x N).map i
        ((moduleSkyscraperUnderlyingMap X x g).app U m)
    exact h

private def moduleSkyscraperPresheafFunctor (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.PresheafOfModules where
  obj := moduleSkyscraperPresheaf X x
  map := moduleSkyscraperMap X x
  map_id M := by
    classical
    ext U m
    change moduleSkyscraperMapApp X x (𝟙 M) U m = m
    rw [moduleSkyscraperMapApp_apply]
    let M' := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj M
    have h := CategoryTheory.congr_fun
      (congr_app (SkyscraperPresheafFunctor.map'_id (C := AddCommGrpCat) x) U) m
    change (moduleSkyscraperUnderlyingMap X x (𝟙 M)).app U m = m
    exact h
  map_comp {M N P} g h := by
    classical
    ext U m
    change moduleSkyscraperMapApp X x (g ≫ h) U m =
      moduleSkyscraperMapApp X x h U
        (moduleSkyscraperMapApp X x g U m)
    rw [moduleSkyscraperMapApp_apply]
    change (moduleSkyscraperUnderlyingMap X x (g ≫ h)).app U m =
      moduleSkyscraperMapApp X x h U
        (moduleSkyscraperMapApp X x g U m)
    rw [moduleSkyscraperMapApp_apply, moduleSkyscraperMapApp_apply]
    have q := CategoryTheory.congr_fun
      (congr_app (SkyscraperPresheafFunctor.map'_comp x
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map g)
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map h)) U) m
    exact q

private def neighborhoodModuleSkyscraperIso (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).obj (moduleSkyscraperPresheaf X x N) ≅
      (_root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x)).obj N :=
  _root_.PresheafOfModules.isoMk
    (fun V ↦ moduleSkyscraperPresheafAppIso X x N
      ((OpenNhds.inclusion x).op.obj V) V.unop.2)
    (fun {V W} i ↦ by
    ext m
    change (moduleSkyscraperPresheafAppIso X x N
          ((OpenNhds.inclusion x).op.obj W) W.unop.2).hom
        ((moduleSkyscraperPresheaf X x N).map
          ((OpenNhds.inclusion x).op.map i) m) =
      ((_root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone X x)).obj N).map i
        ((moduleSkyscraperPresheafAppIso X x N
          ((OpenNhds.inclusion x).op.obj V) V.unop.2).hom m)
    rw [moduleSkyscraperPresheafAppIso_hom_apply,
      moduleSkyscraperPresheafAppIso_hom_apply]
    change moduleSkyscraperPositiveEquiv X x N
          ((OpenNhds.inclusion x).op.obj W) W.unop.2
          ((moduleSkyscraperUnderlying X x N).map
            ((OpenNhds.inclusion x).op.map i) m) = _
    rw [moduleSkyscraperPositiveEquiv_map]
    rfl)

private def skyscraperHomToNeighborhoodHom (X : Scheme.{u}) (x : X)
    (M : X.PresheafOfModules) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (φ : M ⟶ moduleSkyscraperPresheaf X x N) :
    (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).obj M ⟶
      (_root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x)).obj N :=
  (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
    X.ringCatSheaf.obj).map φ ≫
      (neighborhoodModuleSkyscraperIso X x N).hom

private def neighborhoodHomToSkyscraperHom (X : Scheme.{u}) (x : X)
    (M : X.PresheafOfModules) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (ψ : (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj).obj M ⟶
        (_root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone X x)).obj N) :
    M ⟶ moduleSkyscraperPresheaf X x N where
  app U := by
    classical
    by_cases hU : x ∈ U.unop
    · exact (ψ ≫ (neighborhoodModuleSkyscraperIso X x N).inv).app
        (op (⟨U.unop, hU⟩ : OpenNhds x))
    · exact 0
  naturality {U V} i := by
    classical
    ext m
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := i.unop.le hV
      let j : op (⟨U.unop, hU⟩ : OpenNhds x) ⟶
          op (⟨V.unop, hV⟩ : OpenNhds x) :=
        (homOfLE i.unop.le).op
      let θ := ψ ≫ (neighborhoodModuleSkyscraperIso X x N).inv
      have hθ := CategoryTheory.congr_fun
        (θ.naturality j) m
      have hj : (OpenNhds.inclusion x).op.map j = i := Subsingleton.elim _ _
      change θ.app (op (⟨V.unop, hV⟩ : OpenNhds x))
          (M.map ((OpenNhds.inclusion x).op.map j) m) =
        (moduleSkyscraperPresheaf X x N).map
          ((OpenNhds.inclusion x).op.map j)
          (θ.app (op (⟨U.unop, hU⟩ : OpenNhds x)) m) at hθ
      rw [hj] at hθ
      simp only [dif_pos hU, dif_pos hV]
      change θ.app (op (⟨V.unop, hV⟩ : OpenNhds x)) (M.map i m) =
        (moduleSkyscraperPresheaf X x N).map i
          (θ.app (op (⟨U.unop, hU⟩ : OpenNhds x)) m)
      exact hθ
    · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
        terminalAddCommGrpSubsingleton
      apply (eqToIso (if_neg hV) :
        (moduleSkyscraperUnderlying X x N).obj V ≅
          terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
      exact Subsingleton.elim _ _

private def skyscraperNeighborhoodHomEquiv (X : Scheme.{u}) (x : X)
    (M : X.PresheafOfModules) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (M ⟶ moduleSkyscraperPresheaf X x N) ≃
      ((_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj).obj M ⟶
        (_root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone X x)).obj N) where
  toFun := skyscraperHomToNeighborhoodHom X x M N
  invFun := neighborhoodHomToSkyscraperHom X x M N
  left_inv φ := by
    classical
    ext U m
    by_cases hU : x ∈ U.unop
    · simp [skyscraperHomToNeighborhoodHom,
        neighborhoodHomToSkyscraperHom, hU]
      rfl
    · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
        terminalAddCommGrpSubsingleton
      apply (eqToIso (if_neg hU) :
        (moduleSkyscraperUnderlying X x N).obj U ≅
          terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
      exact Subsingleton.elim _ _
  right_inv ψ := by
    ext V m
    obtain ⟨⟨V, hV⟩⟩ := V
    let Q : (OpenNhds x)ᵒᵖ := op ⟨V, hV⟩
    change (neighborhoodModuleSkyscraperIso X x N).hom.app Q
        ((neighborhoodHomToSkyscraperHom X x M N ψ).app (op V) m) =
      ψ.app Q m
    have happ : (neighborhoodHomToSkyscraperHom X x M N ψ).app (op V) =
        ψ.app Q ≫ (neighborhoodModuleSkyscraperIso X x N).inv.app Q := by
      dsimp only [neighborhoodHomToSkyscraperHom]
      rw [dif_pos hV]
      rfl
    rw [happ]
    have hc : ψ.app Q ≫
          (neighborhoodModuleSkyscraperIso X x N).inv.app Q ≫
          (neighborhoodModuleSkyscraperIso X x N).hom.app Q =
        ψ.app Q := by
      have hi : (neighborhoodModuleSkyscraperIso X x N).inv.app Q ≫
          (neighborhoodModuleSkyscraperIso X x N).hom.app Q = 𝟙 _ := by
        have hi' := (neighborhoodModuleSkyscraperIso X x N).inv_hom_id
        exact congrArg (fun k ↦ k.app Q) hi'
      calc
        ψ.app Q ≫ (neighborhoodModuleSkyscraperIso X x N).inv.app Q ≫
            (neighborhoodModuleSkyscraperIso X x N).hom.app Q =
          ψ.app Q ≫ 𝟙 _ := congrArg (fun k ↦ ψ.app Q ≫ k) hi
        _ = ψ.app Q := Category.comp_id _
    exact CategoryTheory.congr_fun hc m

private def neighborhoodModuleSkyscraperNatIso (X : Scheme.{u}) (x : X) :
    moduleSkyscraperPresheafFunctor X x ⋙
        _root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj ≅
      _root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x) :=
  NatIso.ofComponents (neighborhoodModuleSkyscraperIso X x)
    (fun {M N} g ↦ by
      ext V m
      obtain ⟨⟨V, hV⟩⟩ := V
      change (moduleSkyscraperPresheafAppIso X x N (op V) hV).hom
          (moduleSkyscraperMapApp X x g (op V) m) =
        ((ModuleCat.restrictScalars
          (X.presheaf.germ V x hV).hom).map g)
          ((moduleSkyscraperPresheafAppIso X x M (op V) hV).hom m)
      simp [moduleSkyscraperMapApp, hV]
      rfl)

private theorem skyscraperNeighborhoodHomEquiv_naturality_left
    (X : Scheme.{u}) (x : X)
    {M M' : X.PresheafOfModules} (f : M' ⟶ M)
    {N : ModuleCat.{u} (X.presheaf.stalk x)}
    (g : M ⟶ moduleSkyscraperPresheaf X x N) :
    skyscraperNeighborhoodHomEquiv X x M' N (f ≫ g) =
      (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).map f ≫
        skyscraperNeighborhoodHomEquiv X x M N g := by
  simp [skyscraperNeighborhoodHomEquiv,
    skyscraperHomToNeighborhoodHom, CategoryTheory.Functor.map_comp, Category.assoc]

private theorem skyscraperNeighborhoodHomEquiv_naturality_right
    (X : Scheme.{u}) (x : X)
    {M : X.PresheafOfModules}
    {N N' : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : M ⟶ moduleSkyscraperPresheaf X x N) (g : N ⟶ N') :
    skyscraperNeighborhoodHomEquiv X x M N'
        (f ≫ (moduleSkyscraperPresheafFunctor X x).map g) =
      skyscraperNeighborhoodHomEquiv X x M N f ≫
        (_root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone X x)).map g := by
  change (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).map
        (f ≫ (moduleSkyscraperPresheafFunctor X x).map g) ≫
      (neighborhoodModuleSkyscraperIso X x N').hom =
    (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).map f ≫
      (neighborhoodModuleSkyscraperIso X x N).hom ≫
        (_root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone X x)).map g
  have hn := (neighborhoodModuleSkyscraperNatIso X x).hom.naturality g
  change (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).map
          ((moduleSkyscraperPresheafFunctor X x).map g) ≫
      (neighborhoodModuleSkyscraperIso X x N').hom =
    (neighborhoodModuleSkyscraperIso X x N).hom ≫
      (_root_.PresheafOfModules.constFunctor
        (moduleStalkRingCocone X x)).map g at hn
  calc
    (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj).map
          (f ≫ (moduleSkyscraperPresheafFunctor X x).map g) ≫
        (neighborhoodModuleSkyscraperIso X x N').hom =
      (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj).map f ≫
        ((_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
            X.ringCatSheaf.obj).map
            ((moduleSkyscraperPresheafFunctor X x).map g) ≫
          (neighborhoodModuleSkyscraperIso X x N').hom) := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj).map f ≫
        ((neighborhoodModuleSkyscraperIso X x N).hom ≫
          (_root_.PresheafOfModules.constFunctor
            (moduleStalkRingCocone X x)).map g) :=
      congrArg (fun k ↦
        (_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
          X.ringCatSheaf.obj).map f ≫ k) hn
    _ = _ := (Category.assoc _ _ _).symm

private def presheafModuleStalkSkyscraperHomEquiv (X : Scheme.{u}) (x : X)
    (M : X.PresheafOfModules) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((presheafModuleStalkFunctor X x).obj M ⟶ N) ≃
      (M ⟶ (moduleSkyscraperPresheafFunctor X x).obj N) := by
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  exact ((_root_.PresheafOfModules.colimitAdjunction
    (moduleStalkRingIsColimit X x)).homEquiv
      ((_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
        X.ringCatSheaf.obj).obj M) N).trans
    (skyscraperNeighborhoodHomEquiv X x M N).symm

private def presheafModuleStalkSkyscraperAdjunction (X : Scheme.{u}) (x : X) :
    presheafModuleStalkFunctor X x ⊣
      moduleSkyscraperPresheafFunctor X x := by
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  let a := _root_.PresheafOfModules.colimitAdjunction
    (moduleStalkRingIsColimit X x)
  apply Adjunction.mkOfHomEquiv
  refine {
    homEquiv := presheafModuleStalkSkyscraperHomEquiv X x
    homEquiv_naturality_left_symm := ?_
    homEquiv_naturality_right := ?_ }
  · intro M' M N f g
    change (a.homEquiv _ _).symm
        (skyscraperNeighborhoodHomEquiv X x M' N (f ≫ g)) =
      (presheafModuleStalkFunctor X x).map f ≫
        (a.homEquiv _ _).symm
          (skyscraperNeighborhoodHomEquiv X x M N g)
    rw [skyscraperNeighborhoodHomEquiv_naturality_left]
    exact a.homEquiv_naturality_left_symm _ _
  · intro M N N' f g
    change (skyscraperNeighborhoodHomEquiv X x M N').symm
        (a.homEquiv _ _ (f ≫ g)) =
      (skyscraperNeighborhoodHomEquiv X x M N).symm
          (a.homEquiv _ _ f) ≫
        (moduleSkyscraperPresheafFunctor X x).map g
    apply (skyscraperNeighborhoodHomEquiv X x M N').injective
    rw [Equiv.apply_symm_apply]
    let q := (skyscraperNeighborhoodHomEquiv X x M N).symm
      (a.homEquiv _ _ f)
    have hn := skyscraperNeighborhoodHomEquiv_naturality_right
      X x q g
    have hq : skyscraperNeighborhoodHomEquiv X x M N q =
        a.homEquiv _ _ f := Equiv.apply_symm_apply _ _
    exact (a.homEquiv_naturality_right f g).trans
      ((congrArg (fun k ↦ k ≫
        (_root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone X x)).map g) hq.symm).trans hn.symm)

private def moduleSkyscraperPushforwardIsoAppOfMem {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y)ᵒᵖ) (hV : f x ∈ V.unop) :
    ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (moduleSkyscraperPresheaf X x N)).obj V ≅
      (moduleSkyscraperPresheaf Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V := by
  classical
  let a := (f.app V.unop).hom
  let b := (X.presheaf.germ (f ⁻¹ᵁ V.unop) x hV).hom
  let c := (Y.presheaf.germ V.unop (f x) hV).hom
  let d := (f.stalkMap x).hom
  let ba := b.comp a
  let dc := d.comp c
  have h : ba = dc := congrArg CommRingCat.Hom.hom
    (Scheme.Hom.germ_stalkMap f V.unop x hV).symm
  exact (ModuleCat.restrictScalars a).mapIso
        (moduleSkyscraperPresheafAppIso X x N
          (op (f ⁻¹ᵁ V.unop)) hV) ≪≫
      ((ModuleCat.restrictScalarsComp' a b ba rfl).app N).symm ≪≫
      (ModuleCat.restrictScalarsCongr h).app N ≪≫
      (ModuleCat.restrictScalarsComp' c d dc rfl).app N ≪≫
      (moduleSkyscraperPresheafAppIso Y (f x)
        ((ModuleCat.restrictScalars d).obj N) V hV).symm

private def moduleSkyscraperPushforwardIsoApp {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y)ᵒᵖ) :
    ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (moduleSkyscraperPresheaf X x N)).obj V ≅
      (moduleSkyscraperPresheaf Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V := by
  classical
  by_cases hV : f x ∈ V.unop
  · exact moduleSkyscraperPushforwardIsoAppOfMem f x N V hV
  · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
      terminalAddCommGrpSubsingleton
    let L := ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
      (moduleSkyscraperPresheaf X x N)).obj V
    let R := (moduleSkyscraperPresheaf Y (f x)
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V
    let eL : (L : Type u) ≃+ (terminal AddCommGrpCat.{u} : Type u) :=
      (eqToIso (if_neg hV) :
        (moduleSkyscraperUnderlying X x N).obj
            (op (f ⁻¹ᵁ V.unop)) ≅
          terminal AddCommGrpCat).addCommGroupIsoToAddEquiv
    let eR : (R : Type u) ≃+ (terminal AddCommGrpCat.{u} : Type u) :=
      (eqToIso (if_neg hV) :
        (moduleSkyscraperUnderlying Y (f x)
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V ≅
            terminal AddCommGrpCat).addCommGroupIsoToAddEquiv
    let e : (forget₂ (ModuleCat (Y.ringCatSheaf.obj.obj V)) AddCommGrpCat).obj L ≅
        (forget₂ (ModuleCat (Y.ringCatSheaf.obj.obj V)) AddCommGrpCat).obj R :=
      (eL.trans eR.symm).toAddCommGrpIso
    apply ModuleCat.isoMk e
    intro r
    ext m
    apply eR.injective
    exact Subsingleton.elim _ _

private theorem moduleSkyscraperPushforwardIsoApp_hom_apply {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y)ᵒᵖ) (hV : f x ∈ V.unop)
    (m : ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
      (moduleSkyscraperPresheaf X x N)).obj V) :
    moduleSkyscraperPositiveEquiv Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) V hV
        ((moduleSkyscraperPushforwardIsoApp f x N V).hom m) =
      moduleSkyscraperPositiveEquiv X x N
        (op (f ⁻¹ᵁ V.unop)) hV m := by
  classical
  let a := (f.app V.unop).hom
  let b := (X.presheaf.germ (f ⁻¹ᵁ V.unop) x hV).hom
  let c := (Y.presheaf.germ V.unop (f x) hV).hom
  let d := (f.stalkMap x).hom
  let ba := b.comp a
  let dc := d.comp c
  have h : ba = dc := congrArg CommRingCat.Hom.hom
    (Scheme.Hom.germ_stalkMap f V.unop x hV).symm
  let eL := moduleSkyscraperPositiveEquiv X x N
    (op (f ⁻¹ᵁ V.unop)) hV
  let eR := moduleSkyscraperPositiveEquiv Y (f x)
    ((ModuleCat.restrictScalars d).obj N) V hV
  rw [show moduleSkyscraperPushforwardIsoApp f x N V =
      moduleSkyscraperPushforwardIsoAppOfMem f x N V hV by
    simp [moduleSkyscraperPushforwardIsoApp, hV]]
  change eR
      ((moduleSkyscraperPresheafAppIso Y (f x)
          ((ModuleCat.restrictScalars d).obj N) V hV).inv
        ((ModuleCat.restrictScalarsComp' c d dc rfl).hom.app N
          ((ModuleCat.restrictScalarsCongr h).hom.app N
            ((ModuleCat.restrictScalarsComp' a b ba rfl).inv.app N
              ((ModuleCat.restrictScalars a).map
                (moduleSkyscraperPresheafAppIso X x N
                  (op (f ⁻¹ᵁ V.unop)) hV).hom m))))) = eL m
  simp [eL, eR]
  change eR (eR.symm (eL m)) = eL m
  exact eR.apply_symm_apply _

private def moduleSkyscraperPushforwardIsoObj {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (moduleSkyscraperPresheaf X x N) ≅
      moduleSkyscraperPresheaf Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) :=
  _root_.PresheafOfModules.isoMk (moduleSkyscraperPushforwardIsoApp f x N)
    (fun {V W} i ↦ by
      classical
      ext m
      by_cases hW : f x ∈ W.unop
      · have hV : f x ∈ V.unop := i.unop.le hW
        let NY :=
          (ModuleCat.restrictScalars (f.stalkMap x).hom).obj N
        let eW := moduleSkyscraperPositiveEquiv Y (f x) NY W hW
        let eV := moduleSkyscraperPositiveEquiv Y (f x) NY V hV
        let eXW := moduleSkyscraperPositiveEquiv X x N
          (op (f ⁻¹ᵁ W.unop)) hW
        let eXV := moduleSkyscraperPositiveEquiv X x N
          (op (f ⁻¹ᵁ V.unop)) hV
        apply eW.injective
        have hsource :
            eXW
                (((_root_.PresheafOfModules.pushforward
                    f.toRingCatSheafHom.hom).obj
                    (moduleSkyscraperPresheaf X x N)).map i m) =
              eXV m := by
          change eXW
              ((moduleSkyscraperUnderlying X x N).map
                ((Opens.map f.base).op.map i) m) = eXV m
          exact moduleSkyscraperPositiveEquiv_map X x N
            ((Opens.map f.base).op.map i) hW m
        have hVapp :
            eXV m =
              eV ((moduleSkyscraperPushforwardIsoApp f x N V).hom m) :=
          (moduleSkyscraperPushforwardIsoApp_hom_apply
            f x N V hV m).symm
        have htarget :
            eV ((moduleSkyscraperPushforwardIsoApp f x N V).hom m) =
              eW
                ((moduleSkyscraperPresheaf Y (f x) NY).map i
                  ((moduleSkyscraperPushforwardIsoApp f x N V).hom m)) :=
          (moduleSkyscraperPositiveEquiv_map Y (f x) NY i hW _).symm
        exact (moduleSkyscraperPushforwardIsoApp_hom_apply
          f x N W hW _).trans (hsource.trans (hVapp.trans htarget))
      · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
          terminalAddCommGrpSubsingleton
        apply (eqToIso (if_neg hW) :
          (moduleSkyscraperUnderlying Y (f x)
            ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj W ≅
              terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
        exact Subsingleton.elim _ _)

private theorem moduleSkyscraperPositiveEquiv_mapApp
    (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N)
    (U : (Opens X)ᵒᵖ) (hU : x ∈ U.unop)
    (m : (moduleSkyscraperPresheaf X x M).obj U) :
    moduleSkyscraperPositiveEquiv X x N U hU
        (moduleSkyscraperMapApp X x g U m) =
      g (moduleSkyscraperPositiveEquiv X x M U hU m) := by
  classical
  rw [show moduleSkyscraperMapApp X x g U =
      (moduleSkyscraperPresheafAppIso X x M U hU).hom ≫
        (ModuleCat.restrictScalars
          (X.presheaf.germ U.unop x hU).hom).map g ≫
        (moduleSkyscraperPresheafAppIso X x N U hU).inv by
    simp [moduleSkyscraperMapApp, hU]]
  change moduleSkyscraperPositiveEquiv X x N U hU
      ((moduleSkyscraperPresheafAppIso X x N U hU).inv
        (g ((moduleSkyscraperPresheafAppIso X x M U hU).hom m))) = _
  rw [moduleSkyscraperPresheafAppIso_hom_apply,
    moduleSkyscraperPresheafAppIso_inv_apply]
  exact (moduleSkyscraperPositiveEquiv X x N U hU).apply_symm_apply _

private def moduleSkyscraperPushforwardIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    moduleSkyscraperPresheafFunctor X x ⋙
        _root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙
        moduleSkyscraperPresheafFunctor Y (f x) :=
  NatIso.ofComponents (moduleSkyscraperPushforwardIsoObj f x)
    (fun {M N} g ↦ by
      classical
      ext V m
      by_cases hV : f x ∈ V.unop
      · let eN := moduleSkyscraperPositiveEquiv Y (f x)
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) V hV
        let eM := moduleSkyscraperPositiveEquiv Y (f x)
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) V hV
        let eXN := moduleSkyscraperPositiveEquiv X x N
          (op (f ⁻¹ᵁ V.unop)) hV
        let eXM := moduleSkyscraperPositiveEquiv X x M
          (op (f ⁻¹ᵁ V.unop)) hV
        apply eN.injective
        have hleft :
            eN
                ((moduleSkyscraperPushforwardIsoApp f x N V).hom
                  (((_root_.PresheafOfModules.pushforward
                    f.toRingCatSheafHom.hom).map
                    (moduleSkyscraperMap X x g)).app V m)) =
              g (eXM m) := by
          rw [moduleSkyscraperPushforwardIsoApp_hom_apply]
          change eXN
              (moduleSkyscraperMapApp X x g
                (op (f ⁻¹ᵁ V.unop)) m) = g (eXM m)
          exact moduleSkyscraperPositiveEquiv_mapApp X x g
            (op (f ⁻¹ᵁ V.unop)) hV m
        have hright :
            eN
                (moduleSkyscraperMapApp Y (f x)
                  ((ModuleCat.restrictScalars (f.stalkMap x).hom).map g) V
                  ((moduleSkyscraperPushforwardIsoApp f x M V).hom m)) =
              g (eXM m) := by
          rw [moduleSkyscraperPositiveEquiv_mapApp]
          exact congrArg g
            (moduleSkyscraperPushforwardIsoApp_hom_apply
              f x M V hV m)
        exact hleft.trans hright.symm
      · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
          terminalAddCommGrpSubsingleton
        apply (eqToIso (if_neg hV) :
          (moduleSkyscraperUnderlying Y (f x)
            ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V ≅
              terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
        exact Subsingleton.elim _ _)



/-- Pulling back a presheaf of modules and then taking its stalk agrees with
first taking the stalk at the image point and extending scalars along the
induced local-ring map. -/
def presheafModulePullbackStalkIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    _root_.PresheafOfModules.pullback f.toRingCatSheafHom.hom ⋙
        presheafModuleStalkFunctor X x ≅
      presheafModuleStalkFunctor Y (f x) ⋙
        ModuleCat.extendScalars (f.stalkMap x).hom :=
  Adjunction.leftAdjointCompIso
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction
      f.toRingCatSheafHom.hom)
    (presheafModuleStalkSkyscraperAdjunction X x)
    ((presheafModuleStalkSkyscraperAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
    (moduleSkyscraperPushforwardIso f x)

/-- Pulling back a sheaf of modules and then taking its stalk agrees with
first taking the stalk at the image point and extending scalars along the
induced local-ring map. -/
def pullbackStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    pullback f ⋙ moduleStalkFunctor X x ≅
      moduleStalkFunctor Y (f x) ⋙
        ModuleCat.extendScalars (f.stalkMap x).hom :=
  pullbackStalkPresheafIso f x ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (toPresheafOfModules Y)
      (presheafModulePullbackStalkIso f x) ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm

end

end AlgebraicGeometry.Scheme.Modules
