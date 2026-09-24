/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Generator
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-!
# Stalkwise-flat generators for scheme module sheaves

The free-Yoneda module sheaf attached to an open `U` has stalk zero away from `U`. The
inside-support stalk calculation identifies the module stalk with the local ring; together
these results prove stalkwise flatness. The generic natural element-indexed epimorphism is
specialized to `X.Modules` below without introducing another generator construction.

These are flat generators, not projective objects or K-flat resolutions.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private noncomputable def neighborhoodUnitToRegularStalk
    (X : Scheme.{u}) (x : X) :
    PresheafOfModules.unit
      ((OpenNhds.inclusion x).op ⋙ X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (PresheafOfModules.constFunctor (moduleStalkRingCocone X x)).obj
        (ModuleCat.of (moduleStalkRingCocone X x).pt
          (moduleStalkRingCocone X x).pt) := by
  let cR := moduleStalkRingCocone X x
  refine PresheafOfModules.homMk ?_ ?_
  · refine ⟨fun V => (forget₂ RingCat AddCommGrpCat).map (cR.ι.app V), ?_⟩
    intro V W f
    ext r
    exact ConcreteCategory.congr_hom (cR.w f) r
  · intro V r m
    let S := (((OpenNhds.inclusion x).op ⋙ X.presheaf ⋙
      forget₂ CommRingCat RingCat).obj V)
    let f := (cR.ι.app V).hom
    letI : Module S (moduleStalkRingCocone X x).pt := f.toModule
    let e : S →ₗ[S] (moduleStalkRingCocone X x).pt := {
      toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a b
        change f (a * b) = f a * f b
        exact f.map_mul a b
    }
    change e (r • m) = r • e m
    exact e.map_smul r m

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleStalkUnitIsoRegular
    (X : Scheme.{u}) (x : X) :
    (moduleStalkFunctor X x).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  let R := (OpenNhds.inclusion x).op ⋙ X.presheaf ⋙ forget₂ CommRingCat RingCat
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  let cR := moduleStalkRingCocone X x
  let hcR := moduleStalkRingIsColimit X x
  let M := PresheafOfModules.unit R
  let cM := colimit.cocone M.presheaf
  let hcM := colimit.isColimit M.presheaf
  let A : Type u := ↑cR.pt
  letI : Ring A := inferInstanceAs (Ring (↑cR.pt))
  let α := neighborhoodUnitToRegularStalk X x
  let φ := (PresheafOfModules.ModuleColimit.homEquiv hcR hcM).symm α
  let Utop : OpenNhds x := ⊤
  let η : PresheafOfModules.ModuleColimit hcR hcM :=
    PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM)
      (1 : R.obj (op Utop))
  have hφ (V : (OpenNhds x)ᵒᵖ) (s : M.obj V) :
      φ (PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM) s) =
        (cR.ι.app V).hom s := by
    change (ConcreteCategory.hom
        ((PresheafOfModules.ModuleColimit.homEquiv hcR hcM).symm α))
      ((ConcreteCategory.hom (cM.ι.app V)) s) =
        (ConcreteCategory.hom (α.app V)) s
    exact PresheafOfModules.ModuleColimit.homEquiv_symm_apply hcR hcM α s
  have hη (V : OpenNhds x) :
      η = PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM)
        (1 : R.obj (op V)) := by
    let f : op Utop ⟶ op V := (homOfLE (show V ≤ Utop from le_top)).op
    have hw := ConcreteCategory.congr_hom (cM.w f) (1 : R.obj (op Utop))
    change (ConcreteCategory.hom (cM.ι.app (op V)))
          ((PresheafOfModules.unit R).map f (1 : R.obj (op Utop))) =
        (ConcreteCategory.hom (cM.ι.app (op Utop))) (1 : R.obj (op Utop)) at hw
    rw [PresheafOfModules.unit_map_one (R := R) f] at hw
    change (ConcreteCategory.hom (cM.ι.app (op Utop))) (1 : R.obj (op Utop)) =
      (ConcreteCategory.hom (cM.ι.app (op V))) (1 : R.obj (op V))
    exact hw.symm
  let ψ : A →ₗ[A] PresheafOfModules.ModuleColimit hcR hcM := {
    toFun a := a • η
    map_add' a b := by simp [add_smul]
    map_smul' a b := by simp [mul_smul]
  }
  let e : PresheafOfModules.ModuleColimit hcR hcM ≃ₗ[A] A := {
    toFun := φ.hom
    invFun := ψ
    left_inv := by
      intro m
      obtain ⟨V, s, rfl⟩ :=
        PresheafOfModules.ModuleColimit.ιM_jointly_surjective (hcR := hcR) (hcM := hcM) m
      change φ (PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM) s) • η =
        PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM) s
      rw [hφ V s, hη V.unop]
      change PresheafOfModules.ModuleColimit.ιR cR s •
          PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM)
            (1 : R.obj V) =
        PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM) s
      change ↑(ModuleCat.of (R.obj V) (R.obj V)) at s
      change PresheafOfModules.ModuleColimit.ιR cR s •
          PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM)
            (1 : ↑(ModuleCat.of (R.obj V) (R.obj V))) =
        PresheafOfModules.ModuleColimit.ιM (hcR := hcR) (hcM := hcM) s
      rw [PresheafOfModules.ModuleColimit.smul_eq
        (hcR := hcR) (hcM := hcM) (r := s)
        (m := (1 : ↑(ModuleCat.of (R.obj V) (R.obj V)) ))]
      have hreg : s • (1 : ↑(ModuleCat.of (R.obj V) (R.obj V))) = s := by
        change s * 1 = s
        exact mul_one s
      exact congrArg (PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR) (hcM := hcM)) hreg
    right_inv := by
      intro a
      change φ.hom (a • η) = a
      have hφη : φ.hom η = 1 := by
        change φ (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcR) (hcM := hcM) (1 : R.obj (op Utop))) = 1
        calc
          φ (PresheafOfModules.ModuleColimit.ιM
              (hcR := hcR) (hcM := hcM) (1 : R.obj (op Utop))) =
              (cR.ι.app (op Utop)).hom 1 := hφ (op Utop) _
          _ = 1 := map_one (cR.ι.app (op Utop)).hom
      calc
        φ.hom (a • η) = a • φ.hom η := φ.hom.map_smul a η
        _ = a := by rw [hφη]; exact mul_one a
    map_add' := map_add φ.hom
    map_smul' := fun a b => φ.hom.map_smul a b
  }
  exact e.toModuleIso

/-- The canonical free-Yoneda `𝒪_X`-module sheaf associated to an open subset. -/
noncomputable abbrev freeYonedaModuleSheaf (X : Scheme.{u}) (U : X.Opens) : X.Modules :=
  SheafOfModules.freeYonedaSheaf X.ringCatSheaf U

private noncomputable def moduleUnitOne (S : Type u) [Ring S] :
    ↑(ModuleCat.of S S) :=
  (ModuleCat.coe_of S S).symm ▸ (1 : S)

private noncomputable def freeYonedaUnitMap
    (X : Scheme.{u}) (U : X.Opens) :
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U) ⟶
      PresheafOfModules.unit X.ringCatSheaf.obj :=
  PresheafOfModules.freeYonedaEquiv.symm
    (moduleUnitOne (X.ringCatSheaf.obj.obj (op U)))

private lemma freeMapYonedaMapEval {C : Type u} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {V U : C} (i : V ⟶ U) :
    _root_.PresheafOfModules.freeYonedaEquiv
      ((_root_.PresheafOfModules.free R).map (yoneda.map i)) = ModuleCat.freeMk i := by
  change ((ModuleCat.free (R.obj (op V))).map ((yoneda.map i).app (op V)))
    (ModuleCat.freeMk (𝟙 V)) = ModuleCat.freeMk i
  rw [ModuleCat.free_map_apply]
  congr 1
  simp

private lemma freeYonedaEquivFreeMapComp {C : Type u} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {V U : C} (i : V ⟶ U)
    (N : _root_.PresheafOfModules R)
    (f : (_root_.PresheafOfModules.free R).obj (yoneda.obj U) ⟶ N) :
    _root_.PresheafOfModules.freeYonedaEquiv
      ((_root_.PresheafOfModules.free R).map (yoneda.map i) ≫ f) =
      N.map i.op (_root_.PresheafOfModules.freeYonedaEquiv f) := by
  have h1 : _root_.PresheafOfModules.freeHomEquiv
      ((_root_.PresheafOfModules.free R).map (yoneda.map i) ≫ f) =
      yoneda.map i ≫ _root_.PresheafOfModules.freeHomEquiv f := by
    rw [← _root_.PresheafOfModules.freeAdjunction_homEquiv,
      ← _root_.PresheafOfModules.freeAdjunction_homEquiv]
    exact Adjunction.homEquiv_naturality_left _ _ _
  change yonedaEquiv
      (_root_.PresheafOfModules.freeHomEquiv
        ((_root_.PresheafOfModules.free R).map (yoneda.map i) ≫ f)) = _
  rw [h1]
  exact (yonedaEquiv_naturality _ _).symm

private lemma freeYonedaUnitMap_app_freeMk
    (X : Scheme.{u}) (U W : X.Opens) (f : W ⟶ U) :
    (freeYonedaUnitMap X U).app (op W) (ModuleCat.freeMk f) =
      moduleUnitOne (X.ringCatSheaf.obj.obj (op W)) := by
  have h := freeYonedaEquivFreeMapComp f
    (PresheafOfModules.unit X.ringCatSheaf.obj) (freeYonedaUnitMap X U)
  rw [_root_.PresheafOfModules.freeYonedaEquiv_comp,
    freeMapYonedaMapEval] at h
  have hs : _root_.PresheafOfModules.freeYonedaEquiv (freeYonedaUnitMap X U) =
      moduleUnitOne (X.ringCatSheaf.obj.obj (op U)) := by
    simp [freeYonedaUnitMap]
  rw [hs] at h
  have hu : (PresheafOfModules.unit X.ringCatSheaf.obj).map f.op
      (moduleUnitOne (X.ringCatSheaf.obj.obj (op U))) =
      moduleUnitOne (X.ringCatSheaf.obj.obj (op W)) := by
    simp [moduleUnitOne, _root_.PresheafOfModules.unit_map_one]
  exact h.trans hu

private noncomputable def freePUnitRegularIso (S : Type u) [Ring S] :
    ModuleCat.of S S ≅ (ModuleCat.free S).obj PUnit.{u + 1} := by
  refine ⟨ModuleCat.ofHom (Finsupp.lsingle PUnit.unit),
    ModuleCat.ofHom (Finsupp.lapply PUnit.unit), ?_, ?_⟩
  · ext
    simp [ModuleCat.free]
  · ext a
    cases a
    dsimp [ModuleCat.freeMk]
    erw [Finsupp.lapply_apply, Finsupp.lsingle_apply]
    rw [Finsupp.single_eq_same]

private noncomputable def freeUniqueRegularIso (S : Type u) [Ring S]
    (T : Type u) [Unique T] :
    (ModuleCat.free S).obj T ≅ ModuleCat.of S S := by
  let e : T ≃ PUnit.{u + 1} := {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => default
    left_inv := by intro t; exact Subsingleton.elim _ _
    right_inv := by intro z; cases z; rfl
  }
  exact (Functor.mapIso (ModuleCat.free S) (Equiv.toIso e)) ≪≫
    (freePUnitRegularIso S).symm

private theorem freeUniqueRegularIso_hom_freeMk (S : Type u) [Ring S]
    (T : Type u) [Unique T] (t : T) :
    (freeUniqueRegularIso S T).hom (ModuleCat.freeMk t) = 1 := by
  have ht : t = default := Subsingleton.elim _ _
  subst t
  simp [freeUniqueRegularIso, freePUnitRegularIso, ModuleCat.free_map_apply]
  change (Finsupp.lapply PUnit.unit) (Finsupp.single PUnit.unit 1) = 1
  rw [Finsupp.lapply_apply, Finsupp.single_eq_same]

private lemma freeYonedaUnitMap_app_isIso_of_le
    (X : Scheme.{u}) (U W : X.Opens) (hWU : W ≤ U) :
    IsIso ((freeYonedaUnitMap X U).app (op W)) := by
  let T := (yoneda.obj U).obj (op W)
  letI : Unique T := {
    default := ⟨⟨hWU⟩⟩
    uniq := by
      intro a
      cases a with
      | up a =>
        cases a with
        | up _ => rfl
  }
  let e := freeUniqueRegularIso (X.ringCatSheaf.obj.obj (op W)) T
  have hmap : (freeYonedaUnitMap X U).app (op W) = e.hom := by
    apply ModuleCat.free_hom_ext
    intro t
    have ht : t = homOfLE hWU := Subsingleton.elim _ _
    subst t
    calc
      (freeYonedaUnitMap X U).app (op W) (ModuleCat.freeMk (homOfLE hWU)) =
          moduleUnitOne (X.ringCatSheaf.obj.obj (op W)) :=
        freeYonedaUnitMap_app_freeMk X U W (homOfLE hWU)
      _ = 1 := by simp [moduleUnitOne]
      _ = e.hom (ModuleCat.freeMk (homOfLE hWU)) :=
        (freeUniqueRegularIso_hom_freeMk _ _ _).symm
  rw [hmap]
  infer_instance

private lemma freeYonedaUnitMap_app_injective
    (X : Scheme.{u}) (U W : X.Opens) :
    Function.Injective ((freeYonedaUnitMap X U).app (op W)) := by
  by_cases hWU : W ≤ U
  · haveI : IsIso ((freeYonedaUnitMap X U).app (op W)) :=
      freeYonedaUnitMap_app_isIso_of_le X U W hWU
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · letI : IsEmpty ((yoneda.obj U).obj (op W)) :=
      ⟨fun f => hWU f.down.down⟩
    intro a b _
    change ((yoneda.obj U).obj (op W) →₀ X.ringCatSheaf.obj.obj (op W)) at a
    change ((yoneda.obj U).obj (op W) →₀ X.ringCatSheaf.obj.obj (op W)) at b
    have hsub : Subsingleton
        ((yoneda.obj U).obj (op W) →₀ X.ringCatSheaf.obj.obj (op W)) := by
      refine ⟨?_⟩
      intro s t
      ext i
      exact (hWU i.down.down).elim
    exact hsub.elim a b

private lemma moduleStalk_map_isIso_of_app_inj_surj
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (M N : _root_.PresheafOfModules X.ringCatSheaf.obj) (f : M ⟶ N)
    (hinj : ∀ W : X.Opens, Function.Injective
      (((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f).app (op W)))
    (hsurj : ∀ W : X.Opens, W ≤ U → Function.Surjective
      (((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f).app (op W))) :
    IsIso ((presheafModuleStalkFunctor X x).map f) := by
  rw [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})]
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f))
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (f := (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) hinj x
  · intro t
    let FN : TopCat.Presheaf AddCommGrpCat.{u} X :=
      (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj N
    obtain ⟨W, hWU, hxW, s, hs⟩ :=
      TopCat.Presheaf.exists_le_germ_eq FN t hxU
    obtain ⟨r, hr⟩ := hsurj W hWU s
    refine ⟨TopCat.Presheaf.germ
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj M) W x hxW r, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hr]
    exact hs

private lemma moduleStalk_map_isIso_of_local_apps
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (M N : _root_.PresheafOfModules X.ringCatSheaf.obj) (f : M ⟶ N)
    (hinj : ∀ W : X.Opens, Function.Injective (f.app (op W)))
    (happ : ∀ W : X.Opens, W ≤ U → IsIso (f.app (op W))) :
    IsIso ((presheafModuleStalkFunctor X x).map f) := by
  apply moduleStalk_map_isIso_of_app_inj_surj X x U hxU M N f
  · intro W
    change Function.Injective (f.app (op W))
    exact hinj W
  · intro W hWU
    have hi := happ W hWU
    haveI : IsIso (f.app (op W)) := hi
    have hb : Function.Bijective (f.app (op W)) := by
      rw [← ConcreteCategory.isIso_iff_bijective]
      infer_instance
    change Function.Surjective (f.app (op W))
    exact hb.2

private lemma freeYonedaUnitMap_stalk_isIso
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    IsIso ((presheafModuleStalkFunctor X x).map (freeYonedaUnitMap X U)) := by
  apply moduleStalk_map_isIso_of_local_apps X x U hxU
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))
    (PresheafOfModules.unit X.ringCatSheaf.obj) (freeYonedaUnitMap X U)
  · exact fun W => freeYonedaUnitMap_app_injective X U W
  · exact fun W hWU => freeYonedaUnitMap_app_isIso_of_le X U W hWU

private noncomputable def freeYonedaUnitSheafMap
    (X : Scheme.{u}) (U : X.Opens) :
    freeYonedaModuleSheaf X U ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (freeYonedaUnitMap X U) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
      (SheafOfModules.unit X.ringCatSheaf)

private lemma freeYonedaUnitSheafMap_stalk_isIso
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    IsIso ((moduleStalkFunctor X x).map (freeYonedaUnitSheafMap X U)) := by
  let σ := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let P : X.PresheafOfModules :=
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)
  let Q : X.PresheafOfModules := PresheafOfModules.unit X.ringCatSheaf.obj
  let η := presheafModuleStalkSheafificationIso X x
  let α := freeYonedaUnitMap X U
  have hnat := η.hom.naturality α
  change (presheafModuleStalkFunctor X x).map α ≫ (η.app Q).hom =
      (η.app P).hom ≫ (moduleStalkFunctor X x).map (σ.map α) at hnat
  haveI : IsIso ((presheafModuleStalkFunctor X x).map α) :=
    freeYonedaUnitMap_stalk_isIso X U x hxU
  haveI : IsIso ((η.app P).hom) := inferInstance
  haveI : IsIso ((η.app Q).hom) := inferInstance
  have hsheaf : IsIso ((moduleStalkFunctor X x).map (σ.map α)) := by
    have hcomp : IsIso ((presheafModuleStalkFunctor X x).map α ≫ (η.app Q).hom) :=
      IsIso.comp_isIso'
        (show IsIso ((presheafModuleStalkFunctor X x).map α) from inferInstance)
        (show IsIso (η.app Q).hom from inferInstance)
    have hcomp' : IsIso ((η.app P).hom ≫ (moduleStalkFunctor X x).map (σ.map α)) := by
      rw [← hnat]
      exact hcomp
    exact (isIso_comp_left_iff ((η.app P).hom)
      ((moduleStalkFunctor X x).map (σ.map α))).mp hcomp'
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  haveI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  haveI : IsIso (adj.counit.app (SheafOfModules.unit X.ringCatSheaf)) :=
    NatIso.isIso_app_of_isIso adj.counit _
  have hε : IsIso ((moduleStalkFunctor X x).map
      (adj.counit.app (SheafOfModules.unit X.ringCatSheaf))) := by
    let ε : _ ≅ _ := @asIso _ _ _ _
      (adj.counit.app (SheafOfModules.unit X.ringCatSheaf))
      (NatIso.isIso_app_of_isIso adj.counit _)
    exact ((moduleStalkFunctor X x).mapIso ε).isIso_hom
  haveI : IsIso ((moduleStalkFunctor X x).map (σ.map α)) := hsheaf
  haveI : IsIso ((moduleStalkFunctor X x).map
      (adj.counit.app (SheafOfModules.unit X.ringCatSheaf))) := hε
  dsimp [freeYonedaUnitSheafMap]
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' hsheaf hε

/-- On an open containing `x`, the stalk of the free-Yoneda module sheaf is the
regular module over the local ring. -/
noncomputable def freeYonedaModuleSheaf_stalkIsoRegular_of_mem
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U) :
    (moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  have h := freeYonedaUnitSheafMap_stalk_isIso X U x hx
  exact asIso ((moduleStalkFunctor X x).map (freeYonedaUnitSheafMap X U)) ≪≫
    moduleStalkUnitIsoRegular X x

/-- On an open containing `x`, the free-Yoneda module sheaf is flat at the stalk. -/
theorem freeYonedaModuleSheaf_stalk_flat_of_mem
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U) :
    Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) := by
  let e := freeYonedaModuleSheaf_stalkIsoRegular_of_mem X U x hx
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

private lemma freeModuleYonedaPresheaf_stalk_isZero_of_not_mem
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∉ U) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
        ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)))) := by
  let F : TopCat.Presheaf AddCommGrpCat.{u} X :=
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))
  change IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F)
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  constructor
  intro s t
  obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F s
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F t
  have hWU : ¬ W ≤ U := fun h ↦ hx (h hxW)
  have hVU : ¬ V ≤ U := fun h ↦ hx (h hxV)
  letI : IsEmpty ((yoneda.obj U).obj (op W)) := ⟨fun f ↦ hWU f.down.down⟩
  letI : IsEmpty ((yoneda.obj U).obj (op V)) := ⟨fun f ↦ hVU f.down.down⟩
  change ((yoneda.obj U).obj (op W) →₀ X.ringCatSheaf.obj.obj (op W)) at s
  change ((yoneda.obj U).obj (op V) →₀ X.ringCatSheaf.obj.obj (op V)) at t
  haveI : Subsingleton ((yoneda.obj U).obj (op W) →₀ X.ringCatSheaf.obj.obj (op W)) := inferInstance
  haveI : Subsingleton ((yoneda.obj U).obj (op V) →₀ X.ringCatSheaf.obj.obj (op V)) := inferInstance
  rw [Subsingleton.elim s 0, Subsingleton.elim t 0]
  exact (map_zero _).trans (map_zero _).symm

private lemma freeYonedaModulePresheafModuleStalk_zero
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∉ U) :
    IsZero ((presheafModuleStalkFunctor X x).obj
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))) := by
  have hAb := freeModuleYonedaPresheaf_stalk_isZero_of_not_mem X U x hx
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))))
  exact AddCommGrpCat.subsingleton_of_isZero hAb

/-- The stalk at `x` of the free-Yoneda sheaf on an open not containing `x` is zero. -/
theorem freeYonedaModuleSheaf_stalk_isZero_of_not_mem
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∉ U) :
    IsZero ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) := by
  let P : X.PresheafOfModules :=
    (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)
  have hP := freeYonedaModulePresheafModuleStalk_zero X U x hx
  let E := (presheafModuleStalkSheafificationIso X x).app P
  exact IsZero.of_iso hP E.symm

/-- Away from its representing open, the free-Yoneda module sheaf is flat at the stalk. -/
theorem freeYonedaModuleSheaf_stalk_flat_of_not_mem
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∉ U) :
    Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) := by
  have hzero := freeYonedaModuleSheaf_stalk_isZero_of_not_mem X U x hx
  letI : Subsingleton ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Module.Free (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) :=
    Module.Free.of_subsingleton _ _
  infer_instance

/-- Every stalk of a free-Yoneda module sheaf on an open is flat over the local ring. -/
theorem freeYonedaModuleSheaf_stalk_flat
    (X : Scheme.{u}) (U : X.Opens) (x : X) :
    Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) := by
  by_cases hx : x ∈ U
  · exact freeYonedaModuleSheaf_stalk_flat_of_mem X U x hx
  · exact freeYonedaModuleSheaf_stalk_flat_of_not_mem X U x hx

/-- The canonical free-Yoneda module sheaf on an open is flat over the identity map. -/
theorem freeYonedaModuleSheaf_isFlatOver_id
    (X : Scheme.{u}) (U : X.Opens) :
    AlgebraicGeometry.Scheme.Modules.IsFlatOver (𝟙 X)
      (freeYonedaModuleSheaf X U) := by
  intro x
  dsimp [AlgebraicGeometry.Scheme.Modules.IsFlatOver]
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_id]
  change Module.Flat (X.presheaf.stalk x)
    ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)))
  haveI : Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U)) :=
    freeYonedaModuleSheaf_stalk_flat X U x
  exact Module.Flat.of_linearEquiv
    (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
      ((moduleStalkFunctor X x).obj (freeYonedaModuleSheaf X U))).toLinearEquiv

/-- The generic element-indexed coproduct, specialized to `X.Modules`.

Its indexing type is `M.val.Elements : Type u`; the coproduct is the one defined at the
small-ringed-site owner, not a second geometric presentation. -/
noncomputable abbrev freeYonedaSheafCoproduct (X : Scheme.{u}) (M : X.Modules) : X.Modules :=
  (show SheafOfModules X.ringCatSheaf from M).freeYonedaSheafCoproduct X.ringCatSheaf

/-- The generic epimorphism from the element-indexed free-Yoneda coproduct, specialized to
`X.Modules`. -/
noncomputable abbrev fromFreeYonedaSheafCoproduct (X : Scheme.{u}) (M : X.Modules) :
    freeYonedaSheafCoproduct X M ⟶ M :=
  (show SheafOfModules X.ringCatSheaf from M).fromFreeYonedaSheafCoproduct X.ringCatSheaf

/-- The map on specialized coproducts induced by a morphism, inherited from the generic root. -/
noncomputable def freeYonedaSheafCoproductMap (X : Scheme.{u}) {M N : X.Modules}
    (f : M ⟶ N) : freeYonedaSheafCoproduct X M ⟶ freeYonedaSheafCoproduct X N :=
  (show SheafOfModules X.ringCatSheaf from M).freeYonedaSheafCoproductMap X.ringCatSheaf
    (show (show SheafOfModules X.ringCatSheaf from M) ⟶
      (show SheafOfModules X.ringCatSheaf from N) from f)

/-- The element-indexed free-Yoneda coproduct epimorphism in `X.Modules`. -/
theorem fromFreeYonedaSheafCoproduct_epi (X : Scheme.{u}) (M : X.Modules) :
    Epi (fromFreeYonedaSheafCoproduct X M) := by
  refine ⟨?_⟩
  intro N f g hfg
  let M' : SheafOfModules X.ringCatSheaf := M
  let e : M'.freeYonedaSheafCoproduct X.ringCatSheaf ⟶ M' :=
    M'.fromFreeYonedaSheafCoproduct X.ringCatSheaf
  have he : Epi (C := SheafOfModules.{u} X.ringCatSheaf) e :=
    SheafOfModules.fromFreeYonedaSheafCoproduct_epi X.ringCatSheaf M'
  have hfg' : e ≫ f = e ≫ g := hfg
  exact (cancel_epi (C := SheafOfModules.{u} X.ringCatSheaf) e).mp hfg'

/-- Every element-indexed summand of the canonical presentation has flat stalks. -/
theorem freeYonedaSheafCoproduct_summand_stalk_flat
    (X : Scheme.{u}) (M : X.Modules) (m : M.val.Elements) (x : X) :
    Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj
        (SheafOfModules.Elements.freeYonedaSheaf
          (R := X.ringCatSheaf) (M := M) m)) := by
  exact freeYonedaModuleSheaf_stalk_flat X m.1.unop x

/-- Naturality of the specialized coproduct map follows from the generic naturality theorem. -/
lemma fromFreeYonedaSheafCoproduct_natural (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) :
    freeYonedaSheafCoproductMap X f ≫ fromFreeYonedaSheafCoproduct X N =
      fromFreeYonedaSheafCoproduct X M ≫ f := by
  exact SheafOfModules.fromFreeYonedaSheafCoproduct_natural X.ringCatSheaf f

end

end AlgebraicGeometry.Scheme.Modules
