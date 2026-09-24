/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Localization
import DerivedAlgGeo.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Coherent subobjects after localization on an affine spectrum

For a finitely generated submodule of the affine global sections of a coherent sheaf,
the corresponding coherent tilde monomorphism pulls back to the subobject given by
localizing that submodule. The comparison is on `Spec (Localization.Away r)`.
The canonical `Localization.Away r`-module is Mathlib's `localizedModuleFunctor`
carrier, not definitionally the sections of the pulled-back sheaf; the natural
isomorphism below performs that transport explicitly.

This file asserts nothing about the actual basic open `D(r)`, unions of opens,
derived Hom, or Theorem 5.7(2).
-/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Coh

/-- Affine global sections of coherent pullback to the localized spectrum agree
naturally with canonical localization of the original finite module. The factors
are `affineTildePullbackIso`, the affine-equivalence counit, and
`ModuleCat.extendScalarsLocalizationNatIso`; none is treated as definitional. -/
def localizedSpectrumGlobalSectionsNatIso {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) :
    let A := Localization.Away r
    let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let FR := FGModuleCat.affineTilde (R := R)
    let F := Coh.pullback k
    let EA := Coh.affineEquivalence (R := CommRingCat.of A)
    let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
    let H := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
    (((FR ⋙ F) ⋙ EA.functor) ⋙ J) ≅ ((ModuleCat.isFG R).ι ⋙ H) := by
  let A := Localization.Away r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let FR := FGModuleCat.affineTilde (R := R)
  let F := Coh.pullback k
  let L := Coh.finiteExtendScalars (R := R) (A := A)
  let FA := FGModuleCat.affineTilde (R := CommRingCat.of A)
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let H := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let β : FR ⋙ F ≅ L ⋙ FA := Coh.affineTildePullbackIso (R := R) (A := A)
  let γ := ModuleCat.extendScalarsLocalizationNatIso (Submonoid.powers r)
  calc
    (((FR ⋙ F) ⋙ EA.functor) ⋙ J)
        ≅ (((L ⋙ FA) ⋙ EA.functor) ⋙ J) :=
      Functor.isoWhiskerRight (Functor.isoWhiskerRight β EA.functor) J
    _ ≅ ((L ⋙ (FA ⋙ EA.functor)) ⋙ J) :=
      Functor.isoWhiskerRight (Functor.associator L FA EA.functor) J
    _ ≅ ((L ⋙ 𝟭 (FGModuleCat.{u} A)) ⋙ J) :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft L EA.counitIso) J
    _ ≅ (L ⋙ J) := Functor.isoWhiskerRight (Functor.rightUnitor L) J
    _ ≅ ((ModuleCat.isFG R).ι ⋙
      ModuleCat.extendScalars (algebraMap R A)) := Iso.refl _
    _ ≅ ((ModuleCat.isFG R).ι ⋙ H) :=
      Functor.isoWhiskerLeft (ModuleCat.isFG R).ι γ

/-- Transport affine global sections of the pullback of `E` to the canonical
localization of `M`. For `M = Γ(E)`, take `cR` to be the affine-equivalence
unit. The isomorphism `cR` is retained explicitly to avoid conflating the
two module actions on global sections. -/
def localizedSpectrumGlobalSectionsIso {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M) :
    let A := Localization.Away r
    let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let F := Coh.pullback k
    let EA := Coh.affineEquivalence (R := CommRingCat.of A)
    let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
    let H : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
      ModuleCat.localizedModuleFunctor (Submonoid.powers r)
    J.obj (EA.functor.obj (F.obj E)) ≅ H.obj M.obj := by
  let A := Localization.Away r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let F := Coh.pullback k
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let H : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
    ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let κ := localizedSpectrumGlobalSectionsNatIso r
  exact (J.mapIso (EA.functor.mapIso (F.mapIso cR))) ≪≫ κ.app M

/-- The coherent tilde monomorphism associated to a finite submodule of the
module presenting `E`. In the canonical case `M = Γ(E)`, `cR` is the unit of
the affine coherent equivalence. -/
def coherentTildeSubobject {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) : Subobject E := by
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let ER := Coh.affineEquivalence (R := R)
  let FR := FGModuleCat.affineTilde (R := R)
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let f : FR.obj K ⟶ E := FR.map g ≫ cR.inv
  letI : FR.IsRightAdjoint := ER.toAdjunction.isRightAdjoint
  haveI : FR.PreservesMonomorphisms := inferInstance
  have hgm : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  haveI : Mono g := ((ModuleCat.isFG R).ι).mono_of_mono_map hgm
  haveI : Mono (FR.map g) := FR.map_mono g
  haveI : Mono f := by
    dsimp [f]
    infer_instance
  exact Subobject.mk f

/-- The subobject of the canonical localized module obtained by pulling back
the coherent tilde inclusion of a finite submodule and transporting global
sections along `localizedSpectrumGlobalSectionsNatIso`. -/
def localizedSpectrumSubobject {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (N : Submodule R M.obj) (hN : N.FG) :
    Subobject ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj) := by
  let A := Localization.Away r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let FR := FGModuleCat.affineTilde (R := R)
  let F := Coh.pullback k
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let H := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let κ := localizedSpectrumGlobalSectionsNatIso r
  let m : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ H.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g))) ≫ (κ.app M).hom
  have hm : m = (κ.app K).hom ≫ H.map ((ModuleCat.isFG R).ι.map g) := by
    exact κ.hom.naturality g
  have hg : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have hloc : Mono (H.map ((ModuleCat.isFG R).ι.map g)) := by
    letI := hg
    infer_instance
  have hκ : Mono (κ.app K).hom := inferInstance
  haveI : Mono m := by
    rw [hm]
    refine ⟨?_⟩
    intro Z f g h
    apply hκ.right_cancellation
    apply hloc.right_cancellation
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  exact Subobject.mk m

private theorem subobjectModule_mk_range {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : N ⟶ M) [Mono f] :
    ModuleCat.subobjectModule M (Subobject.mk f) = LinearMap.range f.hom := by
  unfold ModuleCat.subobjectModule
  change LinearMap.range (Subobject.mk f).arrow.hom = LinearMap.range f.hom
  have h := Subobject.underlyingIso_arrow f
  conv_rhs => rw [← h]
  change LinearMap.range (Subobject.mk f).arrow.hom =
    LinearMap.range ((Subobject.mk f).arrow.hom.comp
      (Subobject.underlyingIso f).inv.hom)
  exact (LinearEquiv.range_comp (Subobject.underlyingIso f).symm.toLinearEquiv
    (Subobject.mk f).arrow.hom).symm

private theorem localizedSubtype_range {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (N : Submodule R M) (r : R) :
    let S := Submonoid.powers r
    let g : ModuleCat.of R N ⟶ M := ModuleCat.ofHom N.subtype
    LinearMap.range ((ModuleCat.localizedModuleFunctor S).map g).hom =
      N.localized' (Localization.Away r) S (M.localizedModuleMkLinearMap S) := by
  let S := Submonoid.powers r
  let g : ModuleCat.of R N ⟶ M := ModuleCat.ofHom N.subtype
  letI : IsLocalizedModule S ((ModuleCat.of R N).localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R N) S
  letI : IsLocalizedModule S (M.localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule M S
  have heq :
      (IsLocalizedModule.mapExtendScalars S
        ((ModuleCat.of R N).localizedModuleMkLinearMap S)
        (M.localizedModuleMkLinearMap S)
        (Localization.Away r) N.subtype) =
      ((IsLocalizedModule.map S
        ((ModuleCat.of R N).localizedModuleMkLinearMap S)
        (M.localizedModuleMkLinearMap S) N.subtype).extendScalarsOfIsLocalization S
          (Localization.Away r)) := by
    ext x
    rfl
  change LinearMap.range
      ((IsLocalizedModule.mapExtendScalars S
        ((ModuleCat.of R N).localizedModuleMkLinearMap S)
        (M.localizedModuleMkLinearMap S)
        (Localization.Away r) N.subtype)) =
    N.localized' (Localization.Away r) S (M.localizedModuleMkLinearMap S)
  rw [heq]
  have h := (LinearMap.localized'_range_eq_range_localizedMap
    (Localization.Away r) S
    ((ModuleCat.of R N).localizedModuleMkLinearMap S)
    (M.localizedModuleMkLinearMap S) N.subtype)
  simpa only [Submodule.range_subtype] using h.symm

/-- The transported pullback of the coherent tilde subobject has precisely the
localized finite submodule as its underlying submodule. The target module is
the canonical localized-module carrier, with transport through `κ` explicit
in `localizedSpectrumSubobject`. -/
theorem localizedSpectrumSubobject_subobjectModule {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (N : Submodule R M.obj) (hN : N.FG) :
    ModuleCat.subobjectModule
        ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
        (localizedSpectrumSubobject r M N hN) =
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  let A := Localization.Away r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let FR := FGModuleCat.affineTilde (R := R)
  let F := Coh.pullback k
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let H := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let κ := localizedSpectrumGlobalSectionsNatIso r
  let m : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ H.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g))) ≫ (κ.app M).hom
  have hm : m = (κ.app K).hom ≫ H.map ((ModuleCat.isFG R).ι.map g) := by
    exact κ.hom.naturality g
  have hg : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have hloc : Mono (H.map ((ModuleCat.isFG R).ι.map g)) := by
    letI := hg
    infer_instance
  have hκ : Mono (κ.app K).hom := inferInstance
  haveI : Mono m := by
    rw [hm]
    refine ⟨?_⟩
    intro Z f g h
    apply hκ.right_cancellation
    apply hloc.right_cancellation
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  change ModuleCat.subobjectModule (H.obj M.obj) (Subobject.mk m) = _
  rw [subobjectModule_mk_range m, hm]
  change LinearMap.range
      ((H.map ((ModuleCat.isFG R).ι.map g)).hom.comp (κ.app K).hom.hom) = _
  calc
    LinearMap.range
        ((H.map ((ModuleCat.isFG R).ι.map g)).hom.comp (κ.app K).hom.hom) =
        LinearMap.range (H.map ((ModuleCat.isFG R).ι.map g)).hom := by
      apply Submodule.ext
      intro x
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨(κ.app K).hom.hom y, hy⟩
      · rintro ⟨y, hy⟩
        obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (κ.app K).hom).2 y
        exact ⟨z, hy⟩
    _ = _ := localizedSubtype_range M.obj N r

/-- Pull back the coherent tilde inclusion into `E`, take affine global
sections, and transport its target along the explicit localized-spectrum
comparison. This is a subobject of the canonical localized module, not an
identification of the two carrier types. -/
def localizedSpectrumCoherentSubobject {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    Subobject ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj) := by
  let A := Localization.Away r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let FR := FGModuleCat.affineTilde (R := R)
  let F := Coh.pullback k
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let H : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
    ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let κ := localizedSpectrumGlobalSectionsNatIso r
  let κE := localizedSpectrumGlobalSectionsIso r M E cR
  let mE : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ H.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g ≫ cR.inv))) ≫ κE.hom
  let mM : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ H.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g))) ≫ (κ.app M).hom
  have heq : mE = mM := by
    change J.map (EA.functor.map (F.map (FR.map g ≫ cR.inv))) ≫
      (J.map (EA.functor.map (F.map cR.hom)) ≫ (κ.app M).hom) =
      J.map (EA.functor.map (F.map (FR.map g))) ≫ (κ.app M).hom
    rw [← Category.assoc, ← J.map_comp, ← EA.functor.map_comp, ← F.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm : mE = (κ.app K).hom ≫ H.map ((ModuleCat.isFG R).ι.map g) := by
    rw [heq]
    exact κ.hom.naturality g
  have hg : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have hloc : Mono (H.map ((ModuleCat.isFG R).ι.map g)) := by
    letI := hg
    infer_instance
  have hκ : Mono (κ.app K).hom := inferInstance
  haveI : Mono mE := by
    rw [hm]
    refine ⟨?_⟩
    intro Z f g h
    apply hκ.right_cancellation
    apply hloc.right_cancellation
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  exact Subobject.mk mE

/-- On the localized spectrum, the subobject obtained from the coherent
inclusion into `E` is exactly `N.localized'` after transporting the target
along `localizedSpectrumGlobalSectionsIso`. This is not a statement on the
actual basic open `D(r)`. -/
theorem localizedSpectrumCoherentSubobject_subobjectModule {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    ModuleCat.subobjectModule
        ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
        (localizedSpectrumCoherentSubobject r M E cR N hN) =
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  let A := Localization.Away r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let FR := FGModuleCat.affineTilde (R := R)
  let F := Coh.pullback k
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let H : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
    ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let κ := localizedSpectrumGlobalSectionsNatIso r
  let κE := localizedSpectrumGlobalSectionsIso r M E cR
  let mE : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ H.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g ≫ cR.inv))) ≫ κE.hom
  let mM : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ H.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g))) ≫ (κ.app M).hom
  have heq : mE = mM := by
    change J.map (EA.functor.map (F.map (FR.map g ≫ cR.inv))) ≫
      (J.map (EA.functor.map (F.map cR.hom)) ≫ (κ.app M).hom) =
      J.map (EA.functor.map (F.map (FR.map g))) ≫ (κ.app M).hom
    rw [← Category.assoc, ← J.map_comp, ← EA.functor.map_comp, ← F.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm : mM = (κ.app K).hom ≫ H.map ((ModuleCat.isFG R).ι.map g) := by
    exact κ.hom.naturality g
  have hg : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have hloc : Mono (H.map ((ModuleCat.isFG R).ι.map g)) := by
    letI := hg
    infer_instance
  have hκ : Mono (κ.app K).hom := inferInstance
  haveI : Mono mM := by
    rw [hm]
    refine ⟨?_⟩
    intro Z f g h
    apply hκ.right_cancellation
    apply hloc.right_cancellation
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  haveI : Mono mE := heq ▸ inferInstance
  have hobj : localizedSpectrumCoherentSubobject r M E cR N hN =
      localizedSpectrumSubobject r M N hN := by
    change Subobject.mk mE = Subobject.mk mM
    exact Subobject.mk_eq_mk_of_comm
      (C := ModuleCat.{u} (Localization (Submonoid.powers r)))
      mE mM (Iso.refl _) (by simpa using heq.symm)
  rw [hobj]
  exact localizedSpectrumSubobject_subobjectModule r M N hN

/-- Canonical `M = Γ(E)` specialization of the localized-spectrum coherent
subobject comparison. The affine-equivalence unit supplies `cR`; no equality
of the two global-sections module actions is assumed. -/
theorem localizedSpectrumCoherentSubobject_globalSections {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (E : Coh (Spec R)) :
    let M : FGModuleCat.{u} R := (Coh.affineEquivalence (R := R)).functor.obj E
    ∀ (N : Submodule R M.obj) (hN : N.FG),
      ModuleCat.subobjectModule
          ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
          (localizedSpectrumCoherentSubobject r M E
            ((Coh.affineEquivalence (R := R)).unitIso.app E) N hN) =
        N.localized' (Localization.Away r) (Submonoid.powers r)
          (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  intro M N hN
  exact localizedSpectrumCoherentSubobject_subobjectModule r M E
    ((Coh.affineEquivalence (R := R)).unitIso.app E) N hN

end AlgebraicGeometry.Coh
