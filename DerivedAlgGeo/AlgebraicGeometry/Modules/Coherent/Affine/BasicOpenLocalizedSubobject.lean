/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpen
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.LocalizedSubobject

/-!
# Coherent subobjects on an affine basic open

The coherent tilde subobject associated to a finite submodule is pulled back along
the *actual* immersion `D(r) ↪ Spec R`. Its affine global sections, transported
across `basicOpenIsoSpecAway r`, agree with the canonical localized submodule.
This is a one-chart, underived statement; it does not glue subobjects over a
union of opens.
-/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Coh

private def basicOpenToLocalizedSpectrumIso {R : CommRingCat.{u}} (r : R) :
    let e := basicOpenIsoSpecAway r
    let β := pullbackEquivalence e
    let k := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
    let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
    let F := pullback k
    let G := pullback j
    G ⋙ β.inverse ≅ F := by
  let e := basicOpenIsoSpecAway r
  let β := pullbackEquivalence e
  let k := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
  let F := pullback k
  let G := pullback j
  let α : G ≅ F ⋙ β.functor := pullbackBasicOpenIsoSpecAway r
  exact (Functor.isoWhiskerRight α β.inverse) ≪≫
    (Functor.associator F β.functor β.inverse) ≪≫
    (Functor.isoWhiskerLeft F β.unitIso.symm) ≪≫
    (Functor.rightUnitor F)

/-- Transport global sections of the pullback of `E` on the actual basic open
to Mathlib's canonical localization of its chosen finite-module presentation.
The comparison factors through `basicOpenIsoSpecAway r`; it is not definitional. -/
def basicOpenGlobalSectionsIso {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M) :
    let A := Localization.Away r
    let e := basicOpenIsoSpecAway r
    let β := pullbackEquivalence e
    let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
    let G := pullback j
    let EA := affineEquivalence (R := CommRingCat.of A)
    let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
    let Hloc : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
      ModuleCat.localizedModuleFunctor (Submonoid.powers r)
    J.obj (EA.functor.obj (β.inverse.obj (G.obj E))) ≅ Hloc.obj M.obj := by
  let A := Localization.Away r
  let e := basicOpenIsoSpecAway r
  let β := pullbackEquivalence e
  let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
  let G := pullback j
  let EA := affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let Hloc : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
    ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let χ := basicOpenToLocalizedSpectrumIso r
  let κE := localizedSpectrumGlobalSectionsIso r M E cR
  exact J.mapIso (EA.functor.mapIso (χ.app E)) ≪≫ κE

private def basicOpenCoherentSubobjectData {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    { P : Subobject ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj) //
      P = localizedSpectrumCoherentSubobject r M E cR N hN } := by
  let A := Localization.Away r
  let e := basicOpenIsoSpecAway r
  let β := pullbackEquivalence e
  let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
  let FR := FGModuleCat.affineTilde (R := R)
  let G := pullback j
  let EA := affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let Hloc : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
    ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let F := pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let f : FR.obj K ⟶ E := FR.map g ≫ cR.inv
  let χ := basicOpenToLocalizedSpectrumIso r
  let κE := localizedSpectrumGlobalSectionsIso r M E cR
  let κD := basicOpenGlobalSectionsIso r M E cR
  let mD : J.obj (EA.functor.obj (β.inverse.obj (G.obj (FR.obj K)))) ⟶
      Hloc.obj M.obj :=
    J.map (EA.functor.map (β.inverse.map (G.map f))) ≫ κD.hom
  let mE : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ Hloc.obj M.obj :=
    J.map (EA.functor.map (F.map f)) ≫ κE.hom
  let mM : J.obj (EA.functor.obj (F.obj (FR.obj K))) ⟶ Hloc.obj M.obj :=
    J.map (EA.functor.map (F.map (FR.map g))) ≫
      ((localizedSpectrumGlobalSectionsNatIso r).app M).hom
  have heq : mE = mM := by
    change J.map (EA.functor.map (F.map (FR.map g ≫ cR.inv))) ≫
      (J.map (EA.functor.map (F.map cR.hom)) ≫
        ((localizedSpectrumGlobalSectionsNatIso r).app M).hom) =
      J.map (EA.functor.map (F.map (FR.map g))) ≫
        ((localizedSpectrumGlobalSectionsNatIso r).app M).hom
    rw [← Category.assoc, ← J.map_comp, ← EA.functor.map_comp, ← F.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm : mE = ((localizedSpectrumGlobalSectionsNatIso r).app K).hom ≫
      Hloc.map ((ModuleCat.isFG R).ι.map g) := by
    rw [heq]
    exact (localizedSpectrumGlobalSectionsNatIso r).hom.naturality g
  have hgm : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have hloc : Mono (Hloc.map ((ModuleCat.isFG R).ι.map g)) := by
    letI := hgm
    infer_instance
  haveI : Mono mE := by
    rw [hm]
    have hκ : Mono ((localizedSpectrumGlobalSectionsNatIso r).app K).hom := inferInstance
    refine ⟨?_⟩
    intro Z a b h
    apply hκ.right_cancellation
    apply hloc.right_cancellation
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  let θ : (((G ⋙ β.inverse) ⋙ EA.functor) ⋙ J) ≅
      ((F ⋙ EA.functor) ⋙ J) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight χ EA.functor) J
  let ιL := θ.app (FR.obj K)
  have hd : mD = ιL.hom ≫ mE := by
    change ((((G ⋙ β.inverse) ⋙ EA.functor) ⋙ J).map f ≫
        θ.hom.app E) ≫ κE.hom =
      (θ.hom.app (FR.obj K) ≫
        (((F ⋙ EA.functor) ⋙ J).map f)) ≫ κE.hom
    exact congrArg (fun t => t ≫ κE.hom) (θ.hom.naturality f)
  haveI : Mono mD := by
    rw [hd]
    have hι : Mono ιL.hom := inferInstance
    have hmE : Mono mE := inferInstance
    refine ⟨?_⟩
    intro Z a b h
    apply hι.right_cancellation
    apply hmE.right_cancellation
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  refine ⟨Subobject.mk mD, ?_⟩
  change Subobject.mk mD = Subobject.mk mE
  exact Subobject.mk_eq_mk_of_comm mD mE ιL hd.symm

/-- Pull the coherent tilde inclusion for `N ≤ M` back to the actual basic open,
then take affine global sections through `basicOpenIsoSpecAway r`. The target is
transported to Mathlib's canonical localized-module carrier. -/
def basicOpenCoherentSubobject {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    Subobject ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj) :=
  (basicOpenCoherentSubobjectData r M E cR N hN).1

/-- The actual basic-open construction agrees with the localized-spectrum
construction after transporting through `basicOpenIsoSpecAway r`. -/
theorem basicOpenCoherentSubobject_eq_localizedSpectrum {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    basicOpenCoherentSubobject r M E cR N hN =
      localizedSpectrumCoherentSubobject r M E cR N hN :=
  (basicOpenCoherentSubobjectData r M E cR N hN).2

/-- On the actual affine basic open `D(r)`, the transported coherent subobject
has underlying module exactly `N.localized'` inside canonical localization. -/
theorem basicOpenCoherentSubobject_subobjectModule {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    ModuleCat.subobjectModule
        ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
        (basicOpenCoherentSubobject r M E cR N hN) =
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  rw [basicOpenCoherentSubobject_eq_localizedSpectrum]
  exact localizedSpectrumCoherentSubobject_subobjectModule r M E cR N hN

end AlgebraicGeometry.Coh
