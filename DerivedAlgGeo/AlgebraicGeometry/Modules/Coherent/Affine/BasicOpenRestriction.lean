/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenLocalizedSubobject
import DerivedAlgGeo.Algebra.Module.LocalizedModule.NestedSubmodule

/-!
# Restricting a chosen coherent subobject between basic opens

For a finite submodule `N ≤ M`, the coherent tilde inclusion on `D(r)` restricts
to the same inclusion constructed directly on `D(r * s)`. After affine global
sections and explicit transport from `Shrink` to the raw localized-module
carrier, its submodule is the span of the image under the canonical map
`M[1/r] → M[1/(r*s)]`. This is a one-chart, underived statement for the chosen
finite `N`; it neither classifies arbitrary subobjects nor glues a union.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Coh

private theorem mapFunctor_map_iso {C : Type u} {D : Type u}
    [Category C] [Category D] (F G : C ⥤ D)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    (η : F ≅ G) {X : C} (P : Subobject X) :
    (Subobject.map (η.app X).hom).obj (Subobject.mapFunctor F P) =
      Subobject.mapFunctor G P := by
  induction P using Subobject.ind with
  | h f =>
    simp only [Subobject.mapFunctor_mk, Subobject.map_mk]
    exact Subobject.mk_eq_mk_of_comm _ _ (η.app _) (η.hom.naturality f).symm

set_option backward.isDefEq.respectTransparency false in
private theorem mapFunctor_comp_general {C D E : Type u}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [(F ⋙ G).PreservesMonomorphisms] {X : C} (P : Subobject X) :
    Subobject.mapFunctor G (Subobject.mapFunctor F P) =
      Subobject.mapFunctor (F ⋙ G) P := by
  induction P using Subobject.ind with
  | h f => simp only [Subobject.mapFunctor_mk, Functor.comp_map]

/-- The actual coherent tilde inclusion for a chosen finite `N ≤ M`, pulled
back from `Spec R` to the basic open `D(r)`. -/
def basicOpenChosenTildeSubobject {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    Subobject ((Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E) := by
  let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
  let G := Coh.pullback j
  letI : PreservesFiniteLimits (Scheme.Modules.pullback j) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback j)
  letI : G.PreservesMonomorphisms := inferInstance
  exact Subobject.mapFunctor G (coherentTildeSubobject M E cR N hN)

/-- Restrict a coherent subobject on `D(a)` along `D(x) ⊆ D(a)`, using the
pullback-composition isomorphism to place it on the canonical `D(x)` pullback. -/
def restrictBasicOpenSubobject {R : CommRingCat.{u}} [IsNoetherianRing R]
    (a x : R) (h : PrimeSpectrum.basicOpen x ≤ PrimeSpectrum.basicOpen a)
    (E : Coh (Spec R))
    (S : Subobject ((Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen a))).obj E)) :
    Subobject ((Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen x))).obj E) := by
  let U := PrimeSpectrum.basicOpen x
  let V := PrimeSpectrum.basicOpen a
  let i : Scheme.Opens.toScheme (X := Spec R) U ⟶
      Scheme.Opens.toScheme (X := Spec R) V := (Spec R).homOfLE h
  let ja := Scheme.Opens.ι (X := Spec R) V
  let jx := Scheme.Opens.ι (X := Spec R) U
  let F := Coh.pullback i
  let G := Coh.pullback ja
  let H := Coh.pullback jx
  letI : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback i)
  letI : F.PreservesMonomorphisms := inferInstance
  have hi : i ≫ ja = jx := Scheme.homOfLE_ι (Spec R) h
  let η : G ⋙ F ≅ H :=
    (Coh.pullbackComp i ja) ≪≫ eqToIso (congrArg Coh.pullback hi)
  exact (Subobject.map (η.app E).hom).obj (Subobject.mapFunctor F S)

private theorem restrictBasicOpenSubobject_chosen {R : CommRingCat.{u}}
    [IsNoetherianRing R] (a x : R)
    (h : PrimeSpectrum.basicOpen x ≤ PrimeSpectrum.basicOpen a)
    (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    restrictBasicOpenSubobject a x h E
        (basicOpenChosenTildeSubobject a M E cR N hN) =
      basicOpenChosenTildeSubobject x M E cR N hN := by
  let U := PrimeSpectrum.basicOpen x
  let V := PrimeSpectrum.basicOpen a
  let i : Scheme.Opens.toScheme (X := Spec R) U ⟶
      Scheme.Opens.toScheme (X := Spec R) V := (Spec R).homOfLE h
  let ja := Scheme.Opens.ι (X := Spec R) V
  let jx := Scheme.Opens.ι (X := Spec R) U
  let F := Coh.pullback i
  let G := Coh.pullback ja
  let H := Coh.pullback jx
  letI : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback i)
  letI : F.PreservesMonomorphisms := inferInstance
  have hi : i ≫ ja = jx := Scheme.homOfLE_ι (Spec R) h
  letI : PreservesFiniteLimits (Scheme.Modules.pullback ja) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback ja)
  letI : G.PreservesMonomorphisms := inferInstance
  letI : PreservesFiniteLimits (Scheme.Modules.pullback jx) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback jx)
  letI : H.PreservesMonomorphisms := inferInstance
  letI : (G ⋙ F).PreservesMonomorphisms := inferInstance
  let P := coherentTildeSubobject M E cR N hN
  let η : G ⋙ F ≅ H :=
    (Coh.pullbackComp i ja) ≪≫ eqToIso (congrArg Coh.pullback hi)
  unfold restrictBasicOpenSubobject basicOpenChosenTildeSubobject
  dsimp only
  rw [mapFunctor_comp_general G F]
  exact mapFunctor_map_iso (G ⋙ F) H η P

private def basicOpenSubobjectModule {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (S : Subobject ((Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)) :
    Subobject ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj) := by
  let A := Localization.Away r
  let e := basicOpenIsoSpecAway r
  let β := pullbackEquivalence e
  let EA := affineEquivalence (R := CommRingCat.of A)
  let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
  let T : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r))
      ⥤ ModuleCat.{u} A := (β.inverse ⋙ EA.functor) ⋙ J
  letI : PreservesFiniteLimits J := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))
    infer_instance
  letI : T.PreservesMonomorphisms := inferInstance
  exact (Subobject.map (basicOpenGlobalSectionsIso r M E cR).hom).obj
    (Subobject.mapFunctor T S)

private theorem basicOpenSubobjectModule_chosen {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    basicOpenSubobjectModule r M E cR
        (basicOpenChosenTildeSubobject r M E cR N hN) =
      basicOpenCoherentSubobject r M E cR N hN := by
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let FR := FGModuleCat.affineTilde (R := R)
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let f : FR.obj K ⟶ E := FR.map g ≫ cR.inv
  letI : FR.IsRightAdjoint := (affineEquivalence (R := R)).toAdjunction.isRightAdjoint
  have hgm : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  letI : Mono g := ((ModuleCat.isFG R).ι).mono_of_mono_map hgm
  letI : FR.PreservesMonomorphisms := inferInstance
  letI : Mono f := by dsimp [f]; infer_instance
  have hP : coherentTildeSubobject M E cR N hN = Subobject.mk f := by
    dsimp [coherentTildeSubobject, f, g]
  unfold basicOpenSubobjectModule basicOpenChosenTildeSubobject
  rw [hP]
  simp only [Subobject.mapFunctor_mk]
  rfl

/-- Transport a coherent subobject on the actual `D(r)` through the affine
global-sections comparison and then explicitly to the raw `M[1/r]` carrier. -/
def basicOpenSubobjectRawModule {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (S : Subobject ((Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)) :
    Submodule (Localization.Away r) (LocalizedModule.Away r M.obj) :=
  (ModuleCat.subobjectModule _ (basicOpenSubobjectModule r M E cR S)).map
    (Shrink.linearEquiv.{u} (Localization.Away r)
      (LocalizedModule.Away r M.obj)).toLinearMap

private theorem shrink_localizedModuleMk_apply {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R) (m : M.obj) :
    (Shrink.linearEquiv.{u} (Localization.Away r)
      (LocalizedModule.Away r M.obj))
        (M.obj.localizedModuleMkLinearMap (Submonoid.powers r) m) =
      LocalizedModule.mkLinearMap (Submonoid.powers r) M.obj m := by
  change (equivShrink (LocalizedModule.Away r M.obj)).symm
    ((equivShrink (LocalizedModule.Away r M.obj))
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M.obj m)) = _
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem localized'_map_shrink_eq {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (N : Submodule R M.obj) :
    (N.localized' (Localization.Away r) (Submonoid.powers r)
      (M.obj.localizedModuleMkLinearMap (Submonoid.powers r))).map
        (Shrink.linearEquiv.{u} (Localization.Away r)
          (LocalizedModule.Away r M.obj)).toLinearMap =
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M.obj) := by
  rw [Submodule.localized'_eq_span, Submodule.map_span,
    Submodule.localized'_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, (shrink_localizedModuleMk_apply r M m).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨M.obj.localizedModuleMkLinearMap (Submonoid.powers r) m,
      ⟨m, hm, rfl⟩, shrink_localizedModuleMk_apply r M m⟩

private theorem basicOpenSubobjectRawModule_chosen {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    basicOpenSubobjectRawModule r M E cR
        (basicOpenChosenTildeSubobject r M E cR N hN) =
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M.obj) := by
  unfold basicOpenSubobjectRawModule
  rw [basicOpenSubobjectModule_chosen,
    basicOpenCoherentSubobject_subobjectModule]
  exact localized'_map_shrink_eq r M N

/-- The chosen finite tilde subobject, restricted from `D(r)` to `D(r*s)`,
has raw affine-global-sections submodule equal to the span of the image of
its `D(r)` submodule under the canonical nested-localization map. -/
theorem basicOpenChosenTildeSubobject_restrict_rawModule {R : CommRingCat.{u}}
    [IsNoetherianRing R] (r s : R) (M : FGModuleCat.{u} R)
    (E : Coh (Spec R)) (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    let h : PrimeSpectrum.basicOpen (r * s) ≤ PrimeSpectrum.basicOpen r :=
      (PrimeSpectrum.basicOpen_mul r s).trans_le inf_le_left
    basicOpenSubobjectRawModule (r * s) M E cR
        (restrictBasicOpenSubobject r (r * s) h E
          (basicOpenChosenTildeSubobject r M E cR N hN)) =
      Submodule.span (Localization.Away (r * s))
        ((LocalizedModule.awayToAwayRightLinearMap (M := M.obj) r s) ''
          (basicOpenSubobjectRawModule r M E cR
            (basicOpenChosenTildeSubobject r M E cR N hN) :
              Set (LocalizedModule.Away r M.obj))) := by
  dsimp only
  rw [restrictBasicOpenSubobject_chosen, basicOpenSubobjectRawModule_chosen,
    basicOpenSubobjectRawModule_chosen]
  exact Submodule.localized'_awayToAwayRight_eq_span r s N

end AlgebraicGeometry.Coh
