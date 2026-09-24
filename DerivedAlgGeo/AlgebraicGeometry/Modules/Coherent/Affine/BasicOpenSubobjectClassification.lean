/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenSubobject
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenLocalizedSubobject
import Mathlib.Algebra.Category.FGModuleCat.Limits

/-!
# Classifying coherent subobjects on one affine basic open

An arbitrary coherent mono into the restriction of `E` to `D(r)` is, up to an
isomorphism on its source, the restriction of the tilde inclusion associated
to a finitely generated submodule of the affine global sections of `E`.
The explicit chart comparison identifies that inclusion with localization of
the chosen submodule. This is underived and does not glue across opens.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Coh

/-- A mono of coherent sheaves on a noetherian affine scheme is represented by
the tilde inclusion of the range of its map on finite global sections. -/
private theorem exists_tilde_representation_of_mono
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    (E L : Coh (Spec R)) (m : L ⟶ E) [Mono m]
    (M : FGModuleCat.{u} R)
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M) :
    let FR := FGModuleCat.affineTilde (R := R)
    ∃ (N : Submodule R M.obj) (hN : N.FG),
      letI : Module.Finite R N := Module.Finite.of_fg hN
      let K : FGModuleCat.{u} R := FGModuleCat.of R N
      let g : K ⟶ M := FGModuleCat.ofHom N.subtype
      ∃ e : L ≅ FR.obj K,
        m = e.hom ≫ (FR.map g ≫ cR.inv) := by
  let ER := affineEquivalence (R := R)
  let A : FGModuleCat.{u} R := ER.functor.obj L
  let FR := FGModuleCat.affineTilde (R := R)
  let g : A ⟶ M := ER.functor.map (m ≫ cR.hom) ≫ (ER.counitIso.app M).hom
  letI : ER.functor.PreservesMonomorphisms := inferInstance
  haveI : Mono g := by
    dsimp [g]
    infer_instance
  have hg : Function.Injective g.hom.hom := by
    letI : PreservesFiniteLimits ((ModuleCat.isFG R).ι) := by
      change PreservesFiniteLimits (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
      infer_instance
    exact (ModuleCat.mono_iff_injective ((ModuleCat.isFG R).ι.map g)).mp inferInstance
  let N : Submodule R M.obj := LinearMap.range g.hom.hom
  have hN : N.FG := IsNoetherian.noetherian N
  refine ⟨N, hN, ?_⟩
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let gN : K ⟶ M := FGModuleCat.ofHom N.subtype
  let i : A ≅ K := (LinearEquiv.ofInjective g.hom.hom hg).toFGModuleCatIso
  have hi : i.hom ≫ gN = g := by
    ext x
    exact LinearEquiv.ofInjective_apply (h := hg) g.hom.hom x
  let cL : L ≅ FR.obj A := ER.unitIso.app L
  let cM : FR.obj M ≅ FR.obj (ER.functor.obj (FR.obj M)) :=
    ER.unitIso.app (FR.obj M)
  let e : L ≅ FR.obj K := cL ≪≫ FR.mapIso i
  refine ⟨e, ?_⟩
  have hunit : cM.hom ≫
      FR.map (ER.counitIso.app M).hom = 𝟙 (FR.obj M) := by
    exact ER.unit_inverse_comp M
  have hnat : (m ≫ cR.hom) ≫ cM.hom =
      cL.hom ≫ FR.map (ER.functor.map (m ≫ cR.hom)) :=
    ER.unitIso.hom.naturality (m ≫ cR.hom)
  have hfirst : cL.hom ≫ FR.map g =
      ((m ≫ cR.hom) ≫ cM.hom) ≫ FR.map (ER.counitIso.app M).hom := by
    calc
      cL.hom ≫ FR.map g =
          (cL.hom ≫ FR.map (ER.functor.map (m ≫ cR.hom))) ≫
            FR.map (ER.counitIso.app M).hom := by
        change cL.hom ≫ FR.map
            (ER.functor.map (m ≫ cR.hom) ≫ (ER.counitIso.app M).hom) = _
        rw [Functor.map_comp, ← Category.assoc]
      _ = ((m ≫ cR.hom) ≫ cM.hom) ≫
          FR.map (ER.counitIso.app M).hom := by rw [hnat]
  have hsecond : ((m ≫ cR.hom) ≫ cM.hom) ≫
      FR.map (ER.counitIso.app M).hom = m ≫ cR.hom := by
    rw [Category.assoc, hunit]
    exact Category.comp_id _
  have hc' : cL.hom ≫ FR.map g = m ≫ cR.hom := hfirst.trans hsecond
  have hc : m ≫ cR.hom = cL.hom ≫ FR.map g := hc'.symm
  apply (cancel_mono cR.hom).mp
  calc
    m ≫ cR.hom = cL.hom ≫ FR.map g := hc
    _ = e.hom ≫ FR.map gN := by
      change cL.hom ≫ FR.map g =
        (cL.hom ≫ FR.map i.hom) ≫ FR.map gN
      rw [Category.assoc, ← FR.map_comp, hi]
    _ = (e.hom ≫ (FR.map gN ≫ cR.inv)) ≫ cR.hom := by simp

/-- Every coherent mono on the actual basic open is the restriction, up to a
source isomorphism, of the coherent tilde inclusion of a finite submodule of
the chosen module presentation of `E`. The transported chart subobject is its
canonical localization. -/
theorem exists_tilde_subobject_pullbackBasicOpen
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)
    [Mono β] :
    let FR := FGModuleCat.affineTilde (R := R)
    let G := pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
    ∃ (N : Submodule R M.obj) (hN : N.FG),
      letI : Module.Finite R N := Module.Finite.of_fg hN
      let K : FGModuleCat.{u} R := FGModuleCat.of R N
      let g : K ⟶ M := FGModuleCat.ofHom N.subtype
      let f : FR.obj K ⟶ E := FR.map g ≫ cR.inv
      (∃ e : Z ≅ G.obj (FR.obj K), β = e.hom ≫ G.map f) ∧
        ModuleCat.subobjectModule
            ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
            (basicOpenCoherentSubobject r M E cR N hN) =
          N.localized' (Localization.Away r) (Submonoid.powers r)
            (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  let FR := FGModuleCat.affineTilde (R := R)
  let G := pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
  obtain ⟨L, m, hm, e₁, he₁⟩ := exists_mono_lift_pullbackBasicOpen r E Z β
  letI : Mono m := hm
  obtain ⟨N, hN, e₂, he₂⟩ := exists_tilde_representation_of_mono E L m M cR
  refine ⟨N, hN, ?_, basicOpenCoherentSubobject_subobjectModule r M E
    cR N hN⟩
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let f : FR.obj K ⟶ E := FR.map g ≫ cR.inv
  refine ⟨e₁ ≪≫ G.mapIso e₂, ?_⟩
  calc
    β = e₁.hom ≫ G.map m := he₁
    _ = (e₁ ≪≫ G.mapIso e₂).hom ≫ G.map f := by
      rw [he₂]
      change e₁.hom ≫ G.map (e₂.hom ≫ f) =
        (e₁.hom ≫ G.map e₂.hom) ≫ G.map f
      simp only [Functor.map_comp, Category.assoc]

/-- Every prescribed mono on `D(r)` is the restriction of the actual coherent
tilde subobject of a finite submodule. The chart module subobject, with target
transported by `basicOpenGlobalSectionsIso`, is `N.localized'`. -/
theorem exists_coherentTildeSubobject_pullbackBasicOpen
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)
    [Mono β] :
    let G := pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
    ∃ (N : Submodule R M.obj) (hN : N.FG),
      let P := coherentTildeSubobject M E cR N hN
      (∃ e : Z ≅ G.obj P, β = e.hom ≫ G.map P.arrow) ∧
        ModuleCat.subobjectModule
            ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
            (basicOpenCoherentSubobject r M E cR N hN) =
          N.localized' (Localization.Away r) (Submonoid.powers r)
            (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  let ER := affineEquivalence (R := R)
  let FR := FGModuleCat.affineTilde (R := R)
  let G := pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
  obtain ⟨N, hN, ⟨e, he⟩, hchart⟩ :=
    exists_tilde_subobject_pullbackBasicOpen r M E cR Z β
  letI : Module.Finite R N := Module.Finite.of_fg hN
  let K : FGModuleCat.{u} R := FGModuleCat.of R N
  let g : K ⟶ M := FGModuleCat.ofHom N.subtype
  let f : FR.obj K ⟶ E := FR.map g ≫ cR.inv
  letI : FR.IsRightAdjoint := ER.toAdjunction.isRightAdjoint
  have hgm : Mono ((ModuleCat.isFG R).ι.map g) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  letI : Mono g := ((ModuleCat.isFG R).ι).mono_of_mono_map hgm
  letI : FR.PreservesMonomorphisms := inferInstance
  letI : Mono f := by
    dsimp [f]
    infer_instance
  let P := coherentTildeSubobject M E cR N hN
  have hP : P = Subobject.mk f := by
    dsimp [P, coherentTildeSubobject, f, g]
  refine ⟨N, hN, ?_, hchart⟩
  have hP' : coherentTildeSubobject M E cR N hN = Subobject.mk f := hP
  rw [hP']
  refine ⟨e ≪≫ G.mapIso (Subobject.underlyingIso f).symm, ?_⟩
  calc
    β = e.hom ≫ G.map f := he
    _ = e.hom ≫ G.map
        ((Subobject.underlyingIso f).inv ≫ (Subobject.mk f).arrow) := by
          rw [Subobject.underlyingIso_arrow]
    _ = (e ≪≫ G.mapIso (Subobject.underlyingIso f).symm).hom ≫
        G.map (Subobject.mk f).arrow := by
          simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
            Iso.symm_hom, Category.assoc]

/-- Canonical `M = Γ(E)` specialization of the one-chart classification.
No presentation or ring action equality is left for the caller to choose. -/
theorem exists_coherentTildeSubobject_pullbackBasicOpen_globalSections
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (E : Coh (Spec R))
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)
    [Mono β] :
    let ER := affineEquivalence (R := R)
    let M : FGModuleCat.{u} R := ER.functor.obj E
    let G := pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
    ∃ (N : Submodule R M.obj) (hN : N.FG),
      let P := coherentTildeSubobject M E (ER.unitIso.app E) N hN
      (∃ e : Z ≅ G.obj P, β = e.hom ≫ G.map P.arrow) ∧
        ModuleCat.subobjectModule
            ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
            (basicOpenCoherentSubobject r M E (ER.unitIso.app E) N hN) =
          N.localized' (Localization.Away r) (Submonoid.powers r)
            (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  let ER := affineEquivalence (R := R)
  let M : FGModuleCat.{u} R := ER.functor.obj E
  exact exists_coherentTildeSubobject_pullbackBasicOpen r M E (ER.unitIso.app E) Z β

end AlgebraicGeometry.Coh
