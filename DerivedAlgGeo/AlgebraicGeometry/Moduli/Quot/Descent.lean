/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Descent.Zariski
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Free
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Locality

/-!
# Quotients of a free sheaf glue along open covers

Quotients `free I ↠ Q` of the free module sheaf on a scheme `S` descend along a jointly
surjective family of open immersions `f i : X i ⟶ S`: a family of quotients of `free I` on the
`X i`, isomorphic as quotients on every common refinement of two members, is the family of
pullbacks of a quotient of `free I` on `S`, and that quotient is unique up to isomorphism of
quotients.

## Main definitions

* `ModuleQuotient.freePullback`: the pullback of a quotient of `free I` along a morphism, read on
  `free I` through `f^* (free I) ≅ free I`.
* `ModuleQuotient.descentData`: the descent datum of `modulesPseudofunctor` that a compatible
  family of quotients defines.

## Main results

* `ModuleQuotient.exists_glue`: a compatible family of quotients of `free I` on the members of an
  open cover is the family of pullbacks of a quotient on the base.
* `ModuleQuotient.nonempty_iso_of_freePullback_iso`: two quotients of `free I` on the base whose
  pullbacks to the members of an open cover are isomorphic are isomorphic.

## Implementation notes

The gluing morphisms of the descent datum are the morphisms of quotients over the test object,
chosen from the compatibility hypothesis. Quotient arrows are epimorphisms, so there is at most
one morphism between two quotients of `free I` (`ModuleQuotient.instSubsingletonHom`). That
uniqueness makes the three conditions of a descent datum automatic once it is known that
`pullHom` of a morphism of quotients is again a morphism of quotients
(`ModuleQuotient.freePullback_pullHom`), which is where the coherence of `pullbackFreeIso` with
the compositor of pullback enters. The glued module sheaf is `ZariskiDescent.glue`; the quotient
arrow is glued by fullness of `toDescentData`, and is an epimorphism because its pullbacks to the
cover are (`Scheme.Modules.epi_of_epi_pullback`).
-/

open CategoryTheory Limits SheafOfModules

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (I : Type u)

/-- Along `g ≫ f = h`, the inverse of `pullbackFreeIso` along `h`, followed by the compositor of
pullback at the free sheaf, is the inverse of `pullbackFreeIso` along `g` followed by `g^*` of the
inverse of `pullbackFreeIso` along `f`. -/
lemma pullbackFreeIso_inv_comp_pullbackComp'_hom (g : Y ⟶ X) (f : X ⟶ Z) (h : Y ⟶ Z)
    (hgf : g ≫ f = h) :
    (pullbackFreeIso I h).inv ≫ (pullbackComp' g f h hgf).hom.app (free I) =
      (pullbackFreeIso I g).inv ≫ (pullback g).map (pullbackFreeIso I f).inv := by
  subst hgf
  have h := pullbackFreeIso_comp I g f
  have hc : (pullbackComp' g f (g ≫ f) rfl).hom.app (free I : Z.Modules) =
      (pullbackComp g f).inv.app (free I) := by
    simp [pullbackComp', pullbackCongr]
  rw [hc, Iso.inv_comp_eq, ← h]
  simp

end AlgebraicGeometry.Scheme.Modules

namespace ModuleQuotient

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ZariskiDescent

variable {S T Y Y' : Scheme.{u}} (I : Type u)

/-- A quotient of `free I` on `T` pulled back along `g : Y ⟶ T`, read on `free I` on `Y` through
`g^* (free I) ≅ free I`. -/
noncomputable abbrev freePullback (g : Y ⟶ T) (q : ModuleQuotient (free I : T.Modules)) :
    ModuleQuotient (free I : Y.Modules) :=
  q.pullbackVia g (pullbackFreeIso I g).symm

variable {I}

/-- `pullHom` of a morphism of pulled back quotients along `g` is again a morphism of pulled back
quotients: the pullback of the quotient arrow along `g ≫ f` is the pullback along `g` of the
pullback along `f`, through the compositor of pullback. -/
lemma freePullback_pullHom {f₁ : Y ⟶ S} {f₂ : Y ⟶ T} {A : ModuleQuotient (free I : S.Modules)}
    {B : ModuleQuotient (free I : T.Modules)}
    (φ : freePullback I f₁ A ⟶ freePullback I f₂ B) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ S) (gf₂ : Y' ⟶ T)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (freePullback I gf₁ A).hom ≫ ((pullbackComp' g f₁ gf₁ h₁).hom.app A.target ≫
      (Scheme.Modules.pullback g).map φ.right ≫ (pullbackComp' g f₂ gf₂ h₂).inv.app B.target) =
      (freePullback I gf₂ B).hom := by
  subst h₁ h₂
  have hφ := φ.comm
  have hn₁ := (pullbackComp' g f₁ (g ≫ f₁) rfl).hom.naturality A.hom
  have hn₂ := (pullbackComp' g f₂ (g ≫ f₂) rfl).hom.naturality B.hom
  simp only [Functor.comp_map] at hn₁ hn₂
  have e₁ : (freePullback I (g ≫ f₁) A).hom =
      (pullbackFreeIso I (g ≫ f₁)).inv ≫ (Scheme.Modules.pullback (g ≫ f₁)).map A.hom := rfl
  have e₂ : (freePullback I (g ≫ f₂) B).hom =
      (pullbackFreeIso I (g ≫ f₂)).inv ≫ (Scheme.Modules.pullback (g ≫ f₂)).map B.hom := rfl
  rw [e₁, e₂]
  simp only [Category.assoc]
  rw [reassoc_of% hn₁, ← Category.assoc (pullbackFreeIso I (g ≫ f₁)).inv,
    pullbackFreeIso_inv_comp_pullbackComp'_hom, Category.assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  have hn₂' : (Scheme.Modules.pullback (g ≫ f₂)).map B.hom =
      (pullbackComp' g f₂ (g ≫ f₂) rfl).hom.app (free I) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f₂).map B.hom) ≫
        (pullbackComp' g f₂ (g ≫ f₂) rfl).inv.app B.target := by
    rw [← Category.assoc, ← hn₂, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hn₂', ← Category.assoc (pullbackFreeIso I (g ≫ f₂)).inv,
    pullbackFreeIso_inv_comp_pullbackComp'_hom, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  change (pullbackFreeIso I g).inv ≫ (Scheme.Modules.pullback g).map
      ((freePullback I f₁ A).hom ≫ φ.right) ≫ _ = _
  rw [hφ, show (freePullback I f₂ B).hom = (pullbackFreeIso I f₂).inv ≫
    (Scheme.Modules.pullback f₂).map B.hom from rfl]


section Descent

variable {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
  (q : ∀ i, ModuleQuotient (free I : (X i).Modules))
  (h : ∀ ⦃Y : Scheme.{u}⦄ ⦃i₁ i₂ : ι⦄ (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂),
    g₁ ≫ f i₁ = g₂ ≫ f i₂ →
      Nonempty (ModuleQuotient.freePullback I g₁ (q i₁) ≅ ModuleQuotient.freePullback I g₂ (q i₂)))

/-- The descent datum of `modulesPseudofunctor` defined by a family of quotients of `free I` on the
members of a family `f` that are isomorphic as quotients over every test object mapping to two
members compatibly. The gluing morphism is the chosen isomorphism of quotients. -/
noncomputable def descentData : modulesPseudofunctor.DescentData f where
  obj i := (q i).target
  hom Y qq i₁ i₂ f₁ f₂ hf₁ hf₂ := (h f₁ f₂ (hf₁.trans hf₂.symm)).some.hom.right
  pullHom_hom Y' Y g qq qq' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullHom_eq _ g gf₁ gf₂ hgf₁ hgf₂]
    have := Subsingleton.elim (α := ModuleQuotient.freePullback I gf₁ (q i₁) ⟶
        ModuleQuotient.freePullback I gf₂ (q i₂))
      ⟨_, ModuleQuotient.freePullback_pullHom (h f₁ f₂ (hf₁.trans hf₂.symm)).some.hom g gf₁ gf₂
        hgf₁ hgf₂⟩
      (h gf₁ gf₂ (by rw [← hgf₁, ← hgf₂, Category.assoc, Category.assoc, hf₁, hf₂])).some.hom
    exact congrArg ModuleQuotient.Hom.right this
  hom_self Y qq i g hg := by
    exact congrArg ModuleQuotient.Hom.right
      (Subsingleton.elim (h g g rfl).some.hom (𝟙 _))
  hom_comp Y qq i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    exact congrArg ModuleQuotient.Hom.right
      (Subsingleton.elim ((h f₁ f₂ (hf₁.trans hf₂.symm)).some.hom ≫
        (h f₂ f₃ (hf₂.trans hf₃.symm)).some.hom) (h f₁ f₃ (hf₁.trans hf₃.symm)).some.hom)

/-- The quotient arrows commute with the gluing morphisms of the descent datum of the family of
quotients, over every test object. -/
lemma descentArrow_comm ⦃Y : Scheme.{u}⦄ (qq : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = qq) (hf₂ : f₂ ≫ f i₂ = qq) :
    (Modules.pullback f₁).map ((pullbackFreeIso I (f i₁)).hom ≫ (q i₁).hom) ≫
        (h f₁ f₂ (hf₁.trans hf₂.symm)).some.hom.right =
      ((pullbackCompApp f₁ (f i₁) qq hf₁ (free I : S.Modules)).inv ≫
        (pullbackCompApp f₂ (f i₂) qq hf₂ (free I : S.Modules)).hom) ≫
        (Modules.pullback f₂).map ((pullbackFreeIso I (f i₂)).hom ≫ (q i₂).hom) := by
  let ρ : (free I : Y.Modules) ≅
      (Modules.pullback f₁).obj ((Modules.pullback (f i₁)).obj (free I : S.Modules)) :=
    (pullbackFreeIso I qq).symm ≪≫ pullbackCompApp f₁ (f i₁) qq hf₁ _
  rw [← cancel_epi ρ.hom]
  have L₁ := pullbackFreeIso_inv_comp_pullbackComp'_hom I f₁ (f i₁) qq hf₁
  have L₂ := pullbackFreeIso_inv_comp_pullbackComp'_hom I f₂ (f i₂) qq hf₂
  have hφ := (h f₁ f₂ (hf₁.trans hf₂.symm)).some.hom.comm
  have e₁ : ρ.hom = (pullbackFreeIso I qq).inv ≫
      (pullbackComp' f₁ (f i₁) qq hf₁).hom.app (free I) := rfl
  have e₂ : (pullbackCompApp f₁ (f i₁) qq hf₁ (free I : S.Modules)).hom =
      (pullbackComp' f₁ (f i₁) qq hf₁).hom.app (free I) := rfl
  have e₃ : (pullbackCompApp f₂ (f i₂) qq hf₂ (free I : S.Modules)).hom =
      (pullbackComp' f₂ (f i₂) qq hf₂).hom.app (free I) := rfl
  have e₄ : (pullbackCompApp f₁ (f i₁) qq hf₁ (free I : S.Modules)).inv ≫
      (pullbackCompApp f₂ (f i₂) qq hf₂ (free I : S.Modules)).hom =
      (pullbackComp' f₁ (f i₁) qq hf₁).inv.app (free I) ≫
        (pullbackComp' f₂ (f i₂) qq hf₂).hom.app (free I) := rfl
  rw [e₄, e₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% L₁, reassoc_of% L₂]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  exact hφ

/-- The quotient arrows, as a morphism of descent data from the descent datum of the free sheaf. -/
noncomputable def descentArrow :
    (modulesPseudofunctor.toDescentData f).obj (free I : S.Modules) ⟶
      descentData f q h where
  hom i := (pullbackFreeIso I (f i)).hom ≫ (q i).hom
  comm Y qq i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    rw [toDescentData_obj_hom f _ qq f₁ f₂ hf₁ hf₂]
    exact descentArrow_comm f q h qq f₁ f₂ hf₁ hf₂

/-- A jointly surjective family of open immersions has every point in the range of a member. -/
lemma exists_mem_range_of_iSup_opensRange [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) (x : S) : ∃ i, x ∈ Set.range (f i) := by
  have hx : x ∈ (⨆ i, (f i).opensRange : S.Opens) := by rw [hf]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨i, by simpa using hi⟩

variable [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤)

include h hf in
/-- **Gluing of quotients.** A compatible family of quotients of the free sheaf on the members of
an open cover is the family of pullbacks of a quotient of the free sheaf on the base. -/
theorem exists_glue :
    ∃ Q : ModuleQuotient (free I : S.Modules),
      ∀ i, Nonempty (ModuleQuotient.freePullback I (f i) Q ≅ q i) := by
  let D := descentData f q h
  let e := glueIso D
  haveI := full_toDescentData (f := f) hf
  let ψ : (modulesPseudofunctor.toDescentData f).obj (free I : S.Modules) ⟶
      (modulesPseudofunctor.toDescentData f).obj (glue D) :=
    descentArrow f q h ≫ e.inv
  let π : (free I : S.Modules) ⟶ glue D := (modulesPseudofunctor.toDescentData f).preimage ψ
  have hπ : (modulesPseudofunctor.toDescentData f).map π = ψ := Functor.map_preimage _ _
  have hπi (i : ι) : (Modules.pullback (f i)).map π =
      (pullbackFreeIso I (f i)).hom ≫ (q i).hom ≫ e.inv.hom i := by
    have := congrArg (fun φ ↦ φ.hom i) hπ
    exact this
  let ei (i : ι) : (Modules.pullback (f i)).obj (glue D) ≅ (q i).target :=
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := congrArg (fun φ ↦ φ.hom i) e.hom_inv_id
      inv_hom_id := congrArg (fun φ ↦ φ.hom i) e.inv_hom_id }
  have hepi : Epi π := by
    refine epi_of_epi_pullback π f (exists_mem_range_of_iSup_opensRange f hf) fun i ↦ ?_
    rw [hπi i]
    have : Epi ((q i).hom ≫ e.inv.hom i) := by
      have : IsIso (e.inv.hom i) := (ei i).symm.isIso_hom
      infer_instance
    infer_instance
  refine ⟨⟨glue D, π, hepi⟩, fun i ↦ ⟨ModuleQuotient.isoMk (ei i) ?_⟩⟩
  change ((pullbackFreeIso I (f i)).inv ≫ (Modules.pullback (f i)).map π) ≫ (ei i).hom = (q i).hom
  rw [hπi i]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  change (q i).hom ≫ (ei i).inv ≫ (ei i).hom = (q i).hom
  rw [Iso.inv_hom_id, Category.comp_id]

end Descent

section Uniqueness

variable {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- The gluing morphisms of the descent datum of a module sheaf are natural in the module sheaf,
read through the quotient arrows out of the free sheaf. -/
lemma toDescentData_hom_natural {N : S.Modules} (t : (free I : S.Modules) ⟶ N)
    ⦃Y : Scheme.{u}⦄ (qq : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = qq) (hf₂ : f₂ ≫ f i₂ = qq) :
    (pullbackFreeIso I qq).inv ≫ (pullbackCompApp f₁ (f i₁) qq hf₁ (free I : S.Modules)).hom ≫
        (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map t) ≫
        (pullbackCompApp f₁ (f i₁) qq hf₁ N).inv ≫ (pullbackCompApp f₂ (f i₂) qq hf₂ N).hom =
      (pullbackFreeIso I qq).inv ≫ (pullbackCompApp f₂ (f i₂) qq hf₂ (free I : S.Modules)).hom ≫
        (Modules.pullback f₂).map ((Modules.pullback (f i₂)).map t) := by
  have n₁ := (pullbackComp' f₁ (f i₁) qq hf₁).hom.naturality t
  have n₂ := (pullbackComp' f₂ (f i₂) qq hf₂).hom.naturality t
  simp only [Functor.comp_map] at n₁ n₂
  change (pullbackFreeIso I qq).inv ≫ (pullbackComp' f₁ (f i₁) qq hf₁).hom.app (free I) ≫
        (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map t) ≫
        (pullbackComp' f₁ (f i₁) qq hf₁).inv.app N ≫ (pullbackComp' f₂ (f i₂) qq hf₂).hom.app N =
      (pullbackFreeIso I qq).inv ≫ (pullbackComp' f₂ (f i₂) qq hf₂).hom.app (free I) ≫
        (Modules.pullback f₂).map ((Modules.pullback (f i₂)).map t)
  have e₁ : (pullbackComp' f₁ (f i₁) qq hf₁).hom.app (free I) ≫
      (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map t) ≫
      (pullbackComp' f₁ (f i₁) qq hf₁).inv.app N = (Modules.pullback qq).map t := by
    rw [← Category.assoc, ← n₁, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [reassoc_of% e₁, n₂]

/-- Isomorphisms of the pullbacks of two quotients of `free I` to the members of a family that are
compatible with the quotient arrows commute with the gluing morphisms of their descent data. -/
lemma toDescentData_map_comm {Q Q' : ModuleQuotient (free I : S.Modules)}
    (m : ∀ i, (Modules.pullback (f i)).obj Q.target ≅ (Modules.pullback (f i)).obj Q'.target)
    (hm : ∀ i, (Modules.pullback (f i)).map Q.hom ≫ (m i).hom =
      (Modules.pullback (f i)).map Q'.hom) :
    ∀ ⦃Y : Scheme.{u}⦄ (qq : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = qq) (hf₂ : f₂ ≫ f i₂ = qq),
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (m i₁).hom ≫
        ((modulesPseudofunctor.toDescentData f).obj Q'.target).hom qq f₁ f₂ hf₁ hf₂ =
      ((modulesPseudofunctor.toDescentData f).obj Q.target).hom qq f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (m i₂).hom := by
    intro Y qq i₁ i₂ f₁ f₂ hf₁ hf₂
    rw [toDescentData_obj_hom f _ qq f₁ f₂ hf₁ hf₂, toDescentData_obj_hom f _ qq f₁ f₂ hf₁ hf₂]
    let ρ : (free I : Y.Modules) ≅
        (Modules.pullback f₁).obj ((Modules.pullback (f i₁)).obj (free I : S.Modules)) :=
      (pullbackFreeIso I qq).symm ≪≫ pullbackCompApp f₁ (f i₁) qq hf₁ _
    have : Epi Q.hom := Q.isEpi
    have : Epi ((Modules.pullback f₁).map ((Modules.pullback (f i₁)).map Q.hom)) := inferInstance
    have hepi : Epi (ρ.hom ≫ (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map Q.hom)) :=
      epi_comp _ _
    rw [← cancel_epi (ρ.hom ≫ (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map Q.hom))]
    have k₁ := toDescentData_hom_natural f Q'.hom qq f₁ f₂ hf₁ hf₂
    have k₂ := toDescentData_hom_natural f Q.hom qq f₁ f₂ hf₁ hf₂
    have e₁ : ρ.hom = (pullbackFreeIso I qq).inv ≫
      (pullbackCompApp f₁ (f i₁) qq hf₁ (free I : S.Modules)).hom := rfl
    show (ρ.hom ≫ (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map Q.hom)) ≫
        (Modules.pullback f₁).map (m i₁).hom ≫
          (pullbackCompApp f₁ (f i₁) qq hf₁ Q'.target).inv ≫
            (pullbackCompApp f₂ (f i₂) qq hf₂ Q'.target).hom =
      (ρ.hom ≫ (Modules.pullback f₁).map ((Modules.pullback (f i₁)).map Q.hom)) ≫
        ((pullbackCompApp f₁ (f i₁) qq hf₁ Q.target).inv ≫
          (pullbackCompApp f₂ (f i₂) qq hf₂ Q.target).hom) ≫
          (Modules.pullback f₂).map (m i₂).hom
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hm i₁, e₁]
    simp only [Category.assoc]
    rw [k₁, reassoc_of% k₂, ← Functor.map_comp, hm i₂]

variable [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤)

include hf in
/-- Two quotients of the free sheaf on the base whose pullbacks to the members of an open cover
are isomorphic as quotients are isomorphic as quotients. -/
theorem nonempty_iso_of_freePullback_iso {Q Q' : ModuleQuotient (free I : S.Modules)}
    (h : ∀ i, Nonempty (ModuleQuotient.freePullback I (f i) Q ≅
      ModuleQuotient.freePullback I (f i) Q')) : Nonempty (Q ≅ Q') := by
  haveI := faithful_toDescentData (f := f) hf
  haveI := full_toDescentData (f := f) hf
  let m (i : ι) : (Modules.pullback (f i)).obj Q.target ≅ (Modules.pullback (f i)).obj Q'.target :=
    (ModuleQuotient.targetFunctor _).mapIso (h i).some
  have hm (i : ι) : (Modules.pullback (f i)).map Q.hom ≫ (m i).hom =
      (Modules.pullback (f i)).map Q'.hom := by
    have := (h i).some.hom.comm
    exact (cancel_epi (pullbackFreeIso I (f i)).inv).1 this
  have comm := toDescentData_map_comm f m hm
  let Φ : (modulesPseudofunctor.toDescentData f).obj Q.target ≅
      (modulesPseudofunctor.toDescentData f).obj Q'.target :=
    Pseudofunctor.DescentData.isoMk m comm
  let e : Q.target ≅ Q'.target :=
    (Functor.FullyFaithful.ofFullyFaithful (modulesPseudofunctor.toDescentData f)).preimageIso Φ
  have he : (modulesPseudofunctor.toDescentData f).map e.hom = Φ.hom :=
    Functor.map_preimage _ _
  refine ⟨ModuleQuotient.isoMk e ?_⟩
  apply (modulesPseudofunctor.toDescentData f).map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  rw [Functor.map_comp]
  change (Modules.pullback (f i)).map Q.hom ≫
      ((modulesPseudofunctor.toDescentData f).map e.hom).hom i =
    (Modules.pullback (f i)).map Q'.hom
  rw [he]
  exact hm i

end Uniqueness


end ModuleQuotient
