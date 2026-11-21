/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Pseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Descent

/-!
# The tilde construction as a strong transformation

For a commutative ring `R`, Mathlib's `tildeEquiv` identifies `ModuleCat R` with the quasi-coherent
module sheaves on `Spec R`. As `R` varies, these equivalences form a strong transformation
`AlgebraicGeometry.Scheme.tildeStrongTrans` from the pseudofunctor of extension of scalars on
`CommRingCatᵒᵖ` to the pseudofunctor of pullback of quasi-coherent sheaves along `Spec`. Its
naturality isomorphisms are the inverses of `Scheme.Modules.pullbackSpecMapTildeIso`.

## Main definitions

* `AlgebraicGeometry.Scheme.tildeStrongTrans`: the strong transformation `R ↦ tildeEquiv`, from
  `CommRingCat.moduleCatAdjPseudofunctor.comp Bicategory.Adj.forget₁` to
  `Scheme.Spec.op.toPseudofunctor.comp qcohPseudofunctor`.

## Main results

* `AlgebraicGeometry.Scheme.tildeStrongTrans_app_isEquivalence`: its components are
  equivalences of categories.

## Implementation notes

`pullbackSpecMapTildeIso` is defined by `Adjunction.leftAdjointUniq` from the affine
global-sections comparison `gammaPushforwardNatIso`. Its compatibility with identities and
composites is therefore proved on right adjoints: under `conjugateEquiv` it becomes the
compatibility of `gammaPushforwardNatIso` with `pushforwardId`, `pushforwardComp`,
`restrictScalarsId` and `restrictScalarsComp`, which holds elementwise because each of these
maps is the identity on global sections. The conjugates of the compositors of both
pseudofunctors are Mathlib's `conjugateEquiv_pullbackComp_inv`,
`conjugateEquiv_pullbackId_hom` and the definitions of `extendScalarsComp` and
`extendScalarsId`.

The compositors of `Scheme.Spec.op.toPseudofunctor` are `eqToHom`s of `Spec.map_comp` and
`Spec.map_id`, which are not definitional equalities. The coherence of the strong transformation
is therefore proved once, for a functor `Φ : D ⥤ Scheme` and abstract functors and natural
isomorphisms satisfying the coherence conditions on module sheaves (a private construction of
this file), and `tildeStrongTrans` is its instance at `Scheme.Spec`. Each scheme
morphism enters in the presentation `(Scheme.Spec.op.toPseudofunctor.map f).as.unop` that the
compositors produce, so that instantiating the abstract construction compares no two
presentations of the same morphism inside these `eqToHom`s.

## References

* [Stacks, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7): Schemes, Lemma 26.7.1, the
  tilde construction is left adjoint to global sections.
* [Stacks, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9): Schemes, Lemma 26.7.3, the
  pullback of `M~` along `Spec(B) → Spec(A)` is `(B ⊗_A M)~`, functorially in `M`.

## Tags

quasi-coherent sheaf, tilde, affine scheme, strong transformation, pseudofunctor
-/

universe u

open CategoryTheory Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)

/-! ### Conjugates -/

/-- Replacing the right adjoint of `adj₁` by an isomorphic functor changes conjugates by that
isomorphism. -/
private lemma conjugateEquiv_ofNatIsoRight {C₀ D₀ : Type*} [Category* C₀] [Category* D₀]
    {L₁ L₂ : C₀ ⥤ D₀} {G H R₂ : D₀ ⥤ C₀} (adj₁ : L₁ ⊣ G) (ρ : G ≅ H) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ adj₂ α = ρ.hom ≫ conjugateEquiv (adj₁.ofNatIsoRight ρ) adj₂ α := by
  ext d
  have h₁ : α.app (H.obj d) ≫ L₁.map (ρ.inv.app d) = L₂.map (ρ.inv.app d) ≫ α.app (G.obj d) :=
    (α.naturality _).symm
  have h₂ : adj₂.unit.app (H.obj d) ≫ R₂.map (L₂.map (ρ.inv.app d)) =
      ρ.inv.app d ≫ adj₂.unit.app (G.obj d) :=
    (adj₂.unit.naturality _).symm
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight, NatTrans.comp_app,
    Functor.comp_obj, Functor.id_obj, Functor.whiskerRight_app, Functor.map_comp]
  rw [← R₂.map_comp_assoc, h₁, R₂.map_comp_assoc, reassoc_of% h₂, Iso.hom_inv_id_app_assoc]

/-- The conjugate of the inverse associator is the inverse associator. -/
private lemma conjugateEquiv_associator_inv {C₀ C₁ C₂ C₃ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] [Category* C₃]
    {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀} {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁}
    {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  have h := conjugateEquiv_comm ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
    (α := (Functor.associator _ _ _).inv) (β := (Functor.associator _ _ _).hom) (by simp)
  rw [conjugateEquiv_associator_hom] at h
  ext X
  simpa using NatTrans.congr_app h X

/-- `pullbackSpecMapTildeIso` is the conjugate of `gammaPushforwardNatIso`. -/
private lemma conjugateEquiv_pullbackSpecMapTildeIso_inv :
    conjugateEquiv ((tilde.adjunction (R := A)).comp (pullbackPushforwardAdjunction (Spec.map φ)))
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := B)))
      (pullbackSpecMapTildeIso φ).inv = (gammaPushforwardNatIso φ).hom := by
  rw [conjugateEquiv_ofNatIsoRight _ (gammaPushforwardNatIso φ)]
  change _ ≫ conjugateEquiv _ _ ((conjugateEquiv _ _).symm (𝟙 _)) = _
  rw [Equiv.apply_symm_apply, Category.comp_id]

private lemma conjugateEquiv_extendScalarsComp_hom :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
        (ModuleCat.extendRestrictScalarsAdj ψ.hom))
      (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom)
      (ModuleCat.extendScalarsComp φ.hom ψ.hom).hom =
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv := by
  simp [ModuleCat.extendScalarsComp, conjugateIsoEquiv]

private lemma conjugateEquiv_extendScalarsId_hom :
    conjugateEquiv Adjunction.id (ModuleCat.extendRestrictScalarsAdj (𝟙 A : A ⟶ A).hom)
      (ModuleCat.extendScalarsId A).hom = (ModuleCat.restrictScalarsId A).inv := by
  simp [ModuleCat.extendScalarsId, conjugateIsoEquiv]

private lemma conjugateEquiv_pullbackCongr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
      (pullbackCongr h).hom = (pushforwardCongr h.symm).hom := by
  subst h
  ext M U : 3
  simp [pullbackCongr]

/-! ### Global sections of pushforwards -/

private lemma moduleSpecΓFunctor_map_pushforwardCongr_hom_app_apply {f g : Spec C ⟶ Spec A}
    (h : f = g) (M : (Spec C).Modules) (x) :
    (moduleSpecΓFunctor.map ((pushforwardCongr h).hom.app M)).hom x = x := by
  subst h
  change (M.presheaf.map (𝟙 _)).hom x = x
  simp
  rfl

private lemma gammaPushforward_comp_apply (M : (Spec C).Modules)
    {h : Spec.map ψ ≫ Spec.map φ = Spec.map (φ ≫ ψ)} (x) :
    (moduleSpecΓFunctor.map ((pushforwardComp (Spec.map ψ) (Spec.map φ)).hom.app M ≫
      (pushforwardCongr h).hom.app M) ≫ (gammaPushforwardNatIso (φ ≫ ψ)).hom.app M).hom x =
      (moduleSpecΓFunctor.map ((pushforwardCongr h).hom.app M)).hom x :=
  rfl

private lemma gammaPushforward_restrictScalarsComp_apply (M : (Spec C).Modules) (x) :
    ((gammaPushforwardNatIso φ).hom.app _ ≫
      (ModuleCat.restrictScalars φ.hom).map ((gammaPushforwardNatIso ψ).hom.app M) ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv.app _).hom x = x :=
  rfl

private lemma gammaPushforward_id_apply (M : (Spec A).Modules)
    {h : 𝟙 (Spec A) = Spec.map (𝟙 A)} (x) :
    (moduleSpecΓFunctor.map ((pushforwardId _).inv.app M ≫ (pushforwardCongr h).hom.app M) ≫
      (gammaPushforwardNatIso (𝟙 A)).hom.app M).hom x =
      (moduleSpecΓFunctor.map ((pushforwardCongr h).hom.app M)).hom x :=
  rfl

private lemma restrictScalarsId_inv_app_apply (M : (Spec A).Modules) (x) :
    ((ModuleCat.restrictScalarsId A).inv.app (moduleSpecΓFunctor.obj M)).hom x = x :=
  rfl

/-- `gammaPushforwardNatIso` is compatible with `pushforwardComp` and `restrictScalarsComp`. -/
private lemma gammaPushforwardNatIso_comp {h : Spec.map ψ ≫ Spec.map φ = Spec.map (φ ≫ ψ)}
    (M : (Spec C).Modules) :
    moduleSpecΓFunctor.map ((pushforwardComp (Spec.map ψ) (Spec.map φ)).hom.app M ≫
      (pushforwardCongr h).hom.app M) ≫ (gammaPushforwardNatIso (φ ≫ ψ)).hom.app M =
    (gammaPushforwardNatIso φ).hom.app _ ≫
      (ModuleCat.restrictScalars φ.hom).map ((gammaPushforwardNatIso ψ).hom.app M) ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv.app _ := by
  ext x
  rw [gammaPushforward_comp_apply φ ψ M x, gammaPushforward_restrictScalarsComp_apply]
  exact moduleSpecΓFunctor_map_pushforwardCongr_hom_app_apply h M x

/-- `gammaPushforwardNatIso` is compatible with `pushforwardId` and `restrictScalarsId`. -/
private lemma gammaPushforwardNatIso_id {h : 𝟙 (Spec A) = Spec.map (𝟙 A)}
    (M : (Spec A).Modules) :
    moduleSpecΓFunctor.map ((pushforwardId _).inv.app M ≫ (pushforwardCongr h).hom.app M) ≫
      (gammaPushforwardNatIso (𝟙 A)).hom.app M =
    (ModuleCat.restrictScalarsId A).inv.app (moduleSpecΓFunctor.obj M) := by
  ext x
  rw [gammaPushforward_id_apply M x, restrictScalarsId_inv_app_apply]
  exact moduleSpecΓFunctor_map_pushforwardCongr_hom_app_apply h M x

/-! ### Coherence of `pullbackSpecMapTildeIso` -/

/-- `pullbackSpecMapTildeIso` is compatible with composition. -/
private lemma pullbackSpecMapTildeIso_inv_comp (h : Spec.map ψ ≫ Spec.map φ = Spec.map (φ ≫ ψ)) :
    (pullbackSpecMapTildeIso (φ ≫ ψ)).inv ≫
        Functor.whiskerLeft (tilde.functor A) (pullbackComp' (Spec.map ψ) (Spec.map φ) _ h).hom =
      Functor.whiskerRight (ModuleCat.extendScalarsComp φ.hom ψ.hom).hom (tilde.functor C) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (ModuleCat.extendScalars φ.hom) (pullbackSpecMapTildeIso ψ).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackSpecMapTildeIso φ).inv (pullback (Spec.map ψ)) ≫
        (Functor.associator _ _ _).hom := by
  let tA := tilde.adjunction (R := A)
  let tB := tilde.adjunction (R := B)
  let tC := tilde.adjunction (R := C)
  let pφ := pullbackPushforwardAdjunction (Spec.map φ)
  let pψ := pullbackPushforwardAdjunction (Spec.map ψ)
  let pφψ := pullbackPushforwardAdjunction (Spec.map (φ ≫ ψ))
  let pc := pullbackPushforwardAdjunction (Spec.map ψ ≫ Spec.map φ)
  let eφ := ModuleCat.extendRestrictScalarsAdj φ.hom
  let eψ := ModuleCat.extendRestrictScalarsAdj ψ.hom
  let eφψ := ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom
  apply (conjugateEquiv (tA.comp (pφ.comp pψ)) (eφψ.comp tC)).injective
  rw [← conjugateEquiv_comp (tA.comp (pφ.comp pψ)) (tA.comp pφψ) (eφψ.comp tC),
    conjugateEquiv_whiskerLeft, conjugateEquiv_pullbackSpecMapTildeIso_inv (φ ≫ ψ),
    pullbackComp', Iso.trans_hom, Iso.symm_hom, ← conjugateEquiv_comp (pφ.comp pψ) pc pφψ,
    conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr_hom]
  rw [← conjugateEquiv_comp (tA.comp (pφ.comp pψ)) ((eφ.comp eψ).comp tC) (eφψ.comp tC),
    ← conjugateEquiv_comp (tA.comp (pφ.comp pψ)) (eφ.comp (eψ.comp tC)) ((eφ.comp eψ).comp tC),
    ← conjugateEquiv_comp (tA.comp (pφ.comp pψ)) (eφ.comp (tB.comp pψ)) (eφ.comp (eψ.comp tC)),
    ← conjugateEquiv_comp (tA.comp (pφ.comp pψ)) ((eφ.comp tB).comp pψ) (eφ.comp (tB.comp pψ)),
    ← conjugateEquiv_comp (tA.comp (pφ.comp pψ)) ((tA.comp pφ).comp pψ) ((eφ.comp tB).comp pψ),
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_pullbackSpecMapTildeIso_inv, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_pullbackSpecMapTildeIso_inv,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_extendScalarsComp_hom]
  ext M : 2
  simpa using gammaPushforwardNatIso_comp φ ψ M

/-- `pullbackSpecMapTildeIso` is compatible with identities. -/
private lemma pullbackSpecMapTildeIso_inv_id (h : Spec.map (𝟙 A) = 𝟙 (Spec A)) :
    (pullbackSpecMapTildeIso (𝟙 A)).inv ≫
        Functor.whiskerLeft (tilde.functor A) ((pullbackCongr h).hom ≫ (pullbackId _).hom) ≫
        (Functor.rightUnitor _).hom =
      Functor.whiskerRight (ModuleCat.extendScalarsId A).hom (tilde.functor A) ≫
        (Functor.leftUnitor _).hom := by
  let tA := tilde.adjunction (R := A)
  let pId := pullbackPushforwardAdjunction (𝟙 (Spec A))
  let pS := pullbackPushforwardAdjunction (Spec.map (𝟙 A))
  let eId := ModuleCat.extendRestrictScalarsAdj (𝟙 A : A ⟶ A).hom
  apply (conjugateEquiv tA (eId.comp tA)).injective
  rw [← conjugateEquiv_comp tA (tA.comp pS) (eId.comp tA),
    ← conjugateEquiv_comp tA (tA.comp Adjunction.id) (tA.comp pS),
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
    ← conjugateEquiv_comp Adjunction.id pId pS, conjugateEquiv_pullbackId_hom,
    conjugateEquiv_pullbackCongr_hom, conjugateEquiv_pullbackSpecMapTildeIso_inv,
    ← conjugateEquiv_comp tA (Adjunction.id.comp tA) (eId.comp tA),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_extendScalarsId_hom]
  ext M : 2
  simpa using gammaPushforwardNatIso_id M

/-- `pullbackSpecMapTildeIso` followed by a change of presentation of `Spec.map φ`. -/
private noncomputable def tildeNatIso {u₀ : Spec B ⟶ Spec A} (hu : Spec.map φ = u₀) :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor B ≅ tilde.functor A ⋙ pullback u₀ :=
  (pullbackSpecMapTildeIso φ).symm ≪≫ Functor.isoWhiskerLeft _ (pullbackCongr hu)

private lemma tildeNatIso_rfl : tildeNatIso φ rfl = (pullbackSpecMapTildeIso φ).symm := by
  simp [tildeNatIso, pullbackCongr]

private lemma tildeNatIso_comp {u₀ : Spec B ⟶ Spec A} {v₀ : Spec C ⟶ Spec B}
    {w₀ : Spec C ⟶ Spec A} (hu : Spec.map φ = u₀) (hv : Spec.map ψ = v₀)
    (hw : Spec.map (φ ≫ ψ) = w₀) (h : v₀ ≫ u₀ = w₀) :
    (tildeNatIso (φ ≫ ψ) hw).hom ≫
        Functor.whiskerLeft (tilde.functor A) (pullbackComp' v₀ u₀ w₀ h).hom =
      Functor.whiskerRight (ModuleCat.extendScalarsComp φ.hom ψ.hom).hom (tilde.functor C) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (ModuleCat.extendScalars φ.hom) (tildeNatIso ψ hv).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tildeNatIso φ hu).hom (pullback v₀) ≫
        (Functor.associator _ _ _).hom := by
  subst hu hv hw
  rw [tildeNatIso_rfl, tildeNatIso_rfl, tildeNatIso_rfl, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom]
  exact pullbackSpecMapTildeIso_inv_comp φ ψ h

private lemma tildeNatIso_id {u₀ : Spec A ⟶ Spec A} (hu : Spec.map (𝟙 A) = u₀)
    (h : u₀ = 𝟙 (Spec A)) :
    (tildeNatIso (𝟙 A) hu).hom ≫
        Functor.whiskerLeft (tilde.functor A) ((pullbackCongr h).hom ≫ (pullbackId _).hom) ≫
        (Functor.rightUnitor _).hom =
      Functor.whiskerRight (ModuleCat.extendScalarsId A).hom (tilde.functor A) ≫
        (Functor.leftUnitor _).hom := by
  subst hu
  rw [tildeNatIso_rfl, Iso.symm_hom]
  exact pullbackSpecMapTildeIso_inv_id h

end Scheme.Modules

namespace Scheme

/-! ### Compositors of the reindexed pseudofunctors -/

section Compositors

/-- The compositor of a full sub-pseudofunctor after reindexing, on underlying objects. -/
private lemma comp_fullsubcategory_mapComp_hom_app_hom {B₀ B₁ : Type*} [Bicategory B₀]
    [Bicategory B₁] (Ψ : Pseudofunctor B₀ B₁) {F : Pseudofunctor B₁ Cat.{u, u + 1}}
    (P : F.ObjectProperty) [P.IsClosedUnderMapObj] {x y z : B₀} (f₀ : x ⟶ y) (g₀ : y ⟶ z)
    (X : (Ψ.comp P.fullsubcategory).obj x) :
    (((Ψ.comp P.fullsubcategory).mapComp f₀ g₀).hom.toNatTrans.app X).hom =
      ((Ψ.comp F).mapComp f₀ g₀).hom.toNatTrans.app X.obj :=
  rfl

/-- The unitor of a full sub-pseudofunctor after reindexing, on underlying objects. -/
private lemma comp_fullsubcategory_mapId_hom_app_hom {B₀ B₁ : Type*} [Bicategory B₀]
    [Bicategory B₁] (Ψ : Pseudofunctor B₀ B₁) {F : Pseudofunctor B₁ Cat.{u, u + 1}}
    (P : F.ObjectProperty) [P.IsClosedUnderMapObj] (x : B₀)
    (X : (Ψ.comp P.fullsubcategory).obj x) :
    (((Ψ.comp P.fullsubcategory).mapId x).hom.toNatTrans.app X).hom =
      ((Ψ.comp F).mapId x).hom.toNatTrans.app X.obj :=
  rfl

variable {D : Type*} [Category* D] (Φ : D ⥤ Scheme.{u}) {a b c : LocallyDiscrete Dᵒᵖ}
  (f : a ⟶ b) (g : b ⟶ c)

private lemma toPseudofunctor_map_comp_as_unop :
    (Φ.op.toPseudofunctor.map g).as.unop ≫ (Φ.op.toPseudofunctor.map f).as.unop =
      (Φ.op.toPseudofunctor.map (f ≫ g)).as.unop :=
  (Φ.map_comp _ _).symm

private lemma toPseudofunctor_map_id_as_unop :
    (Φ.op.toPseudofunctor.map (𝟙 a)).as.unop = 𝟙 _ :=
  Φ.map_id _

private lemma modulesPseudofunctor_mapId'_hom_app {X : Scheme.{u}}
    (U : LocallyDiscrete.mk (op X) ⟶ .mk (op X)) (p : U = 𝟙 _) (h : U.as.unop = 𝟙 X)
    (M : X.Modules) :
    (modulesPseudofunctor.mapId' U p).hom.toNatTrans.app M =
      (Modules.pullbackCongr h).hom.app M ≫ (Modules.pullbackId X).hom.app M := by
  subst p
  simp only [Pseudofunctor.mapId'_eq_mapId, Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

/-- The compositor of `Φ.op.toPseudofunctor.comp modulesPseudofunctor` is `pullbackComp'`. -/
private lemma comp_modulesPseudofunctor_mapComp_hom_app
    (N : (Φ.op.toPseudofunctor.comp modulesPseudofunctor).obj a) :
    ((Φ.op.toPseudofunctor.comp modulesPseudofunctor).mapComp f g).hom.toNatTrans.app N =
      (Modules.pullbackComp' _ _ _ (toPseudofunctor_map_comp_as_unop Φ f g)).hom.app N := by
  have e : (Φ.op.toPseudofunctor.comp modulesPseudofunctor).mapComp f g =
      modulesPseudofunctor.mapComp' (Φ.op.toPseudofunctor.map f) (Φ.op.toPseudofunctor.map g)
        (Φ.op.toPseudofunctor.map (f ≫ g))
        (LocallyDiscrete.eq_of_hom (Φ.op.toPseudofunctor.mapComp f g).inv) := by
    rw [Pseudofunctor.comp_mapComp, Pseudofunctor.mapComp']
    congr 1
  rw [e]
  exact ZariskiDescent.mapComp'_hom_app _ _ _ _ _ N

/-- The unitor of `Φ.op.toPseudofunctor.comp modulesPseudofunctor` is `pullbackId`, up to the
change of presentation of the identity. -/
private lemma comp_modulesPseudofunctor_mapId_hom_app
    (N : (Φ.op.toPseudofunctor.comp modulesPseudofunctor).obj a) :
    ((Φ.op.toPseudofunctor.comp modulesPseudofunctor).mapId a).hom.toNatTrans.app N =
      (Modules.pullbackCongr (toPseudofunctor_map_id_as_unop Φ (a := a))).hom.app N ≫
        (Modules.pullbackId _).hom.app N := by
  have e : (Φ.op.toPseudofunctor.comp modulesPseudofunctor).mapId a =
      modulesPseudofunctor.mapId' (Φ.op.toPseudofunctor.map (𝟙 a))
        (LocallyDiscrete.eq_of_hom (Φ.op.toPseudofunctor.mapId a).hom) := by
    rw [Pseudofunctor.comp_mapId, Pseudofunctor.mapId']
    congr 1
  rw [e]
  exact modulesPseudofunctor_mapId'_hom_app _ _ _ N

end Compositors

/-! ### Strong transformations into reindexed module sheaves -/

section Lift

variable {D : Type*} [Category* D] {F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{u, u + 1}}
  (Φ : D ⥤ Scheme.{u}) (P : modulesPseudofunctor.{u}.ObjectProperty) [P.IsClosedUnderMapObj]

/-- A strong transformation from `F` to `Φ.op.toPseudofunctor.comp P.fullsubcategory`, from
functors to module sheaves landing in `P` and natural isomorphisms with pullback satisfying the
coherence conditions on module sheaves. -/
private noncomputable def liftStrongTrans
    (T : ∀ a, F.obj a ⥤ (Φ.op.toPseudofunctor.obj a).as.unop.Modules)
    (hT : ∀ a M, P.prop (Φ.op.toPseudofunctor.obj a) ((T a).obj M))
    (ν : ∀ {a b : LocallyDiscrete Dᵒᵖ} (f : a ⟶ b),
      (F.map f).toFunctor ⋙ T b ≅ T a ⋙ Modules.pullback (Φ.op.toPseudofunctor.map f).as.unop)
    (hid : ∀ a, (ν (𝟙 a)).hom ≫ Functor.whiskerLeft (T a)
        ((Modules.pullbackCongr (toPseudofunctor_map_id_as_unop Φ (a := a))).hom ≫
          (Modules.pullbackId _).hom) ≫ (Functor.rightUnitor _).hom =
      Functor.whiskerRight (F.mapId a).hom.toNatTrans (T a) ≫ (Functor.leftUnitor _).hom)
    (hcomp : ∀ {a b c : LocallyDiscrete Dᵒᵖ} (f : a ⟶ b) (g : b ⟶ c),
      (ν (f ≫ g)).hom ≫ Functor.whiskerLeft (T a)
          (Modules.pullbackComp' _ _ _ (toPseudofunctor_map_comp_as_unop Φ f g)).hom =
        Functor.whiskerRight (F.mapComp f g).hom.toNatTrans (T c) ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (F.map f).toFunctor (ν g).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (ν f).hom (Modules.pullback (Φ.op.toPseudofunctor.map g).as.unop) ≫
          (Functor.associator _ _ _).hom) :
    F ⟶ Φ.op.toPseudofunctor.comp P.fullsubcategory where
  app a := Cat.Hom.ofFunctor ((P.prop _).lift (T a) (hT a))
  naturality f := Cat.Hom.isoMk (NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((ν f).app M)) (fun g ↦ by
      apply ObjectProperty.hom_ext
      exact (ν f).hom.naturality g))
  naturality_naturality {_ _ f _} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    simp only [PrelaxFunctor.map₂_id, Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id,
      Category.id_comp, Category.comp_id]
  naturality_id a := by
    ext M : 3
    apply ObjectProperty.hom_ext
    have h := NatTrans.congr_app (hid a) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at h
    refine (ObjectProperty.FullSubcategory.comp_hom _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((comp_fullsubcategory_mapId_hom_app_hom _ _ _ _).trans
      (comp_modulesPseudofunctor_mapId_hom_app Φ _))).trans ?_
    refine h.trans ?_
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
      Cat.rightUnitor_inv_app]
    rfl
  naturality_comp f g := by
    ext M : 3
    apply ObjectProperty.hom_ext
    have h := NatTrans.congr_app (hcomp f g) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp] at h
    refine (ObjectProperty.FullSubcategory.comp_hom _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((comp_fullsubcategory_mapComp_hom_app_hom _ _ _ _ _).trans
      (comp_modulesPseudofunctor_mapComp_hom_app Φ f g _))).trans ?_
    refine h.trans ?_
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      Cat.associator_hom_app, Cat.associator_inv_app]
    rfl

end Lift

/-! ### The tilde construction -/

/-- The tilde construction `R ↦ tildeEquiv`, as a strong transformation from the pseudofunctor of
extension of scalars on `CommRingCatᵒᵖ` to the pseudofunctor of pullback of quasi-coherent
sheaves along `Spec`. Its component at `R` is the functor of `tildeEquiv`, and its naturality
isomorphism at a ring map `φ` is the inverse of `Scheme.Modules.pullbackSpecMapTildeIso φ`. -/
noncomputable def tildeStrongTrans :
    CommRingCat.moduleCatAdjPseudofunctor.{u}.comp Bicategory.Adj.forget₁ ⟶
      Scheme.Spec.op.toPseudofunctor.comp qcohPseudofunctor :=
  liftStrongTrans Scheme.Spec Modules.quasicoherentProperty
    (fun a ↦ tilde.functor a.as.unop.unop)
    (fun a M ↦ ((tildeEquiv (R := a.as.unop.unop)).functor.obj M).property)
    (fun f ↦ Modules.tildeNatIso f.as.unop.unop rfl)
    (fun _ ↦ Modules.tildeNatIso_id rfl _)
    (fun _ _ ↦ Modules.tildeNatIso_comp _ _ rfl rfl rfl _)

@[simp]
lemma tildeStrongTrans_app_toFunctor (R : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    (tildeStrongTrans.app R).toFunctor = (tildeEquiv (R := R.as.unop.unop)).functor :=
  rfl

instance tildeStrongTrans_app_isEquivalence (R : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    (tildeStrongTrans.app R).toFunctor.IsEquivalence :=
  (tildeEquiv (R := R.as.unop.unop)).isEquivalence_functor

end Scheme

end AlgebraicGeometry
