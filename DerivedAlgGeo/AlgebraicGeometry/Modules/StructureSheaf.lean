/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Presheaf.Sections
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Pullback
import DerivedAlgGeo.Topology.Category.TopCat.Opens.Final
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The structure sheaf as a module

For a scheme `X`, the structure sheaf `𝒪_X = SheafOfModules.unit X.ringCatSheaf` is a
quasi-coherent `𝒪_X`-module, its endomorphisms are its global functions, and pullback fixes it
coherently.

For a morphism of schemes `f : X ⟶ Y`, Mathlib's `SheafOfModules.pullbackObjUnitToUnit` is the
map `f^* 𝒪_Y ⟶ 𝒪_X` adjoint to the ring map `𝒪_Y ⟶ f_* 𝒪_X`. It is an isomorphism, because
inverse image on opens is a final functor (`TopologicalSpace.Opens.map_final`). These maps are
compatible with the unitor `Scheme.Modules.pullbackId` and the compositor
`Scheme.Modules.pullbackComp` of pullback, so that `X ↦ 𝒪_X` is a cartesian section of
quasi-coherent modules.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.endUnitRingEquiv`: `End 𝒪_X ≃+* Γ(X, ⊤)`, `φ ↦ φ(1)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_unit`: the structure sheaf is
  quasi-coherent.
* `AlgebraicGeometry.Scheme.Modules.unit_hom_comm`: endomorphisms of the structure sheaf
  commute.
* `AlgebraicGeometry.Scheme.Modules.pullbackObjUnitToUnit_id`: along the identity, the map
  `f^* 𝒪_Y ⟶ 𝒪_X` is the unitor of pullback.
* `AlgebraicGeometry.Scheme.Modules.pullbackObjUnitToUnit_comp`: along `f ≫ g`, it is the
  compositor of pullback followed by `f^*` of the map along `g` and the map along `f`.

## Implementation notes

The two coherence statements are checked after transposing along the pullback-pushforward
adjunction. The unitor and compositor of pullback are conjugate to those of pushforward
(`Scheme.Modules.conjugateEquiv_pullbackId_hom`, `Scheme.Modules.conjugateEquiv_pullbackComp_inv`),
which are identities on sections, and the transpose of `pullbackObjUnitToUnit` is
`SheafOfModules.unitToPushforwardObjUnit`, whose sections are those of the ring map of the
morphism.

## Tags

module sheaf, structure sheaf, pullback, endomorphism, pseudofunctor, coherence
-/

open CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The transpose of `α.app c ≫ h` along `adj₂` is the transpose of `h` along `adj₁`, followed
by the conjugate of `α`. -/
private lemma homEquiv_conjugateEquiv {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C}
    {d : D} (h : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ h) =
      adj₁.homEquiv c d h ≫ (conjugateEquiv adj₁ adj₂ α).app d := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← unit_conjugateEquiv, Category.assoc, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality]

private lemma homEquiv_pullbackObjUnitToUnit (f : X ⟶ Y) :
    (pullbackPushforwardAdjunction f).homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-! ### Quasi-coherence -/

private lemma isQuasicoherent_unit_spec (R : CommRingCat.{u}) :
    (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent := by
  have : (tilde (ModuleCat.of R R)).IsQuasicoherent := inferInstance
  exact this

/-- The structure sheaf of a scheme is quasi-coherent: it is the pullback of the structure sheaf
of `Spec Γ(X, ⊤)`, which is `tilde Γ(X, ⊤)`. -/
theorem isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  have h := isQuasicoherent_pullback X.toSpecΓ _ (isQuasicoherent_unit_spec Γ(X, ⊤))
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso (SheafOfModules.pullbackObjUnitToUnit X.toSpecΓ.toRingCatSheafHom)) h

/-! ### Endomorphisms -/

/-- The value of an endomorphism of the structure sheaf at a section. -/
private noncomputable abbrev unitApp
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opensᵒᵖ) (x : Γ(X, U.unop)) : Γ(X, U.unop) :=
  (φ.val.app U).hom x

/-- An endomorphism of the structure sheaf is multiplication by its value at `1`. -/
private lemma unitApp_eq
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opensᵒᵖ) (x : Γ(X, U.unop)) :
    unitApp φ U x = x * unitApp φ U 1 := by
  have h := (φ.val.app U).hom.map_smul (x : X.ringCatSheaf.obj.obj U)
    (1 : X.ringCatSheaf.obj.obj U)
  erw [smul_eq_mul, mul_one] at h
  exact h

/-- Endomorphisms of the structure sheaf commute: each one is multiplication by a global
function. -/
theorem unit_hom_comm
    (φ ψ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf) :
    φ ≫ ψ = ψ ≫ φ := by
  apply SheafOfModules.hom_ext
  ext U : 2
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ : ∃ y : Γ(X, U.unop), (y : _) = x := ⟨x, rfl⟩
  change unitApp ψ U (unitApp φ U y) = unitApp φ U (unitApp ψ U y)
  rw [unitApp_eq ψ U (unitApp φ U y), unitApp_eq φ U y, unitApp_eq φ U (unitApp ψ U y),
    unitApp_eq ψ U y]
  ring

variable (X) in
/-- The endomorphisms of the structure sheaf are its global functions: `φ ↦ φ(1)`, with inverse
multiplication by a global function. -/
noncomputable def endUnitRingEquiv :
    End (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) ≃+* Γ(X, ⊤) where
  toEquiv := End.homEquiv.trans ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.trans
    ((SheafOfModules.unit X.ringCatSheaf).val.sectionsEquivOfIsTerminal
      (Limits.isTerminalTop (α := X.Opens))))
  map_mul' φ ψ := by
    change unitApp φ.asHom (op ⊤) (unitApp ψ.asHom (op ⊤) 1) =
      unitApp φ.asHom (op ⊤) 1 * unitApp ψ.asHom (op ⊤) 1
    rw [unitApp_eq φ.asHom]
    exact mul_comm _ _
  map_add' _ _ := rfl

/-- `endUnitRingEquiv` evaluates an endomorphism at the global function `1`. -/
lemma endUnitRingEquiv_apply
    (φ : End (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf)) :
    endUnitRingEquiv X φ = (φ.asHom.val.app (op (⊤ : X.Opens))).hom (1 : Γ(X, ⊤)) :=
  rfl

/-! ### Pullback -/

/-- Along the identity, `SheafOfModules.pullbackObjUnitToUnit` is the unitor of pullback at the
structure sheaf. -/
theorem pullbackObjUnitToUnit_id :
    SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom (𝟙 X)) =
      (pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [homEquiv_pullbackObjUnitToUnit, ← Category.comp_id ((pullbackId X).hom.app _),
    homEquiv_conjugateEquiv Adjunction.id, conjugateEquiv_pullbackId_hom]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rfl

/-- Along a composite `f ≫ g`, `SheafOfModules.pullbackObjUnitToUnit` is the compositor of
pullback, followed by `f^*` of the map along `g` and the map along `f`:
`(f ≫ g)^* 𝒪_Z ≅ f^* g^* 𝒪_Z ⟶ f^* 𝒪_Y ⟶ 𝒪_X`. -/
theorem pullbackObjUnitToUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom =
      (pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        (pullback f).map (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)),
    conjugateEquiv_pullbackComp_inv]
  have h : ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).homEquiv
      _ _ ((pullback f).map (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    have h' : (pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackPushforwardAdjunction f).homEquiv _ _
          ((pullback f).map (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)) =
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
          (pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
      rw [Adjunction.homEquiv_naturality_left, homEquiv_pullbackObjUnitToUnit,
        Adjunction.homEquiv_naturality_right, homEquiv_pullbackObjUnitToUnit]
    rw [Adjunction.comp_homEquiv]
    exact h'
  rw [h, homEquiv_pullbackObjUnitToUnit]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rfl

end AlgebraicGeometry.Scheme.Modules
