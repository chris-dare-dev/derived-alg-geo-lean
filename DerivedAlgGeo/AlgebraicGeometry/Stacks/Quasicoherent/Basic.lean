/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Preadditive.LeftExact
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Coproducts
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Descent
import DerivedAlgGeo.AlgebraicGeometry.Modules.StructureSheaf
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Colimits
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.FiberProduct
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Yoneda

/-!
# Quasi-coherent sheaves on a stack

Let `S` be a scheme and `𝒳 : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat` a pseudofunctor over the
schemes over `S`, such as the presheaf of a stack in groupoids. A quasi-coherent sheaf on `𝒳`
assigns to every `S`-scheme `T` and object `x ∈ 𝒳(T)` a quasi-coherent `𝒪_T`-module `F_x`, with
coherent isomorphisms `F_{f^* x} ≅ f^* F_x`. It is a strong transformation from `𝒳` to the
pseudofunctor `𝒬_S = Scheme.qcohPseudofunctorOver S` of quasi-coherent modules, and a morphism
is a modification.

## Main definitions

* `AlgebraicGeometry.Scheme.qcohPseudofunctorOver S`: quasi-coherent modules on the schemes
  over `S`, with pullback.
* `AlgebraicGeometry.AlgebraicStack.structureSheaf S`: the structure sheaf, as a global section
  of `Scheme.qcohPseudofunctorOver S`.
* `AlgebraicGeometry.QCoh 𝒳`: quasi-coherent sheaves on `𝒳`.
* `AlgebraicGeometry.QCoh.unit 𝒳`, `AlgebraicGeometry.QCoh.Γ` and
  `AlgebraicGeometry.QCoh.globalFunctions`: the structure sheaf `𝒪_𝒳`, global sections
  `Γ(𝒳, F) = (𝒪_𝒳 ⟶ F)` and the commutative ring `Γ(𝒳, 𝒪_𝒳)`.
* `AlgebraicGeometry.QCoh.pullback g`: pullback along `g : 𝒳 ⟶ 𝒴`, by precomposition, with
  `QCoh.pullbackUnitIso`, `QCoh.pullbackId` and `QCoh.pullbackComp`.
* `AlgebraicGeometry.QCoh.IsPointwiseEpi`: morphisms whose components are epimorphisms.
* `AlgebraicGeometry.QCoh.representableEquiv T`: quasi-coherent sheaves on the representable
  stack of `T` are quasi-coherent modules on `T`, with
  `QCoh.representableGlobalFunctionsEquiv` and the ring map `QCoh.structureMap`.

## Main results

* `QCoh 𝒳` is preadditive, with cokernels and coproducts indexed by `Type u`, all computed
  componentwise. Kernels are not componentwise; see the cokernel instance.
* `AlgebraicGeometry.QCoh.globalFunctions_mul_comm`: global functions commute.

## Implementation notes

The category, preadditive and colimit structures are those of strong transformations into a
`Cat`-valued pseudofunctor: Mathlib's `Pseudofunctor.StrongTrans.homCategory`,
`Pseudofunctor.StrongTrans.preadditive` and `Pseudofunctor.StrongTrans.hasColimitsOfShape`.

`𝒬_S` has fibres in `Cat.{u, u + 1}`, while the stacks of interest have fibres in larger
universes. `QCoh` is stated for `𝒳` with fibres in `Cat.{max u w₁, max (u + 1) w₂}`, against
`𝒬_S` lifted once by `Pseudofunctor.ulift.{w₁, w₂}`. The structure sheaf is lifted with it
(`AlgebraicStack.structureSheafULift`), and the representable stack of `T` is taken in the same
universes.

## References

* [Stacks, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK): Lemma 96.12.2, a presheaf of
  `𝒪_𝒳`-modules is quasi-coherent if and only if it is locally quasi-coherent and its comparison
  maps are isomorphisms.
* [Stacks, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG): Definition 96.11.1,
  quasi-coherent modules on the ringed site `(𝒳_fppf, 𝒪_𝒳)`.
* [Stacks, Tag 077A](https://stacks.math.columbia.edu/tag/077A): Proposition 103.11.1, the
  quasi-coherent pushforward, built with the coherator `Q`.
* J. Alper, D. Halpern-Leistner, J. Heinloth, *Existence of moduli spaces for algebraic stacks*,
  arXiv:1812.01128v5, Remark 7.5: `A_𝒳 := Map(𝒳, A)` for a stack of categories `A`.

## Tags

quasi-coherent sheaf, algebraic stack, cartesian section, strong transformation, structure sheaf
-/

open CategoryTheory Bicategory Limits Opposite
open scoped Pseudofunctor.StrongTrans

universe w₁ w₂ u

namespace AlgebraicGeometry

noncomputable section

/-! ### The quasi-coherent pseudofunctor over a base -/

/-- `𝒬_S`: quasi-coherent module sheaves on the schemes over `S`, with pullback. It is
`Scheme.qcohPseudofunctor` restricted along `Over.forget S`, and stays definitionally that
composite. -/
noncomputable abbrev Scheme.qcohPseudofunctorOver (S : Scheme.{u}) :
    LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  (Over.forget S).op.toPseudofunctor.comp Scheme.qcohPseudofunctor

namespace Scheme.qcohPseudofunctorOver

variable {S : Scheme.{u}}

/-- The compositors of `Scheme.qcohPseudofunctorOver S` are those of pullback of module
sheaves. -/
lemma mapComp_hom_app {a b c : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (M : (Scheme.qcohPseudofunctorOver S).obj a) :
    ((Scheme.qcohPseudofunctorOver S).mapComp f g).hom.toNatTrans.app M =
      ObjectProperty.homMk
        ((Scheme.Modules.pullbackComp g.as.unop.left f.as.unop.left).inv.app M.obj) := by
  simp
  rfl

/-- The unitors of `Scheme.qcohPseudofunctorOver S` are those of pullback of module sheaves. -/
lemma mapId_hom_app {a : LocallyDiscrete (Over S)ᵒᵖ} (M : (Scheme.qcohPseudofunctorOver S).obj a) :
    ((Scheme.qcohPseudofunctorOver S).mapId a).hom.toNatTrans.app M =
      ObjectProperty.homMk ((Scheme.Modules.pullbackId _).hom.app M.obj) := by
  simp
  rfl

/-- The transition functors of `Scheme.qcohPseudofunctorOver S` act on morphisms by pullback. -/
lemma map_map_hom {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b)
    {M N : (Scheme.qcohPseudofunctorOver S).obj a} (φ : M ⟶ N) :
    (((Scheme.qcohPseudofunctorOver S).map f).toFunctor.map φ).hom =
      (Scheme.Modules.pullback f.as.unop.left).map φ.hom :=
  rfl

instance preadditiveObj (a : LocallyDiscrete (Over S)ᵒᵖ) :
    Preadditive ((Scheme.qcohPseudofunctorOver S).obj a) :=
  inferInstanceAs
    (Preadditive (SheafOfModules.isQuasicoherent a.as.unop.left.ringCatSheaf).FullSubcategory)

instance map_additive {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) :
    ((Scheme.qcohPseudofunctorOver S).map f).toFunctor.Additive where
  map_add {_ _ φ ψ} := by
    apply ObjectProperty.hom_ext
    rw [map_map_hom]
    exact (Scheme.Modules.pullback f.as.unop.left).map_add (f := φ.hom) (g := ψ.hom)

/-- The transition functors of `Scheme.qcohPseudofunctorOver S`, followed by the inclusion of
quasi-coherent modules, are the inclusion followed by pullback. -/
lemma map_comp_ι {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) :
    ((Scheme.qcohPseudofunctorOver S).map f).toFunctor ⋙
        (SheafOfModules.isQuasicoherent b.as.unop.left.ringCatSheaf).ι =
      (SheafOfModules.isQuasicoherent a.as.unop.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback f.as.unop.left :=
  rfl

instance hasCokernels_obj (a : LocallyDiscrete (Over S)ᵒᵖ) :
    HasCokernels ((Scheme.qcohPseudofunctorOver S).obj a) :=
  inferInstanceAs
    (HasCokernels (SheafOfModules.isQuasicoherent a.as.unop.left.ringCatSheaf).FullSubcategory)

instance hasCoequalizers_obj (a : LocallyDiscrete (Over S)ᵒᵖ) :
    HasColimitsOfShape WalkingParallelPair ((Scheme.qcohPseudofunctorOver S).obj a) :=
  Preadditive.hasCoequalizers_of_hasCokernels

instance hasCoproductsOfShape_obj (a : LocallyDiscrete (Over S)ᵒᵖ) (ι : Type u) :
    HasColimitsOfShape (Discrete ι) ((Scheme.qcohPseudofunctorOver S).obj a) :=
  quasicoherentSheaves_hasCoproductsOfShape a.as.unop.left ι

instance preservesCoproductsOfShape_map {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b)
    (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) ((Scheme.qcohPseudofunctorOver S).map f).toFunctor := by
  have h₁ := quasicoherentSheavesInclusion_preservesCoproductsOfShape a.as.unop.left ι
  have h₂ : PreservesColimitsOfShape (Discrete ι) (Scheme.Modules.pullback f.as.unop.left) := by
    have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f.as.unop.left) :=
      (Scheme.Modules.pullbackPushforwardAdjunction f.as.unop.left).leftAdjoint_preservesColimits
    infer_instance
  exact @preservesColimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _ _
    (SheafOfModules.isQuasicoherent b.as.unop.left.ringCatSheaf).ι
    (@comp_preservesColimitsOfShape _ _ _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent a.as.unop.left.ringCatSheaf).ι
      (Scheme.Modules.pullback f.as.unop.left) h₁ h₂)
    (quasicoherentSheavesInclusion_reflectsCoproductsOfShape b.as.unop.left ι)

instance preservesCokernel_map {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b)
    {M N : (Scheme.qcohPseudofunctorOver S).obj a} (φ : M ⟶ N) :
    PreservesColimit (parallelPair φ 0) ((Scheme.qcohPseudofunctorOver S).map f).toFunctor := by
  have h₁ := ObjectProperty.preservesCokernels_ι
    (SheafOfModules.isQuasicoherent a.as.unop.left.ringCatSheaf) φ
  have h₂ : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback f.as.unop.left) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f.as.unop.left).leftAdjoint_preservesColimits
  have h₃ : ReflectsColimitsOfSize.{0, 0}
      (SheafOfModules.isQuasicoherent b.as.unop.left.ringCatSheaf).ι :=
    fullyFaithful_reflectsColimits _
  exact @preservesColimit_of_reflects_of_preserves _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.isQuasicoherent b.as.unop.left.ringCatSheaf).ι
    (@comp_preservesColimit _ _ _ _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent a.as.unop.left.ringCatSheaf).ι
      (Scheme.Modules.pullback f.as.unop.left) h₁
      (h₂.preservesColimitsOfShape (J := WalkingParallelPair)).preservesColimit)
    (h₃.reflectsColimitsOfShape (J := WalkingParallelPair)).reflectsColimit

instance hasBinaryBiproducts_obj (a : LocallyDiscrete (Over S)ᵒᵖ) :
    HasBinaryBiproducts ((Scheme.qcohPseudofunctorOver S).obj a) :=
  have : HasColimitsOfShape (Discrete WalkingPair) ((Scheme.qcohPseudofunctorOver S).obj a) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{u})
  HasBinaryBiproducts.of_hasBinaryCoproducts

instance preservesCoequalizers_map {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) :
    PreservesColimitsOfShape WalkingParallelPair
      ((Scheme.qcohPseudofunctorOver S).map f).toFunctor :=
  Functor.preservesCoequalizers_of_preservesCokernels _

end Scheme.qcohPseudofunctorOver

/-! ### The structure sheaf as a global section of `𝒬_S` -/

namespace AlgebraicStack

open Scheme.qcohPseudofunctorOver

variable {S : Scheme.{u}}

/-- The structure sheaf of `T`, as an object of the fibre of `Scheme.qcohPseudofunctorOver S`
over `T`. -/
private noncomputable def unitObj (a : LocallyDiscrete (Over S)ᵒᵖ) :
    (Scheme.qcohPseudofunctorOver S).obj a :=
  ⟨SheafOfModules.unit a.as.unop.left.ringCatSheaf, Scheme.Modules.isQuasicoherent_unit _⟩

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `𝒪_T ≅ f^* 𝒪_{T'}`, the inverse of `SheafOfModules.pullbackObjUnitToUnit`. -/
private noncomputable def unitIso {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) :
    unitObj b ≅
      ((Scheme.qcohPseudofunctorOver S).map f).toFunctor.obj (unitObj a) :=
  ObjectProperty.isoMk _
    (asIso (SheafOfModules.pullbackObjUnitToUnit f.as.unop.left.toRingCatSheafHom)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma unitIso_hom_hom {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) :
    (unitIso f).hom.hom =
      inv (SheafOfModules.pullbackObjUnitToUnit f.as.unop.left.toRingCatSheafHom) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma unitIso_id (a : LocallyDiscrete (Over S)ᵒᵖ) :
    (unitIso (𝟙 a)).hom ≫
      ((Scheme.qcohPseudofunctorOver S).mapId a).hom.toNatTrans.app (unitObj a) =
        𝟙 _ := by
  rw [mapId_hom_app]
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, unitIso_hom_hom,
    IsIso.inv_comp_eq, ObjectProperty.FullSubcategory.id_hom, Category.comp_id]
  exact Scheme.Modules.pullbackObjUnitToUnit_id.symm

set_option backward.isDefEq.respectTransparency false in
private lemma unitIso_comp {a b c : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (unitIso (f ≫ g)).hom ≫
      ((Scheme.qcohPseudofunctorOver S).mapComp f g).hom.toNatTrans.app (unitObj a) =
      (unitIso g).hom ≫ ((Scheme.qcohPseudofunctorOver S).map g).toFunctor.map (unitIso f).hom := by
  rw [mapComp_hom_app]
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, unitIso_hom_hom,
    IsIso.inv_comp_eq, ObjectProperty.FullSubcategory.comp_hom, unitIso_hom_hom, map_map_hom,
    unitIso_hom_hom]
  rw [show SheafOfModules.pullbackObjUnitToUnit (f ≫ g).as.unop.left.toRingCatSheafHom = _ from
    Scheme.Modules.pullbackObjUnitToUnit_comp g.as.unop.left f.as.unop.left]
  simp
  rfl

/-- The components of `structureSheaf`: the constant functor at the structure sheaf. -/
@[simps]
private noncomputable def structureSheafApp (a : LocallyDiscrete (Over S)ᵒᵖ) :
    (Pseudofunctor.terminal (Over S)ᵒᵖ).obj a ⥤ (Scheme.qcohPseudofunctorOver S).obj a where
  obj _ := unitObj a
  map _ := 𝟙 _

/-- The naturality isomorphisms of `structureSheaf`. -/
private noncomputable def structureSheafNaturality {a b : LocallyDiscrete (Over S)ᵒᵖ}
    (f : a ⟶ b) :
    ((Pseudofunctor.terminal (Over S)ᵒᵖ).map f).toFunctor ⋙ structureSheafApp b ≅
      structureSheafApp a ⋙ ((Scheme.qcohPseudofunctorOver S).map f).toFunctor :=
  NatIso.ofComponents (fun _ ↦ unitIso f) (fun _ ↦ by
    simp only [Functor.comp_map, structureSheafApp_map]
    exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans
      (congrArg _ (((Scheme.qcohPseudofunctorOver S).map f).toFunctor.map_id _).symm)))

private lemma structureSheafNaturality_hom_app {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b)
    (x) : (structureSheafNaturality f).hom.app x = (unitIso f).hom :=
  rfl

variable (S) in
set_option backward.isDefEq.respectTransparency false in
/-- `𝒪_S`: the structure sheaf, as a global section of `Scheme.qcohPseudofunctorOver S`. Its
component at `T` is `𝒪_T`, and its naturality isomorphisms `𝒪_{T'} ≅ f^* 𝒪_T` are the inverses
of `SheafOfModules.pullbackObjUnitToUnit`. Their coherence with the unitors and compositors of
pullback is `Scheme.Modules.pullbackObjUnitToUnit_id` and
`Scheme.Modules.pullbackObjUnitToUnit_comp`. -/
noncomputable def structureSheaf :
    Pseudofunctor.terminal (Over S)ᵒᵖ ⟶ Scheme.qcohPseudofunctorOver S where
  app a := (structureSheafApp a).toCatHom
  naturality f := Cat.Hom.isoMk (structureSheafNaturality f)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id a := by
    apply Cat.Hom₂.ext
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_inv_toNatTrans, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Cat.Hom.isoMk_hom, structureSheafApp_map,
      NatTrans.toCatHom₂_toNatTrans, structureSheafNaturality_hom_app,
      Functor.toCatHom_toFunctor, Category.comp_id]
    exact unitIso_id a
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, Functor.associator_hom_app,
      Functor.associator_inv_app, Cat.Hom.isoMk_hom, structureSheafApp_map,
      NatTrans.toCatHom₂_toNatTrans, structureSheafNaturality_hom_app,
      Functor.toCatHom_toFunctor]
    exact unitIso_comp f g

/-- The components of `structureSheaf S` are the structure sheaves. -/
lemma structureSheaf_app_obj_obj (a : LocallyDiscrete (Over S)ᵒᵖ)
    (x : (Pseudofunctor.terminal (Over S)ᵒᵖ).obj a) :
    (((structureSheaf S).app a).toFunctor.obj x).obj =
      SheafOfModules.unit a.as.unop.left.ringCatSheaf :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverses of the naturality isomorphisms of `structureSheaf S` are
`SheafOfModules.pullbackObjUnitToUnit`. -/
lemma structureSheaf_naturality_inv_app_hom {a b : LocallyDiscrete (Over S)ᵒᵖ} (f : a ⟶ b)
    (x : (Pseudofunctor.terminal (Over S)ᵒᵖ).obj a) :
    (((structureSheaf S).naturality f).inv.toNatTrans.app x).hom =
      SheafOfModules.pullbackObjUnitToUnit f.as.unop.left.toRingCatSheafHom :=
  rfl

attribute [local instance] uliftCategory in
/-- The components of `structureSheafULift`. -/
@[simps]
private noncomputable def structureSheafULiftApp (a : LocallyDiscrete (Over S)ᵒᵖ) :
    (Pseudofunctor.terminal (Over S)ᵒᵖ :
      LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{max u w₁, max (u + 1) w₂}).obj a ⥤
      ((Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}).obj a where
  obj _ := (Pseudofunctor.ulift.objEquivalence.{w₁, w₂} (Scheme.qcohPseudofunctorOver S)
    a).functor.obj (unitObj a)
  map _ := 𝟙 _

/-- The naturality isomorphisms of `structureSheafULift`. -/
private noncomputable def structureSheafULiftNaturality {a b : LocallyDiscrete (Over S)ᵒᵖ}
    (f : a ⟶ b) :
    ((Pseudofunctor.terminal (Over S)ᵒᵖ :
      LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{max u w₁, max (u + 1) w₂}).map f).toFunctor ⋙
        structureSheafULiftApp.{w₁, w₂} b ≅
      structureSheafULiftApp a ⋙
        ((Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}.map f).toFunctor :=
  NatIso.ofComponents (fun _ ↦ (Pseudofunctor.ulift.objEquivalence.{w₁, w₂}
      (Scheme.qcohPseudofunctorOver S) b).functor.mapIso (unitIso f))
    (fun _ ↦ by
      simp only [Functor.comp_map, structureSheafULiftApp_map]
      exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans
        (congrArg _ (((Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}.map f).toFunctor.map_id
          _).symm)))

private lemma structureSheafULiftNaturality_hom_app {a b : LocallyDiscrete (Over S)ᵒᵖ}
    (f : a ⟶ b) (x) :
    (structureSheafULiftNaturality.{w₁, w₂} f).hom.app x =
      (Pseudofunctor.ulift.objEquivalence.{w₁, w₂} (Scheme.qcohPseudofunctorOver S) b).functor.map
        (unitIso f).hom :=
  rfl

variable (S) in
/-- `structureSheaf S`, lifted along `Pseudofunctor.ulift` to the fibre universes of `QCoh`:
its components are those of `structureSheaf S` lifted by `Pseudofunctor.ulift.objEquivalence`. -/
noncomputable def structureSheafULift :
    (Pseudofunctor.terminal (Over S)ᵒᵖ :
      LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{max u w₁, max (u + 1) w₂}) ⟶
      (Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂} where
  app a := (structureSheafULiftApp a).toCatHom
  naturality f := Cat.Hom.isoMk (structureSheafULiftNaturality f)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id a := by
    apply Cat.Hom₂.ext
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_inv_toNatTrans, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Cat.Hom.isoMk_hom, structureSheafULiftApp_map,
      NatTrans.toCatHom₂_toNatTrans, structureSheafULiftNaturality_hom_app,
      Functor.toCatHom_toFunctor, Category.comp_id]
    rw [Pseudofunctor.ulift.mapId_hom_app]
    have h := congrArg (Pseudofunctor.ulift.objEquivalence.{w₁, w₂}
      (Scheme.qcohPseudofunctorOver S) a).functor.map (unitIso_id a)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h.trans (Category.id_comp _).symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, Functor.associator_hom_app,
      Functor.associator_inv_app, Cat.Hom.isoMk_hom, structureSheafULiftApp_map,
      NatTrans.toCatHom₂_toNatTrans, structureSheafULiftNaturality_hom_app,
      Functor.toCatHom_toFunctor, Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp,
      Category.comp_id]
    rw [← Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.ulift.mapComp'_hom_app,
      Pseudofunctor.mapComp'_eq_mapComp]
    have h := congrArg (Pseudofunctor.ulift.objEquivalence.{w₁, w₂}
      (Scheme.qcohPseudofunctorOver S) _).functor.map (unitIso_comp f g)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h.trans (Category.id_comp _).symm

attribute [local instance] uliftCategory in
/-- Endomorphisms of the lifted structure sheaf commute: they are lifts of endomorphisms of
`𝒪_T`. -/
private lemma structureSheafULift_comm (a : LocallyDiscrete (Over S)ᵒᵖ)
    (φ ψ : (Pseudofunctor.ulift.objEquivalence.{w₁, w₂} (Scheme.qcohPseudofunctorOver S)
        a).functor.obj (unitObj a) ⟶
      (Pseudofunctor.ulift.objEquivalence.{w₁, w₂} (Scheme.qcohPseudofunctorOver S)
        a).functor.obj (unitObj a)) :
    φ ≫ ψ = ψ ≫ φ := by
  apply (Pseudofunctor.ulift.objEquivalence.{w₁, w₂} (Scheme.qcohPseudofunctorOver S)
    a).inverse.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply ObjectProperty.hom_ext
  exact Scheme.Modules.unit_hom_comm _ _

end AlgebraicStack

/-! ### Quasi-coherent sheaves on a stack -/

variable {S : Scheme.{u}}

/-- Quasi-coherent sheaves on `𝒳`: strong transformations from `𝒳` to the quasi-coherent
pseudofunctor `Scheme.qcohPseudofunctorOver S`, lifted to the fibre universes of `𝒳`, with
modifications as morphisms. An object assigns to every `S`-scheme `T` and `x ∈ 𝒳(T)` a
quasi-coherent `𝒪_T`-module, together with coherent isomorphisms along every morphism of
`S`-schemes: a cartesian section of quasi-coherent modules over `𝒳`.

This is the cartesian description of Stacks 06WK (Lemma 96.12.2), which characterizes the
quasi-coherent modules on a category fibred in groupoids over `(Sch/S)_fppf` by quasi-coherent
restrictions with invertible comparison maps; the comparison with that category is not
formalized here. It is also the construction `A_𝒳 := Map(𝒳, A)` of Alper, Halpern-Leistner and
Heinloth (arXiv:1812.01128v5, Remark 7.5), with the stack of quasi-coherent modules for `A`.

Stacks' own definition (06WG, Definition 96.11.1), quasi-coherent modules on the big ringed site
`(𝒳_fppf, 𝒪_𝒳)`, is not used: it needs a second site built from `𝒳`, and the quasi-coherent
pushforward of 077A (Proposition 103.11.1) composes the big-site pushforward with the coherator
`Q`. Nothing here assumes that `𝒳` is a stack or algebraic.

Conventions: the base is a scheme `S`, and test objects are `T : Over S`; absolute stacks are the
case `S = Spec ℤ`, which is terminal. The fibres of `𝒳` lie in `Cat.{max u w₁, max (u + 1) w₂}`,
and `Scheme.qcohPseudofunctorOver S` is lifted to them once, by `Pseudofunctor.ulift.{w₁, w₂}`;
a consumer never lifts it again. -/
def QCoh (𝒳 : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{max u w₁, max (u + 1) w₂}) : Type _ :=
  𝒳 ⟶ (Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}

namespace QCoh

variable (𝒳 : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{max u w₁, max (u + 1) w₂})

/-- Morphisms of quasi-coherent sheaves are modifications: the category structure is Mathlib's
`Pseudofunctor.StrongTrans.homCategory`. -/
instance : Category (QCoh 𝒳) :=
  inferInstanceAs (Category (𝒳 ⟶ (Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}))

/-- Morphisms of quasi-coherent sheaves are added componentwise
(`Pseudofunctor.StrongTrans.preadditive`). -/
instance : Preadditive (QCoh 𝒳) :=
  inferInstanceAs (Preadditive (𝒳 ⟶ (Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}))

/-- Coproducts indexed by `ι : Type u` are computed componentwise
(`Pseudofunctor.StrongTrans.hasColimitsOfShape`): pullback of module sheaves preserves
coproducts, and quasi-coherent modules are closed under them. -/
instance (ι : Type u) : HasCoproductsOfShape ι (QCoh 𝒳) :=
  inferInstanceAs (HasColimitsOfShape (Discrete ι)
    (𝒳 ⟶ (Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}))

/-- Cokernels are computed componentwise (`Pseudofunctor.StrongTrans.hasColimitsOfShape`):
pullback of module sheaves is right exact, and quasi-coherent modules are closed under
cokernels.

Kernels are *not* componentwise, because pullback is only right exact. Over the representable
stack of `𝔸¹ = Spec k[t]`, multiplication by `t` on the structure sheaf has kernel `0` at the
identity point, while its pullback to the origin `Spec k ⟶ 𝔸¹` is multiplication by `0` on `k`,
with kernel `k`. So no `HasKernels` or `Abelian` instance is declared here; abelianness for
algebraic stacks comes from descent along an atlas. -/
instance : HasCokernels (QCoh 𝒳) :=
  have : HasColimitsOfShape WalkingParallelPair (QCoh 𝒳) :=
    inferInstanceAs (HasColimitsOfShape WalkingParallelPair
      (𝒳 ⟶ (Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}))
  ⟨fun _ ↦ inferInstance⟩

/-- `𝒪_𝒳`, the structure sheaf of `𝒳`: the unique map to the terminal pseudofunctor followed by
the lifted structure sheaf `AlgebraicStack.structureSheafULift S`. -/
noncomputable def unit : QCoh 𝒳 :=
  Pseudofunctor.toTerminal 𝒳 ≫ AlgebraicStack.structureSheafULift.{w₁, w₂} S

/-- Global sections `Γ(𝒳, F) := (𝒪_𝒳 ⟶ F)`.

It is a `def`, not an `abbrev`: `Γ 𝒳 F` is a module over `globalFunctions 𝒳` acting by
precomposition, and for `F = unit 𝒳` Mathlib's `Preadditive.moduleEndRight` would otherwise
supply a second action, by postcomposition. -/
def Γ (F : QCoh 𝒳) : Type _ :=
  unit 𝒳 ⟶ F

instance (F : QCoh 𝒳) : AddCommGroup (Γ 𝒳 F) :=
  inferInstanceAs (AddCommGroup (unit 𝒳 ⟶ F))

/-- `Γ(𝒳, 𝒪_𝒳)`, the ring of global functions of `𝒳`. It lives above `Type u`: a modification
is indexed by every `S`-scheme. -/
abbrev globalFunctions : Type _ :=
  End (unit 𝒳)

/-- Global functions commute: at every `x ∈ 𝒳(T)` they are endomorphisms of `𝒪_T`. -/
theorem globalFunctions_mul_comm (a b : globalFunctions 𝒳) : a * b = b * a := by
  refine End.ext (Pseudofunctor.StrongTrans.hom_ext' fun T ↦ NatTrans.ext (funext fun x ↦ ?_))
  exact AlgebraicStack.structureSheafULift_comm T _ _

noncomputable instance : CommRing (globalFunctions 𝒳) :=
  { (inferInstance : Ring (End (unit 𝒳))) with mul_comm := globalFunctions_mul_comm 𝒳 }

/-- Global functions act on global sections by precomposition. -/
noncomputable instance (F : QCoh 𝒳) : Module (globalFunctions 𝒳) (Γ 𝒳 F) where
  smul a s := a.asHom ≫ s
  one_smul _ := Category.id_comp _
  mul_smul a b s := by
    change (a * b).asHom ≫ s = a.asHom ≫ b.asHom ≫ s
    rw [globalFunctions_mul_comm, End.mul_asHom]
    exact Category.assoc _ _ _
  smul_zero _ := Limits.comp_zero
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp

/-- The action of global functions on global sections is precomposition. -/
lemma smul_def {F : QCoh 𝒳} (a : globalFunctions 𝒳) (s : Γ 𝒳 F) :
    a • s = (a.asHom ≫ s : unit 𝒳 ⟶ F) :=
  rfl

/-! ### Pullback -/

variable {𝒳} {𝒴 𝒵 : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{max u w₁, max (u + 1) w₂}}

/-- Pullback along `g : 𝒳 ⟶ 𝒴` is precomposition with `g` (`Bicategory.precomp`). -/
def pullback (g : 𝒳 ⟶ 𝒴) : QCoh 𝒴 ⥤ QCoh 𝒳 :=
  Bicategory.precomp ((Scheme.qcohPseudofunctorOver S).ulift.{w₁, w₂}) g

/-- Pullback along `g` sends `F` to `g ≫ F`. -/
@[simp]
lemma pullback_obj (g : 𝒳 ⟶ 𝒴) (F : QCoh 𝒴) : (pullback g).obj F = (g ≫ F : 𝒳 ⟶ _) :=
  rfl

/-- The components of the pullback of a morphism are those of the morphism, at the images under
`g`. -/
lemma pullback_map_as_app_toNatTrans_app (g : 𝒳 ⟶ 𝒴) {F G : QCoh 𝒴} (p : F ⟶ G)
    (a : LocallyDiscrete (Over S)ᵒᵖ) (x : 𝒳.obj a) :
    (((pullback g).map p).as.app a).toNatTrans.app x =
      (p.as.app a).toNatTrans.app ((g.app a).toFunctor.obj x) :=
  rfl

instance (g : 𝒳 ⟶ 𝒴) : (pullback g).Additive where
  map_add := rfl

/-- Pullback along the identity is the identity: the left unitor of the bicategory of
pseudofunctors. -/
def pullbackId : pullback (𝟙 𝒳) ≅ 𝟭 (QCoh 𝒳) :=
  NatIso.ofComponents (fun F ↦ λ_ (F : 𝒳 ⟶ _)) (fun p ↦ leftUnitor_naturality p)

/-- Pullback along a composite is the composite of the pullbacks: the associator of the
bicategory of pseudofunctors. -/
def pullbackComp (g : 𝒳 ⟶ 𝒴) (h : 𝒴 ⟶ 𝒵) : pullback (g ≫ h) ≅ pullback h ⋙ pullback g :=
  NatIso.ofComponents (fun F ↦ α_ g h (F : 𝒵 ⟶ _)) (fun p ↦ associator_naturality_right g h p)

/-- Any two strong transformations to the terminal pseudofunctor are isomorphic: the fibres of
the terminal pseudofunctor are terminal categories. -/
private def toTerminalIso (g : 𝒳 ⟶ 𝒴) :
    g ≫ Pseudofunctor.toTerminal 𝒴 ≅ Pseudofunctor.toTerminal 𝒳 :=
  Pseudofunctor.StrongTrans.isoMk
    (fun a ↦ eqToIso (Cat.chosenTerminalIsTerminal.hom_ext _ _)) (fun f ↦ by
      ext x
      rfl)

/-- Pullback sends the structure sheaf to the structure sheaf. -/
def pullbackUnitIso (g : 𝒳 ⟶ 𝒴) : (pullback g).obj (unit 𝒴) ≅ unit 𝒳 :=
  (α_ g (Pseudofunctor.toTerminal 𝒴) (AlgebraicStack.structureSheafULift.{w₁, w₂} S)).symm ≪≫
    whiskerRightIso (toTerminalIso g) _

/-! ### Pointwise epimorphisms -/

/-- A morphism of quasi-coherent sheaves is a pointwise epimorphism when its component at every
object `x ∈ 𝒳(T)` is an epimorphism. -/
def IsPointwiseEpi {F G : QCoh 𝒳} (p : F ⟶ G) : Prop :=
  ∀ (a : LocallyDiscrete (Over S)ᵒᵖ) (x : 𝒳.obj a), Epi ((p.as.app a).toNatTrans.app x)

/-- Pullback preserves pointwise epimorphisms. -/
lemma IsPointwiseEpi.pullback (g : 𝒳 ⟶ 𝒴) {F G : QCoh 𝒴} {p : F ⟶ G}
    (hp : IsPointwiseEpi p) : IsPointwiseEpi ((QCoh.pullback g).map p) :=
  fun a x ↦ hp a ((g.app a).toFunctor.obj x)

/-! ### Global functions -/

/-- Pullback of global functions along `g : 𝒳 ⟶ 𝒴`: pull back an endomorphism of `𝒪_𝒴` and
identify `g^* 𝒪_𝒴` with `𝒪_𝒳` by `pullbackUnitIso`. -/
def globalFunctionsMap (g : 𝒳 ⟶ 𝒴) : globalFunctions 𝒴 →+* globalFunctions 𝒳 :=
  { ((pullbackUnitIso g).conj.toMonoidHom.comp (Functor.mapEnd (unit 𝒴) (pullback g))) with
    map_zero' := End.ext (by
      change (pullbackUnitIso g).inv ≫ (pullback g).map 0 ≫ (pullbackUnitIso g).hom = 0
      rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero])
    map_add' a b := End.ext (by
      change (pullbackUnitIso g).inv ≫ (pullback g).map (a.asHom + b.asHom) ≫
        (pullbackUnitIso g).hom = (pullbackUnitIso g).inv ≫ (pullback g).map a.asHom ≫
          (pullbackUnitIso g).hom + (pullbackUnitIso g).inv ≫ (pullback g).map b.asHom ≫
            (pullbackUnitIso g).hom
      rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]) }

/-! ### Representable stacks -/

/-- Quasi-coherent sheaves on the representable stack of `T` are quasi-coherent sheaves on `T`:
evaluation at the universal point `𝟙 T`, the 2-Yoneda equivalence
`Pseudofunctor.yonedaEquivalence`, followed by `Pseudofunctor.ulift.objEquivalence`. The
representable stack is taken in the fibre universes of `QCoh`. -/
def representableEquiv (T : Over S) :
    QCoh (Pseudofunctor.representable.{w₁, max (u + 1) w₂} T) ≌
      (SheafOfModules.isQuasicoherent T.left.ringCatSheaf).FullSubcategory :=
  (Pseudofunctor.yonedaEquivalence _ T).trans (Pseudofunctor.ulift.objEquivalence _ _).symm

/-- `representableEquiv` is additive: the preadditive structure of `QCoh` on a representable
stack is the one of quasi-coherent modules on the scheme. -/
instance (T : Over S) : (representableEquiv.{w₁, w₂} T).functor.Additive where
  map_add := rfl

/-- `representableEquiv` sends the structure sheaf to the structure sheaf. -/
def representableEquivUnitIso (T : Over S) :
    (representableEquiv.{w₁, w₂} T).functor.obj (unit _) ≅
      ⟨SheafOfModules.unit T.left.ringCatSheaf, Scheme.Modules.isQuasicoherent_unit _⟩ :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Endomorphisms of the structure sheaf in the fibre of `Scheme.qcohPseudofunctorOver S` over
`T` are the global functions of `T`. -/
private def endUnitObjRingEquiv (a : LocallyDiscrete (Over S)ᵒᵖ) :
    End (AlgebraicStack.unitObj a) ≃+* Γ(a.as.unop.left, ⊤) :=
  RingEquiv.trans
    { toFun φ := .of φ.asHom.hom
      invFun φ := .of (ObjectProperty.homMk φ.asHom)
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
    (Scheme.Modules.endUnitRingEquiv a.as.unop.left)

/-- The global functions of the representable stack of `T` are the global functions of `T`. The
two rings live in different universes, so they are compared by a ring isomorphism. -/
def representableGlobalFunctionsEquiv (T : Over S) :
    globalFunctions (Pseudofunctor.representable.{w₁, max (u + 1) w₂} T) ≃+* Γ(T.left, ⊤) :=
  (({ (representableEquiv.{w₁, w₂} T).fullyFaithfulFunctor.mulEquivEnd (unit _) with
      map_add' := fun _ _ ↦ End.ext ((representableEquiv.{w₁, w₂} T).functor.map_add) } :
        globalFunctions _ ≃+* End ((representableEquiv.{w₁, w₂} T).functor.obj (unit _))).trans
      (endUnitObjRingEquiv (.mk (op T))))

/-- The ring map `Γ(T, 𝒪_T) → Γ(𝒳, 𝒪_𝒳)` induced by a morphism `q : 𝒳 ⟶ h_T` to the
representable stack of `T`. -/
def structureMap {T : Over S} (q : 𝒳 ⟶ Pseudofunctor.representable.{w₁, max (u + 1) w₂} T) :
    Γ(T.left, ⊤) →+* globalFunctions 𝒳 :=
  (globalFunctionsMap q).comp (representableGlobalFunctionsEquiv T).symm.toRingHom

end QCoh

end

end AlgebraicGeometry
