/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
-- Narrowed from `Divisors.Determinant` (2026-08-15). Everything below needs only
-- `Modules.Tensor.Basic`; the single declaration that needed `Determinant` moved to
-- `Divisors.LineBundleDual`, which took `Dual` off `ExteriorPower`'s critical path.
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CoversTop

/-!
# Duals of invertible module sheaves

This file constructs the dual of an invertible module sheaf without assuming an internal-Hom
API for sheaves. On an open `U`, the dual presheaf consists of morphisms from the restriction of
the line sheaf to `U` into the restricted structure sheaf. Evaluation is locally the ordinary
rank-one evaluation isomorphism, so sheafification supplies an explicit tensor inverse.

The main public declarations are `dualPresheaf`, `dualLine`, `tensorDualIso`, and
`dualLine_isInvertible`. `LineBundleData.ofIsInvertible`, which bridges these to the
`LineBundleData` of `Divisors.Determinant`, lives in `Divisors.LineBundleDual`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance dualCategory : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

local instance dualMonoidalCategory : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance dualSymmetricCategory : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private def unitOne (U : X.Opens) (Y : (Over U)ᵒᵖ) :
    (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj Y :=
  show (X.ringCatSheaf.over U).obj.obj Y from
    (1 : Γ(X, Y.unop.left))

private noncomputable def restrictScalar (U : X.Opens) (Y : (Over U)ᵒᵖ)
    (r : Γ(X, U)) : (X.ringCatSheaf.over U).obj.obj Y :=
  (X.ringCatSheaf.over U).obj.map
    (Over.homMk Y.unop.hom).op
    (show (X.ringCatSheaf.over U).obj.obj
      (Opposite.op (Over.mk (𝟙 U))) from r)

@[simp] private lemma restrictScalar_zero (U : X.Opens) (Y : (Over U)ᵒᵖ) :
    restrictScalar U Y 0 = 0 := by
  change (X.presheaf.map Y.unop.hom.op).hom 0 = 0
  exact (X.presheaf.map Y.unop.hom.op).hom.map_zero

@[simp] private lemma restrictScalar_one (U : X.Opens) (Y : (Over U)ᵒᵖ) :
    restrictScalar U Y 1 = 1 := by
  change (X.presheaf.map Y.unop.hom.op).hom 1 = 1
  exact (X.presheaf.map Y.unop.hom.op).hom.map_one

@[simp] private lemma restrictScalar_add (U : X.Opens) (Y : (Over U)ᵒᵖ)
    (r s : Γ(X, U)) : restrictScalar U Y (r + s) =
      restrictScalar U Y r + restrictScalar U Y s := by
  change (X.presheaf.map Y.unop.hom.op).hom (r + s) = _
  exact (X.presheaf.map Y.unop.hom.op).hom.map_add r s

@[simp] private lemma restrictScalar_mul (U : X.Opens) (Y : (Over U)ᵒᵖ)
    (r s : Γ(X, U)) : restrictScalar U Y (r * s) =
      restrictScalar U Y r * restrictScalar U Y s := by
  change (X.presheaf.map Y.unop.hom.op).hom (r * s) = _
  exact (X.presheaf.map Y.unop.hom.op).hom.map_mul r s

private lemma restrictScalar_naturality (U : X.Opens) {Y Z : (Over U)ᵒᵖ}
    (f : Y ⟶ Z) (r : Γ(X, U)) :
    (X.ringCatSheaf.over U).obj.map f (restrictScalar U Y r) =
      restrictScalar U Z r := by
  change (X.presheaf.map (f.unop.left).op).hom
      ((X.presheaf.map Y.unop.hom.op).hom r) =
    (X.presheaf.map Z.unop.hom.op).hom r
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 2

private noncomputable def unitScalarHom (U : X.Opens) (r : Γ(X, U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) where
  val :=
    { app := fun Y ↦ ModuleCat.ofHom
          { toFun := fun x ↦ by
              exact restrictScalar U Y r • x
            map_add' := fun x y ↦ by
              exact smul_add _ _ _
            map_smul' := fun a x ↦ by
              change restrictScalar U Y r • (a • x) =
                a • (restrictScalar U Y r • x)
              rw [smul_smul, smul_smul]
              have hc : restrictScalar U Y r * a =
                  a * restrictScalar U Y r := by
                letI : CommRing ((X.ringCatSheaf.over U).obj.obj Y) :=
                  inferInstanceAs (CommRing Γ(X, Y.unop.left))
                exact mul_comm _ _
              exact congrArg (fun z : (X.ringCatSheaf.over U).obj.obj Y ↦ z • x)
                hc }
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (X.ringCatSheaf.over U).obj.obj Y at x
        change restrictScalar U Z r •
            ((X.ringCatSheaf.over U).obj.map f x) =
          (X.ringCatSheaf.over U).obj.map f
            (restrictScalar U Y r • x)
        change restrictScalar U Z r *
            ((X.ringCatSheaf.over U).obj.map f).hom x =
          ((X.ringCatSheaf.over U).obj.map f).hom
            (restrictScalar U Y r * x)
        calc
          _ = ((X.ringCatSheaf.over U).obj.map f).hom
                (restrictScalar U Y r) *
              ((X.ringCatSheaf.over U).obj.map f).hom x := by
                rw [restrictScalar_naturality]
          _ = _ := (((X.ringCatSheaf.over U).obj.map f).hom.map_mul
            (restrictScalar U Y r) x).symm }

private lemma unitScalarHom_zero (U : X.Opens) :
    unitScalarHom U 0 = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change restrictScalar U Y 0 • x = 0
  simp

private lemma unitScalarHom_add (U : X.Opens) (r s : Γ(X, U)) :
    unitScalarHom U (r + s) = unitScalarHom U r + unitScalarHom U s := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (X.ringCatSheaf.over U).obj.obj Y at x
  change restrictScalar U Y (r + s) • x =
    restrictScalar U Y r • x + restrictScalar U Y s • x
  simp [add_mul]

private lemma unitScalarHom_one (U : X.Opens) :
    unitScalarHom U 1 = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change restrictScalar U Y 1 • x = x
  simp

private lemma unitScalarHom_mul (U : X.Opens) (r s : Γ(X, U)) :
    unitScalarHom U (r * s) = unitScalarHom U s ≫ unitScalarHom U r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (X.ringCatSheaf.over U).obj.obj Y at x
  change restrictScalar U Y (r * s) • x =
    restrictScalar U Y r • (restrictScalar U Y s • x)
  simp [mul_assoc]

private lemma unitScalarHom_of_endomorphism (U : X.Opens)
    (φ : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U)) :
    unitScalarHom U
        (φ.val.app (Opposite.op (Over.mk (𝟙 U)))
          (unitOne U (Opposite.op (Over.mk (𝟙 U))))) = φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (X.ringCatSheaf.over U).obj.obj Y at x
  let f : Opposite.op (Over.mk (𝟙 U)) ⟶ Y :=
    (Over.homMk Y.unop.hom).op
  have h := congrArg
    (fun q ↦ q (unitOne U (Opposite.op (Over.mk (𝟙 U)))))
    (φ.val.naturality f)
  dsimp [unitOne] at h
  change φ.val.app Y ((X.ringCatSheaf.over U).obj.map f
      (unitOne U (Opposite.op (Over.mk (𝟙 U))))) =
    (X.ringCatSheaf.over U).obj.map f
      (φ.val.app (Opposite.op (Over.mk (𝟙 U)))
        (unitOne U (Opposite.op (Over.mk (𝟙 U))))) at h
  have hone : (X.ringCatSheaf.over U).obj.map f
      (unitOne U (Opposite.op (Over.mk (𝟙 U)))) = unitOne U Y := by
    change (X.presheaf.map f.unop.left.op).hom 1 = 1
    exact (X.presheaf.map f.unop.left.op).hom.map_one
  rw [hone] at h
  have hcoeff : restrictScalar U Y
      (φ.val.app (Opposite.op (Over.mk (𝟙 U)))
        (unitOne U (Opposite.op (Over.mk (𝟙 U))))) =
      φ.val.app Y (unitOne U Y) := by
    exact h.symm
  change restrictScalar U Y
      (φ.val.app (Opposite.op (Over.mk (𝟙 U)))
        (unitOne U (Opposite.op (Over.mk (𝟙 U))))) * x =
    φ.val.app Y x
  letI : CommRing ((X.ringCatSheaf.over U).obj.obj Y) :=
    inferInstanceAs (CommRing Γ(X, Y.unop.left))
  rw [hcoeff, mul_comm]
  change x • φ.val.app Y (unitOne U Y) = φ.val.app Y x
  have hlin := (φ.val.app Y).hom.map_smul x (unitOne U Y)
  have hone : x • unitOne U Y = x := by
    change x * 1 = x
    exact mul_one x
  rw [hone] at hlin
  exact hlin.symm

@[reducible] private noncomputable def localDualModule (L : X.Modules) (U : X.Opens) :
    Module Γ(X, U)
      ((L.over U) ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) where
  smul r f := f ≫ unitScalarHom U r
  one_smul f := by
    change f ≫ unitScalarHom U 1 = f
    rw [unitScalarHom_one, Category.comp_id]
  mul_smul r s f := by
    change f ≫ unitScalarHom U (r * s) =
      (f ≫ unitScalarHom U s) ≫ unitScalarHom U r
    rw [unitScalarHom_mul, Category.assoc]
  smul_add r f g := by
    change (f + g) ≫ unitScalarHom U r =
      f ≫ unitScalarHom U r + g ≫ unitScalarHom U r
    exact Preadditive.add_comp _ _ _ _ _ _
  smul_zero r := by
    change (0 : (L.over U) ⟶ _) ≫ unitScalarHom U r = 0
    exact Limits.zero_comp
  add_smul r s f := by
    change f ≫ unitScalarHom U (r + s) =
      f ≫ unitScalarHom U r + f ≫ unitScalarHom U s
    rw [unitScalarHom_add]
    exact Preadditive.comp_add _ _ _ _ _ _
  zero_smul f := by
    change f ≫ unitScalarHom U 0 = 0
    rw [unitScalarHom_zero]
    exact Limits.comp_zero

private noncomputable instance (L : X.Modules) (U : X.Opens) :
    Module Γ(X, U)
      ((L.over U) ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  localDualModule L U

@[reducible] private noncomputable def localDualObj (L : X.Modules)
    (U : X.Opensᵒᵖ) : ModuleCat (X.ringCatSheaf.obj.obj U) := by
  letI : Module (X.ringCatSheaf.obj.obj U)
      ((L.over U.unop) ⟶
        SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :=
    localDualModule L U.unop
  exact ModuleCat.of (X.ringCatSheaf.obj.obj U)
    ((L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop))

private noncomputable def localDualRestrict (L : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (φ : (L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    (L.over V.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over V.unop) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf f.unop).app L).inv ≫
    (SheafOfModules.overMap X.ringCatSheaf f.unop).map φ ≫
    (SheafOfModules.overMapUnitIso f.unop).hom

private lemma localDualRestrict_id (L : X.Modules) (U : X.Opensᵒᵖ)
    (φ : (L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    localDualRestrict L (𝟙 U) φ = φ := by
  rfl

private lemma localDualRestrict_comp (L : X.Modules)
    {U V W : X.Opensᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (φ : (L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    localDualRestrict L (f ≫ g) φ =
      localDualRestrict L g (localDualRestrict L f φ) := by
  rfl

private lemma localDualRestrict_add (L : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (φ ψ : (L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    localDualRestrict L f (φ + ψ) =
      localDualRestrict L f φ + localDualRestrict L f ψ := by
  rfl

private lemma overMap_unitScalarHom {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (r : Γ(X, U.unop)) :
    (SheafOfModules.overMap X.ringCatSheaf f.unop).map
        (unitScalarHom U.unop r) ≫
      (SheafOfModules.overMapUnitIso f.unop).hom =
    (SheafOfModules.overMapUnitIso f.unop).hom ≫
      unitScalarHom V.unop ((X.presheaf.map f).hom r) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [unitScalarHom, restrictScalar]
  have hs :
      (show (X.ringCatSheaf.over V.unop).obj.obj Y from
        restrictScalar U.unop
          (Opposite.op ((Over.map f.unop).obj Y.unop)) r) =
        restrictScalar V.unop Y ((X.presheaf.map f).hom r) := by
    change (X.presheaf.map
        (((Over.map f.unop).obj Y.unop).hom.op)).hom r =
      (X.presheaf.map Y.unop.hom.op).hom
        ((X.presheaf.map f).hom r)
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    congr 2
  exact congrArg
    (fun z : (X.ringCatSheaf.over V.unop).obj.obj Y ↦ z • x) hs

private lemma localDualRestrict_smul (L : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (r : Γ(X, U.unop))
    (φ : (L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    localDualRestrict L f (φ ≫ unitScalarHom U.unop r) =
      localDualRestrict L f φ ≫
        unitScalarHom V.unop ((X.presheaf.map f).hom r) := by
  dsimp only [localDualRestrict]
  rw [Functor.map_comp]
  let A := ((SheafOfModules.overFunctorMap
    X.ringCatSheaf f.unop).app L).inv
  let B := (SheafOfModules.overMap X.ringCatSheaf f.unop).map φ
  let C := (SheafOfModules.overMap X.ringCatSheaf f.unop).map
    (unitScalarHom U.unop r)
  let D := (SheafOfModules.overMapUnitIso
    (R := X.ringCatSheaf) f.unop).hom
  let E := unitScalarHom V.unop ((X.presheaf.map f).hom r)
  change A ≫ ((B ≫ C) ≫ D) = ((A ≫ B) ≫ D) ≫ E
  have hunit : C ≫ D = D ≫ E := overMap_unitScalarHom (X := X) f r
  calc
    A ≫ ((B ≫ C) ≫ D) = A ≫ (B ≫ (C ≫ D)) :=
      congrArg (fun q ↦ A ≫ q) (Category.assoc B C D)
    _ = A ≫ (B ≫ (D ≫ E)) :=
      congrArg (fun q ↦ A ≫ (B ≫ q)) hunit
    _ = ((A ≫ B) ≫ D) ≫ E := by simp only [Category.assoc]

private lemma localDualRestrict_evaluation (L : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (φ : (L.over U.unop) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop))
    (m : L.val.obj U) :
    (localDualRestrict L f φ).val.app
        (Opposite.op (Over.mk (𝟙 V.unop))) (L.val.map f m) =
      (X.presheaf.map f).hom
        (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m) := by
  let Y : (Over U.unop)ᵒᵖ :=
    Opposite.op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop)))
  let g : Opposite.op (Over.mk (𝟙 U.unop)) ⟶ Y :=
    (Over.homMk f.unop).op
  change φ.val.app Y (L.val.map f m) =
    (X.presheaf.map f).hom
      (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m)
  have h := congrArg (fun q ↦ q m) (φ.val.naturality g)
  change φ.val.app Y (L.val.map g.unop.left.op m) =
    (X.presheaf.map g.unop.left.op).hom
      (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m) at h
  have hg : g.unop.left.op = f := Subsingleton.elim _ _
  rw [hg] at h
  exact h


noncomputable def dualPresheaf (L : X.Modules) : X.PresheafOfModules where
  obj U := localDualObj L U
  map {U V} f := by
    let Z := localDualObj L U
    letI : Module (X.ringCatSheaf.obj.obj U) Z :=
      ModuleCat.isModule Z
    letI hV : Module (X.ringCatSheaf.obj.obj V)
        ((L.over V.unop) ⟶
          SheafOfModules.unit (X.ringCatSheaf.over V.unop)) :=
      localDualModule L V.unop
    let Y := ModuleCat.of (X.ringCatSheaf.obj.obj V)
      ((L.over V.unop) ⟶
        SheafOfModules.unit (X.ringCatSheaf.over V.unop))
    exact ModuleCat.ofHom
      (X := Z)
      (Y := (ModuleCat.restrictScalars
        (X.ringCatSheaf.obj.map f).hom).obj Y)
      { toFun := localDualRestrict L f
        map_add' := localDualRestrict_add L f
        map_smul' := by
          intro r φ
          exact localDualRestrict_smul L f r φ }
  map_id U := by
    rfl
  map_comp f g := by
    rfl

private noncomputable def evaluationApp (L : X.Modules) (U : X.Opensᵒᵖ) :
    ((Modules.toPresheafOfModules X).obj L ⊗ dualPresheaf L).obj U ⟶
      (PresheafOfModules.unit X.ringCatSheaf.obj).obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m φ ↦ φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m)
    (by
      intro m m' φ
      exact map_add _ _ _)
    (by
      intro r m φ
      exact (φ.val.app (Opposite.op
        (Over.mk (𝟙 U.unop)))).hom.map_smul r m)
    (by
      intro m φ ψ
      rfl)
    (by
      intro r m φ
      dsimp only [localDualModule]
      change restrictScalar U.unop
          (Opposite.op (Over.mk (𝟙 U.unop))) r •
          φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m =
        r • φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m
      congr 1
      change (X.presheaf.map (𝟙 U)).hom r = r
      simp)

set_option maxHeartbeats 1600000 in
noncomputable def evaluation (L : X.Modules) :
    (Modules.toPresheafOfModules X).obj L ⊗ dualPresheaf L ⟶
      PresheafOfModules.unit X.ringCatSheaf.obj where
  app U := evaluationApp L U
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m φ
    change (localDualRestrict L f φ).val.app
        (Opposite.op (Over.mk (𝟙 V.unop))) (L.val.map f m) =
      (X.presheaf.map f).hom
        (φ.val.app (Opposite.op (Over.mk (𝟙 U.unop))) m)
    exact localDualRestrict_evaluation L f φ m

private noncomputable def dualLinearEquiv (L : X.Modules) (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U) :
    ((L.over U) ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) ≃ₗ[Γ(X, U)]
      Γ(X, U) := by
  letI : Module Γ(X, U)
      ((L.over U) ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    localDualModule L U
  exact
    { toFun := fun φ ↦
        (e.hom ≫ φ).val.app (Opposite.op (Over.mk (𝟙 U)))
          (unitOne U (Opposite.op (Over.mk (𝟙 U))))
      invFun := fun r ↦ e.inv ≫ unitScalarHom U r
      left_inv := by
        intro φ
        change e.inv ≫ unitScalarHom U
          ((e.hom ≫ φ).val.app (Opposite.op (Over.mk (𝟙 U)))
            (unitOne U (Opposite.op (Over.mk (𝟙 U))))) = φ
        rw [unitScalarHom_of_endomorphism U (e.hom ≫ φ)]
        simp
      right_inv := by
        intro r
        simp only [e.hom_inv_id_assoc]
        dsimp [unitScalarHom, unitOne]
        change restrictScalar U (Opposite.op (Over.mk (𝟙 U))) r * 1 = r
        rw [mul_one]
        change (X.presheaf.map (𝟙 (Opposite.op U))).hom r = r
        simp
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro r φ
        change restrictScalar U (Opposite.op (Over.mk (𝟙 U))) r •
            (e.hom ≫ φ).val.app (Opposite.op (Over.mk (𝟙 U)))
              (unitOne U (Opposite.op (Over.mk (𝟙 U)))) =
          r • (e.hom ≫ φ).val.app (Opposite.op (Over.mk (𝟙 U)))
              (unitOne U (Opposite.op (Over.mk (𝟙 U))))
        congr 1
        change (X.presheaf.map (𝟙 (Opposite.op U))).hom r = r
        simp }

private noncomputable def localSectionLinearEquiv (L : X.Modules) (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U) :
    Γ(X, U) ≃ₗ[Γ(X, U)] L.val.obj (Opposite.op U) where
  toFun r := e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
    (show (X.ringCatSheaf.over U).obj.obj
      (Opposite.op (Over.mk (𝟙 U))) from r)
  invFun m := show Γ(X, U) from
    e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m
  left_inv r := by
    have h := congrArg
      (fun f ↦ f.val.app (Opposite.op (Over.mk (𝟙 U)))
        (show (X.ringCatSheaf.over U).obj.obj
          (Opposite.op (Over.mk (𝟙 U))) from r)) e.hom_inv_id
    exact h
  right_inv m := by
    have h := congrArg
      (fun f ↦ f.val.app (Opposite.op (Over.mk (𝟙 U))) m) e.inv_hom_id
    exact h
  map_add' r s := map_add _ _ _
  map_smul' r s :=
    (e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))).hom.map_smul r s

private lemma evaluationApp_eq_of_trivialization (L : X.Modules) (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U) :
    evaluationApp L (Opposite.op U) =
      ((localSectionLinearEquiv L U e).toModuleIso.inv ⊗ₘ
        (dualLinearEquiv L U e).toModuleIso.hom) ≫
        (λ_ (ModuleCat.of Γ(X, U) Γ(X, U))).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m φ
  letI : CommRing (X.ringCatSheaf.obj.obj (Opposite.op U)) :=
    inferInstanceAs (CommRing Γ(X, U))
  change φ.val.app (Opposite.op (Over.mk (𝟙 U))) m =
    (e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m) •
      φ.val.app (Opposite.op (Over.mk (𝟙 U)))
        (e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
          (unitOne U (Opposite.op (Over.mk (𝟙 U)))))
  have hlin := (φ.val.app (Opposite.op (Over.mk (𝟙 U)))).hom.map_smul
    ((e.inv.val.app (Opposite.op (Over.mk (𝟙 U)))) m)
    ((e.hom.val.app (Opposite.op (Over.mk (𝟙 U))))
      (unitOne U (Opposite.op (Over.mk (𝟙 U)))))
  have hm :
      (e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m) •
          e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
            (unitOne U (Opposite.op (Over.mk (𝟙 U)))) = m := by
    have hecomp := congrArg
      (fun f ↦ f.val.app (Opposite.op (Over.mk (𝟙 U))))
      e.inv_hom_id
    have he := congrArg (fun q ↦ q m) hecomp
    change e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
        (e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m) = m at he
    calc
      _ = e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
          ((e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m) •
            unitOne U (Opposite.op (Over.mk (𝟙 U)))) :=
        ((e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))).hom.map_smul _ _).symm
      _ = e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
          (e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m) := by
        congr 1
        change _ * 1 = _
        simp
      _ = m := by
        exact he
  calc
    φ.val.app (Opposite.op (Over.mk (𝟙 U))) m =
        φ.val.app (Opposite.op (Over.mk (𝟙 U)))
          ((e.inv.val.app (Opposite.op (Over.mk (𝟙 U))) m) •
            e.hom.val.app (Opposite.op (Over.mk (𝟙 U)))
              (unitOne U (Opposite.op (Over.mk (𝟙 U))))) :=
      congrArg _ hm.symm
    _ = _ := hlin

private lemma evaluationApp_isIso_of_trivialization (L : X.Modules)
    (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U) :
    IsIso (evaluationApp L (Opposite.op U)) := by
  rw [evaluationApp_eq_of_trivialization L U e]
  infer_instance

private lemma restrictedEvaluation_mem_W (L : X.Modules)
    (q : (show SheafOfModules X.ringCatSheaf from L).LocalGeneratorsData)
    [q.IsLocallyFreeData] (hq : q.IsRankOne) (i : q.I) :
    ((_root_.Opens.grothendieckTopology X).over (q.X i)).W
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.pushforward
          (F := Over.forget (q.X i))
          (𝟙 (X.ringCatSheaf.over (q.X i)).obj)).map
            (evaluation L))) := by
  let t := (PresheafOfModules.pushforward
    (F := Over.forget (q.X i))
    (𝟙 (X.ringCatSheaf.over (q.X i)).obj)).map (evaluation L)
  haveI : IsIso t := by
    rw [← isIso_iff_of_reflects_iso t
      (PresheafOfModules.toPresheaf _), NatTrans.isIso_iff_isIso_app]
    intro Y
    haveI : IsIso (t.app Y) :=
      evaluationApp_isIso_of_trivialization L Y.unop.left
        (q.rankOneTrivializationOver hq i Y.unop.hom)
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (t.app Y)
  exact ((_root_.Opens.grothendieckTopology X).over (q.X i)).W.of_isIso _

private lemma isLocallySurjective_of_coversTop
    {P Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (p : P ⟶ Q)
    {ι : Type*} (Y : ι → X.Opens)
    (hY : (_root_.Opens.grothendieckTopology X).CoversTop Y)
    (h : ∀ i, Presheaf.IsLocallySurjective
      ((_root_.Opens.grothendieckTopology X).over (Y i))
        (Functor.whiskerLeft (Over.forget (Y i)).op p)) :
    Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X) p := by
  let K := _root_.Opens.grothendieckTopology X
  constructor
  intro U s
  apply K.transitive (hY U) (Presheaf.imageSieve p s)
  intro V k hk
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hk
  let Z : Over (Y i) := Over.mk b
  let p' := Functor.whiskerLeft (Over.forget (Y i)).op p
  let s' := Q.map k.op s
  change ToType (((Over.forget (Y i)).op ⋙ Q).obj (.op Z)) at s'
  letI : Presheaf.IsLocallySurjective (K.over (Y i)) p' := h i
  have hcover := Presheaf.imageSieve_mem (K.over (Y i)) p' s'
  rw [GrothendieckTopology.mem_over_iff] at hcover
  change Sieve.overEquiv Z (Presheaf.imageSieve p' s') ∈ K V at hcover
  have heq : Sieve.overEquiv Z (Presheaf.imageSieve p' s') =
      Sieve.pullback k (Presheaf.imageSieve p s) := by
    ext W a
    rw [Sieve.overEquiv_iff]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change p.app (.op W) t = Q.map (a ≫ k).op s
      change p.app (.op W) t = Q.map a.op (Q.map k.op s) at ht
      simpa only [op_comp, Q.map_comp, ConcreteCategory.comp_apply]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change p.app (.op W) t = Q.map a.op (Q.map k.op s)
      rw [op_comp, Q.map_comp] at ht
      change p.app (.op W) t = Q.map a.op (Q.map k.op s) at ht
      exact ht
  rw [heq] at hcover
  exact hcover

private lemma evaluation_mem_W (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    (_root_.Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (evaluation L)) := by
  obtain ⟨q, hq, hrank⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from L)
  letI : q.IsLocallyFreeData := hq
  let K := _root_.Opens.grothendieckTopology X
  let p := (PresheafOfModules.toPresheaf _).map (evaluation L)
  letI : Presheaf.IsLocallyInjective K p := by
    apply Presheaf.isLocallyInjective_of_coversTop p q.X q.coversTop
    intro i
    exact (restrictedEvaluation_mem_W L q hrank i).isLocallyInjective
  letI : Presheaf.IsLocallySurjective K p := by
    apply isLocallySurjective_of_coversTop p q.X q.coversTop
    intro i
    exact (restrictedEvaluation_mem_W L q hrank i).isLocallySurjective
  exact K.W_of_isLocallyBijective p

/-- The dual line sheaf, obtained by sheafifying local morphisms into the
structure sheaf. -/
noncomputable def dualLine (L : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (dualPresheaf L)

private lemma isIso_sheafification_map_evaluation (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (evaluation L)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    ((_root_.Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
  exact evaluation_mem_W L

/-- Evaluation identifies a line sheaf tensored with its sheafified local
dual with the structure sheaf. -/
noncomputable def tensorDualIso (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    tensorObj L (dualLine L) ≅ SheafOfModules.unit X.ringCatSheaf :=
  (@asIso _ _ _ _ (tensorSheafificationComparisonLeft L (dualPresheaf L))
    (isIso_tensorSheafificationComparisonLeft L (dualPresheaf L))).symm ≪≫
    @asIso _ _ _ _
      ((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (evaluation L))
      (isIso_sheafification_map_evaluation L) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit X.ringCatSheaf)

private noncomputable def overUnitIso (U : X.Opens) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (SheafOfModules.unit X.ringCatSheaf).over U :=
  Iso.refl _

private noncomputable def tensorCancelTrivialization
    (L D : X.Modules) (U : X.Opens)
    (eL : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U)
    (h : tensorObj L D ≅ SheafOfModules.unit X.ringCatSheaf) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅ D.over U := by
  letI : MonoidalCategory
      (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let F := PresheafOfModules.pushforward
    (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U).obj)
  let PL := (toPresheafOfModules X).obj L
  let PD := (toPresheafOfModules X).obj D
  let eLP := (SheafOfModules.forget
    (X.ringCatSheaf.over U)).mapIso eL
  let c := overSheafificationComparison (PL ⊗ PD) U
  let dToTensor : D.over U ≅ (tensorObj L D).over U :=
    ((asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit).app (D.over U)).symm ≪≫
      aU.mapIso (λ_ ((D.over U).val)).symm ≪≫
      aU.mapIso (MonoidalCategory.tensorIso eLP (Iso.refl (F.obj PD))) ≪≫
      aU.mapIso (overTensorPresheafIso PL PD U).symm ≪≫
      @asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)
  exact (dToTensor ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso h ≪≫
    (overUnitIso U).symm).symm

/-- The sheafified local dual of an invertible sheaf is invertible. -/
lemma dualLine_isInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from dualLine L) := by
  obtain ⟨q, hq, hrank⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from L)
  letI : q.IsLocallyFreeData := hq
  apply SheafOfModules.IsInvertible.of_trivializations q.X q.coversTop
  intro i
  exact tensorCancelTrivialization L (dualLine L) (q.X i)
    (q.rankOneTrivialization hrank i) (tensorDualIso L)

end

end AlgebraicGeometry.Scheme.Modules
