/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Variety.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional coherent cohomology data

This file defines the output interface for the projective finiteness theorem independently of
eventual cohomological vanishing. The separation matters mathematically and for the issue graph:

* finite-dimensionality of each `Hⁱ(X, F)` is the content of #29;
* a bound above which the groups vanish is the separate content of #30.

Mathlib currently exposes `Sheaf.H` only as an abelian group. This file constructs its canonical
functorial `k`-linear lift from the central action of global functions and proves the natural
comparison after forgetting scalars. `LinearCohomology` records that lift, while
`FiniteDimensionalCohomology` adds exactly the still-geometric degreewise `Module.Finite`
conclusion. These are structures carrying explicit proof data, not global existence axioms.
-/

universe u v w x

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]

/-- The existing abelian-group-valued degree-`i` cohomology functor on coherent sheaves.

The explicit `HasExt` instance is required by the current `Sheaf.H` API. -/
noncomputable def coherentH (X : Scheme.{u}) (i : ℕ) :
    Coh X ⥤ AddCommGrpCat.{u + 1} := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  exact Coh.ι X ⋙ Scheme.Modules.toSheaf X ⋙
    Sheaf.functorH (Opens.grothendieckTopology X) i

/-- A functorial base-field-linear realization of Mathlib's coherent sheaf cohomology.

The natural comparison rules out an unrelated family of vector spaces with the desired
dimensions: after forgetting scalars these are the actual `Sheaf.H` groups and maps. -/
structure LinearCohomology (X : Variety k) where
  /-- The base-field vector spaces `Hⁱ(X, F)`, functorial in the coherent sheaf `F`. -/
  moduleH : ℕ → Coh X.toScheme ⥤ ModuleCat.{u + 1} k
  /-- Forgetting the vector-space structure recovers derived-functor sheaf cohomology. -/
  comparison : ∀ i,
    moduleH i ⋙ forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1} ≅
      coherentH X.toScheme i

/-- Degreewise finite-dimensional coherent cohomology, with no eventual-vanishing claim.

This is the exact output interface for #29. A later boundedness result can extend it without
re-proving or repackaging the linear comparison. -/
structure FiniteDimensionalCohomology (X : Variety k) extends LinearCohomology X where
  /-- Every coherent cohomology vector space is finite-dimensional. -/
  finite : ∀ (i : ℕ) (F : Coh X.toScheme), Module.Finite k ((moduleH i).obj F)

variable {X : Scheme.{u}}

/-- Multiplication by a global function as an endomorphism of a sheaf of modules. -/
noncomputable def globalSectionSmul (M : X.Modules)
    (r : Γ(X, (⊤ : X.Opens))) : M ⟶ M := by
  apply (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimage
  exact
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun m ↦
            (show X.ringCatSheaf.obj.obj U from
              X.presheaf.map
                (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r) • m
          map_add' := by simp
          map_smul' := by
            intro s m
            simp only [RingHom.id_apply]
            rw [← mul_smul, ← mul_smul]
            apply congrArg (fun z : X.ringCatSheaf.obj.obj U ↦ z • m)
            change (_ : X.presheaf.obj U) * (show X.presheaf.obj U from s) =
              (show X.presheaf.obj U from s) * _
            exact mul_comm _ _ }
      naturality := by
        intro U V f
        ext m
        simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
          ModuleCat.restrictScalars.map_apply]
        let rU : X.ringCatSheaf.obj.obj U :=
          X.presheaf.map
            (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r
        let rV : X.ringCatSheaf.obj.obj V :=
          X.presheaf.map
            (homOfLE (show V.unop ≤ (⊤ : X.Opens) from le_top)).op r
        change rV • (show M.val.obj V from M.val.map f m) =
          M.val.map f (rU • m)
        have hr : rV = X.ringCatSheaf.obj.map f rU := by
          change X.presheaf.map
              (homOfLE (show V.unop ≤ (⊤ : X.Opens) from le_top)).op r =
            X.presheaf.map f
              (X.presheaf.map
                (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r)
          rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
          congr
        rw [hr]
        exact (M.val.map_smul f rU m).symm }

/-- Evaluation of multiplication by a global function on an open set. -/
@[simp]
theorem globalSectionSmul_app (M : X.Modules) (r : Γ(X, (⊤ : X.Opens)))
    (U : X.Opens) (m : Γ(M, U)) :
    ((globalSectionSmul M r).val.app (op U)).hom m =
      (X.presheaf.map
        (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op r) • m := by
  change (((SheafOfModules.forget X.ringCatSheaf).map
    (globalSectionSmul M r)).app (op U)).hom m = _
  simp [globalSectionSmul]
  rfl

/-- The ring action of global functions on a sheaf of modules. -/
noncomputable def globalSectionAction (M : X.Modules) :
    Γ(X, (⊤ : X.Opens)) →+* End M where
  toFun := globalSectionSmul M
  map_one' := by
    change globalSectionSmul M 1 = 𝟙 M
    apply SheafOfModules.hom_ext
    change (globalSectionSmul M 1).val = 𝟙 M.val
    ext U m
    rw [globalSectionSmul_app (U := U.unop)]
    let a : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op 1
    change a • m = m
    have ha : a = 1 := by
      change X.presheaf.map
        (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op 1 = 1
      rw [map_one]
    rw [ha]
    exact one_smul _ _
  map_mul' r s := by
    rw [CategoryTheory.End.mul_def]
    apply SheafOfModules.hom_ext
    change (globalSectionSmul M (r * s)).val =
      (globalSectionSmul M s).val ≫ (globalSectionSmul M r).val
    ext U m
    change ((globalSectionSmul M (r * s)).val.app U).hom m =
      ((globalSectionSmul M r).val.app U).hom
        (((globalSectionSmul M s).val.app U).hom m)
    rw [globalSectionSmul_app (U := U.unop),
      globalSectionSmul_app (U := U.unop),
      globalSectionSmul_app (U := U.unop)]
    let a : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r
    let b : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op s
    let c : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op (r * s)
    change c • m = a • (b • m)
    have hc : c = a * b := by
      change X.presheaf.map
          (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op (r * s) =
        X.presheaf.map
            (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r *
          X.presheaf.map
            (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op s
      rw [map_mul]
    rw [hc, mul_smul]
  map_zero' := by
    change globalSectionSmul M 0 = 0
    apply SheafOfModules.hom_ext
    have hz : (0 : M ⟶ M).val = 0 := by rfl
    rw [hz]
    ext U m
    rw [PresheafOfModules.zero_app]
    rw [globalSectionSmul_app (U := U.unop)]
    let a : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op 0
    change a • m = 0
    have ha : a = 0 := by
      change X.presheaf.map
        (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op 0 = 0
      rw [map_zero]
    rw [ha]
    exact zero_smul _ _
  map_add' r s := by
    change globalSectionSmul M (r + s) =
      globalSectionSmul M r + globalSectionSmul M s
    apply SheafOfModules.hom_ext
    change (globalSectionSmul M (r + s)).val =
      (globalSectionSmul M r).val + (globalSectionSmul M s).val
    ext U m
    rw [PresheafOfModules.add_app]
    change ((globalSectionSmul M (r + s)).val.app U).hom m =
      ((globalSectionSmul M r).val.app U).hom m +
        ((globalSectionSmul M s).val.app U).hom m
    rw [globalSectionSmul_app (U := U.unop),
      globalSectionSmul_app (U := U.unop),
      globalSectionSmul_app (U := U.unop)]
    let a : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r
    let b : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op s
    let c : X.ringCatSheaf.obj.obj U := X.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op (r + s)
    change c • m = a • m + b • m
    have hc : c = a + b := by
      change X.presheaf.map
          (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op (r + s) =
        X.presheaf.map
            (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r +
          X.presheaf.map
            (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op s
      rw [map_add]
    rw [hc, add_smul]

/-- Multiplication by a global function commutes with every morphism of module sheaves. -/
theorem globalSectionSmul_naturality {M N : X.Modules} (f : M ⟶ N)
    (r : Γ(X, (⊤ : X.Opens))) :
    globalSectionSmul M r ≫ f = f ≫ globalSectionSmul N r := by
  apply SheafOfModules.hom_ext
  change (globalSectionSmul M r).val ≫ f.val =
    f.val ≫ (globalSectionSmul N r).val
  ext U m
  change (f.val.app U).hom (((globalSectionSmul M r).val.app U).hom m) =
    ((globalSectionSmul N r).val.app U).hom ((f.val.app U).hom m)
  rw [globalSectionSmul_app (U := U.unop),
    globalSectionSmul_app (U := U.unop)]
  exact (f.val.app U).hom.map_smul _ _

/-- The structure morphism realizes base-field scalars as global functions on a variety. -/
noncomputable def baseFieldToGlobalSections (Y : Variety k) :
    k →+* Γ(Y.toScheme, (⊤ : Y.toScheme.Opens)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    Y.structureMorphism.appTop).hom

/-- The canonical base-field action on a module sheaf over a variety. -/
noncomputable def varietyScalarAction (Y : Variety k)
    (M : Y.toScheme.Modules) : k →+* End M :=
  (globalSectionAction M).comp (baseFieldToGlobalSections Y)

/-- The canonical base-field action is central on morphisms of module sheaves. -/
theorem varietyScalarAction_naturality (Y : Variety k)
    {M N : Y.toScheme.Modules} (f : M ⟶ N) (r : k) :
    varietyScalarAction Y M r ≫ f = f ≫ varietyScalarAction Y N r :=
  globalSectionSmul_naturality f (baseFieldToGlobalSections Y r)

/-- The canonical base-field action on a coherent sheaf. -/
noncomputable def coherentScalarAction (Y : Variety k)
    (F : Coh Y.toScheme) : k →+* End F where
  toFun r := ObjectProperty.homMk
    (varietyScalarAction Y ((Coh.ι Y.toScheme).obj F) r)
  map_one' := by
    apply ObjectProperty.hom_ext
    exact map_one (varietyScalarAction Y ((Coh.ι Y.toScheme).obj F))
  map_mul' r s := by
    apply ObjectProperty.hom_ext
    exact map_mul (varietyScalarAction Y ((Coh.ι Y.toScheme).obj F)) r s
  map_zero' := by
    apply ObjectProperty.hom_ext
    exact map_zero (varietyScalarAction Y ((Coh.ι Y.toScheme).obj F))
  map_add' r s := by
    apply ObjectProperty.hom_ext
    exact map_add (varietyScalarAction Y ((Coh.ι Y.toScheme).obj F)) r s

/-- The canonical base-field action is central on coherent-sheaf morphisms. -/
theorem coherentScalarAction_naturality (Y : Variety k)
    {F G : Coh Y.toScheme} (f : F ⟶ G) (r : k) :
    coherentScalarAction Y F r ≫ f = f ≫ coherentScalarAction Y G r := by
  apply ObjectProperty.hom_ext
  exact varietyScalarAction_naturality Y f.hom r

/-- An additive functor induces a ring homomorphism on endomorphism rings. -/
noncomputable def additiveMapEndRingHom {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{x} D] [Preadditive C] [Preadditive D]
    (H : C ⥤ D) [H.Additive] (A : C) : End A →+* End (H.obj A) where
  __ := H.mapEnd A
  map_zero' := H.map_zero A A
  map_add' _ _ := H.map_add

/-- Endomorphisms of an abelian group in `AddCommGrpCat` are additive-monoid endomorphisms. -/
noncomputable def addCommGrpEndRingHom (A : AddCommGrpCat) :
    End A →+* AddMonoid.End A where
  toFun f := f.hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Derived coherent cohomology is additive. -/
noncomputable instance coherentH_additive (Y : Variety k) (i : ℕ) :
    (coherentH Y.toScheme i).Additive := by
  dsimp [coherentH]
  infer_instance

/-- The base-field action induced on a derived coherent cohomology group. -/
noncomputable def coherentHScalarAction (Y : Variety k) (i : ℕ)
    (F : Coh Y.toScheme) : k →+* AddMonoid.End ((coherentH Y.toScheme i).obj F) :=
  (addCommGrpEndRingHom ((coherentH Y.toScheme i).obj F)).comp
    ((additiveMapEndRingHom (coherentH Y.toScheme i) F).comp
      (coherentScalarAction Y F))

/-- The canonical base-field module structure on a derived coherent cohomology group. -/
@[reducible]
noncomputable def coherentHModule (Y : Variety k) (i : ℕ)
    (F : Coh Y.toScheme) : Module k ((coherentH Y.toScheme i).obj F) :=
  Module.compHom _ (coherentHScalarAction Y i F)

/-- Every derived coherent cohomology map respects the canonical base-field action. -/
theorem coherentH_map_smul (Y : Variety k) (i : ℕ)
    {F G : Coh Y.toScheme} (f : F ⟶ G) (r : k)
    (x : (coherentH Y.toScheme i).obj F) :
    letI := coherentHModule Y i F
    letI := coherentHModule Y i G
    (coherentH Y.toScheme i).map f (r • x) =
      r • (coherentH Y.toScheme i).map f x := by
  let H := coherentH Y.toScheme i
  have h := congrArg H.map (coherentScalarAction_naturality Y f r)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

set_option maxHeartbeats 400000 in
/-- Coherent sheaf cohomology with its canonical functorial base-field module structure. -/
noncomputable def linearCoherentH (Y : Variety k) (i : ℕ) :
    Coh Y.toScheme ⥤ ModuleCat.{u + 1} k where
  obj F := letI := coherentHModule Y i F
    ModuleCat.of k ((coherentH Y.toScheme i).obj F)
  map {F G} f := by
    letI := coherentHModule Y i F
    letI := coherentHModule Y i G
    exact ModuleCat.ofHom
      { toFun := (coherentH Y.toScheme i).map f
        map_add' := by simp
        map_smul' := coherentH_map_smul Y i f }
  map_id F := by
    apply (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).map_injective
    exact (coherentH Y.toScheme i).map_id F
  map_comp f g := by
    apply (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).map_injective
    exact (coherentH Y.toScheme i).map_comp f g

set_option maxHeartbeats 400000 in
/-- Forgetting scalars from `linearCoherentH` recovers Mathlib's derived cohomology functor. -/
noncomputable def linearCoherentHComparison (Y : Variety k) (i : ℕ) :
    linearCoherentH Y i ⋙ forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1} ≅
      coherentH Y.toScheme i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The canonical functorial linear realization of coherent sheaf cohomology on a variety. -/
noncomputable def canonicalLinearCohomology (Y : Variety k) :
    LinearCohomology Y where
  moduleH := linearCoherentH Y
  comparison := linearCoherentHComparison Y

namespace FiniteDimensionalCohomology

variable {X : Variety k}

/-- The dimension of degree-`i` coherent cohomology. -/
noncomputable abbrev dimension (D : FiniteDimensionalCohomology X)
    (F : Coh X.toScheme) (i : ℕ) : ℕ :=
  Module.finrank k ((D.moduleH i).obj F)

/-- Isomorphic coherent sheaves have equal cohomology dimensions in every degree. -/
theorem dimension_iso (D : FiniteDimensionalCohomology X)
    {F G : Coh X.toScheme} (e : F ≅ G) (i : ℕ) :
    D.dimension F i = D.dimension G i :=
  ((D.moduleH i).mapIso e).toLinearEquiv.finrank_eq

end FiniteDimensionalCohomology

end AlgebraicGeometry.Cohomology
