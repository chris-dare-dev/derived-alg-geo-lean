/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.ModuleObject.Tensor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Module objects of `ModuleCat k`

An `R`-module object of `ModuleCat k` is a `k`-module with a `k`-algebra map from `R` to its
endomorphisms, that is, an `R`-module. This file makes the identification an equivalence
`ModuleObject.moduleCatEquiv : ModuleObject k (ModuleCat k) R ≌ ModuleCat R`, which is
`R`-linear and compatible with restriction and extension of scalars.

## Main definitions

* `ModuleObject.ofModule M`: an `R`-module `M` as an `R`-module object of `ModuleCat k`.
* `ModuleObject.toModule E`: the `R`-module underlying an `R`-module object of `ModuleCat k`.
* `ModuleObject.moduleCatEquiv`: the equivalence `ModuleObject k (ModuleCat k) R ≌ ModuleCat R`.
* `ModuleObject.restrictModuleCatIso`: restriction of module objects along `φ` corresponds to
  `ModuleCat.restrictScalars φ`.
* `ModuleObject.extendModuleCatIso`: base change of module objects along `φ` corresponds to
  `ModuleCat.extendScalars φ`.

## References

* [AHLH] J. Alper, D. Halpern-Leistner, J. Heinloth, *Existence of moduli spaces for algebraic
  stacks*, arXiv:1812.01128v5, §7.1.
-/

universe u w u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

namespace ModuleObject

variable {k : Type u} [CommRing k] {R : Type u₁} [CommRing R] [Algebra k R]

section OfModule

variable (M : ModuleCat.{w} R)

/-- An `R`-module as an `R`-module object of `ModuleCat k`: its restriction to `k`, with `R`
acting by scalar multiplication. -/
noncomputable def ofModule : ModuleObject k (ModuleCat.{w} k) R where
  obj := (ModuleCat.restrictScalars (algebraMap k R)).obj M
  act :=
    { toFun r := .of ((ModuleCat.restrictScalars (algebraMap k R)).map (r • 𝟙 M))
      map_one' := by ext : 1; simp
      map_mul' r s := by
        ext : 1
        simp [← Functor.map_comp, smul_smul]
      map_zero' := by ext : 1; simp
      map_add' r s := by ext : 1; simp [add_smul]
      commutes' c := by
        ext x
        change algebraMap k R c • x = ModuleCat.Hom.hom
          (algebraMap k (End ((ModuleCat.restrictScalars (algebraMap k R)).obj M)) c).asHom x
        rw [Algebra.algebraMap_eq_smul_one (A := End _) c]
        rfl }

@[simp]
lemma ofModule_act_asHom_apply (r : R) (x : M) :
    ((ofModule (k := k) M).act r).asHom.hom x = r • x :=
  rfl

end OfModule

section ToModule

variable (E : ModuleObject k (ModuleCat.{w} k) R)

/-- The `R`-module underlying an `R`-module object of `ModuleCat k`: `r` acts through
`E.act r`. -/
noncomputable def toModule : ModuleCat.{w} R :=
  letI : Module R E.obj := Module.compHom E.obj
    ((ModuleCat.endRingEquiv E.obj).toRingHom.comp E.act.toRingHom)
  ModuleCat.of R E.obj

lemma toModule_smul (r : R) (x : E.toModule) :
    r • x = ((E.act r).asHom.hom x : E.obj) :=
  rfl

end ToModule

section Equivalence

variable (k R)

/-- The `R`-module underlying an `R`-module object of `ModuleCat k`, as a functor. -/
noncomputable def toModuleFunctor : ModuleObject k (ModuleCat.{w} k) R ⥤ ModuleCat.{w} R where
  obj E := E.toModule
  map {E F} f := ConcreteCategory.ofHom (C := ModuleCat.{w} R) (X := E.toModule) (Y := F.toModule)
    { toFun x := f.hom.hom x
      map_add' := f.hom.hom.map_add
      map_smul' r x := congr(ModuleCat.Hom.hom $(f.comm r) x) }

/-- `R`-modules as `R`-module objects of `ModuleCat k`, as a functor. -/
noncomputable def ofModuleFunctor : ModuleCat.{w} R ⥤ ModuleObject k (ModuleCat.{w} k) R where
  obj M := ofModule M
  map {M N} g := ⟨(ModuleCat.restrictScalars (algebraMap k R)).map g, fun r => by
    change (ModuleCat.restrictScalars (algebraMap k R)).map (r • 𝟙 M) ≫ _ =
      _ ≫ (ModuleCat.restrictScalars (algebraMap k R)).map (r • 𝟙 N)
    simp [← Functor.map_comp]⟩
  map_id M := by ext : 1; exact (ModuleCat.restrictScalars (algebraMap k R)).map_id M
  map_comp f g := by ext : 1; exact (ModuleCat.restrictScalars (algebraMap k R)).map_comp f g

lemma act_algebraMap_hom_apply (E : ModuleObject k (ModuleCat.{w} k) R) (c : k) (x : E.obj) :
    (E.act (algebraMap k R c)).asHom.hom x = c • x := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rfl

/-- The identity of the carrier of an `R`-module object `E` of `ModuleCat k`, as an isomorphism
between `E.obj` and the restriction to `k` of the `R`-module `E.toModule`. -/
noncomputable def objIsoRestrictToModule (E : ModuleObject k (ModuleCat.{w} k) R) :
    E.obj ≅ (ModuleCat.restrictScalars (algebraMap k R)).obj E.toModule where
  hom := ConcreteCategory.ofHom (C := ModuleCat.{w} k) (X := E.obj)
    (Y := (ModuleCat.restrictScalars (algebraMap k R)).obj E.toModule)
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' c x := (act_algebraMap_hom_apply k R E c x).symm }
  inv := ConcreteCategory.ofHom (C := ModuleCat.{w} k)
    (X := (ModuleCat.restrictScalars (algebraMap k R)).obj E.toModule) (Y := E.obj)
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' c x := act_algebraMap_hom_apply k R E c x }

/-- `R`-module objects of `ModuleCat k` are `R`-modules. -/
noncomputable def moduleCatEquiv : ModuleObject k (ModuleCat.{w} k) R ≌ ModuleCat.{w} R where
  functor := toModuleFunctor k R
  inverse := ofModuleFunctor k R
  unitIso := NatIso.ofComponents
    (fun E => isoMk (objIsoRestrictToModule k R E) fun _ => rfl) fun _ => rfl
  counitIso := NatIso.ofComponents
    (fun M => (LinearEquiv.refl R M).toModuleIso) fun _ => rfl
  functor_unitIso_comp _ := rfl

variable {k R}

@[simp]
lemma moduleCatEquiv_functor_map_hom_apply {E F : ModuleObject k (ModuleCat.{w} k) R}
    (f : E ⟶ F) (x : E.toModule) :
    ((moduleCatEquiv k R).functor.map f).hom x = f.hom.hom x :=
  rfl

/-- `moduleCatEquiv` is `R`-linear. -/
instance : (moduleCatEquiv k R).functor.Linear R where
  map_smul {E F} f r := by
    ext x
    exact congr(ModuleCat.Hom.hom $(f.comm r) x)

/-- The `R`-linear structure of `ModuleObject k (ModuleCat k) R` agrees with the one of
`ModuleCat R` along `moduleCatEquiv`. -/
example {E F : ModuleObject k (ModuleCat.{w} k) R} (r : R) (f : E ⟶ F) (x : E.toModule) :
    ((moduleCatEquiv k R).functor.map (r • f)).hom x =
      r • ((moduleCatEquiv k R).functor.map f).hom x :=
  congr(ModuleCat.Hom.hom $(f.comm r) x)

end Equivalence

section Restrict

variable {R₁ : Type u₁} {R₂ : Type u₂} [CommRing R₁] [CommRing R₂] [Algebra k R₁] [Algebra k R₂]
  (φ : R₁ →ₐ[k] R₂)

/-- Restriction of module objects of `ModuleCat k` along `φ` is `ModuleCat.restrictScalars φ`. -/
noncomputable def restrictModuleCatIso :
    restrict φ ⋙ (moduleCatEquiv k R₁).functor ≅
      (moduleCatEquiv k R₂).functor ⋙ ModuleCat.restrictScalars.{w} (φ : R₁ →+* R₂) :=
  NatIso.ofComponents (fun E =>
    { hom := ConcreteCategory.ofHom (C := ModuleCat.{w} R₁) (X := ((restrict φ).obj E).toModule)
        (Y := (ModuleCat.restrictScalars (φ : R₁ →+* R₂)).obj E.toModule)
        { toFun x := x
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      inv := ConcreteCategory.ofHom (C := ModuleCat.{w} R₁)
        (X := (ModuleCat.restrictScalars (φ : R₁ →+* R₂)).obj E.toModule)
        (Y := ((restrict φ).obj E).toModule)
        { toFun x := x
          map_add' _ _ := rfl
          map_smul' _ _ := rfl } }) fun _ => rfl

end Restrict

section Extend

variable {R₁ R₂ : Type w} [CommRing R₁] [CommRing R₂] [Algebra k R₁] [Algebra k R₂]
  (φ : R₁ →ₐ[k] R₂)

/-- The right adjoints of `extendModuleCatIso`: `ModuleCat.restrictScalars φ` corresponds to
restriction of module objects. -/
noncomputable def restrictScalarsCompInverseIso :
    ModuleCat.restrictScalars.{w} (φ : R₁ →+* R₂) ⋙ (moduleCatEquiv k R₁).inverse ≅
      (moduleCatEquiv k R₂).inverse ⋙ restrict φ :=
  (Functor.isoWhiskerLeft (moduleCatEquiv k R₂).inverse
      (Iso.isoCompInverse (restrictModuleCatIso φ)) ≪≫
    (moduleCatEquiv k R₂).invFunIdAssoc
      (ModuleCat.restrictScalars.{w} (φ : R₁ →+* R₂) ⋙ (moduleCatEquiv k R₁).inverse)).symm

/-- Base change of module objects of `ModuleCat k` along `φ` is `ModuleCat.extendScalars φ`: the
isomorphism of left adjoints conjugate to `restrictModuleCatIso`. -/
noncomputable def extendModuleCatIso :
    extend (ModuleCat.{w} k) φ ⋙ (moduleCatEquiv k R₂).functor ≅
      (moduleCatEquiv k R₁).functor ⋙ ModuleCat.extendScalars (φ : R₁ →+* R₂) :=
  (conjugateIsoEquiv
    ((moduleCatEquiv k R₁).toAdjunction.comp
      (ModuleCat.extendRestrictScalarsAdj (φ : R₁ →+* R₂)))
    ((extendRestrictAdj φ).comp (moduleCatEquiv k R₂).toAdjunction)).symm
      (restrictScalarsCompInverseIso φ)

end Extend

end ModuleObject

end CategoryTheory
