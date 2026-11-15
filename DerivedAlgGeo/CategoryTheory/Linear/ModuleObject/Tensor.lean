/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.ModuleObject.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Tensor products of modules with module objects

Let `A` be a `k`-linear category with coproducts indexed by `Type w` (the universe of its
morphisms) and coequalizers, and let `E` be an `R`-module object of `A`. For an `R`-module `M`
the object `M ⊗_R E` of `A` is characterized by
`Hom_A(M ⊗_R E, F) ≃ Hom_R(M, Hom_A(E, F))` [AHLH, (7.2)]. It is the coequalizer of the two maps
`∐_{relations} E ⇉ ∐_M E` imposing `ι (m + m') = ι m + ι m'` and `ι (r • m) = r • ι m`.

## Main definitions

* `ModuleObject.HomModule E F`: `Hom_A(E, F)` as an `R`-module.
* `ModuleObject.tensorObj E M`: the object `M ⊗_R E`, with the maps
  `ιTensorObj E M m : E ⟶ M ⊗_R E`.
* `ModuleObject.tensorHomEquiv`: the bijection `(M ⊗_R E ⟶ F) ≃ (M ⟶ Hom_A(E, F))`.
* `ModuleObject.tensorAdj E`: the adjunction `(-) ⊗_R E ⊣ Hom_A(E, -)`.
* `ModuleObject.tensor k A R`: the bifunctor `(M, E) ↦ M ⊗_R E`.

## References

* [AHLH] J. Alper, D. Halpern-Leistner, J. Heinloth, *Existence of moduli spaces for algebraic
  stacks*, arXiv:1812.01128v5, §7.1.
-/

universe u v w u₁ u₂

namespace CategoryTheory

open Limits

namespace ModuleObject

variable {k : Type u} [CommRing k] {A : Type v} [Category.{w} A] [Preadditive A] [Linear k A]
  {R : Type u₁} [CommRing R] [Algebra k R]

section HomModule

variable (E : ModuleObject k A R)

/-- `Hom_A(E, F)`, on which `R` acts by precomposition with its action on `E`. -/
@[ext]
structure HomModule (F : A) : Type w where
  /-- A morphism `E.obj ⟶ F` as an element of `HomModule E F`. -/
  of ::
  /-- The morphism underlying an element of `HomModule E F`. -/
  hom : E.obj ⟶ F

namespace HomModule

variable {E} {F : A}

/-- `HomModule E F` is `Hom_A(E, F)`. -/
@[simps]
def equiv : E.HomModule F ≃ (E.obj ⟶ F) where
  toFun := hom
  invFun := of

instance : AddCommGroup (E.HomModule F) :=
  equiv.addCommGroup

@[simp] lemma hom_zero : (0 : E.HomModule F).hom = 0 := rfl

@[simp] lemma hom_add (f g : E.HomModule F) : (f + g).hom = f.hom + g.hom := rfl

@[simp] lemma hom_neg (f : E.HomModule F) : (-f).hom = -f.hom := rfl

@[simp] lemma hom_sub (f g : E.HomModule F) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul R (E.HomModule F) :=
  ⟨fun r f => .of ((E.act r).asHom ≫ f.hom)⟩

@[simp] lemma hom_smul (r : R) (f : E.HomModule F) : (r • f).hom = (E.act r).asHom ≫ f.hom := rfl

instance : Module R (E.HomModule F) where
  one_smul _ := by ext; simp
  mul_smul r s _ := by ext; simp [act_comm E s r]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp
  add_smul _ _ _ := by ext; simp
  zero_smul _ := by ext; simp

end HomModule

/-- `Hom_A(E, -)` as a functor to `R`-modules. -/
abbrev homFunctor : A ⥤ ModuleCat.{w} R where
  obj F := ModuleCat.of R (E.HomModule F)
  map {F G} g := ModuleCat.ofHom
    { toFun f := .of (f.hom ≫ g)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- Two maps into `Hom_A(E, F)` agree if they agree on underlying morphisms. -/
lemma homModule_hom_ext {N : ModuleCat.{w} R} {F : A} {f g : N ⟶ ModuleCat.of R (E.HomModule F)}
    (h : ∀ n, (f.hom n).hom = (g.hom n).hom) : f = g := by
  ext n
  exact h n

@[simp]
lemma homFunctor_map_apply_hom {F G : A} (g : F ⟶ G) (f : E.HomModule F) :
    ((E.homFunctor.map g).hom f).hom = f.hom ≫ g :=
  rfl

end HomModule

section Tensor

variable (E : ModuleObject k A R) (M : ModuleCat.{w} R)

/-- The relations presenting `M ⊗_R E`: one for each pair `(m, m')`, imposing additivity, and one
for each value `(E.act r, m, r • m)`, imposing `R`-linearity. The second family is indexed by
these values rather than by `R × M`, so that the index lives in the universe of morphisms of `A`
whatever the universe of `R`. -/
abbrev Relations : Type w :=
  (M × M) ⊕ Set.range fun p : R × M => (E.act p.1, p.2, p.1 • p.2)

variable [HasCoproducts.{w} A]

/-- The first map from the relations to the generators: `m + m'`, resp. `r • m`. -/
noncomputable def relationsFst : ∐ (fun _ : E.Relations M => E.obj) ⟶ ∐ (fun _ : M => E.obj) :=
  Sigma.desc fun
    | .inl p => Sigma.ι (fun _ : M => E.obj) (p.1 + p.2)
    | .inr t => Sigma.ι (fun _ : M => E.obj) t.1.2.2

/-- The second map from the relations to the generators: `m` plus `m'`, resp. `r` acting on
`m`. -/
noncomputable def relationsSnd : ∐ (fun _ : E.Relations M => E.obj) ⟶ ∐ (fun _ : M => E.obj) :=
  Sigma.desc fun
    | .inl p => Sigma.ι (fun _ : M => E.obj) p.1 + Sigma.ι (fun _ : M => E.obj) p.2
    | .inr t => t.1.1.asHom ≫ Sigma.ι (fun _ : M => E.obj) t.1.2.1

@[reassoc (attr := simp)]
lemma ι_relationsFst_inl (m m' : M) :
    Sigma.ι (fun _ : E.Relations M => E.obj) (.inl (m, m')) ≫ E.relationsFst M =
      Sigma.ι (fun _ : M => E.obj) (m + m') :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
lemma ι_relationsSnd_inl (m m' : M) :
    Sigma.ι (fun _ : E.Relations M => E.obj) (.inl (m, m')) ≫ E.relationsSnd M =
      Sigma.ι (fun _ : M => E.obj) m + Sigma.ι (fun _ : M => E.obj) m' :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
lemma ι_relationsFst_inr (r : R) (m : M) :
    Sigma.ι (fun _ : E.Relations M => E.obj) (.inr ⟨_, (r, m), rfl⟩) ≫ E.relationsFst M =
      Sigma.ι (fun _ : M => E.obj) (r • m) :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
lemma ι_relationsSnd_inr (r : R) (m : M) :
    Sigma.ι (fun _ : E.Relations M => E.obj) (.inr ⟨_, (r, m), rfl⟩) ≫ E.relationsSnd M =
      (E.act r).asHom ≫ Sigma.ι (fun _ : M => E.obj) m :=
  Sigma.ι_comp_desc _ _

variable [HasCoequalizers A]

/-- The tensor product `M ⊗_R E` of an `R`-module with an `R`-module object [AHLH, (7.2)]. -/
noncomputable abbrev tensorObj : A :=
  coequalizer (E.relationsFst M) (E.relationsSnd M)

/-- The map `E ⟶ M ⊗_R E` at an element `m` of `M`. -/
noncomputable def ιTensorObj (m : M) : E.obj ⟶ E.tensorObj M :=
  Sigma.ι (fun _ : M => E.obj) m ≫ coequalizer.π _ _

lemma ιTensorObj_add (m m' : M) :
    E.ιTensorObj M (m + m') = E.ιTensorObj M m + E.ιTensorObj M m' := by
  have h := Sigma.ι (fun _ : E.Relations M => E.obj) (.inl (m, m')) ≫=
    coequalizer.condition (E.relationsFst M) (E.relationsSnd M)
  rw [ι_relationsFst_inl_assoc, ι_relationsSnd_inl_assoc, Preadditive.add_comp] at h
  exact h

lemma ιTensorObj_smul (r : R) (m : M) :
    E.ιTensorObj M (r • m) = (E.act r).asHom ≫ E.ιTensorObj M m := by
  have h := Sigma.ι (fun _ : E.Relations M => E.obj) (.inr ⟨_, (r, m), rfl⟩) ≫=
    coequalizer.condition (E.relationsFst M) (E.relationsSnd M)
  rw [ι_relationsFst_inr_assoc, ι_relationsSnd_inr_assoc] at h
  exact h

@[simp]
lemma ιTensorObj_zero : E.ιTensorObj M 0 = 0 := by
  simpa using E.ιTensorObj_add M 0 0

/-- Morphisms out of `M ⊗_R E` are determined by their composites with the `ιTensorObj`. -/
lemma tensorObj_hom_ext {F : A} {f g : E.tensorObj M ⟶ F}
    (h : ∀ m, E.ιTensorObj M m ≫ f = E.ιTensorObj M m ≫ g) : f = g :=
  coequalizer.hom_ext <| Sigma.hom_ext _ _ fun m =>
    (Category.assoc _ _ _).symm.trans ((h m).trans (Category.assoc _ _ _))

/-- The universal property of `M ⊗_R E`: morphisms `M ⊗_R E ⟶ F` are the `R`-linear maps
`M → Hom_A(E, F)` [AHLH, (7.2)]. -/
noncomputable def tensorHomEquiv (F : A) :
    (E.tensorObj M ⟶ F) ≃ (M ⟶ ModuleCat.of R (E.HomModule F)) where
  toFun g := ModuleCat.ofHom
    { toFun m := .of (E.ιTensorObj M m ≫ g)
      map_add' m m' := by ext; simp [ιTensorObj_add]
      map_smul' r m := by ext; simp [ιTensorObj_smul] }
  invFun f := coequalizer.desc (Sigma.desc fun m => (f.hom m).hom) <|
    Sigma.hom_ext _ _ <| by
      rintro (⟨m, m'⟩ | ⟨_, ⟨r, m⟩, rfl⟩)
      · rw [ι_relationsFst_inl_assoc, ι_relationsSnd_inl_assoc, Preadditive.add_comp,
          Sigma.ι_comp_desc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, f.hom.map_add,
          HomModule.hom_add]
      · rw [ι_relationsFst_inr_assoc, ι_relationsSnd_inr_assoc, Sigma.ι_comp_desc,
          Sigma.ι_comp_desc, f.hom.map_smul, HomModule.hom_smul]
  left_inv g := E.tensorObj_hom_ext M fun m => by
    simp [ιTensorObj]
  right_inv f := by
    ext m
    simp [ιTensorObj]

@[simp]
lemma tensorHomEquiv_apply_hom_apply_hom {F : A} (g : E.tensorObj M ⟶ F) (m : M) :
    ((E.tensorHomEquiv M F g).hom m).hom = E.ιTensorObj M m ≫ g :=
  rfl

@[reassoc (attr := simp)]
lemma ιTensorObj_tensorHomEquiv_symm {F : A} (f : M ⟶ ModuleCat.of R (E.HomModule F)) (m : M) :
    E.ιTensorObj M m ≫ (E.tensorHomEquiv M F).symm f = (f.hom m).hom := by
  simp [tensorHomEquiv, ιTensorObj]

/-- The morphism `M ⊗_R E ⟶ M' ⊗_R E` induced by a linear map `M ⟶ M'`. -/
noncomputable def tensorObjMap {M M' : ModuleCat.{w} R} (g : M ⟶ M') :
    E.tensorObj M ⟶ E.tensorObj M' :=
  (E.tensorHomEquiv M _).symm <| ModuleCat.ofHom
    { toFun m := .of (E.ιTensorObj M' (g.hom m))
      map_add' m m' := by ext; simp [ιTensorObj_add]
      map_smul' r m := by ext; simp [ιTensorObj_smul] }

@[reassoc (attr := simp)]
lemma ιTensorObj_tensorObjMap {M M' : ModuleCat.{w} R} (g : M ⟶ M') (m : M) :
    E.ιTensorObj M m ≫ E.tensorObjMap g = E.ιTensorObj M' (g.hom m) :=
  E.ιTensorObj_tensorHomEquiv_symm M _ m

/-- The functor `(-) ⊗_R E` from `R`-modules to `A`. -/
noncomputable abbrev tensorFunctor : ModuleCat.{w} R ⥤ A where
  obj M := E.tensorObj M
  map g := E.tensorObjMap g
  map_id M := E.tensorObj_hom_ext M fun m => by simp
  map_comp g g' := E.tensorObj_hom_ext _ fun m => by simp

/-- The adjunction `(-) ⊗_R E ⊣ Hom_A(E, -)` [AHLH, (7.2)]. -/
noncomputable def tensorAdj : E.tensorFunctor ⊣ E.homFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv M F := E.tensorHomEquiv M F
      homEquiv_naturality_left_symm {M' M F} g f := E.tensorObj_hom_ext M' fun m => by
        simp
      homEquiv_naturality_right {M F F'} f g := E.homModule_hom_ext fun _ =>
        (Category.assoc _ _ _).symm }

@[simp]
lemma tensorAdj_homEquiv (F : A) : E.tensorAdj.homEquiv M F = E.tensorHomEquiv M F := by
  rw [tensorAdj, Adjunction.mkOfHomEquiv_homEquiv]

/-- A morphism of module objects induces a morphism of tensor products. -/
noncomputable def tensorMap {E E' : ModuleObject k A R} (f : E ⟶ E') :
    E.tensorObj M ⟶ E'.tensorObj M :=
  (E.tensorHomEquiv M _).symm <| ModuleCat.ofHom
    { toFun m := .of (f.hom ≫ E'.ιTensorObj M m)
      map_add' m m' := by ext; simp [ιTensorObj_add]
      map_smul' r m := by ext; simp [ιTensorObj_smul] }

@[reassoc (attr := simp)]
lemma ιTensorObj_tensorMap {E E' : ModuleObject k A R} (f : E ⟶ E') (m : M) :
    E.ιTensorObj M m ≫ tensorMap M f = f.hom ≫ E'.ιTensorObj M m :=
  E.ιTensorObj_tensorHomEquiv_symm M _ m

variable (k A R) in
/-- The tensor product `(M, E) ↦ M ⊗_R E` as a bifunctor. -/
@[simps]
noncomputable def tensor : ModuleCat.{w} R ⥤ ModuleObject k A R ⥤ A where
  obj M :=
    { obj E := E.tensorObj M
      map f := tensorMap M f
      map_id E := E.tensorObj_hom_ext M fun m => by simp
      map_comp f g := tensorObj_hom_ext _ M fun m => by simp }
  map g :=
    { app E := E.tensorObjMap g
      naturality _ _ f := tensorObj_hom_ext _ _ fun m => by simp }
  map_id M := NatTrans.ext <| funext fun E => E.tensorObj_hom_ext M fun m => by simp
  map_comp f g := NatTrans.ext <| funext fun E => E.tensorObj_hom_ext _ fun m => by simp

end Tensor

end ModuleObject

section ModuleTensor

open ModuleObject Opposite

variable (k : Type u) [CommRing k] (A : Type v) [Category.{w} A] [Preadditive A] [Linear k A]
  [HasCoproducts.{w} A] [HasCoequalizers A]

/-- The tensor action `(M, E) ↦ M ⊗_k E` of `k`-modules on a `k`-linear category with colimits,
characterized by `Hom_A(M ⊗_k E, F) ≃ Hom_k(M, Hom_A(E, F))` [AHLH, (7.2)]; see
`moduleTensorHomEquiv` and `moduleTensorAdj₂`. -/
noncomputable def moduleTensor : ModuleCat.{w} k ⥤ A ⥤ A :=
  tensor k A k ⋙ (Functor.whiskeringLeft _ _ _).obj (ofObjFunctor k A)

variable {k A}

/-- The map `E ⟶ M ⊗_k E` at an element `m` of `M`. -/
noncomputable def moduleTensorι (M : ModuleCat.{w} k) (E : A) (m : M) :
    E ⟶ ((moduleTensor k A).obj M).obj E :=
  (ofObj E).ιTensorObj M m

variable (M : ModuleCat.{w} k) (E : A)

lemma moduleTensorι_add (m m' : M) :
    moduleTensorι M E (m + m') = moduleTensorι M E m + moduleTensorι M E m' :=
  (ofObj E).ιTensorObj_add M m m'

lemma moduleTensorι_smul (c : k) (m : M) :
    moduleTensorι M E (c • m) = c • moduleTensorι M E m :=
  ((ofObj E).ιTensorObj_smul M c m).trans <| by
    rw [ofObj_act_asHom, Linear.smul_comp, Category.id_comp]
    rfl

@[simp]
lemma moduleTensorι_zero : moduleTensorι M E 0 = 0 :=
  (ofObj E).ιTensorObj_zero M

/-- Morphisms out of `M ⊗_k E` are determined by their composites with the `moduleTensorι`. -/
lemma moduleTensor_hom_ext {F : A} {f g : ((moduleTensor k A).obj M).obj E ⟶ F}
    (h : ∀ m, moduleTensorι M E m ≫ f = moduleTensorι M E m ≫ g) : f = g :=
  (ofObj E).tensorObj_hom_ext M h

@[reassoc (attr := simp)]
lemma moduleTensorι_map {E' : A} (f : E ⟶ E') (m : M) :
    moduleTensorι M E m ≫ ((moduleTensor k A).obj M).map f = f ≫ moduleTensorι M E' m :=
  ιTensorObj_tensorMap M ((ofObjFunctor k A).map f) m

@[reassoc (attr := simp)]
lemma moduleTensorι_map_app {M' : ModuleCat.{w} k} (g : M ⟶ M') (m : M) :
    moduleTensorι M E m ≫ ((moduleTensor k A).map g).app E = moduleTensorι M' E (g.hom m) :=
  (ofObj E).ιTensorObj_tensorObjMap g m

/-- The universal property of `M ⊗_k E`: morphisms `M ⊗_k E ⟶ F` are the `k`-linear maps
`M → Hom_A(E, F)` [AHLH, (7.2)]. -/
noncomputable def moduleTensorHomEquiv (F : A) :
    (((moduleTensor k A).obj M).obj E ⟶ F) ≃ (M ⟶ ModuleCat.of k (E ⟶ F)) where
  toFun g := ModuleCat.ofHom
    { toFun m := moduleTensorι M E m ≫ g
      map_add' m m' := by rw [moduleTensorι_add, Preadditive.add_comp]
      map_smul' c m := by rw [moduleTensorι_smul, Linear.smul_comp]; rfl }
  invFun f := ((ofObj E).tensorHomEquiv M F).symm <| ModuleCat.ofHom
    { toFun m := .of (f.hom m)
      map_add' m m' := by ext; simp
      map_smul' c m := by ext; simp [Algebra.algebraMap_eq_smul_one] }
  left_inv g := moduleTensor_hom_ext M E fun m =>
    (ofObj E).ιTensorObj_tensorHomEquiv_symm M _ m
  right_inv f := by
    ext m
    exact (ofObj E).ιTensorObj_tensorHomEquiv_symm M _ m

@[simp]
lemma moduleTensorHomEquiv_apply_hom_apply {F : A} (g : ((moduleTensor k A).obj M).obj E ⟶ F)
    (m : M) : (moduleTensorHomEquiv M E F g).hom m = moduleTensorι M E m ≫ g :=
  rfl

@[reassoc (attr := simp)]
lemma moduleTensorι_moduleTensorHomEquiv_symm {F : A} (f : M ⟶ ModuleCat.of k (E ⟶ F))
    (m : M) : moduleTensorι M E m ≫ (moduleTensorHomEquiv M E F).symm f = f.hom m :=
  (ofObj E).ιTensorObj_tensorHomEquiv_symm M _ m

/-- `(-) ⊗_k E` is left adjoint to `Hom_A(E, -)` [AHLH, (7.2)]. -/
noncomputable def moduleTensorAdj :
    (moduleTensor k A).flip.obj E ⊣ (linearCoyoneda k A).obj (op E) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M F := moduleTensorHomEquiv M E F
      homEquiv_naturality_left_symm {M' M F} g f := moduleTensor_hom_ext M' E fun m =>
        (moduleTensorι_moduleTensorHomEquiv_symm M' E _ m).trans <|
          (moduleTensorι_moduleTensorHomEquiv_symm M E f (g.hom m)).symm.trans
            (moduleTensorι_map_app_assoc M' E g m _).symm
      homEquiv_naturality_right {M F F'} f g := by
        ext m
        exact (Category.assoc _ _ _).symm }

@[simp]
lemma moduleTensorAdj_homEquiv (F : A) :
    (moduleTensorAdj E).homEquiv M F = moduleTensorHomEquiv M E F := by
  rw [moduleTensorAdj, Adjunction.mkOfHomEquiv_homEquiv]

variable (k A) in
/-- The tensor action and `Hom_A(-, -)` form an adjunction with a parameter: the bijections
`moduleTensorHomEquiv` are natural in all three variables [AHLH, (7.2)]. -/
noncomputable def moduleTensorAdj₂ : (moduleTensor k A).flip ⊣₂ linearCoyoneda k A :=
  .mk' moduleTensorAdj fun {E E'} f {M} {F} g => by
    ext m
    simp only [moduleTensorAdj_homEquiv]
    exact moduleTensorι_map_assoc M E f m g

instance : ((moduleTensor k A).flip.obj E).IsLeftAdjoint :=
  (moduleTensorAdj E).isLeftAdjoint

/-- `M ⊗_k (-)` sends colimit cocones to colimit cocones. -/
noncomputable def isColimitMapCoconeModuleTensor {J : Type*} [Category* J] {K : J ⥤ A}
    {c : Cocone K} (hc : IsColimit c) : IsColimit (((moduleTensor k A).obj M).mapCocone c) where
  desc s := (moduleTensorHomEquiv M c.pt s.pt).symm <| ModuleCat.ofHom
    { toFun m := hc.desc
        { pt := s.pt
          ι :=
            { app j := moduleTensorι M (K.obj j) m ≫ s.ι.app j
              naturality j j' f := by
                have := s.w f
                dsimp at this ⊢
                rw [Category.comp_id, ← this, moduleTensorι_map_assoc] } }
      map_add' m m' := hc.hom_ext fun j => by
        simp [moduleTensorι_add, Preadditive.add_comp]
      map_smul' c m := hc.hom_ext fun j => by
        simp [moduleTensorι_smul] }
  fac s j := moduleTensor_hom_ext M _ fun m => by simp
  uniq s f hf := moduleTensor_hom_ext M _ fun m => hc.hom_ext fun j => by
    simp [← hf j]

/-- `M ⊗_k (-)` preserves all colimits; in particular it is right exact and commutes with
filtered colimits [AHLH, §7.1]. -/
instance : PreservesColimitsOfSize.{u₁, u₂} ((moduleTensor k A).obj M) where
  preservesColimitsOfShape :=
    { preservesColimit := ⟨fun hc => ⟨isColimitMapCoconeModuleTensor M hc⟩⟩ }

/-! The tensor action is right exact and commutes with filtered colimits in each variable
[AHLH, §7.1]: `(-) ⊗_k E` is a left adjoint, and `M ⊗_k (-)` preserves all colimits. -/

example : PreservesFiniteColimits ((moduleTensor k A).obj M) := inferInstance

example : PreservesFiniteColimits ((moduleTensor k A).flip.obj E) := inferInstance

example : PreservesFilteredColimits ((moduleTensor k A).obj M) := inferInstance

example : PreservesFilteredColimits ((moduleTensor k A).flip.obj E) := inferInstance

variable (k A) in
/-- An object `E` of `A` is flat if `(-) ⊗_k E : Mod_k ⥤ A` is exact [AHLH, Definition 7.2,
citing AZ, §C1]. Being a left adjoint, `(-) ⊗_k E` is always right exact, so flatness asks that
it preserve finite limits. -/
def IsFlatObject (E : A) : Prop :=
  PreservesFiniteLimits ((moduleTensor k A).flip.obj E)

end ModuleTensor

end CategoryTheory
