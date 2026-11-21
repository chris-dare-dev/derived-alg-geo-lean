/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import DerivedAlgGeo.CategoryTheory.Sites.CartesianMonoidal
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData
import DerivedAlgGeo.CategoryTheory.Sites.Descent.SheafOver

/-!
# Objects with an action of a sheaf of monoids form a stack

Let `G` be a monoid object in the category of sheaves of types on a site `(C, J)`. Over each
`X : C`, the restriction `(J.overPullback (Type w) X).obj G` of `G` to `Over X` is a monoid
object, through the monoidal structure of the restriction functor, and the sheaves on `Over X`
with an action of it are Mathlib's module objects. This file assembles them into a pseudofunctor
`J.pseudofunctorModOver G` on `LocallyDiscrete Cᵒᵖ`, whose transition functors restrict along
`Over.map`, and shows that it is a stack whenever sheaves of types on the slices form one.

## Main definitions

* `GrothendieckTopology.modObjOverMapPullback`: an action restricts along `Over.map f`.
* `GrothendieckTopology.pseudofunctorModOver J G`: the pseudofunctor sending `X : C` to the
  category `Mod (Sheaf (J.over X) (Type w)) ((J.overPullback (Type w) X).obj G)`.
* `GrothendieckTopology.pseudofunctorModOverForget G`: forgetting the action, a strong
  transformation to `J.pseudofunctorOver (Type w)` with identity naturality isomorphisms.

## Main results

* `GrothendieckTopology.isPrestack_pseudofunctorModOver`: equivariant morphisms glue.
* `GrothendieckTopology.isStack_pseudofunctorModOver`: objects with an action of `G` glue, when
  sheaves of types on the slices do. By `GrothendieckTopology.isStack_pseudofunctorOver` this holds
  when every covering sieve contains a `w`-small covering family.

## Implementation notes

Restriction along `Over.map f` preserves products of sheaves on the nose, and sends the
restriction of `G` to `Over Y` to its restriction to `Over X` on the nose. So the action on a
restriction is the restriction of the action, and the unitors and compositors of
`J.pseudofunctorOver (Type w)` are equivariant (`pseudofunctorOver_mapComp'_hom_app_tensor`):
they are the unitors and compositors of the pseudofunctor of `G`-objects, whose coherence is that
of `J.pseudofunctorOver (Type w)`.

To glue a descent datum of `G`-objects, its underlying descent datum of sheaves is glued first.
The actions of its members, transported to the restrictions of the glued sheaf, form a morphism of
descent data, because the gluing morphisms are equivariant. The glued action is its preimage
under the fully faithful restriction to descent data, and the action axioms hold because they
hold after restriction along every member of the covering sieve.

## References

* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK): its proof glues
  `G`-torsors by gluing the underlying sheaves and their actions.
* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR): gluing of sheaves.

## Tags

stack, descent, monoid object, module object, action
-/

universe w v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Bicategory MonoidalCategory Pseudofunctor.LocallyDiscreteOpToCat
open scoped Obj MonObj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Restriction

variable (G : Sheaf J (Type w)) [MonObj G] {X Y : C} (f : X ⟶ Y)

/-- An action of the restriction of `G` to `Over Y` restricts along `Over.map f` to an action
of the restriction of `G` to `Over X`: the action map is the restriction of the action map. -/
instance modObjOverMapPullback (P : Sheaf (J.over Y) (Type w))
    [ModObj ((J.overPullback (Type w) Y).obj G) P] :
    ModObj ((J.overPullback (Type w) X).obj G) ((J.overMapPullback (Type w) f).obj P) where
  smul := (J.overMapPullback (Type w) f).map γ[(J.overPullback (Type w) Y).obj G, P]
  one_smul := by
    have := (J.overMapPullback (Type w) f).congr_map
      (ModObj.one_smul (M := (J.overPullback (Type w) Y).obj G) P)
    rw [Functor.map_comp] at this
    exact this
  mul_smul := by
    have := (J.overMapPullback (Type w) f).congr_map
      (ModObj.mul_smul (M := (J.overPullback (Type w) Y).obj G) P)
    simp only [Functor.map_comp] at this
    exact this

lemma smul_overMapPullback (P : Sheaf (J.over Y) (Type w))
    [ModObj ((J.overPullback (Type w) Y).obj G) P] :
    γ[(J.overPullback (Type w) X).obj G, (J.overMapPullback (Type w) f).obj P] =
      (J.overMapPullback (Type w) f).map γ[(J.overPullback (Type w) Y).obj G, P] :=
  rfl

omit [MonObj G] in
lemma overMapPullback_map_whiskerLeft {P Q : Sheaf (J.over Y) (Type w)} (φ : P ⟶ Q) :
    (J.overMapPullback (Type w) f).map ((J.overPullback (Type w) Y).obj G ◁ φ) =
      (J.overPullback (Type w) X).obj G ◁ (J.overMapPullback (Type w) f).map φ :=
  rfl

lemma overMapPullback_map_one_whiskerRight (P : Sheaf (J.over Y) (Type w)) :
    (J.overMapPullback (Type w) f).map (η[(J.overPullback (Type w) Y).obj G] ▷ P) =
      η[(J.overPullback (Type w) X).obj G] ▷ (J.overMapPullback (Type w) f).obj P :=
  rfl

lemma overMapPullback_map_mul_whiskerRight (P : Sheaf (J.over Y) (Type w)) :
    (J.overMapPullback (Type w) f).map (μ[(J.overPullback (Type w) Y).obj G] ▷ P) =
      μ[(J.overPullback (Type w) X).obj G] ▷ (J.overMapPullback (Type w) f).obj P :=
  rfl

omit [MonObj G] in
lemma overMapPullback_map_associator_hom (P : Sheaf (J.over Y) (Type w)) :
    (J.overMapPullback (Type w) f).map
        (α_ ((J.overPullback (Type w) Y).obj G) ((J.overPullback (Type w) Y).obj G) P).hom =
      (α_ ((J.overPullback (Type w) X).obj G) ((J.overPullback (Type w) X).obj G)
        ((J.overMapPullback (Type w) f).obj P)).hom :=
  rfl

omit G [MonObj G] in
lemma overMapPullback_map_leftUnitor_hom (P : Sheaf (J.over Y) (Type w)) :
    (J.overMapPullback (Type w) f).map (λ_ P).hom =
      (λ_ ((J.overMapPullback (Type w) f).obj P)).hom :=
  rfl

/-- The restriction of an equivariant morphism is equivariant. -/
instance isModHom_overMapPullback_map {P Q : Sheaf (J.over Y) (Type w)}
    [ModObj ((J.overPullback (Type w) Y).obj G) P] [ModObj ((J.overPullback (Type w) Y).obj G) Q]
    (φ : P ⟶ Q) [IsModHom ((J.overPullback (Type w) Y).obj G) φ] :
    IsModHom ((J.overPullback (Type w) X).obj G) ((J.overMapPullback (Type w) f).map φ) where
  smul_hom := by
    have := (J.overMapPullback (Type w) f).congr_map
      (IsModHom.smul_hom (A := (J.overPullback (Type w) Y).obj G) (f := φ))
    simp only [Functor.map_comp] at this
    exact this

end Restriction

section Tensor

variable (G : Sheaf J (Type w))

/-- The compositors of `J.pseudofunctorOver (Type w)` at a product with a restriction of a sheaf
`G` on `C` are the compositors of the second factor, whiskered by the restriction of `G`. -/
lemma pseudofunctorOver_mapComp'_hom_app_tensor {X₀ X₁ X₂ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (fg : X₂ ⟶ X₀) (h : g ≫ f = fg) (M : Sheaf (J.over X₀) (Type w)) :
    ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app
        ((J.overPullback (Type w) X₀).obj G ⊗ M : Sheaf (J.over X₀) (Type w)) =
      (J.overPullback (Type w) X₂).obj G ◁
        ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app M := by
  refine Sheaf.hom_ext ?_
  ext ⟨Z⟩ ⟨a, m⟩
  erw [pseudofunctorOver_mapComp'_hom_app_hom_app J (Type w) f g fg h _ Z]
  refine Prod.ext ?_ ?_
  · change G.obj.map (𝟙 (op Z.left)) a = a
    simp only [CategoryTheory.Functor.map_id]
    rfl
  · exact (ConcreteCategory.congr_hom
      (pseudofunctorOver_mapComp'_hom_app_hom_app J (Type w) f g fg h M Z) m).symm

/-- The inverse compositors, as in `pseudofunctorOver_mapComp'_hom_app_tensor`. -/
lemma pseudofunctorOver_mapComp'_inv_app_tensor {X₀ X₁ X₂ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (fg : X₂ ⟶ X₀) (h : g ≫ f = fg) (M : Sheaf (J.over X₀) (Type w)) :
    ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app
        ((J.overPullback (Type w) X₀).obj G ⊗ M : Sheaf (J.over X₀) (Type w)) =
      (J.overPullback (Type w) X₂).obj G ◁
        ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app M := by
  refine Sheaf.hom_ext ?_
  ext ⟨Z⟩ ⟨a, m⟩
  erw [pseudofunctorOver_mapComp'_inv_app_hom_app J (Type w) f g fg h _ Z]
  refine Prod.ext ?_ ?_
  · change G.obj.map (𝟙 (op Z.left)) a = a
    simp only [CategoryTheory.Functor.map_id]
    rfl
  · exact (ConcreteCategory.congr_hom
      (pseudofunctorOver_mapComp'_inv_app_hom_app J (Type w) f g fg h M Z) m).symm

/-- The unitors of `J.pseudofunctorOver (Type w)` at a product with a restriction of a sheaf `G`
on `C` are the unitors of the second factor, whiskered by the restriction of `G`. -/
lemma pseudofunctorOver_mapId_hom_app_tensor (X : C) (M : Sheaf (J.over X) (Type w)) :
    ((J.pseudofunctorOver (Type w)).mapId (.mk (op X))).hom.toNatTrans.app
        ((J.overPullback (Type w) X).obj G ⊗ M : Sheaf (J.over X) (Type w)) =
      (J.overPullback (Type w) X).obj G ◁
        ((J.pseudofunctorOver (Type w)).mapId (.mk (op X))).hom.toNatTrans.app M := by
  refine Sheaf.hom_ext ?_
  ext ⟨Z⟩ ⟨a, m⟩
  simp
  rfl

/-- The gluing morphisms of the descent datum of a product with the restriction of `G` are those
of the second factor, whiskered by the restriction of `G`. -/
lemma toDescentData_obj_tensor_hom {S : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (P : Sheaf (J.over S) (Type w)) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (((J.pseudofunctorOver (Type w)).toDescentData f).obj
        ((J.overPullback (Type w) S).obj G ⊗ P : Sheaf (J.over S) (Type w))).hom q f₁ f₂ hf₁ hf₂ =
      (J.overPullback (Type w) Y).obj G ◁
        (((J.pseudofunctorOver (Type w)).toDescentData f).obj P).hom q f₁ f₂ hf₁ hf₂ :=
  (congrArg₂ (· ≫ ·) (pseudofunctorOver_mapComp'_inv_app_tensor G (f i₁) f₁ q hf₁ P)
    (pseudofunctorOver_mapComp'_hom_app_tensor G (f i₂) f₂ q hf₂ P)).trans
    (MonoidalCategory.whiskerLeft_comp (C := Sheaf (J.over Y) (Type w)) _ _ _).symm

end Tensor

section Pseudofunctor

/-- An isomorphism of the underlying objects of two module objects whose forward morphism is
equivariant is an isomorphism of module objects. -/
@[simps]
private def modIsoMk {D : Type*} [Category D] [MonoidalCategory D] {A : D} [MonObj A]
    {P Q : Mod D A} (e : P.X ≅ Q.X) (h : γ[A, P.X] ≫ e.hom = A ◁ e.hom ≫ γ[A, Q.X]) : P ≅ Q :=
  letI : IsModHom A e.hom := ⟨h⟩
  { hom := ⟨e.hom⟩
    inv := ⟨e.inv⟩
    hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id }

variable (G : Sheaf J (Type w)) [MonObj G]

/-- The transition functor of the pseudofunctor of `G`-objects: restriction along
`Over.map f`, with the restricted action. -/
@[simps]
def modOverMap {X Y : C} (f : X ⟶ Y) :
    Mod (Sheaf (J.over Y) (Type w)) ((J.overPullback (Type w) Y).obj G) ⥤
      Mod (Sheaf (J.over X) (Type w)) ((J.overPullback (Type w) X).obj G) where
  obj P := .mk ((J.overMapPullback (Type w) f).obj P.X)
  map φ := .mk ((J.overMapPullback (Type w) f).map φ.hom)

/-- The unitor of the pseudofunctor of `G`-objects: the unitor of `J.pseudofunctorOver (Type w)`,
which is equivariant. -/
def modOverMapId (X : C) : modOverMap G (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ modIsoMk
    ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type w)).mapId (.mk (op X)))).app P.X) (by
      have := ((J.pseudofunctorOver (Type w)).mapId (.mk (op X))).hom.toNatTrans.naturality
        γ[(J.overPullback (Type w) X).obj G, P.X]
      exact this.trans (pseudofunctorOver_mapId_hom_app_tensor G X P.X =≫ _)))
    (fun φ ↦ Mod.hom_ext _ _
      (((J.pseudofunctorOver (Type w)).mapId (.mk (op X))).hom.toNatTrans.naturality φ.hom))

@[simp]
lemma modOverMapId_hom_app_hom (X : C) (P : Mod (Sheaf (J.over X) (Type w))
      ((J.overPullback (Type w) X).obj G)) :
    ((modOverMapId G X).hom.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapId (.mk (op X))).hom.toNatTrans.app P.X :=
  rfl

@[simp]
lemma modOverMapId_inv_app_hom (X : C) (P : Mod (Sheaf (J.over X) (Type w))
      ((J.overPullback (Type w) X).obj G)) :
    ((modOverMapId G X).inv.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapId (.mk (op X))).inv.toNatTrans.app P.X :=
  rfl

/-- The compositor of the pseudofunctor of `G`-objects for an arbitrary composite `fg`: the
compositor `mapComp'` of `J.pseudofunctorOver (Type w)`, which is equivariant. -/
def modOverMapCompIso {X₀ X₁ X₂ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁) (fg : X₂ ⟶ X₀)
    (h : g ≫ f = fg) : modOverMap G fg ≅ modOverMap G f ⋙ modOverMap G g :=
  NatIso.ofComponents (fun P ↦ modIsoMk
    ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc
      fg.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]))).app P.X) (by
      have := ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.naturality
        γ[(J.overPullback (Type w) X₀).obj G, P.X]
      exact this.trans (pseudofunctorOver_mapComp'_hom_app_tensor G f g fg h P.X =≫ _)))
    (fun φ ↦ Mod.hom_ext _ _
      (((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.naturality φ.hom))

@[simp]
lemma modOverMapCompIso_hom_app_hom {X₀ X₁ X₂ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁) (fg : X₂ ⟶ X₀)
    (h : g ≫ f = fg)
    (P : Mod (Sheaf (J.over X₀) (Type w)) ((J.overPullback (Type w) X₀).obj G)) :
    ((modOverMapCompIso G f g fg h).hom.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app P.X :=
  rfl

@[simp]
lemma modOverMapCompIso_inv_app_hom {X₀ X₁ X₂ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁) (fg : X₂ ⟶ X₀)
    (h : g ≫ f = fg)
    (P : Mod (Sheaf (J.over X₀) (Type w)) ((J.overPullback (Type w) X₀).obj G)) :
    ((modOverMapCompIso G f g fg h).inv.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app P.X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The compositors of the pseudofunctor of `G`-objects satisfy the associativity condition of
`LocallyDiscrete.mkPseudofunctor`, for any two bracketings `fgh` and `fgh'` of a triple
composite. -/
theorem modOverMapCompIso_associativity {X₀ X₁ X₂ X₃ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (h : X₃ ⟶ X₂) (fg : X₂ ⟶ X₀) (gh : X₃ ⟶ X₁) (fgh fgh' : X₃ ⟶ X₀)
    (hfg : g ≫ f = fg) (hgh : h ≫ g = gh) (hfgh : h ≫ fg = fgh) (hfgh' : gh ≫ f = fgh')
    (e : fgh = fgh') :
    (Cat.Hom.isoMk (modOverMapCompIso G fg h fgh hfgh)).hom ≫
        (Cat.Hom.isoMk (modOverMapCompIso G f g fg hfg)).hom ▷ (modOverMap G h).toCatHom ≫
        (α_ (modOverMap G f).toCatHom (modOverMap G g).toCatHom (modOverMap G h).toCatHom).hom ≫
        (modOverMap G f).toCatHom ◁ (Cat.Hom.isoMk (modOverMapCompIso G g h gh hgh)).inv ≫
        (Cat.Hom.isoMk (modOverMapCompIso G f gh fgh' hfgh')).inv =
      eqToHom (by rw [e]) := by
  subst e
  rw [eqToHom_refl]
  apply Cat.Hom₂.ext
  ext P : 2
  apply Mod.hom_ext
  have := (J.pseudofunctorOver (Type w)).mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app
    f.op.toLoc g.op.toLoc h.op.toLoc fg.op.toLoc gh.op.toLoc fgh.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hfg])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgh])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hfgh]) P.X
  have key := this =≫
    (((J.pseudofunctorOver (Type w)).mapComp' g.op.toLoc h.op.toLoc gh.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgh])).inv.toNatTrans.app
        (((J.pseudofunctorOver (Type w)).map f.op.toLoc).toFunctor.obj P.X) ≫
      ((J.pseudofunctorOver (Type w)).mapComp' f.op.toLoc gh.op.toLoc fgh.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hfgh'])).inv.toNatTrans.app P.X)
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app] at key
  simp
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- The unitor and compositors of the pseudofunctor of `G`-objects satisfy the left unitality
condition of `LocallyDiscrete.mkPseudofunctor`. -/
theorem modOverMapCompIso_leftUnitality {X₀ X₁ : C} (f f' : X₁ ⟶ X₀) (hf : f ≫ 𝟙 X₀ = f')
    (e : f' = f) :
    (Cat.Hom.isoMk (modOverMapCompIso G (𝟙 X₀) f f' hf)).hom ≫
        (Cat.Hom.isoMk (modOverMapId G X₀)).hom ▷ (modOverMap G f).toCatHom ≫
        (Bicategory.leftUnitor (modOverMap G f).toCatHom).hom =
      eqToHom (by rw [e]) := by
  subst e
  rw [eqToHom_refl]
  apply Cat.Hom₂.ext
  ext P : 2
  apply Mod.hom_ext
  have key : ((J.pseudofunctorOver (Type w)).mapComp' (𝟙 _) f'.op.toLoc f'.op.toLoc
      (Category.id_comp _)).hom.toNatTrans.app P.X ≫
      ((J.pseudofunctorOver (Type w)).map f'.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type w)).mapId (.mk (op X₀))).hom.toNatTrans.app P.X) = 𝟙 _ := by
    rw [Pseudofunctor.mapComp'_id_comp_hom]
    simp [← Functor.map_comp]
  simp
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- The unitor and compositors of the pseudofunctor of `G`-objects satisfy the right unitality
condition of `LocallyDiscrete.mkPseudofunctor`. -/
theorem modOverMapCompIso_rightUnitality {X₀ X₁ : C} (f f' : X₁ ⟶ X₀) (hf : 𝟙 X₁ ≫ f = f')
    (e : f' = f) :
    (Cat.Hom.isoMk (modOverMapCompIso G f (𝟙 X₁) f' hf)).hom ≫
        (modOverMap G f).toCatHom ◁ (Cat.Hom.isoMk (modOverMapId G X₁)).hom ≫
        (Bicategory.rightUnitor (modOverMap G f).toCatHom).hom =
      eqToHom (by rw [e]) := by
  subst e
  rw [eqToHom_refl]
  apply Cat.Hom₂.ext
  ext P : 2
  apply Mod.hom_ext
  have key : ((J.pseudofunctorOver (Type w)).mapComp' f'.op.toLoc (𝟙 _) f'.op.toLoc
      (Category.comp_id _)).hom.toNatTrans.app P.X ≫
      ((J.pseudofunctorOver (Type w)).mapId (.mk (op X₁))).hom.toNatTrans.app
        (((J.pseudofunctorOver (Type w)).map f'.op.toLoc).toFunctor.obj P.X) = 𝟙 _ := by
    rw [Pseudofunctor.mapComp'_comp_id_hom]
    simp
  simp
  exact key

end Pseudofunctor

variable (J) in
/-- The pseudofunctor of `G`-objects on the slices of a site: it sends `X : C` to the category
of objects of `Sheaf (J.over X) (Type w)` with an action of the restriction of `G` to
`Over X`, and `f : Y ⟶ X` to restriction along `Over.map f`. Its unitors and compositors are
those of `J.pseudofunctorOver (Type w)`, which are equivariant. -/
def pseudofunctorModOver (G : Sheaf J (Type w)) [MonObj G] :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max u v w, max u v (w + 1)} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Mod (Sheaf (J.over X.unop) (Type w)) ((J.overPullback (Type w) X.unop).obj G)))
    (fun f ↦ (modOverMap G f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (modOverMapId G X.unop))
    (fun f g ↦ Cat.Hom.isoMk (modOverMapCompIso G f.unop g.unop _ rfl))
    (fun f g h ↦ modOverMapCompIso_associativity G f.unop g.unop h.unop _ _ _ _ rfl rfl rfl rfl
      (congrArg Quiver.Hom.unop (Category.assoc f g h)))
    (fun f ↦ modOverMapCompIso_leftUnitality G f.unop _ rfl
      (congrArg Quiver.Hom.unop (Category.id_comp f)))
    (fun f ↦ modOverMapCompIso_rightUnitality G f.unop _ rfl
      (congrArg Quiver.Hom.unop (Category.comp_id f)))

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.GrothendieckTopology

open Opposite MonoidalCategory Pseudofunctor.LocallyDiscreteOpToCat
open scoped Obj MonObj Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (G : Sheaf J (Type w))
  [MonObj G]

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the action is a strong transformation from the pseudofunctor of `G`-objects to
`J.pseudofunctorOver (Type w)`, with identity naturality isomorphisms. -/
def pseudofunctorModOverForget : J.pseudofunctorModOver G ⟶ J.pseudofunctorOver (Type w) where
  app X := Cat.Hom.ofFunctor (Mod.forget (D := Sheaf (J.over X.as.unop) (Type w))
    ((J.overPullback (Type w) X.as.unop).obj G))
  naturality f := Iso.refl _
  naturality_naturality θ := by
    obtain rfl := LocallyDiscrete.eq_of_hom θ
    obtain rfl : θ = 𝟙 _ := Subsingleton.elim _ _
    simp only [PrelaxFunctor.map₂_id, Bicategory.id_whiskerRight, Category.id_comp,
      Iso.refl_hom, Category.comp_id]
    exact (Bicategory.whiskerLeft_id _ _).symm
  naturality_id a := by
    apply Cat.Hom₂.ext
    ext P
    simp
    rfl
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext P
    simp
    rfl

@[simp]
lemma pseudofunctorModOver_map_toFunctor {X Y : C} (f : X ⟶ Y) :
    ((J.pseudofunctorModOver G).map f.op.toLoc).toFunctor = modOverMap G f :=
  rfl

/-- The compositors of the pseudofunctor of `G`-objects are those of
`J.pseudofunctorOver (Type w)`. -/
lemma pseudofunctorModOver_mapComp'_hom_app_hom {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (P : Mod (Sheaf (J.over a.as.unop) (Type w)) ((J.overPullback (Type w) a.as.unop).obj G)) :
    (((J.pseudofunctorModOver G).mapComp' f g fg h).hom.toNatTrans.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' f g fg h).hom.toNatTrans.app P.X := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The inverse compositors of the pseudofunctor of `G`-objects are those of
`J.pseudofunctorOver (Type w)`. -/
lemma pseudofunctorModOver_mapComp'_inv_app_hom {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (P : Mod (Sheaf (J.over a.as.unop) (Type w)) ((J.overPullback (Type w) a.as.unop).obj G)) :
    (((J.pseudofunctorModOver G).mapComp' f g fg h).inv.toNatTrans.app P).hom =
      ((J.pseudofunctorOver (Type w)).mapComp' f g fg h).inv.toNatTrans.app P.X := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

section Descent

variable {S : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The gluing morphisms of the descent datum of a `G`-object are those of its underlying
sheaf. -/
lemma pseudofunctorModOver_toDescentData_obj_hom_hom
    (P : Mod (Sheaf (J.over S) (Type w)) ((J.overPullback (Type w) S).obj G)) ⦃Y : C⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    ((((J.pseudofunctorModOver G).toDescentData f).obj P).hom q f₁ f₂ hf₁ hf₂).hom =
      (((J.pseudofunctorOver (Type w)).toDescentData f).obj P.X).hom q f₁ f₂ hf₁ hf₂ := by
  exact congrArg₂ (· ≫ ·)
    (pseudofunctorModOver_mapComp'_inv_app_hom G (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁]) P)
    (pseudofunctorModOver_mapComp'_hom_app_hom G (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂]) P)

omit [MonObj G] in
variable {f} in
/-- Two morphisms of sheaves on `Over S` agree when their restrictions along the `f i` agree,
if restriction of sheaves of types to descent data along `f` is faithful. -/
lemma hom_ext_of_faithful_toDescentData
    [((J.pseudofunctorOver (Type w)).toDescentData f).Faithful] {A B : Sheaf (J.over S) (Type w)}
    {φ ψ : A ⟶ B}
    (h : ∀ i, (J.overMapPullback (Type w) (f i)).map φ = (J.overMapPullback (Type w) (f i)).map ψ) :
    φ = ψ :=
  ((J.pseudofunctorOver (Type w)).toDescentData f).map_injective
    (Pseudofunctor.DescentData.hom_ext h)

/-- A morphism of descent data of `G`-objects, as a morphism of descent data of the underlying
sheaves. -/
@[simps]
def descentDataHomOfMod
    {P Q : Mod (Sheaf (J.over S) (Type w)) ((J.overPullback (Type w) S).obj G)}
    (Φ : ((J.pseudofunctorModOver G).toDescentData f).obj P ⟶
      ((J.pseudofunctorModOver G).toDescentData f).obj Q) :
    ((J.pseudofunctorOver (Type w)).toDescentData f).obj P.X ⟶
      ((J.pseudofunctorOver (Type w)).toDescentData f).obj Q.X where
  hom i := (Φ.hom i).hom
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    rw [← pseudofunctorModOver_toDescentData_obj_hom_hom G f Q,
      ← pseudofunctorModOver_toDescentData_obj_hom_hom G f P]
    exact congrArg Mod.Hom.hom (Φ.comm q f₁ f₂ hf₁ hf₂)

variable {f} in
/-- A morphism of underlying sheaves whose restrictions to descent data are those of a morphism
of descent data of `G`-objects is equivariant: its two equivariance composites agree after
restriction along every `f i`. -/
lemma isModHom_of_toDescentData_map_eq
    (hF : ((J.pseudofunctorOver (Type w)).toDescentData f).Faithful)
    {P Q : Mod (Sheaf (J.over S) (Type w)) ((J.overPullback (Type w) S).obj G)}
    (Φ : ((J.pseudofunctorModOver G).toDescentData f).obj P ⟶
      ((J.pseudofunctorModOver G).toDescentData f).obj Q) (φ : P.X ⟶ Q.X)
    (hφ : ((J.pseudofunctorOver (Type w)).toDescentData f).map φ = descentDataHomOfMod G f Φ) :
    IsModHom ((J.overPullback (Type w) S).obj G) φ :=
  ⟨((J.pseudofunctorOver (Type w)).toDescentData f).map_injective
    (Pseudofunctor.DescentData.hom_ext fun i ↦ by
      have h : (J.overMapPullback (Type w) (f i)).map φ = (Φ.hom i).hom :=
        congrArg (fun χ ↦ χ.hom i) hφ
      have := (Φ.hom i).isModHom.smul_hom
      rw [← h] at this
      exact (((J.overMapPullback (Type w) (f i)).map_comp _ _).trans this).trans
        ((J.overMapPullback (Type w) (f i)).map_comp ((J.overPullback (Type w) S).obj G ◁ φ)
          γ[(J.overPullback (Type w) S).obj G, Q.X]).symm)⟩

variable {f} in
/-- If restriction of sheaves of types to descent data along `f` is fully faithful, so is
restriction of `G`-objects. -/
noncomputable def fullyFaithfulToDescentDataOfSheaf
    (hF : ((J.pseudofunctorOver (Type w)).toDescentData f).FullyFaithful) :
    ((J.pseudofunctorModOver G).toDescentData f).FullyFaithful where
  preimage {P Q} Φ :=
    letI := isModHom_of_toDescentData_map_eq G hF.faithful (P := P) (Q := Q) Φ
      (hF.preimage (descentDataHomOfMod G f Φ)) (hF.map_preimage _)
    Mod.Hom.mk (A := (J.overPullback (Type w) S).obj G) (M := P) (N := Q)
      (hF.preimage (descentDataHomOfMod G f Φ))
  map_preimage {P Q} Φ := by
    ext i
    apply Mod.hom_ext
    exact congrArg (fun χ ↦ χ.hom i) (hF.map_preimage (descentDataHomOfMod G f Φ))
  preimage_map {P Q} φ := by
    apply Mod.hom_ext
    exact hF.preimage_map φ.hom

end Descent

/-- Morphisms of `G`-objects glue: the pseudofunctor of `G`-objects is a prestack. -/
instance isPrestack_pseudofunctorModOver : (J.pseudofunctorModOver G).IsPrestack J :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun _ R hR ↦
    ⟨⟨fullyFaithfulToDescentDataOfSheaf G
      ((J.pseudofunctorOver (Type w)).isPrestackFor' R hR).fullyFaithful⟩⟩

namespace PseudofunctorModOver

/-- An action transported along an isomorphism `ε₁ : A₁ ≅ B₁`, as in `ModObj.ofIso`, commutes
with a morphism `c : A₁ ⟶ A₂` conjugate to an equivariant morphism `t : B₁ ⟶ B₂`. -/
private lemma transported_smul_comm {𝒟 : Type*} [Category 𝒟] [MonoidalCategory 𝒟] {M : 𝒟}
    [MonObj M] {A₁ A₂ B₁ B₂ : 𝒟} [ModObj M B₁] [ModObj M B₂] (ε₁ : A₁ ≅ B₁) (ε₂ : A₂ ≅ B₂)
    (t : B₁ ⟶ B₂) [IsModHom M t] (c : A₁ ⟶ A₂) (hc : ε₁.hom ≫ t = c ≫ ε₂.hom)
    (d : M ⊗ A₁ ⟶ M ⊗ A₂) (hd : d = M ◁ c) :
    ((M ◁ ε₁.hom) ≫ γ[M, B₁] ≫ ε₁.inv) ≫ c = d ≫ (M ◁ ε₂.hom) ≫ γ[M, B₂] ≫ ε₂.inv := by
  subst hd
  obtain rfl : c = ε₁.hom ≫ t ≫ ε₂.inv := by rw [reassoc_of% hc]; simp
  simp

/-- An action transported along an isomorphism `ε : A ≅ B` satisfies the unit axiom. -/
private lemma transported_one_smul {𝒟 : Type*} [Category 𝒟] [MonoidalCategory 𝒟] {M : 𝒟}
    [MonObj M] {A B : 𝒟} [ModObj M B] (ε : A ≅ B) :
    η[M] ▷ A ≫ (M ◁ ε.hom ≫ γ[M, B] ≫ ε.inv) = (λ_ A).hom := by
  rw [← MonoidalCategory.whisker_exchange_assoc, ModObj.one_smul_self_assoc,
    MonoidalCategory.leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- An action transported along an isomorphism `ε : A ≅ B` satisfies the multiplication
axiom. -/
private lemma transported_mul_smul {𝒟 : Type*} [Category 𝒟] [MonoidalCategory 𝒟] {M : 𝒟}
    [MonObj M] {A B : 𝒟} [ModObj M B] (ε : A ≅ B) :
    μ[M] ▷ A ≫ (M ◁ ε.hom ≫ γ[M, B] ≫ ε.inv) =
      (α_ M M A).hom ≫ M ◁ (M ◁ ε.hom ≫ γ[M, B] ≫ ε.inv) ≫
        (M ◁ ε.hom ≫ γ[M, B] ≫ ε.inv) := by
  rw [← MonoidalCategory.whisker_exchange_assoc, ModObj.mul_smul_self_assoc]
  simp

variable {S : C} {ι : Type*} {X : ι → C} {f : ∀ i, X i ⟶ S}
  [((J.pseudofunctorOver (Type w)).toDescentData f).IsEquivalence]
  (D : (J.pseudofunctorModOver G).DescentData f)

/-- The objects of a descent datum of `G`-objects. -/
abbrev descentObj (i : ι) :
    Mod (Sheaf (J.over (X i)) (Type w)) ((J.overPullback (Type w) (X i)).obj G) :=
  D.obj i

/-- The descent datum of underlying sheaves of a descent datum of `G`-objects. -/
abbrev descentDataForget : (J.pseudofunctorOver (Type w)).DescentData f :=
  (Pseudofunctor.DescentData.map f (pseudofunctorModOverForget G)).obj D

/-- The sheaf glued from the underlying descent datum of `D`. -/
noncomputable abbrev glueSheaf : Sheaf (J.over S) (Type w) :=
  ((J.pseudofunctorOver (Type w)).toDescentData f).objPreimage (descentDataForget G D)

/-- The descent datum of `glueSheaf G D` is that of the underlying sheaves of `D`. -/
noncomputable abbrev glueSheafIso :
    ((J.pseudofunctorOver (Type w)).toDescentData f).obj (glueSheaf G D) ≅
      descentDataForget G D :=
  ((J.pseudofunctorOver (Type w)).toDescentData f).objObjPreimageIso (descentDataForget G D)

/-- The restriction of `glueSheaf G D` along `f i` is the underlying sheaf of `D.obj i`. -/
noncomputable def glueSheafIsoApp (i : ι) :
    (J.overMapPullback (Type w) (f i)).obj (glueSheaf G D) ≅ (descentObj G D i).X where
  hom := (glueSheafIso G D).hom.hom i
  inv := (glueSheafIso G D).inv.hom i
  hom_inv_id := congrArg (fun χ ↦ χ.hom i) (glueSheafIso G D).hom_inv_id
  inv_hom_id := congrArg (fun χ ↦ χ.hom i) (glueSheafIso G D).inv_hom_id

/-- The action of `D.obj i`, transported to the restriction of `glueSheaf G D` along `f i`. -/
noncomputable def glueSmulApp (i : ι) :
    (J.overPullback (Type w) (X i)).obj G ⊗ (J.overMapPullback (Type w) (f i)).obj (glueSheaf G D) ⟶
      (J.overMapPullback (Type w) (f i)).obj (glueSheaf G D) :=
  (J.overPullback (Type w) (X i)).obj G ◁ (glueSheafIsoApp G D i).hom ≫
    γ[(J.overPullback (Type w) (X i)).obj G, (descentObj G D i).X] ≫ (glueSheafIsoApp G D i).inv

/-- The transported actions on the restrictions of `glueSheaf G D` form a morphism of descent
data, because the gluing morphisms of `D` are equivariant. -/
noncomputable def glueSmulDescent :
    ((J.pseudofunctorOver (Type w)).toDescentData f).obj
        ((J.overPullback (Type w) S).obj G ⊗ glueSheaf G D : Sheaf (J.over S) (Type w)) ⟶
      ((J.pseudofunctorOver (Type w)).toDescentData f).obj (glueSheaf G D) where
  hom i := glueSmulApp G D i
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    let t : (J.overMapPullback (Type w) f₁).obj (descentObj G D i₁).X ⟶
        (J.overMapPullback (Type w) f₂).obj (descentObj G D i₂).X := (D.hom q f₁ f₂ hf₁ hf₂).hom
    have : IsModHom ((J.overPullback (Type w) Y).obj G) t :=
      ⟨(D.hom q f₁ f₂ hf₁ hf₂).isModHom.smul_hom⟩
    have key := transported_smul_comm (M := (J.overPullback (Type w) Y).obj G)
      ((J.overMapPullback (Type w) f₁).mapIso (glueSheafIsoApp G D i₁))
      ((J.overMapPullback (Type w) f₂).mapIso (glueSheafIsoApp G D i₂)) t _
      ((glueSheafIso G D).hom.comm q f₁ f₂ hf₁ hf₂) _
      (toDescentData_obj_tensor_hom G f (glueSheaf G D) q f₁ f₂ hf₁ hf₂)
    exact key

/-- The glued action on `glueSheaf G D`: the morphism whose restrictions along the `f i` are the
transported actions. -/
noncomputable def glueSmul :
    (J.overPullback (Type w) S).obj G ⊗ glueSheaf G D ⟶ glueSheaf G D :=
  ((J.pseudofunctorOver (Type w)).toDescentData f).preimage (glueSmulDescent G D)

lemma overMapPullback_map_glueSmul (i : ι) :
    (J.overMapPullback (Type w) (f i)).map (glueSmul G D) = glueSmulApp G D i :=
  congrArg (fun χ ↦ χ.hom i)
    (((J.pseudofunctorOver (Type w)).toDescentData f).map_preimage (glueSmulDescent G D))

/-- The glued action is an action: its axioms hold after restriction along every `f i`, where
they are those of the transported actions. -/
noncomputable instance modObjGlueSheaf :
    ModObj ((J.overPullback (Type w) S).obj G) (glueSheaf G D) where
  smul := glueSmul G D
  one_smul := by
    change η[_] ▷ glueSheaf G D ≫ glueSmul G D = (λ_ (glueSheaf G D)).hom
    refine hom_ext_of_faithful_toDescentData (f := f) fun i ↦ ?_
    rw [Functor.map_comp, overMapPullback_map_one_whiskerRight, overMapPullback_map_glueSmul,
      overMapPullback_map_leftUnitor_hom]
    exact transported_one_smul (glueSheafIsoApp G D i)
  mul_smul := by
    change μ[_] ▷ glueSheaf G D ≫ glueSmul G D =
      (α_ _ _ _).hom ≫ (J.overPullback (Type w) S).obj G ◁ glueSmul G D ≫ glueSmul G D
    refine hom_ext_of_faithful_toDescentData (f := f) fun i ↦ ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
      overMapPullback_map_mul_whiskerRight, overMapPullback_map_associator_hom,
      overMapPullback_map_whiskerLeft, overMapPullback_map_glueSmul]
    exact transported_mul_smul (glueSheafIsoApp G D i)

lemma smul_glueSheaf : γ[(J.overPullback (Type w) S).obj G, glueSheaf G D] = glueSmul G D :=
  rfl

/-- The `G`-object glued from a descent datum of `G`-objects. -/
noncomputable abbrev glueMod :
    Mod (Sheaf (J.over S) (Type w)) ((J.overPullback (Type w) S).obj G) :=
  .mk (glueSheaf G D)

/-- The descent datum of the glued `G`-object is isomorphic to `D`. -/
noncomputable def glueModIso :
    ((J.pseudofunctorModOver G).toDescentData f).obj (glueMod G D) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦ modIsoMk (P := (modOverMap G (f i)).obj (glueMod G D)) (Q := descentObj G D i)
      (glueSheafIsoApp G D i) (by
        change (J.overMapPullback (Type w) (f i)).map (glueSmul G D) ≫ _ = _
        rw [overMapPullback_map_glueSmul]
        dsimp only [glueSmulApp]
        erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl))
    (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ Mod.hom_ext _ _ (by
      have := (glueSheafIso G D).hom.comm q f₁ f₂ hf₁ hf₂
      rw [← pseudofunctorModOver_toDescentData_obj_hom_hom G f (glueMod G D)] at this
      exact this))

end PseudofunctorModOver

open PseudofunctorModOver in
variable [(J.pseudofunctorOver (Type w)).IsStack J] in
/-- Objects with an action of `G` glue: the pseudofunctor of `G`-objects is a stack whenever
sheaves of types on the slices form one, for instance when every covering sieve contains a
`w`-small covering family (`GrothendieckTopology.isStack_pseudofunctorOver`). -/
instance isStack_pseudofunctorModOver : (J.pseudofunctorModOver G).IsStack J where
  essSurj_of_sieve R hR := by
    have := ((J.pseudofunctorOver (Type w)).isStackFor' R hR).isEquivalence
    exact ⟨fun D ↦ ⟨glueMod G D, ⟨glueModIso G D⟩⟩⟩

end CategoryTheory.GrothendieckTopology
