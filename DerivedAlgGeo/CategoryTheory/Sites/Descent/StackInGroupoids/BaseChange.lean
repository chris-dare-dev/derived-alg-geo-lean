/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representability

/-!
# Base change and composition of representable morphisms of stacks

Representable morphisms of stacks in groupoids, in the sense of
`CategoryTheory.StackMorphism.IsRepresentable`, are stable under base change along an arbitrary
morphism and under composition. The fibre of a base change `X ×_Y Y' ⟶ Y'` over `y'` is the fibre
of `f : X ⟶ Y` over `g(y')`, naturally in the test object, so a base change has the same
representing objects as `f`. The fibre of `f ≫ g` over `z` is represented by `R_f ⟶ R_g ⟶ S`,
where `R_g` represents the fibre of `g` over `z` and `R_f` the fibre of `f` over the universal
object of `R_g`.

## Main definitions

* `CategoryTheory.StackMorphism.fiberCategoryBaseChangeEquiv`: the fibre of the second projection
  of `StackInGroupoids.fiberProduct f g` over `y'` is equivalent to the fibre of `f` over `g(y')`.
* `CategoryTheory.StackMorphism.fiberIsoClassesBaseChangeIso`: the induced isomorphism of the
  presheaves of isomorphism classes, natural in the test object.

## Main results

* `CategoryTheory.StackMorphism.isRepresentable_baseChange` and
  `CategoryTheory.StackMorphism.HasRepresentableProperty.baseChange`: base change preserves
  representability and every property of the representing morphisms.
* `CategoryTheory.StackMorphism.isRepresentable_comp` and
  `CategoryTheory.StackMorphism.HasRepresentableProperty.comp`: composition preserves
  representability, and a property of the representing morphisms that is stable under
  composition.

## Implementation notes

Neither proof uses fibre products in the site: base change keeps the representing objects of `f`,
and the composite is represented by `(Over.map R_g.hom).obj R_f`. The bijection for the composite
is injective because the fibre functors of `g` are faithful, which makes the fibres of `g` thin;
condition (2) of `StackMorphism.IsRepresentable` alone gives only a surjection. The universal
object of `R_g` is a representative of a class, chosen with `Quotient.out`; the construction takes
any representative, so nothing depends on the choice.

Base change is stated for stacks whose fibres have object universe `max v' u'`, where
`StackInGroupoids.fiberProduct` is defined; composition is stated in any fibre universes.

## References

* [Stacks Project, Tag 02ZT](https://stacks.math.columbia.edu/tag/02ZT), Lemma 94.6.4
* [Stacks Project, Tag 02ZS](https://stacks.math.columbia.edu/tag/02ZS), Lemma 94.6.3
* [Stacks Project, Tag 02Y5](https://stacks.math.columbia.edu/tag/02Y5), Lemma 4.42.1

## Tags

stack in groupoids, representable morphism, base change, composition, 2-fibre product
-/

set_option backward.isDefEq.respectTransparency false

universe v' v u' u

namespace CategoryTheory

open Opposite Bicategory Limits CategoricalPullback
open scoped Pseudofunctor.StrongTrans

noncomputable section

namespace StackMorphism

section Coherence

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (α : F ⟶ G)

/-- The naturality isomorphism of a strong transformation along a composite, against the
compositors of its source and target. -/
@[reassoc]
private lemma naturality_inv_app_comp_map_mapComp'_hom {a b c : LocallyDiscrete Cᵒᵖ}
    (φ : a ⟶ b) (ψ : b ⟶ c) (φψ : a ⟶ c) (h : φ ≫ ψ = φψ) (x : F.obj a) :
    (α.naturality φψ).inv.toNatTrans.app x ≫
        (α.app c).toFunctor.map ((F.mapComp' φ ψ φψ h).hom.toNatTrans.app x) =
      (G.mapComp' φ ψ φψ h).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map ψ).toFunctor.map ((α.naturality φ).inv.toNatTrans.app x) ≫
          (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x) := by
  subst h
  simp [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.StrongTrans.naturality_comp_inv_app,
    ← Functor.map_comp]

/-- The coherence behind restriction of a fibre along a composite. -/
private lemma mapComp'_comp_key {s b₁ b₂ b₃ : LocallyDiscrete Cᵒᵖ} (p₁ : s ⟶ b₁) (p₂ : s ⟶ b₂)
    (p₃ : s ⟶ b₃) (φ : b₁ ⟶ b₂) (ψ : b₂ ⟶ b₃) (φψ : b₁ ⟶ b₃) (h₁ : p₁ ≫ φ = p₂)
    (h₂ : p₂ ≫ ψ = p₃) (h₃ : p₁ ≫ φψ = p₃) (h : φ ≫ ψ = φψ) (y : G.obj s) (x : F.obj b₁)
    (u : (G.map p₁).toFunctor.obj y ⟶ (α.app b₁).toFunctor.obj x) :
    (G.mapComp' p₁ φψ p₃ h₃).hom.toNatTrans.app y ≫ (G.map φψ).toFunctor.map u ≫
        (α.naturality φψ).inv.toNatTrans.app x ≫
          (α.app b₃).toFunctor.map ((F.mapComp' φ ψ φψ h).hom.toNatTrans.app x) =
      (G.mapComp' p₂ ψ p₃ h₂).hom.toNatTrans.app y ≫
        (G.map ψ).toFunctor.map ((G.mapComp' p₁ φ p₂ h₁).hom.toNatTrans.app y ≫
          (G.map φ).toFunctor.map u ≫ (α.naturality φ).inv.toNatTrans.app x) ≫
          (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x) := by
  rw [naturality_inv_app_comp_map_mapComp'_hom,
    Pseudofunctor.mapComp'_hom_naturality_assoc,
    G.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc p₁ φ ψ p₂ φψ p₃ h₁ h h₃]
  simp

end Coherence

/-- A functor induces a map of isomorphism classes. -/
private def isoClassesMap {A B : Type*} [Category A] [Category B] (F : A ⥤ B) :
    _root_.Quotient (isIsomorphicSetoid A) → _root_.Quotient (isIsomorphicSetoid B) :=
  Quot.map F.obj fun _ _ ⟨e⟩ ↦ ⟨F.mapIso e⟩

/-- An equivalence of categories induces a bijection of isomorphism classes. -/
private def isoClassesEquiv {A B : Type*} [Category A] [Category B] (E : A ≌ B) :
    _root_.Quotient (isIsomorphicSetoid A) ≃ _root_.Quotient (isIsomorphicSetoid B) where
  toFun := isoClassesMap E.functor
  invFun := isoClassesMap E.inverse
  left_inv := by
    rintro ⟨a⟩
    exact Quot.sound ⟨(E.unitIso.app a).symm⟩
  right_inv := by
    rintro ⟨b⟩
    exact Quot.sound ⟨E.counitIso.app b⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section BaseChange

variable {X Y Y' : StackInGroupoids.{v', v, max v' u', u} C J}

variable (f : StackMorphism X Y) (g : StackMorphism Y' Y) {S : C}
  (y' : Y'.presheaf.obj (.mk (op S)))

/-- The fibre of the base change over `y'` maps to the fibre of `f` over `g(y')`: a pair
`((x, y'', e : f x ≅ g y''), φ : y'|_T ⟶ y'')` goes to `(x, (g y')|_T ≅ g(y'|_T) ⟶ g y'' ⟶ f x)`,
through the naturality isomorphism of `g`, `g(φ)` and `e⁻¹`. -/
private def baseChangeFiberFunctor (T : Over S) :
    StructuredArrow ((Y'.presheaf.map T.hom.op.toLoc).toFunctor.obj y')
        (π₂ (f.app T.left) (g.app T.left)) ⥤
      StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
        (f.app T.left) where
  obj a := StructuredArrow.mk (Y := a.right.fst)
    ((g.naturality T.hom.op.toLoc).inv.toNatTrans.app y' ≫ (g.app T.left).map a.hom ≫
      a.right.iso.inv)
  map {a b} m := StructuredArrow.homMk m.right.fst (by
    have h₁ : a.hom ≫ m.right.snd = b.hom := StructuredArrow.w m
    simp [← h₁])

/-- The object `(x, y'|_T, f x ≅ (g y')|_T ≅ g(y'|_T))` of the 2-fibre product attached to a pair
`(x, ψ)` in the fibre of `f` over `g(y')`. -/
private def baseChangeFiberInverseObj (T : Over S)
    (b : StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
      (f.app T.left)) : (f.app T.left) ⊡ (g.app T.left) :=
  ⟨b.right, (Y'.presheaf.map T.hom.op.toLoc).toFunctor.obj y',
    (asIso b.hom).symm ≪≫ (Cat.Hom.toNatIso (g.naturality T.hom.op.toLoc)).symm.app y'⟩

private lemma baseChangeFiberInverseObj_iso_hom (T : Over S)
    (b : StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
      (f.app T.left)) :
    (baseChangeFiberInverseObj f g y' T b).iso.hom =
      inv b.hom ≫ (g.naturality T.hom.op.toLoc).inv.toNatTrans.app y' :=
  rfl

/-- The morphism of the 2-fibre product attached to a morphism of the fibre of `f`. -/
private def baseChangeFiberInverseMap (T : Over S)
    {b b' : StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
      (f.app T.left)} (m : b ⟶ b') :
    baseChangeFiberInverseObj f g y' T b ⟶ baseChangeFiberInverseObj f g y' T b' where
  fst := m.right
  snd := 𝟙 _
  w := by
    have h₁ : b.hom ≫ (f.app T.left).map m.right = b'.hom := StructuredArrow.w m
    rw [baseChangeFiberInverseObj_iso_hom, baseChangeFiberInverseObj_iso_hom, Functor.map_id,
      Category.comp_id, ← h₁, IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc]

/-- The fibre of `f` over `g(y')` maps back to the fibre of the base change over `y'`, sending
`(x, ψ)` to `((x, y'|_T, f x ≅ g(y'|_T)), 𝟙)`. -/
private def baseChangeFiberInverse (T : Over S) :
    StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
        (f.app T.left) ⥤
      StructuredArrow ((Y'.presheaf.map T.hom.op.toLoc).toFunctor.obj y')
        (π₂ (f.app T.left) (g.app T.left)) where
  obj b := StructuredArrow.mk (T := π₂ (f.app T.left) (g.app T.left))
    (Y := baseChangeFiberInverseObj f g y' T b) (𝟙 _)
  map {b b'} m := StructuredArrow.homMk
    (f := StructuredArrow.mk (T := π₂ (f.app T.left) (g.app T.left))
      (Y := baseChangeFiberInverseObj f g y' T b) (𝟙 _))
    (f' := StructuredArrow.mk (T := π₂ (f.app T.left) (g.app T.left))
      (Y := baseChangeFiberInverseObj f g y' T b') (𝟙 _))
    (baseChangeFiberInverseMap f g y' T m) (Category.comp_id _)
  map_id _ := rfl
  map_comp _ _ := by
    apply StructuredArrow.hom_ext
    apply CategoricalPullback.hom_ext
    · rfl
    · exact (Category.comp_id _).symm

/-- The unit of `baseChangeFiberEquiv`, `(𝟙, φ⁻¹)` on the 2-fibre product. -/
private def baseChangeFiberUnitIso (T : Over S)
    (a : StructuredArrow ((Y'.presheaf.map T.hom.op.toLoc).toFunctor.obj y')
      (π₂ (f.app T.left) (g.app T.left))) :
    a ≅ (baseChangeFiberInverse f g y' T).obj ((baseChangeFiberFunctor f g y' T).obj a) :=
  StructuredArrow.isoMk (mkIso (Iso.refl a.right.fst) (asIso a.hom).symm (by
    change (f.app T.left).map (𝟙 _) ≫ inv ((g.naturality T.hom.op.toLoc).inv.toNatTrans.app y' ≫
      (g.app T.left).map a.hom ≫ a.right.iso.inv) ≫
        (g.naturality T.hom.op.toLoc).inv.toNatTrans.app y' =
      a.right.iso.hom ≫ (g.app T.left).map (inv a.hom)
    simp)) (by
    change a.hom ≫ inv a.hom = 𝟙 _
    simp)

/-- The counit of `baseChangeFiberEquiv`, an identity. -/
private def baseChangeFiberCounitIso (T : Over S)
    (b : StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
      (f.app T.left)) :
    (baseChangeFiberFunctor f g y' T).obj ((baseChangeFiberInverse f g y' T).obj b) ≅ b :=
  StructuredArrow.isoMk (Iso.refl _) (by
    change ((g.naturality T.hom.op.toLoc).inv.toNatTrans.app y' ≫ (g.app T.left).map (𝟙 _) ≫
      (g.naturality T.hom.op.toLoc).hom.toNatTrans.app y' ≫ b.hom) ≫ (f.app T.left).map (𝟙 _) =
        b.hom
    simp)

/-- `baseChangeFiberFunctor` is an equivalence of the structured-arrow categories underlying the
two fibres. -/
private def baseChangeFiberEquiv (T : Over S) :
    StructuredArrow ((Y'.presheaf.map T.hom.op.toLoc).toFunctor.obj y')
        (π₂ (f.app T.left) (g.app T.left)) ≌
      StructuredArrow ((Y.presheaf.map T.hom.op.toLoc).toFunctor.obj ((g.app S).obj y'))
        (f.app T.left) :=
  Equivalence.mk (baseChangeFiberFunctor f g y' T) (baseChangeFiberInverse f g y' T)
    (NatIso.ofComponents (baseChangeFiberUnitIso f g y' T) (fun {a b} m ↦ by
      ext
      · change m.right.fst ≫ 𝟙 _ = 𝟙 _ ≫ m.right.fst
        simp
      · change m.right.snd ≫ inv b.hom = inv a.hom ≫ 𝟙 _
        have h₁ : a.hom ≫ m.right.snd = b.hom := StructuredArrow.w m
        simp [← h₁]))
    (NatIso.ofComponents (baseChangeFiberCounitIso f g y' T) (fun _ ↦ by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- The fibre of the base change `X ×_Y Y' ⟶ Y'` of `f` along `g` over `y'` at `T` is equivalent to
the fibre of `f` over `g(y')` at `T`, as in the proof of
[Stacks Project, Tag 02ZT](https://stacks.math.columbia.edu/tag/02ZT), with the fibres described
by [Stacks Project, Tag 02Y5](https://stacks.math.columbia.edu/tag/02Y5) (Lemma 4.42.1). A pair
`((x, y'', e : f x ≅ g y''), φ : y'|_T ⟶ y'')` goes to `(x, (g y')|_T ≅ g(y'|_T) ⟶ g y'' ⟶ f x)`,
through the naturality isomorphism of `g`, `g(φ)` and `e⁻¹`. -/
def fiberCategoryBaseChangeEquiv (T : Over S) :
    (StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).FiberCategory y' T ≌
      f.FiberCategory ((g.app S).obj y') T :=
  (baseChangeFiberEquiv f g y' T).core

/-- `baseChangeFiberFunctor` commutes with restriction along `t`, on the structure morphisms. -/
private lemma baseChangeFiberFunctor_fiberMap {T₀ T₁ : Over S} (t : T₁ ⟶ T₀)
    (a : StructuredArrow ((Y'.presheaf.map T₀.hom.op.toLoc).toFunctor.obj y')
      (π₂ (f.app T₀.left) (g.app T₀.left))) :
    ((baseChangeFiberFunctor f g y' T₁).obj
      (((StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).fiberMap y' t).obj a)).hom =
    ((f.fiberMap ((g.app S).obj y') t).obj ((baseChangeFiberFunctor f g y' T₀).obj a)).hom := by
  simp only [baseChangeFiberFunctor, fiberMap, StructuredArrow.mk_hom_eq_self,
    StructuredArrow.map₂_obj_hom, StructuredArrow.map₂_obj_right, Functor.map_comp,
    Category.assoc]
  erw [Pseudofunctor.fiberProduct.map_obj_iso_inv]
  have h₀ : ((StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).naturality
      t.left.op.toLoc).inv.toNatTrans.app a.right = 𝟙 _ := rfl
  erw [h₀, Functor.map_id, Category.id_comp]
  erw [(g.naturality t.left.op.toLoc).hom.toNatTrans.naturality_assoc]
  rw [naturality_inv_app_comp_map_mapComp'_hom_assoc]
  simp

/-- The presheaf of isomorphism classes of the fibre of the base change `X ×_Y Y' ⟶ Y'` over `y'`
is isomorphic to that of `f` over `g(y')`, naturally in the test object: the equivalences
`StackMorphism.fiberCategoryBaseChangeEquiv` commute with restriction up to isomorphism. -/
def fiberIsoClassesBaseChangeIso :
    (StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).fiberIsoClasses y' ≅
      f.fiberIsoClasses ((g.app S).obj y') :=
  NatIso.ofComponents
    (fun T ↦ (isoClassesEquiv (fiberCategoryBaseChangeEquiv f g y' T.unop)).toIso)
    (fun {T T'} t ↦ by
      ext ⟨a⟩
      exact Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (Iso.refl _)
        (by
          rw [Iso.refl_hom, Functor.map_id, Category.comp_id]
          exact baseChangeFiberFunctor_fiberMap f g y' t.unop a.of))⟩)

/-- The second projection of `X ×_Y Y'` is faithful on the fibres over `T` where `f` is: two
morphisms with the same second component have the same image under `f`. -/
private lemma faithful_snd_app (T : C) [(f.app T).Faithful] :
    ((StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).app T).Faithful where
  map_injective {p q} m₁ m₂ h := by
    change m₁.snd = m₂.snd at h
    refine CategoricalPullback.hom_ext ?_ h
    apply (f.app T).map_injective
    rw [← cancel_mono q.iso.hom, Hom.w, Hom.w, h]

/-- The base change `X ×_Y Y' ⟶ Y'` of a representable morphism `f : X ⟶ Y` along any
`g : Y' ⟶ Y` is representable
([Stacks Project, Tag 02ZT](https://stacks.math.columbia.edu/tag/02ZT), Lemma 94.6.4). The
fibre over `y'` has the presheaf of classes of the fibre of `f` over `g(y')`, by
`StackMorphism.fiberIsoClassesBaseChangeIso`, so it has the same representing objects. -/
instance isRepresentable_baseChange [f.IsRepresentable] :
    (StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).IsRepresentable where
  faithful T :=
    have := IsRepresentable.faithful (f := f) T
    faithful_snd_app f g T
  representable {S} y' := by
    have := IsRepresentable.representable (f := f) ((g.app S).obj y')
    exact ((f.fiberIsoClasses _).representableBy.ofIso
      (fiberIsoClassesBaseChangeIso f g y').symm).isRepresentable

/-- The base change `X ×_Y Y' ⟶ Y'` of a morphism `f : X ⟶ Y` representable with property `P` is
representable with property `P`, for any `g : Y' ⟶ Y`. Stacks Lemma 94.6.4
([Stacks Project, Tag 02ZT](https://stacks.math.columbia.edu/tag/02ZT)) states only
representability.

No hypothesis on `P` is needed, in particular not `MorphismProperty.IsStableUnderBaseChange`: by
`StackMorphism.fiberIsoClassesBaseChangeIso` the fibre presheaves of the base change are those of
`f`, so every object representing a fibre of the base change represents a fibre of `f`, and the
base change has the same representing objects as `f`. -/
theorem HasRepresentableProperty.baseChange {P : MorphismProperty C}
    [hf : f.HasRepresentableProperty P] :
    (StackInGroupoids.fiberProduct.snd.{v', v, u'} f g).HasRepresentableProperty P where
  isRepresentable := inferInstance
  property y' _ e := hf.property _ (e.ofIso (fiberIsoClassesBaseChangeIso f g y'))

end BaseChange

section Comp

variable {X Y Z : StackInGroupoids.{v', v, u', u} C J} (f : StackMorphism X Y)
  (g : StackMorphism Y Z)

/-- A composite is faithful on the fibres over `T` where both factors are. -/
private lemma faithful_comp_app (T : C) [(f.app T).Faithful] [(g.app T).Faithful] :
    ((comp f g).app T).Faithful :=
  Functor.Faithful.comp (f.app T) (g.app T)

variable {S : C} (z : Z.presheaf.obj (.mk (op S)))

/-- Given `(y, ψ)` in the fibre of `g` over `z`, a pair `(x, φ : y ⟶ f x)` gives the pair
`(x, ψ ≫ g(φ))` in the fibre of `f ≫ g` over `z`. -/
private def compFiberFunctor {T : Over S}
    (b : StructuredArrow ((Z.presheaf.map T.hom.op.toLoc).toFunctor.obj z) (g.app T.left)) :
    StructuredArrow b.right (f.app T.left) ⥤
      StructuredArrow ((Z.presheaf.map T.hom.op.toLoc).toFunctor.obj z) ((comp f g).app T.left) :=
  StructuredArrow.post b.right (f.app T.left) (g.app T.left) ⋙ StructuredArrow.map b.hom

/-- A pair `(x, ψ)` in the fibre of `f ≫ g` over `z` gives the pair `(f x, ψ)` in the fibre of
`g`. -/
private def compFiberProj (T : Over S) :
    StructuredArrow ((Z.presheaf.map T.hom.op.toLoc).toFunctor.obj z) ((comp f g).app T.left) ⥤
      StructuredArrow ((Z.presheaf.map T.hom.op.toLoc).toFunctor.obj z) (g.app T.left) :=
  StructuredArrow.pre _ (f.app T.left) (g.app T.left)

variable {f g z} {R : Over S} (e : (g.fiberIsoClasses z).RepresentableBy R)
  (u : g.FiberCategory z R) (hu : _root_.Quotient.mk _ u = e.homEquiv (𝟙 R))

include hu in
/-- The class corresponding to `t : T ⟶ R` is the restriction of the universal object `u`. -/
private lemma homEquiv_eq_mk {T : Over S} (t : T ⟶ R) :
    e.homEquiv t = _root_.Quotient.mk _ (Core.mk ((g.fiberMap z t).obj u.of)) := by
  rw [← Category.comp_id t, e.homEquiv_comp, ← hu, fiberIsoClasses_map_mk, Category.comp_id]

variable (f) in
/-- For `t : T ⟶ R`, the classes of the fibre of `f` over the universal object, restricted along
`t`, map to the classes of the fibre of `f ≫ g` over `z` at `T`. -/
private def compClasses {T : Over S} (t : T ⟶ R) :
    (f.fiberIsoClasses u.of.right).obj (op (Over.mk t.left)) →
      ((comp f g).fiberIsoClasses z).obj (op T) :=
  isoClassesMap (compFiberFunctor f g z ((g.fiberMap z t).obj u.of)).core

include hu in
/-- The image of `compClasses t` in the classes of the fibre of `g` is the class of `t`. -/
private lemma proj_compClasses {T : Over S} (t : T ⟶ R)
    (c : (f.fiberIsoClasses u.of.right).obj (op (Over.mk t.left))) :
    isoClassesMap (compFiberProj f g z T).core (compClasses f u t c) = e.homEquiv t := by
  obtain ⟨a⟩ := c
  rw [homEquiv_eq_mk e u hu]
  exact Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (asIso a.of.hom).symm (by
    simp [compFiberProj, compFiberFunctor]
    rfl))⟩

/-- `compClasses t` is injective when the fibre functor of `g` over `T` is faithful. -/
private lemma compClasses_injective {T : Over S} (t : T ⟶ R) [(g.app T.left).Faithful] :
    Function.Injective (compClasses f u t) := by
  rintro ⟨a₁⟩ ⟨a₂⟩ h
  obtain ⟨γ⟩ := Quotient.exact (s := isIsomorphicSetoid _) h
  refine Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk
    ((StructuredArrow.proj ((Z.presheaf.map T.hom.op.toLoc).toFunctor.obj z)
      ((comp f g).app T.left)).mapIso γ.hom.iso) ?_)⟩
  have w := StructuredArrow.w γ.hom.iso.hom
  apply (g.app T.left).map_injective
  rw [← cancel_epi ((g.fiberMap z t).obj u.of).hom, Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans w

include hu in
/-- Every class of the fibre of `f ≫ g` over `z` lies in the image of some `compClasses t`. -/
private lemma compClasses_surjective {T : Over S}
    (c : ((comp f g).fiberIsoClasses z).obj (op T)) :
    ∃ (t : T ⟶ R) (c' : (f.fiberIsoClasses u.of.right).obj (op (Over.mk t.left))),
      compClasses f u t c' = c := by
  obtain ⟨x⟩ := c
  let t := e.homEquiv.symm (isoClassesMap (compFiberProj f g z T).core (Quot.mk _ x))
  have ht : _root_.Quotient.mk (isIsomorphicSetoid _) (Core.mk ((g.fiberMap z t).obj u.of)) =
      _root_.Quotient.mk _ ((compFiberProj f g z T).core.obj x) := by
    rw [← homEquiv_eq_mk e u hu, Equiv.apply_symm_apply]
    rfl
  obtain ⟨β⟩ := Quotient.exact ht
  refine ⟨t, Quot.mk _ (Core.mk (StructuredArrow.mk (Y := x.of.right) β.hom.iso.hom.right)),
    Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  rw [Iso.refl_hom, Functor.map_id, Category.comp_id]
  exact StructuredArrow.w β.hom.iso.hom

/-- The structure morphisms of test objects compose along a morphism of test objects. -/
private lemma toLoc_comp_eq' {B : C} {T T' : Over B} (h : T' ⟶ T) :
    T.hom.op.toLoc ≫ h.left.op.toLoc = T'.hom.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w]

variable (f) in
/-- `compClasses` commutes with restriction along a morphism of test objects. -/
private lemma compClasses_naturality {T T' : Over S} (h : T' ⟶ T) (t : T ⟶ R)
    (c : (f.fiberIsoClasses u.of.right).obj (op (Over.mk t.left))) :
    compClasses f u (h ≫ t) ((f.fiberIsoClasses u.of.right).map
      (Over.homMk h.left : Over.mk (h ≫ t).left ⟶ Over.mk t.left).op c) =
    ((comp f g).fiberIsoClasses z).map h.op (compClasses f u t c) := by
  obtain ⟨a⟩ := c
  refine Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (Iso.refl _) ?_)⟩
  have hφψ : t.left.op.toLoc ≫ h.left.op.toLoc = (h ≫ t).left.op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.comp_left]
  have key := mapComp'_comp_key g R.hom.op.toLoc T.hom.op.toLoc T'.hom.op.toLoc t.left.op.toLoc
    h.left.op.toLoc (h ≫ t).left.op.toLoc (toLoc_comp_eq' t) (toLoc_comp_eq' h)
    (toLoc_comp_eq' (h ≫ t)) hφψ z u.of.right u.of.hom
  rw [Iso.refl_hom, Functor.map_id, Category.comp_id]
  change ((Z.presheaf.mapComp' R.hom.op.toLoc (h ≫ t).left.op.toLoc T'.hom.op.toLoc
      (toLoc_comp_eq' (h ≫ t))).hom.toNatTrans.app z ≫
      (Z.presheaf.map (h ≫ t).left.op.toLoc).toFunctor.map u.of.hom ≫
      (g.naturality (h ≫ t).left.op.toLoc).inv.toNatTrans.app u.of.right) ≫
    (g.app T'.left).map ((Y.presheaf.mapComp' t.left.op.toLoc h.left.op.toLoc
      (h ≫ t).left.op.toLoc hφψ).hom.toNatTrans.app u.of.right ≫
      (Y.presheaf.map h.left.op.toLoc).toFunctor.map a.of.hom ≫
      (f.naturality h.left.op.toLoc).inv.toNatTrans.app a.of.right) =
    (Z.presheaf.mapComp' T.hom.op.toLoc h.left.op.toLoc T'.hom.op.toLoc
      (toLoc_comp_eq' h)).hom.toNatTrans.app z ≫
      (Z.presheaf.map h.left.op.toLoc).toFunctor.map
        (((Z.presheaf.mapComp' R.hom.op.toLoc t.left.op.toLoc T.hom.op.toLoc
          (toLoc_comp_eq' t)).hom.toNatTrans.app z ≫
          (Z.presheaf.map t.left.op.toLoc).toFunctor.map u.of.hom ≫
          (g.naturality t.left.op.toLoc).inv.toNatTrans.app u.of.right) ≫
          (g.app T.left).map a.of.hom) ≫
      ((comp f g).naturality h.left.op.toLoc).inv.toNatTrans.app a.of.right
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, Category.assoc]
  erw [reassoc_of% key, ← (g.naturality h.left.op.toLoc).inv.toNatTrans.naturality_assoc]
  change _ = _ ≫ _ ≫ ((f ≫ g : X.presheaf ⟶ Z.presheaf).naturality
    h.left.op.toLoc).inv.toNatTrans.app a.of.right
  simp

variable {R' : Over R.left} (e' : (f.fiberIsoClasses u.of.right).RepresentableBy R')

variable (f) in
/-- `compClasses` on the sigma type. -/
private def compSigma (T : Over S) :
    (Σ t : T ⟶ R, (f.fiberIsoClasses u.of.right).obj (op (Over.mk t.left))) →
      ((comp f g).fiberIsoClasses z).obj (op T) :=
  fun σ ↦ compClasses f u σ.1 σ.2

/-- Two pairs `(t, e'(m))` agree when the `t` agree and the `m` have the same underlying
morphism. -/
private lemma sigma_mk_eq {T : Over S} {t₁ t₂ : T ⟶ R} (h : t₁ = t₂)
    {m₁ : Over.mk t₁.left ⟶ R'} {m₂ : Over.mk t₂.left ⟶ R'} (hm : m₁.left = m₂.left) :
    (⟨t₁, e'.homEquiv m₁⟩ :
      Σ t : T ⟶ R, (f.fiberIsoClasses u.of.right).obj (op (Over.mk t.left))) =
        ⟨t₂, e'.homEquiv m₂⟩ := by
  subst h
  obtain rfl : m₁ = m₂ := Over.OverMorphism.ext hm
  rfl

/-- The morphism `T ⟶ R` underlying a morphism `T ⟶ (Over.map R.hom).obj R'`. -/
private abbrev compFst {T : Over S} (k : T ⟶ (Over.map R.hom).obj R') : T ⟶ R :=
  Over.homMk (k.left ≫ R'.hom) (by simpa using Over.w k)

/-- The morphism over `R.left` underlying a morphism `T ⟶ (Over.map R.hom).obj R'`. -/
private abbrev compSnd {T : Over S} (k : T ⟶ (Over.map R.hom).obj R') :
    Over.mk (compFst k).left ⟶ R' :=
  Over.homMk k.left rfl

include hu in
/-- The representation of the fibre of a composite. -/
private def compRepresentableBy (hg : ∀ T : Over S, (g.app T.left).Faithful) :
    ((comp f g).fiberIsoClasses z).RepresentableBy ((Over.map R.hom).obj R') where
  homEquiv {T} := Equiv.ofBijective
    (fun k ↦ compClasses f u (compFst k) (e'.homEquiv (compSnd k))) (by
      constructor
      · intro k₁ k₂ hk
        have h₁ : compFst k₁ = compFst k₂ := e.homEquiv.injective (by
          rw [← proj_compClasses e u hu (compFst k₁) (e'.homEquiv (compSnd k₁)),
            ← proj_compClasses e u hu (compFst k₂) (e'.homEquiv (compSnd k₂))]
          exact congrArg _ hk)
        let m : Over.mk (compFst k₂).left ⟶ R' :=
          Over.homMk k₁.left (congrArg CommaMorphism.left h₁)
        have h₂ : compClasses f u (compFst k₂) (e'.homEquiv m) =
            compClasses f u (compFst k₂) (e'.homEquiv (compSnd k₂)) :=
          (congrArg (compSigma f u T)
            (sigma_mk_eq u e' h₁ (m₁ := compSnd k₁) (m₂ := m) rfl)).symm.trans hk
        have := hg T
        have := e'.homEquiv.injective (compClasses_injective u (compFst k₂) h₂)
        exact Over.OverMorphism.ext
          (congrArg (fun x : Over.mk (compFst k₂).left ⟶ R' ↦ x.left) this)
      · intro c
        obtain ⟨t, c', hc⟩ := compClasses_surjective e u hu c
        let m := e'.homEquiv.symm c'
        let k : T ⟶ (Over.map R.hom).obj R' := Over.homMk m.left (by
          rw [Over.map_obj_hom, ← Category.assoc, Over.w m]
          exact Over.w t)
        refine ⟨k, ?_⟩
        rw [← hc]
        refine (congrArg (compSigma f u T) (sigma_mk_eq u e' (t₁ := compFst k) (t₂ := t)
          (Over.OverMorphism.ext (Over.w m)) (m₁ := compSnd k) (m₂ := m) rfl)).trans ?_
        exact congrArg (compClasses f u t) (e'.homEquiv.apply_symm_apply c'))
  homEquiv_comp {T T'} h k := by
    refine (congrArg (compSigma f u T) (sigma_mk_eq u e' (t₁ := compFst (h ≫ k))
      (t₂ := h ≫ compFst k) (by ext; simp) (m₁ := compSnd (h ≫ k))
      (m₂ := (Over.homMk h.left : Over.mk (h ≫ compFst k).left ⟶ Over.mk (compFst k).left) ≫
        compSnd k) rfl)).trans ?_
    change compClasses f u (h ≫ compFst k) (e'.homEquiv
      ((Over.homMk h.left : Over.mk (h ≫ compFst k).left ⟶ Over.mk (compFst k).left) ≫
        compSnd k)) = _
    rw [e'.homEquiv_comp]
    exact compClasses_naturality f u h (compFst k) _

end Comp

section CompInstances

variable {X Y Z : StackInGroupoids.{v', v, u', u} C J} (f : StackMorphism X Y)
  (g : StackMorphism Y Z)

/-- The composite of two representable morphisms of stacks in groupoids is representable
([Stacks Project, Tag 02ZS](https://stacks.math.columbia.edu/tag/02ZS), Lemma 94.6.3). If `R_g`
represents the fibre of `g` over `z` and `R_f` represents the fibre of `f` over the universal
object of `R_g`, then `(Over.map R_g.hom).obj R_f` represents the fibre of `f ≫ g` over `z`. The
fibre functors of the composite are faithful because those of `f` and `g` are. -/
instance isRepresentable_comp [hf : f.IsRepresentable] [hg : g.IsRepresentable] :
    (comp f g).IsRepresentable where
  faithful T :=
    have := hf.faithful T
    have := hg.faithful T
    faithful_comp_app f g T
  representable {S} z := by
    have := hg.representable z
    let e := (g.fiberIsoClasses z).representableBy
    let u := (_root_.Quotient.out (e.homEquiv (𝟙 _)))
    have := hf.representable u.of.right
    exact (compRepresentableBy e u (Quotient.out_eq _)
      (f.fiberIsoClasses u.of.right).representableBy fun T ↦ hg.faithful T.left).isRepresentable

/-- The composite of two morphisms representable with property `P` is representable with property
`P` when `P` is stable under composition. Stacks Lemma 94.6.3
([Stacks Project, Tag 02ZS](https://stacks.math.columbia.edu/tag/02ZS)) states only
representability.

Every object representing a fibre of the composite is isomorphic over `S` to
`(Over.map R_g.hom).obj R_f`, so its structure morphism is `i ≫ R_f.hom ≫ R_g.hom` for an
isomorphism `i`. The morphism `i ≫ R_f.hom` is the structure morphism of another object
representing the same fibre of `f`, so it has `P`; no invariance of `P` under isomorphisms is
needed. -/
theorem HasRepresentableProperty.comp {P : MorphismProperty C} [P.IsStableUnderComposition]
    [hf : f.HasRepresentableProperty P] [hg : g.HasRepresentableProperty P] :
    (StackMorphism.comp f g).HasRepresentableProperty P where
  isRepresentable := inferInstance
  property {S} z R'' e'' := by
    have := hg.isRepresentable.representable z
    let e := (g.fiberIsoClasses z).representableBy
    let u := (_root_.Quotient.out (e.homEquiv (𝟙 _)))
    have := hf.isRepresentable.representable u.of.right
    let e' := (f.fiberIsoClasses u.of.right).representableBy
    let i := e''.uniqueUpToIso
      (compRepresentableBy e u (Quotient.out_eq _) e' fun T ↦ hg.isRepresentable.faithful T.left)
    have hR' : P (Over.mk (i.hom.left ≫ (f.fiberIsoClasses u.of.right).reprX.hom)).hom :=
      hf.property u.of.right (e'.ofIsoObj (Over.isoMk ((Over.forget S).mapIso i) rfl))
    have hR := hg.property z e
    rw [← Over.w i.hom, Over.map_obj_hom, ← Category.assoc]
    exact P.comp_mem _ _ hR' hR

end CompInstances

end StackMorphism

end

end CategoryTheory
