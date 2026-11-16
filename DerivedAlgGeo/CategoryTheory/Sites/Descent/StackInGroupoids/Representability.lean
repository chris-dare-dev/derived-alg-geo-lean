/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Representable
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.FiberProduct

/-!
# Representable morphisms of stacks in groupoids

A morphism `f : F ⟶ G` of stacks in groupoids is representable when every fibre functor
`f.app T` is faithful and, for every object `y` of `G` over `S`, the presheaf on `Over S` of
isomorphism classes of the fibre of `f` over `y` is representable. A representation is a natural
isomorphism of presheaves on `Over S`, so it is natural in the test object. The fibre over `y` at
`T` is `StackMorphism.FiberCategory y T`, the fibre of the 2-fibre product `(C/S) ×_{y, G, f} F`.

## Main definitions

* `CategoryTheory.StackMorphism.fiberCategoryEquiv`: the fibre category is the categorical
  pullback of the point `y|_T` and `f.app T.left`.
* `CategoryTheory.StackMorphism.fiberMap`: restriction of the fibre along a morphism of test
  objects.
* `CategoryTheory.StackMorphism.fiberIsoClasses`: the presheaf on `Over S` of isomorphism classes
  of the fibre over `y`, and `CategoryTheory.StackMorphism.fiberIsoClassesIsoOfIso`, its
  invariance under isomorphisms of `y`.
* `CategoryTheory.StackMorphism.IsRepresentable`: representable morphisms of stacks.
* `CategoryTheory.StackMorphism.HasRepresentableProperty`: representable morphisms whose
  representing morphisms have a property `P`.
* `CategoryTheory.StackInGroupoids.HasRepresentableDiagonal`: every Isom sheaf is representable.
* `CategoryTheory.StackMorphism.IsRepresentable.pointwiseFiberRepresentation`: the projection to
  `CategoryTheory.StackMorphism.PointwiseFiberRepresentation`.

## Main results

* `CategoryTheory.StackMorphism.isRepresentable_discreteMap_iff`: on discrete stacks of sheaves
  of types, representability is Mathlib's `Functor.relativelyRepresentable yoneda`.
* `CategoryTheory.StackMorphism.hasRepresentableProperty_discreteMap_iff`: on discrete stacks,
  representability with property `P` is Mathlib's `MorphismProperty.presheaf P`.
* `CategoryTheory.StackMorphism.isRepresentable_id` and
  `CategoryTheory.StackMorphism.hasRepresentableProperty_id`: identities are representable.
* `CategoryTheory.StackMorphism.isPointwiseRepresentable_of_isRepresentable`: a representable
  morphism is pointwise representable.
* `CategoryTheory.StackInGroupoids.hasRepresentableDiagonal_terminal` and
  `CategoryTheory.StackInGroupoids.hasRepresentableDiagonal_yoneda`: the terminal stack and the
  discrete stack of a represented sheaf have representable diagonal.

## Implementation notes

The definition is conditions (1) and (2) of Stacks Lemma 4.42.5; the docstring of
`CategoryTheory.StackMorphism.IsRepresentable` explains why. The restriction maps of
`fiberIsoClasses` pull a pair `(x, φ)` back with `StructuredArrow.map₂`, along the compositors of
`G` and the naturality isomorphisms of `f`. Restriction is functorial only up to isomorphism in
the fibre, so `fiberIsoClasses` is a presheaf of isomorphism classes; no pseudofunctor on
`Over S` is assembled.

The class presheaf of a stack morphism lands in `Type (max u' v')`, the universe of the objects
of the fibre, and representations use the universe-polymorphic `Functor.RepresentableBy`. Only
the comparison with Mathlib's `Functor.relativelyRepresentable yoneda` fixes the universe, to the
hom universe of the site.

## References

* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4), §4.42
* [Stacks Project, Tag 02Y3](https://stacks.math.columbia.edu/tag/02Y3), Lemma 4.40.2
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G), Lemma 94.10.11

## Tags

stack in groupoids, representable morphism, 2-fibre product, isomorphism classes, diagonal
-/

universe w v' v u' u

namespace CategoryTheory

open Opposite Bicategory Limits
open scoped Pseudofunctor.StrongTrans

noncomputable section

namespace StackMorphism

section Coherence

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (α : F ⟶ G)

private lemma naturality_inv_app_comp_map_mapId'_hom {a : LocallyDiscrete Cᵒᵖ} (φ : a ⟶ a)
    (hφ : φ = 𝟙 a) (x : F.obj a) :
    (α.naturality φ).inv.toNatTrans.app x ≫
        (α.app a).toFunctor.map ((F.mapId' φ hφ).hom.toNatTrans.app x) =
      (G.mapId' φ hφ).hom.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  subst hφ
  have := congr_arg (fun t ↦ t.toNatTrans.app x) (α.naturality_id a)
  dsimp at this
  simp only [Category.comp_id] at this
  simp only [Pseudofunctor.mapId'_eq_mapId, ← this, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]

private lemma naturality_inv_app_comp_map_mapComp'_hom {a b c : LocallyDiscrete Cᵒᵖ}
    (φ : a ⟶ b) (ψ : b ⟶ c) (φψ : a ⟶ c) (h : φ ≫ ψ = φψ) (x : F.obj a) :
    (α.naturality φψ).inv.toNatTrans.app x ≫
        (α.app c).toFunctor.map ((F.mapComp' φ ψ φψ h).hom.toNatTrans.app x) =
      (G.mapComp' φ ψ φψ h).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map ψ).toFunctor.map ((α.naturality φ).inv.toNatTrans.app x) ≫
          (α.naturality ψ).inv.toNatTrans.app ((F.map φ).toFunctor.obj x) := by
  subst h
  have := congr_arg (fun t ↦ t.toNatTrans.app x) (α.naturality_comp φ ψ)
  dsimp at this
  simp only [Category.id_comp, Category.comp_id] at this
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rw [← cancel_epi ((α.naturality (φ ≫ ψ)).hom.toNatTrans.app x),
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc, reassoc_of% this]
  simp [← Functor.map_comp_assoc]

/-- The coherence behind restriction of a fibre along an identity. -/
private lemma mapComp'_comp_id_key {s b : LocallyDiscrete Cᵒᵖ} (p : s ⟶ b) (φ : b ⟶ b)
    (hφ : φ = 𝟙 b) (h : p ≫ φ = p) (y : G.obj s) (x : F.obj b)
    (u : (G.map p).toFunctor.obj y ⟶ (α.app b).toFunctor.obj x) :
    (G.mapComp' p φ p h).hom.toNatTrans.app y ≫ (G.map φ).toFunctor.map u ≫
        (α.naturality φ).inv.toNatTrans.app x ≫
          (α.app b).toFunctor.map ((F.mapId' φ hφ).hom.toNatTrans.app x) = u := by
  rw [naturality_inv_app_comp_map_mapId'_hom]
  subst hφ
  rw [Pseudofunctor.mapId'_eq_mapId, Pseudofunctor.mapComp'_comp_id_hom_app]
  simp

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

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : StackInGroupoids.{v', v, u', u} C J}

section FiberIsoClasses

variable (f : StackMorphism F G) {S : C} (y : G.presheaf.obj (.mk (op S)))

/-- The fibre category `f.FiberCategory y T`, whose objects are the pairs `(x, φ : y|_T ⟶ f(x))`
of [Stacks Project, Tag 02Y5](https://stacks.math.columbia.edu/tag/02Y5) (Lemma 4.42.1), is
equivalent to the categorical pullback of the point `y|_T` and the fibre functor `f.app T.left`.
A pair `(x, φ)` corresponds to the triple `(*, x, φ)`; `φ` is an isomorphism because the fibres of
`G` are groupoids. -/
def fiberCategoryEquiv (T : Over S) :
    f.FiberCategory y T ≌
      CategoricalPullback
        (Functor.fromPUnit.{w} ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y))
        (f.app T.left) where
  functor :=
    { obj a := ⟨⟨PUnit.unit⟩, a.of.right, asIso a.of.hom⟩
      map e := ⟨𝟙 _, e.iso.hom.right, by simp⟩
      map_id _ := by ext <;> simp
      map_comp _ _ := by ext <;> simp }
  inverse :=
    { obj c := Core.mk (StructuredArrow.mk c.iso.hom)
      map m := ⟨StructuredArrow.isoMk (asIso m.snd) (by simpa using m.w.symm)⟩
      map_id _ := by ext; simp
      map_comp _ _ := by ext; simp }
  unitIso := NatIso.ofComponents (fun a ↦ Core.isoMk (StructuredArrow.isoMk (Iso.refl _)
    (by simp))) (fun _ ↦ by ext; simp)
  counitIso := NatIso.ofComponents
    (fun c ↦ CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by simp))
    (fun _ ↦ by
      ext
      · exact Subsingleton.elim _ _
      · simp)
  functor_unitIso_comp _ := by ext <;> simp

private lemma toLoc_comp_eq {T T' : Over S} (g : T' ⟶ T) :
    T.hom.op.toLoc ≫ g.left.op.toLoc = T'.hom.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w]

/-- Restriction of the fibre of `f` over `y` along a morphism `g : T' ⟶ T` of test objects, on
the structured arrows underlying `StackMorphism.FiberCategory`. It sends `(x, φ)` to the pullback
of `x` along `g.left`, with `φ` pulled back and conjugated by the compositor of `G` and the
naturality isomorphism of `f`. -/
def fiberMap {T T' : Over S} (g : T' ⟶ T) :
    StructuredArrow ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y) (f.app T.left) ⥤
      StructuredArrow ((G.presheaf.map T'.hom.op.toLoc).toFunctor.obj y) (f.app T'.left) :=
  StructuredArrow.map₂ (F := (F.presheaf.map g.left.op.toLoc).toFunctor)
    (G := (G.presheaf.map g.left.op.toLoc).toFunctor)
    ((G.presheaf.mapComp' _ _ _ (toLoc_comp_eq g)).hom.toNatTrans.app y)
    (f.naturality g.left.op.toLoc).inv.toNatTrans

/-- Restriction along an identity is isomorphic to the identity, object by object. -/
private def fiberMapIdIso (T : Over S)
    (a : StructuredArrow ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y) (f.app T.left)) :
    (f.fiberMap y (𝟙 T)).obj a ≅ a :=
  StructuredArrow.isoMk
    ((Cat.Hom.toNatIso (F.presheaf.mapId' (𝟙 T : T ⟶ T).left.op.toLoc rfl)).app a.right) (by
      simpa [fiberMap] using mapComp'_comp_id_key f _ _ rfl _ y a.right a.hom)

/-- Restriction along a composite is isomorphic to the composite of the restrictions, object by
object. -/
private def fiberMapCompIso {T T' T'' : Over S} (g : T' ⟶ T) (h : T'' ⟶ T')
    (a : StructuredArrow ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y) (f.app T.left)) :
    (f.fiberMap y (h ≫ g)).obj a ≅ (f.fiberMap y h).obj ((f.fiberMap y g).obj a) :=
  StructuredArrow.isoMk
    ((Cat.Hom.toNatIso (F.presheaf.mapComp' g.left.op.toLoc h.left.op.toLoc
      (h ≫ g).left.op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app a.right) (by
      simpa [fiberMap] using mapComp'_comp_key f _ _ _ _ _ _ (toLoc_comp_eq g) (toLoc_comp_eq h)
        (toLoc_comp_eq (h ≫ g)) _ y a.right a.hom)

/-- The isomorphism classes of the fibre of `f` over `y`, as a presheaf on `Over S`. Its value
at `T` is the set of isomorphism classes of `f.FiberCategory y T`, the pairs
`(x, φ : y|_T ⟶ f(x))` of [Stacks Project, Tag 02Y5](https://stacks.math.columbia.edu/tag/02Y5),
and its restriction maps are `StackMorphism.fiberMap`. Restriction is functorial only up to
isomorphism in the fibre, so only the classes form a presheaf. -/
def fiberIsoClasses : (Over S)ᵒᵖ ⥤ Type (max u' v') where
  obj T := _root_.Quotient (isIsomorphicSetoid (f.FiberCategory y T.unop))
  map g := ↾(Quot.map (fun a ↦ Core.mk ((f.fiberMap y g.unop).obj a.of))
    fun _ _ ⟨e⟩ ↦ ⟨Core.isoMk ((f.fiberMap y g.unop).mapIso e.hom.iso)⟩)
  map_id T := by
    ext ⟨a⟩
    exact Quot.sound ⟨Core.isoMk (fiberMapIdIso f y T.unop a.of)⟩
  map_comp g h := by
    ext ⟨a⟩
    exact Quot.sound ⟨Core.isoMk (fiberMapCompIso f y g.unop h.unop a.of)⟩

@[simp]
lemma fiberIsoClasses_map_mk {T T' : Over S} (g : T' ⟶ T) (a : f.FiberCategory y T) :
    (f.fiberIsoClasses y).map g.op (_root_.Quotient.mk _ a) =
      _root_.Quotient.mk _ (Core.mk ((f.fiberMap y g).obj a.of)) :=
  rfl

variable {y} in
/-- Transport of the fibre along a morphism of base points. -/
private def fiberTransport {y' : G.presheaf.obj (.mk (op S))} (u : y' ⟶ y) (T : Over S) :
    StructuredArrow ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y) (f.app T.left) ⥤
      StructuredArrow ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y') (f.app T.left) :=
  StructuredArrow.map ((G.presheaf.map T.hom.op.toLoc).toFunctor.map u)

variable {y} in
private def fiberTransportClasses {y' : G.presheaf.obj (.mk (op S))} (u : y' ⟶ y) (T : Over S) :
    _root_.Quotient (isIsomorphicSetoid (f.FiberCategory y T)) →
      _root_.Quotient (isIsomorphicSetoid (f.FiberCategory y' T)) :=
  Quot.map (fun a ↦ Core.mk ((fiberTransport f u T).obj a.of))
    fun _ _ ⟨e⟩ ↦ ⟨Core.isoMk ((fiberTransport f u T).mapIso e.hom.iso)⟩

variable {y} in
private lemma fiberTransportClasses_comp {y' : G.presheaf.obj (.mk (op S))} (u : y' ⟶ y)
    (u' : y ⟶ y') (hu : u' ≫ u = 𝟙 y) (T : Over S)
    (c : _root_.Quotient (isIsomorphicSetoid (f.FiberCategory y T))) :
    fiberTransportClasses f u' T (fiberTransportClasses f u T c) = c := by
  obtain ⟨a⟩ := c
  exact Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (Iso.refl _) (by
    simp [fiberTransport, ← Functor.map_comp_assoc, hu]))⟩

variable {y} in
private lemma fiberTransportClasses_naturality {y' : G.presheaf.obj (.mk (op S))} (u : y' ⟶ y)
    {T T' : Over S} (g : T' ⟶ T) (c : (f.fiberIsoClasses y).obj (op T)) :
    fiberTransportClasses f u T' ((f.fiberIsoClasses y).map g.op c) =
      (f.fiberIsoClasses y').map g.op (fiberTransportClasses f u T c) := by
  obtain ⟨a⟩ := c
  exact Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (Iso.refl _) (by
    simp [fiberTransport, fiberMap]))⟩

variable {y} in
/-- `StackMorphism.fiberIsoClasses` depends on the base point only up to isomorphism: an
isomorphism `e : y ≅ y'` sends the class of `(x, φ)` to the class of `(x, e⁻¹|_T ≫ φ)`. -/
def fiberIsoClassesIsoOfIso {y' : G.presheaf.obj (.mk (op S))} (e : y ≅ y') :
    f.fiberIsoClasses y ≅ f.fiberIsoClasses y' :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      { toFun := fiberTransportClasses f e.inv T.unop
        invFun := fiberTransportClasses f e.hom T.unop
        left_inv := fiberTransportClasses_comp f e.inv e.hom e.hom_inv_id T.unop
        right_inv := fiberTransportClasses_comp f e.hom e.inv e.inv_hom_id T.unop })
    (fun g ↦ by
      ext c
      exact fiberTransportClasses_naturality f e.inv g.unop c)

end FiberIsoClasses

section Classes

/-- A morphism `f : F ⟶ G` of stacks in groupoids is representable when every fibre functor
`f.app T` is faithful and, for every object `y` of `G` over `S`, the presheaf
`f.fiberIsoClasses y` on `Over S` of isomorphism classes of the fibre over `y` is representable.

These are conditions (1) and (2) of
[Stacks Project, Tag 02Y9](https://stacks.math.columbia.edu/tag/02Y9) (Lemma 4.42.5), which imply
that `f` is representable in the sense of
[Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7) (Definition 4.42.3): every
2-fibre product `(C/S) ×_{y, G, f} F` is representable over `C/S`. They are also necessary:
[Stacks Project, Tag 02Y8](https://stacks.math.columbia.edu/tag/02Y8) (Lemma 4.42.4) gives the
faithfulness, and [Stacks Project, Tag 02Y3](https://stacks.math.columbia.edu/tag/02Y3)
(Lemma 4.40.2) the representability of the presheaf of isomorphism classes. The definition uses
this form because it is stated with the fibre categories `StackMorphism.FiberCategory` that already
exist (the fibres of the 2-fibre product, by `StackMorphism.fiberCategoryEquiv`), on any site and
in any fibre universes. Definition 4.42.3 takes the 2-fibre product with `C/S`, the category
fibred in groupoids represented by `S`; as a stack that is `StackInGroupoids.representable J S`,
which needs a subcanonical topology. The equivalence with Definition 4.42.3 is not proved here.

A representation is a natural isomorphism of presheaves on `Over S`, so it is natural in the test
object. `StackMorphism.PointwiseFiberRepresentation` does not require that.

The second condition does not imply the first. On the category with one object and one morphism,
with the topology in which only the maximal sieve covers, take the constant stack at the
one-object groupoid of `ℤ/2` and its morphism to the terminal stack. Its only fibre has one
isomorphism class, so its class presheaf is represented by `Over.mk (𝟙 _)`, but its fibre functor
is not faithful. -/
class IsRepresentable (f : StackMorphism F G) : Prop where
  /-- Every fibre functor is faithful. -/
  faithful (T : C) : (f.app T).Faithful
  /-- The presheaf of isomorphism classes of every fibre is representable. -/
  representable {S : C} (y : G.presheaf.obj (.mk (op S))) :
    (f.fiberIsoClasses y).IsRepresentable

/-- A morphism of stacks in groupoids is representable with property `P` when it is representable
and every object `R` of `Over S` representing a fibre has structure morphism `R.hom` in `P`. On
discrete stacks this is Mathlib's `MorphismProperty.presheaf P`, by
`StackMorphism.hasRepresentableProperty_discreteMap_iff`. The condition quantifies over every
representation, so it is stated without assuming that `P` respects isomorphisms. -/
class HasRepresentableProperty (P : MorphismProperty C) (f : StackMorphism F G) : Prop where
  /-- The morphism is representable. -/
  isRepresentable : f.IsRepresentable
  /-- Every representing object has structure morphism in `P`. -/
  property {S : C} (y : G.presheaf.obj (.mk (op S))) {R : Over S}
    (e : (f.fiberIsoClasses y).RepresentableBy R) : P R.hom

attribute [instance] HasRepresentableProperty.isRepresentable

end Classes

section Pointwise

/-- A thin groupoid is equivalent to the discrete category on its isomorphism classes. -/
private def thinGroupoidEquiv (X : Type*) [Groupoid X] [Quiver.IsThin X] :
    Discrete (_root_.Quotient (isIsomorphicSetoid X)) ≌ X where
  functor := Discrete.functor fun c ↦ c.out
  inverse :=
    { obj x := Discrete.mk (_root_.Quotient.mk _ x)
      map m := Discrete.eqToHom (_root_.Quotient.sound ⟨asIso m⟩) }
  unitIso := NatIso.ofComponents (fun c ↦ Discrete.eqToIso (Quotient.out_eq c.as).symm)
  counitIso := NatIso.ofComponents fun x ↦
    (Quotient.exact (Quotient.out_eq (_root_.Quotient.mk (isIsomorphicSetoid X) x))).some
  functor_unitIso_comp _ := Subsingleton.elim _ _

variable (f : StackMorphism F G)

/-- A fibre over a test object at which `f` is faithful is thin: a morphism `(x, φ) ⟶ (x', φ')`
is determined by its image `φ⁻¹ ≫ φ'` under `f`. -/
private lemma isThin_fiberCategory {S : C} (y : G.presheaf.obj (.mk (op S))) (T : Over S)
    [(f.app T.left).Faithful] : Quiver.IsThin (f.FiberCategory y T) := fun a _ ↦
  ⟨fun m₁ m₂ ↦ by
    apply Core.hom_ext
    apply StructuredArrow.hom_ext
    apply (f.app T.left).map_injective
    rw [← cancel_epi a.of.hom, StructuredArrow.w m₁.iso.hom, StructuredArrow.w m₂.iso.hom]⟩

/-- The pointwise representation of a fibre of a representable morphism. Its representing object
is the one chosen by `Functor.reprX`, and at each test object `T` its equivalence
`Discrete (T ⟶ R) ≌ f.FiberCategory y T` composes the bijection of the representation with the
equivalence between the fibre, which faithfulness makes thin, and its isomorphism classes. The
projection forgets the naturality of the representation in `T`.

Nothing here proves the converse. With a property of the representing morphisms the pointwise
notion is strictly weaker: the docstring of `StackMorphism.PointwiseFiberRepresentation` gives a
morphism of schemes that is pointwise smooth and surjective, through bijections chosen test object
by test object, but not smooth. -/
def IsRepresentable.pointwiseFiberRepresentation [hf : f.IsRepresentable] {S : C}
    (y : G.presheaf.obj (.mk (op S))) : f.PointwiseFiberRepresentation y :=
  haveI := hf.representable y
  { representing := (f.fiberIsoClasses y).reprX
    fiberEquivalence T :=
      haveI := hf.faithful T.left
      haveI := isThin_fiberCategory f y T
      (Discrete.equivalence (f.fiberIsoClasses y).representableBy.homEquiv).trans
        (thinGroupoidEquiv _) }

/-- A representable morphism of stacks in groupoids is pointwise representable, through
`StackMorphism.IsRepresentable.pointwiseFiberRepresentation`. -/
instance isPointwiseRepresentable_of_isRepresentable [f.IsRepresentable] :
    f.IsPointwiseRepresentable :=
  ⟨fun y ↦ ⟨IsRepresentable.pointwiseFiberRepresentation f y⟩⟩

end Pointwise

section Terminal

variable {S : C}

/-- A presheaf on `Over S` whose values are inhabited subsingletons is represented by the terminal
object `Over.mk (𝟙 S)`. -/
private def representableByOfSubsingleton (P : (Over S)ᵒᵖ ⥤ Type w)
    [∀ T, Subsingleton (P.obj T)] (p : ∀ T, P.obj T) : P.RepresentableBy (Over.mk (𝟙 S)) where
  homEquiv {T} :=
    { toFun _ := p (op T)
      invFun _ := Over.homMk T.hom
      left_inv k := by ext; simpa using (Over.w k).symm
      right_inv _ := Subsingleton.elim _ _ }
  homEquiv_comp _ _ := Subsingleton.elim _ _

private lemma isIso_hom_of_representableBy_of_subsingleton (P : (Over S)ᵒᵖ ⥤ Type w)
    [∀ T, Subsingleton (P.obj T)] (p : ∀ T, P.obj T) {R : Over S} (e : P.RepresentableBy R) :
    IsIso R.hom := by
  let i := e.uniqueUpToIso (representableByOfSubsingleton P p)
  have : R.hom = ((Over.forget S).mapIso i).hom := by simpa using (Over.w i.hom).symm
  rw [this]
  infer_instance

end Terminal

section Id

variable (F : StackInGroupoids.{v', v, u', u} C J) {S : C} (y : F.presheaf.obj (.mk (op S)))

/-- The object `(y|_T, 𝟙)` of a fibre of the identity. -/
private def idFiberObj (T : Over S) : (StackMorphism.id F).FiberCategory y T :=
  Core.mk (StructuredArrow.mk (T := (StackMorphism.id F).app T.left)
    (Y := (F.presheaf.map T.hom.op.toLoc).toFunctor.obj y) (𝟙 _))

/-- Any two objects of a fibre of the identity are isomorphic. -/
private def idFiberIso {T : Over S} (a b : (StackMorphism.id F).FiberCategory y T) : a ≅ b :=
  Core.isoMk (StructuredArrow.isoMk ((asIso a.of.hom).symm ≪≫ asIso b.of.hom :
    ((StackMorphism.id F).app T.left).obj a.of.right ≅
      ((StackMorphism.id F).app T.left).obj b.of.right) (by
        change a.of.hom ≫ inv a.of.hom ≫ b.of.hom = b.of.hom
        simp))

instance (T : (Over S)ᵒᵖ) : Subsingleton ((StackMorphism.id F).fiberIsoClasses y |>.obj T) where
  allEq := by
    rintro ⟨a⟩ ⟨b⟩
    exact Quot.sound ⟨idFiberIso F y a b⟩

/-- The identity of a stack in groupoids is representable: every fibre has a single isomorphism
class, so its class presheaf is represented by `Over.mk (𝟙 S)`. -/
instance isRepresentable_id : (StackMorphism.id F).IsRepresentable where
  faithful _ := ⟨fun h ↦ h⟩
  representable y := (representableByOfSubsingleton _ fun T ↦
    _root_.Quotient.mk _ (idFiberObj F y T.unop)).isRepresentable

/-- The identity has every property `P` that holds for isomorphisms: every object representing a
fibre of the identity is isomorphic to `Over.mk (𝟙 S)`. -/
theorem hasRepresentableProperty_id (P : MorphismProperty C)
    (hP : MorphismProperty.isomorphisms C ≤ P) :
    (StackMorphism.id F).HasRepresentableProperty P where
  isRepresentable := inferInstance
  property y _ e :=
    have := isIso_hom_of_representableBy_of_subsingleton _
      (fun T ↦ _root_.Quotient.mk _ (idFiberObj F y T.unop)) e
    hP _ (MorphismProperty.isomorphisms.infer_property _)

/-- `StackMorphism.hasRepresentableProperty_id` for a property that contains the identities and
respects isomorphisms, as an instance. -/
instance hasRepresentableProperty_id_of_respectsIso (P : MorphismProperty C)
    [P.ContainsIdentities] [P.RespectsIso] : (StackMorphism.id F).HasRepresentableProperty P :=
  hasRepresentableProperty_id F P fun _ _ f (_ : IsIso f) ↦ P.of_isIso f

end Id

section Discrete

variable {P Q : Cᵒᵖ ⥤ Type v} (hP : Presieve.IsSheaf J P) (hQ : Presieve.IsSheaf J Q)
  (φ : P ⟶ Q)

/-- The presheaf `T ↦ {x : P(T) // φ x = q|_T}` on `Over S`. -/
private def discreteFiber {S : C} (q : Q.obj (op S)) : (Over S)ᵒᵖ ⥤ Type v where
  obj T := {x : P.obj (op T.unop.left) // φ.app _ x = Q.map T.unop.hom.op q}
  map g := ↾fun x ↦ ⟨P.map g.unop.left.op x.1, by
    rw [NatTrans.naturality_apply, x.2, ← Functor.map_comp_apply, ← op_comp, Over.w]⟩

/-- The isomorphism classes of a fibre of a morphism of discrete stacks are the elements of `P`
over the restricted base point. -/
private def discreteFiberEquiv {S : C} (q : Q.obj (op S)) (T : Over S) :
    ((StackInGroupoids.discreteMap hP hQ φ).fiberIsoClasses (Discrete.mk q)).obj (op T) ≃
      (discreteFiber φ q).obj (op T) where
  toFun := Quot.lift (fun a ↦ ⟨a.of.right.as, (Discrete.eq_of_hom a.of.hom).symm⟩)
    fun _ _ ⟨e⟩ ↦ Subtype.ext (Discrete.eq_of_hom e.hom.iso.hom.right)
  invFun x := Quot.mk _ (Core.mk (StructuredArrow.mk (Y := Discrete.mk x.1)
    (Discrete.eqToHom x.2.symm)))
  left_inv := by
    have : IsDiscrete ((stackInGroupoidsOfSheaf J Q hQ).presheaf.obj (.mk (op T.left))) :=
      discretePseudofunctor_obj_isDiscrete Q _
    rintro ⟨a⟩
    exact Quot.sound ⟨Core.isoMk (StructuredArrow.isoMk (Iso.refl _) (Subsingleton.elim _ _))⟩
  right_inv _ := rfl

/-- `discreteFiberEquiv`, natural in the test object. -/
private def discreteFiberIso {S : C} (q : Q.obj (op S)) :
    (StackInGroupoids.discreteMap hP hQ φ).fiberIsoClasses (Discrete.mk q) ≅ discreteFiber φ q :=
  NatIso.ofComponents (fun T ↦ (discreteFiberEquiv hP hQ φ q T.unop).toIso) fun _ ↦ by
    ext ⟨_⟩
    rfl

variable {φ} in
/-- A representation of `discreteFiber φ q` by `R` gives a pullback square of `φ` along `q`
with corner `yoneda.obj R.left`. -/
private lemma isPullback_of_representableBy {S : C} {q : Q.obj (op S)} {R : Over S}
    (e : (discreteFiber φ q).RepresentableBy R) :
    IsPullback (yonedaEquiv.symm (e.homEquiv (𝟙 R)).1) (yoneda.map R.hom) φ
      (yonedaEquiv.symm q) := by
  have key {T : Over S} (k : T ⟶ R) :
      (e.homEquiv k).1 = P.map k.left.op (e.homEquiv (𝟙 R)).1 := by
    rw [e.homEquiv_eq]
    rfl
  refine IsPullback.of_forall_isPullback_app fun c ↦ ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, fun k₁ k₂ ⟨h₁, h₂⟩ ↦ ?_, fun x t h ↦ ?_⟩
  · ext k
    change φ.app c (P.map k.op (e.homEquiv (𝟙 R)).1) = Q.map (k ≫ R.hom).op q
    rw [NatTrans.naturality_apply, (e.homEquiv (𝟙 R)).2, op_comp, Functor.map_comp_apply]
  · change P.map k₁.op (e.homEquiv (𝟙 R)).1 = P.map k₂.op (e.homEquiv (𝟙 R)).1 at h₁
    change k₁ ≫ R.hom = k₂ ≫ R.hom at h₂
    have : (Over.homMk k₁ h₂ : Over.mk (k₂ ≫ R.hom) ⟶ R) = Over.homMk k₂ rfl :=
      e.homEquiv.injective (Subtype.ext ((key (T := Over.mk (k₂ ≫ R.hom))
        (Over.homMk k₁ h₂)).trans (h₁.trans (key (T := Over.mk (k₂ ≫ R.hom))
          (Over.homMk k₂ rfl)).symm)))
    exact congrArg CommaMorphism.left this
  · let K : Over.mk t ⟶ R := e.homEquiv.symm ⟨x, h⟩
    refine ⟨K.left, ?_, Over.w K⟩
    exact (key K).symm.trans (congrArg Subtype.val (e.homEquiv.apply_symm_apply _))

variable {φ} in
/-- A pullback square of `φ` along `q` with corner `yoneda.obj b` represents
`discreteFiber φ q` by `Over.mk snd`. -/
private def representableByOfIsPullback {S b : C} {q : Q.obj (op S)} (snd : b ⟶ S)
    (fst : yoneda.obj b ⟶ P) (h : IsPullback fst (yoneda.map snd) φ (yonedaEquiv.symm q)) :
    (discreteFiber φ q).RepresentableBy (Over.mk snd) where
  homEquiv {T} := Equiv.ofBijective
    (fun k ↦ ⟨fst.app (op T.left) k.left, by
      have := congr_arg (fun t : yoneda.obj b ⟶ Q ↦ t.app (op T.left) k.left) h.w
      change φ.app (op T.left) (fst.app (op T.left) k.left) = Q.map (k.left ≫ snd).op q at this
      exact this.trans (by rw [← Over.w k]; rfl)⟩) (by
      obtain ⟨-, hinj, hsurj⟩ := (Types.isPullback_iff _ _ _ _).1 (h.app (op T.left))
      refine ⟨fun k₁ k₂ hk ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
      · ext
        exact hinj _ _ ⟨congrArg Subtype.val hk, (Over.w k₁).trans (Over.w k₂).symm⟩
      · obtain ⟨k, hk₁, hk₂⟩ := hsurj x T.hom hx
        exact ⟨Over.homMk k hk₂, Subtype.ext hk₁⟩)
  homEquiv_comp {X X'} f g := by
    apply Subtype.ext
    exact NatTrans.naturality_apply fst f.left.op g.left

/-- On discrete stacks of sheaves of types, representability is Mathlib's relative
representability `Functor.relativelyRepresentable yoneda` of the underlying morphism of
presheaves. -/
theorem isRepresentable_discreteMap_iff :
    (StackInGroupoids.discreteMap hP hQ φ).IsRepresentable ↔ yoneda.relativelyRepresentable φ := by
  constructor
  · intro h a g
    obtain ⟨R, ⟨e⟩⟩ := (h.representable (S := a) (Discrete.mk (yonedaEquiv g))).has_representation
    let e' := e.ofIso (discreteFiberIso hP hQ φ _)
    exact ⟨R.left, R.hom, _, by simpa using isPullback_of_representableBy e'⟩
  · intro h
    refine ⟨fun T ↦ ⟨fun {_ _} _ _ _ ↦ ?_⟩, fun {S} y ↦ ?_⟩
    · have : IsDiscrete ((stackInGroupoidsOfSheaf J P hP).presheaf.obj (.mk (op T))) :=
        discretePseudofunctor_obj_isDiscrete P _
      exact Subsingleton.elim _ _
    · obtain ⟨b, snd, fst, hb⟩ := h (yonedaEquiv.symm (Discrete.as y))
      exact ((representableByOfIsPullback snd fst hb).ofIso
        (discreteFiberIso hP hQ φ (Discrete.as y)).symm).isRepresentable

/-- On discrete stacks of sheaves of types, representability with property `Pm` is Mathlib's
`MorphismProperty.presheaf Pm` of the underlying morphism of presheaves. -/
theorem hasRepresentableProperty_discreteMap_iff (Pm : MorphismProperty C) :
    (StackInGroupoids.discreteMap hP hQ φ).HasRepresentableProperty Pm ↔ Pm.presheaf φ := by
  constructor
  · intro h
    refine ⟨(isRepresentable_discreteMap_iff hP hQ φ).1 h.isRepresentable,
      fun a b g fst snd hpb ↦ ?_⟩
    have hpb' : IsPullback fst (yoneda.map snd) φ (yonedaEquiv.symm (yonedaEquiv g)) := by
      simpa using hpb
    exact h.property (Discrete.mk (yonedaEquiv g))
      ((representableByOfIsPullback snd fst hpb').ofIso (discreteFiberIso hP hQ φ _).symm)
  · intro h
    refine ⟨(isRepresentable_discreteMap_iff hP hQ φ).2 h.rep, fun {S} y R e ↦ ?_⟩
    exact h.property _ _ _ (isPullback_of_representableBy
      (e.ofIso (discreteFiberIso hP hQ φ (Discrete.as y))))

/-- A relatively representable morphism of sheaves of types induces a representable morphism of
discrete stacks. -/
theorem isRepresentable_discreteMap (h : yoneda.relativelyRepresentable φ) :
    (StackInGroupoids.discreteMap hP hQ φ).IsRepresentable :=
  (isRepresentable_discreteMap_iff hP hQ φ).2 h

/-- A morphism of sheaves of types with `MorphismProperty.presheaf Pm` induces a morphism of
discrete stacks representable with property `Pm`. -/
theorem hasRepresentableProperty_discreteMap {Pm : MorphismProperty C} (h : Pm.presheaf φ) :
    (StackInGroupoids.discreteMap hP hQ φ).HasRepresentableProperty Pm :=
  (hasRepresentableProperty_discreteMap_iff hP hQ φ Pm).2 h

end Discrete

end StackMorphism

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A stack in groupoids has representable diagonal when the Isom sheaf `X.isom x y` on `Over S`
of every two objects `x` and `y` over `S` is representable. This is the analogue of condition (2)
of [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G) (Lemma 94.10.11), with
representability by an object of the site in place of being an algebraic space. Its equivalence
with representability of the diagonal `StackInGroupoids.diag X`, the analogue of condition (1),
is not proved here. -/
class HasRepresentableDiagonal (X : StackInGroupoids.{v', v, u', u} C J) : Prop where
  /-- Every Isom sheaf is representable. -/
  representable {S : C} (x y : X.presheaf.obj (.mk (op S))) : (X.isom x y).obj.IsRepresentable

section Terminal

private lemma subsingleton_chosenTerminal_hom (a b : Cat.chosenTerminal.{v', u'}) :
    Subsingleton (a ⟶ b) := by
  constructor
  rintro ⟨⟨⟨⟨⟩⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
  rfl

private lemma nonempty_chosenTerminal_hom (a b : Cat.chosenTerminal.{v', u'}) :
    Nonempty (a ⟶ b) := by
  obtain ⟨⟨⟨⟨⟩⟩⟩⟩ := a
  obtain ⟨⟨⟨⟨⟩⟩⟩⟩ := b
  exact ⟨𝟙 _⟩

instance (S : C) (x y : (terminal.{v', v, u', u} C J).presheaf.obj (.mk (op S)))
    (T : (Over S)ᵒᵖ) : Subsingleton (((terminal.{v', v, u', u} C J).isom x y).obj.obj T) :=
  subsingleton_chosenTerminal_hom _ _

/-- The Isom sheaves of the terminal stack are terminal, so they are represented by
`Over.mk (𝟙 S)`. -/
instance hasRepresentableDiagonal_terminal :
    (terminal.{v', v, u', u} C J).HasRepresentableDiagonal where
  representable _ _ := (StackMorphism.representableByOfSubsingleton _
    fun _ ↦ (nonempty_chosenTerminal_hom _ _).some).isRepresentable

end Terminal

section Yoneda

/-- The Isom sheaves of the discrete stack of a sheaf of types are subsingletons. -/
private lemma subsingleton_isom_stackInGroupoidsOfSheaf {P : Cᵒᵖ ⥤ Type v}
    (hP : Presieve.IsSheaf J P) {S : C}
    (x y : (stackInGroupoidsOfSheaf J P hP).presheaf.obj (.mk (op S))) (T : (Over S)ᵒᵖ) :
    Subsingleton (((stackInGroupoidsOfSheaf J P hP).isom x y).obj.obj T) :=
  letI : IsDiscrete ((stackInGroupoidsOfSheaf J P hP).presheaf.obj (.mk (op T.unop.left))) :=
    discretePseudofunctor_obj_isDiscrete P _
  IsDiscrete.subsingleton _ _

variable {X : C} [∀ (S : C) (x y : S ⟶ X), HasEqualizer x y]
  (hX : Presieve.IsSheaf J (yoneda.obj X))

/-- The Isom sheaf of two morphisms `x y : S ⟶ X` in the discrete stack of `yoneda.obj X` is
represented by their equalizer. -/
private def isomRepresentableByEqualizer {S : C}
    (x y : (stackInGroupoidsOfSheaf J (yoneda.obj X) hX).presheaf.obj (.mk (op S))) :
    ((stackInGroupoidsOfSheaf J (yoneda.obj X) hX).isom x y).obj.RepresentableBy
      (Over.mk (equalizer.ι x.as y.as)) where
  homEquiv {T} :=
    { toFun k := Discrete.eqToHom (show T.hom ≫ x.as = T.hom ≫ y.as by
        rw [← Over.w k]
        simp only [Over.mk_hom, Category.assoc]
        rw [equalizer.condition])
      invFun h := Over.homMk (equalizer.lift T.hom (Discrete.eq_of_hom h)) (by simp)
      left_inv k := by
        ext
        apply equalizer.hom_ext
        simpa using (Over.w k).symm
      right_inv _ := (subsingleton_isom_stackInGroupoidsOfSheaf _ x y _).elim _ _ }
  homEquiv_comp _ _ := (subsingleton_isom_stackInGroupoidsOfSheaf _ x y _).elim _ _

/-- The discrete stack of a represented sheaf `yoneda.obj X` has representable diagonal when
every two morphisms `S ⟶ X` have an equalizer, which then represents their Isom sheaf. -/
instance hasRepresentableDiagonal_yoneda :
    (stackInGroupoidsOfSheaf J (yoneda.obj X) hX).HasRepresentableDiagonal where
  representable x y := (isomRepresentableByEqualizer hX x y).isRepresentable

end Yoneda

end StackInGroupoids

end

end CategoryTheory
