/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representability

/-!
# The fibres of the diagonal of a stack in groupoids are its Isom sheaves

Let `X` be a stack in groupoids and `x`, `y` two objects of `X` over `S`. The presheaf on `Over S`
of isomorphism classes of the fibre of the diagonal `StackInGroupoids.diag X : X ⟶ X × X` over the
object `(x, y)` of `X × X` is the Isom sheaf `X.isom x y`, lifted to the object universe of the
fibres. So the diagonal is representable, in the sense of `StackMorphism.IsRepresentable`, exactly
when every Isom sheaf is representable.

## Main definitions

* `CategoryTheory.StackInGroupoids.prodMk x y`: the object `(x, y)` of a product `X × Y`, and
  `CategoryTheory.StackInGroupoids.isoProdMk`: every object of `X × Y` is isomorphic to `prodMk`
  of its two components.
* `CategoryTheory.StackInGroupoids.diagFiberIsoClassesIso x y`: the isomorphism between the
  presheaf of isomorphism classes of the fibre of the diagonal over `prodMk x y` and the Isom sheaf
  of `x` and `y`, lifted to `Type (max v' u')`.

## Main results

* `CategoryTheory.StackInGroupoids.diag_app_faithful`: the fibre functors of the diagonal are
  faithful.
* `CategoryTheory.StackInGroupoids.hasRepresentableDiagonal_iff`: a stack in groupoids has
  representable Isom sheaves (`StackInGroupoids.HasRepresentableDiagonal`) exactly when its diagonal
  is representable.

## Implementation notes

In `StackMorphism.FiberCategory` the structure map points from the base point, so an object of the
fibre of the diagonal over `prodMk x y` at `T` is a triple `(z, α, β)` with `α : x|_T ⟶ z` and
`β : y|_T ⟶ z`. It is sent to `α ≫ β⁻¹ : x|_T ⟶ y|_T`, the isomorphism `β ∘ α⁻¹` of the proof hint
of Stacks Lemma 8.2.5 with `α` and `β` pointing the other way. Two objects with the same image are
isomorphic, through their second components, and `(y|_T, φ, 𝟙)` has image `φ`.

Stacks Lemma 8.2.5 is stated for a fibred category, whose Isom presheaf is the subpresheaf of
isomorphisms of `Mor(x, y)`. The fibres here are groupoids, so the Isom sheaf is Mathlib's
`Pseudofunctor.sheafHom`, as in the docstring of `StackInGroupoids.isom`.

The presheaf `StackMorphism.fiberIsoClasses` lands in `Type (max v' u')` and the Isom sheaf in
`Type v'`, so the two are compared after `uliftFunctor`. Representability crosses `uliftFunctor` by
`Functor.isRepresentable_comp_uliftFunctor_iff`.

## References

* [Stacks Project, Tag 04SI](https://stacks.math.columbia.edu/tag/04SI), Lemma 8.2.5
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G), Lemma 94.10.11
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB), Definition 8.2.2

## Tags

stack in groupoids, diagonal, Isom sheaf, representable morphism, 2-fibre product
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v' v u' u

namespace CategoryTheory.StackInGroupoids

open Opposite Bicategory Limits
open scoped Pseudofunctor.StrongTrans

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X : StackInGroupoids.{v', v, max v' u', u} C J}

/-- Any two parallel morphisms of the chosen terminal category are equal. -/
private lemma subsingleton_hom_chosenTerminal (a b : Cat.chosenTerminal.{v', u'}) :
    Subsingleton (a ⟶ b) := by
  constructor
  rintro ⟨⟨⟨⟨⟩⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
  rfl

section ProdMk

variable {Y : StackInGroupoids.{v', v, max v' u', u} C J} {S : C}

/-- The object `(x, y)` of the product `X × Y` over `S`. Its component in the terminal category is
the identity of the unique object. -/
def prodMk (x : X.presheaf.obj (.mk (op S))) (y : Y.presheaf.obj (.mk (op S))) :
    (prod X Y).presheaf.obj (.mk (op S)) :=
  ⟨x, y, Iso.refl _⟩

@[simp]
lemma prodMk_fst (x : X.presheaf.obj (.mk (op S))) (y : Y.presheaf.obj (.mk (op S))) :
    (prodMk x y).fst = x :=
  rfl

@[simp]
lemma prodMk_snd (x : X.presheaf.obj (.mk (op S))) (y : Y.presheaf.obj (.mk (op S))) :
    (prodMk x y).snd = y :=
  rfl

/-- Every object of `X × Y` is isomorphic to `prodMk` of its two components. -/
def isoProdMk (p : (prod X Y).presheaf.obj (.mk (op S))) : p ≅ prodMk p.fst p.snd :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    ((subsingleton_hom_chosenTerminal _ _).elim _ _)

end ProdMk

section Fiber

variable {S : C} {x y : X.presheaf.obj (.mk (op S))} {T : Over S}

/-- The morphism `α ≫ β⁻¹ : x|_T ⟶ y|_T` of an object `(z, α : x|_T ⟶ z, β : y|_T ⟶ z)` of the
fibre of the diagonal over `prodMk x y`. -/
private def fiberHom (a : (diag X).FiberCategory (prodMk x y) T) :
    (X.isom x y).obj.obj (op T) :=
  a.of.hom.fst ≫ inv a.of.hom.snd

@[simp]
private lemma diag_app_map_fst {T : C} {z z' : X.presheaf.obj (.mk (op T))} (f : z ⟶ z') :
    ((diag X).app T |>.map f).fst = f :=
  rfl

@[simp]
private lemma diag_app_map_snd {T : C} {z z' : X.presheaf.obj (.mk (op T))} (f : z ⟶ z') :
    ((diag X).app T |>.map f).snd = f :=
  rfl

/-- The two components of the naturality isomorphism of the diagonal agree. -/
private lemma diag_naturality_inv_app_fst {T T' : C} (f : T' ⟶ T)
    (z : X.presheaf.obj (.mk (op T))) :
    (((diag X).naturality f.op.toLoc).inv.toNatTrans.app z).fst =
      (((diag X).naturality f.op.toLoc).inv.toNatTrans.app z).snd :=
  rfl

/-- Isomorphic objects of the fibre of the diagonal have the same morphism. -/
private lemma fiberHom_eq_of_iso {a b : (diag X).FiberCategory (prodMk x y) T} (e : a ≅ b) :
    fiberHom a = fiberHom b := by
  have h := StructuredArrow.w e.hom.iso.hom
  have h₁ : a.of.hom.fst ≫ e.hom.iso.hom.right = b.of.hom.fst :=
    congrArg CategoricalPullback.Hom.fst h
  have h₂ : a.of.hom.snd ≫ e.hom.iso.hom.right = b.of.hom.snd :=
    congrArg CategoricalPullback.Hom.snd h
  simp [fiberHom, ← h₁, ← h₂]

/-- The object `(y|_T, φ, 𝟙)` of the fibre of the diagonal over `prodMk x y`. -/
private def fiberObj (φ : (X.isom x y).obj.obj (op T)) : (diag X).FiberCategory (prodMk x y) T :=
  Core.mk (StructuredArrow.mk (Y := (X.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
    (CategoricalPullback.Hom.mk φ (𝟙 _) ((subsingleton_hom_chosenTerminal _ _).elim _ _)))

private lemma fiberHom_fiberObj (φ : (X.isom x y).obj.obj (op T)) :
    fiberHom (fiberObj φ) = φ := by
  simp only [fiberHom, fiberObj, StructuredArrow.mk_hom_eq_self]
  exact (congrArg (φ ≫ ·) IsIso.inv_id).trans (Category.comp_id φ)

/-- Every object of the fibre of the diagonal is isomorphic to `fiberObj` of its morphism. -/
private def fiberObjFiberHomIso (a : (diag X).FiberCategory (prodMk x y) T) :
    fiberObj (fiberHom a) ≅ a :=
  Core.isoMk (StructuredArrow.isoMk (asIso a.of.hom.snd) (by
    apply CategoricalPullback.hom_ext <;> simp [fiberObj, fiberHom]))

variable (x y T) in
/-- The isomorphism classes of the fibre of the diagonal over `prodMk x y` at `T` are the
morphisms `x|_T ⟶ y|_T`. -/
private def fiberIsoClassesEquiv :
    ((diag X).fiberIsoClasses (prodMk x y)).obj (op T) ≃
      ULift.{max v' u'} ((X.isom x y).obj.obj (op T)) where
  toFun := Quot.lift (fun a ↦ ULift.up (fiberHom a))
    fun _ _ ⟨e⟩ ↦ congrArg ULift.up (fiberHom_eq_of_iso e)
  invFun φ := Quot.mk _ (fiberObj φ.down)
  left_inv := by
    rintro ⟨a⟩
    exact Quot.sound ⟨fiberObjFiberHomIso a⟩
  right_inv φ := congrArg ULift.up (fiberHom_fiberObj φ.down)

/-- `fiberHom` commutes with restriction along a morphism of test objects. -/
private lemma fiberHom_fiberMap {T' : Over S} (g : T' ⟶ T)
    (a : (diag X).FiberCategory (prodMk x y) T) :
    fiberHom (Core.mk (((diag X).fiberMap (prodMk x y) g).obj a.of)) =
      (X.isom x y).obj.map g.op (fiberHom a) := by
  simp [fiberHom, StackMorphism.fiberMap, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    diag_naturality_inv_app_fst]
  rw [IsIso.inv_eq_of_hom_inv_id (Cat.Hom.hom_inv_id_toNatTrans_app _ y)]

end Fiber

/-- The fibre of the diagonal of a stack in groupoids over the object `(x, y)` of `X × X` is the
Isom sheaf of `x` and `y` ([Stacks Project, Tag 04SI](https://stacks.math.columbia.edu/tag/04SI),
Lemma 8.2.5): the presheaf on `Over S` of isomorphism classes of the fibre is isomorphic to the
Isom sheaf, lifted to the universe `Type (max v' u')` of the classes.

The class of `(z, α : x|_T ⟶ z, β : y|_T ⟶ z)` goes to `α ≫ β⁻¹ : x|_T ⟶ y|_T`
(`StackInGroupoids.diagFiberIsoClassesIso_hom_app_mk`). -/
def diagFiberIsoClassesIso {S : C} (x y : X.presheaf.obj (.mk (op S))) :
    (diag X).fiberIsoClasses (prodMk x y) ≅ (X.isom x y).obj ⋙ uliftFunctor.{max v' u'} :=
  NatIso.ofComponents (fun T ↦ (fiberIsoClassesEquiv x y T.unop).toIso) fun g ↦ by
    ext ⟨a⟩
    exact congrArg ULift.up (fiberHom_fiberMap g.unop a)

/-- `StackInGroupoids.diagFiberIsoClassesIso` sends the class of `(z, α, β)` to `α ≫ β⁻¹`. -/
lemma diagFiberIsoClassesIso_hom_app_mk {S : C} (x y : X.presheaf.obj (.mk (op S))) {T : Over S}
    (a : (diag X).FiberCategory (prodMk x y) T) :
    ((diagFiberIsoClassesIso x y).hom.app (op T) (_root_.Quotient.mk _ a)).down =
      a.of.hom.fst ≫ inv a.of.hom.snd :=
  rfl

/-- The fibre functors of the diagonal of a stack in groupoids are faithful: the first component
of the image of a morphism is the morphism. -/
instance diag_app_faithful (T : C) : ((diag X).app T).Faithful where
  map_injective h := congrArg CategoricalPullback.Hom.fst h

/-- The diagonal of a stack in groupoids is representable exactly when every Isom sheaf is
representable. This is the analogue of the equivalence of conditions (1) and (2) of
[Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G) (Lemma 94.10.11), with
representability by an object of the site in place of representability by algebraic spaces; as
there, it follows from Stacks Lemma 8.2.5 (`StackInGroupoids.diagFiberIsoClassesIso`).

`StackInGroupoids.HasRepresentableDiagonal` is stated through the Isom sheaves rather than as
representability of `StackInGroupoids.diag X` because the Isom sheaves live in the hom universe
`v'` of the fibres, and are defined for stacks in any fibre universes, while the diagonal needs
fibres with object universe `max v' u'` and its classes live there. -/
theorem hasRepresentableDiagonal_iff :
    X.HasRepresentableDiagonal ↔ (diag X).IsRepresentable := by
  constructor
  · intro h
    refine ⟨fun T ↦ inferInstance, fun {S} p ↦ ?_⟩
    have := h.representable p.fst p.snd
    exact isRepresentable_of_natIso ((X.isom p.fst p.snd).obj ⋙ uliftFunctor.{max v' u'})
      ((diagFiberIsoClassesIso p.fst p.snd).symm ≪≫
        ((diag X).fiberIsoClassesIsoOfIso (isoProdMk p)).symm)
  · intro h
    refine ⟨fun {S} x y ↦ ?_⟩
    have := h.representable (prodMk x y)
    exact Functor.isRepresentable_comp_uliftFunctor_iff.{max v' u'}.1
      (isRepresentable_of_natIso _ (diagFiberIsoClassesIso x y))

end

end CategoryTheory.StackInGroupoids
