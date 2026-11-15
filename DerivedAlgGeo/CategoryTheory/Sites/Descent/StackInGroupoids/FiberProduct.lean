/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.FiberProduct
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism

/-!
# Two-fibre products of stacks in groupoids, the diagonal, and Isom sheaves

Stacks in groupoids have 2-fibre products, with their projections and 2-commutativity
isomorphism, a terminal object, products, and relative and absolute diagonals. For two objects
`x` and `y` of a fibre over `S`, the Isom sheaf on `Over S` is Mathlib's `sheafHom`; its sections
over `T` are the isomorphisms between the pullbacks of `x` and `y` to `T`.

## Main definitions

* `CategoryTheory.StackInGroupoids.fiberProduct f g`, with `fiberProduct.fst`,
  `fiberProduct.snd` and `fiberProduct.comm`: the 2-fibre product of two stack morphisms.
* `CategoryTheory.StackInGroupoids.terminal`, `toTerminal` and `prod`: the terminal stack in
  groupoids, the morphism to it, and products.
* `CategoryTheory.StackInGroupoids.diagonal f` and `diag X`: the relative diagonal of a stack
  morphism and the absolute diagonal `X ⟶ X × X`.
* `CategoryTheory.StackInGroupoids.isom x y`: the Isom sheaf of two objects of a fibre.
* `CategoryTheory.StackInGroupoids.isomEquiv`: its sections over `T` are isomorphisms of
  pullbacks.

## Main results

The stack conditions are `Pseudofunctor.isStack_fiberProduct` and
`Pseudofunctor.isStack_terminal`, in `DerivedAlgGeo/CategoryTheory/Sites/Descent/FiberProduct.lean`.

## Implementation notes

An object of a fibre of a 2-fibre product contains an isomorphism of the base, so the fibres of
the 2-fibre product of stacks with fibres in `Cat.{v', u'}` lie in `Cat.{v', max v' u'}`. The
2-fibre products, products and diagonals are therefore stated for stacks whose fibres already
have object universe `max v' u'`, where the construction closes up; the terminal stack and the
Isom sheaves are stated in any fibre universes.

The diagonal is a stack morphism with a target. That its fibres are the Isom sheaves is not
proved here.

## References

* [Stacks Project, Tag 02ZL](https://stacks.math.columbia.edu/tag/02ZL), Lemma 8.5.6
* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G), Lemma 8.4.6
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB), Definition 8.2.2

## Tags

stack in groupoids, 2-fibre product, diagonal, Isom sheaf
-/

universe v' v u' u

namespace CategoryTheory.StackInGroupoids

open Opposite
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section FiberProduct

variable {X Y Z : StackInGroupoids.{v', v, max v' u', u} C J}

/-- The 2-fibre product of two morphisms of stacks in groupoids
([Stacks Project, Tag 02ZL](https://stacks.math.columbia.edu/tag/02ZL)): the 2-fibre product of
the underlying pseudofunctors, a stack by `Pseudofunctor.isStack_fiberProduct`. -/
@[simps presheaf]
def fiberProduct (f : StackMorphism X Z) (g : StackMorphism Y Z) : StackInGroupoids C J where
  presheaf := Pseudofunctor.fiberProduct f g
  fiberIsGroupoid := Pseudofunctor.fiberProduct.isGroupoid_obj f g
  isStack := Pseudofunctor.isStack_fiberProduct f g

namespace fiberProduct

variable (f : StackMorphism X Z) (g : StackMorphism Y Z)

/-- The first projection of the 2-fibre product of stacks in groupoids. -/
abbrev fst : StackMorphism (fiberProduct f g) X :=
  Pseudofunctor.fiberProduct.fst f g

/-- The second projection of the 2-fibre product of stacks in groupoids. -/
abbrev snd : StackMorphism (fiberProduct f g) Y :=
  Pseudofunctor.fiberProduct.snd f g

/-- The 2-commutativity isomorphism of the 2-fibre product of stacks in groupoids. -/
abbrev comm :
    (fst f g ≫ f : (fiberProduct f g).presheaf ⟶ Z.presheaf) ≅ snd f g ≫ g :=
  Pseudofunctor.fiberProduct.comm f g

end fiberProduct

end FiberProduct

section Terminal

variable (C J) in
/-- The terminal stack in groupoids: the constant pseudofunctor at the terminal category, a
stack by `Pseudofunctor.isStack_terminal`. -/
@[simps presheaf]
def terminal : StackInGroupoids.{v', v, u', u} C J where
  presheaf := Pseudofunctor.terminal Cᵒᵖ
  fiberIsGroupoid := Pseudofunctor.isGroupoid_terminal_obj
  isStack := Pseudofunctor.isStack_terminal

/-- The morphism from a stack in groupoids to the terminal one. -/
abbrev toTerminal (X : StackInGroupoids.{v', v, u', u} C J) : StackMorphism X (terminal C J) :=
  Pseudofunctor.toTerminal X.presheaf

end Terminal

section Diagonal

variable {X Z : StackInGroupoids.{v', v, max v' u', u} C J}

/-- The product of two stacks in groupoids, their 2-fibre product over the terminal stack. -/
abbrev prod (X Y : StackInGroupoids.{v', v, max v' u', u} C J) :
    StackInGroupoids.{v', v, max v' u', u} C J :=
  fiberProduct (toTerminal X) (toTerminal Y)

/-- The relative diagonal `X ⟶ X ×_Z X` of a morphism of stacks in groupoids, sending `x` to
`(x, x, 𝟙)`. -/
abbrev diagonal (f : StackMorphism X Z) : StackMorphism X (fiberProduct f f) :=
  Pseudofunctor.diagonal f

/-- The absolute diagonal `X ⟶ X × X` of a stack in groupoids, the relative diagonal of the
morphism to the terminal stack. -/
abbrev diag (X : StackInGroupoids.{v', v, max v' u', u} C J) : StackMorphism X (prod X X) :=
  diagonal (toTerminal X)

end Diagonal

section Isom

variable (X : StackInGroupoids.{v', v, u', u} C J) {S : C}

/-- The Isom sheaf of two objects `x` and `y` of a stack in groupoids over `S`: the sheaf on
`Over S` whose sections over `T` are the morphisms between the pullbacks of `x` and `y`.

Stacks defines `Isom(x, y)` as the subpresheaf of isomorphisms of the presheaf `Mor(x, y)`
([Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)). The fibres of a stack in
groupoids are groupoids, so `Mor(x, y) = Isom(x, y)` and no second presheaf is defined: this is
Mathlib's `Pseudofunctor.sheafHom`, and `isomEquiv` identifies its sections with isomorphisms. -/
abbrev isom (x y : X.presheaf.obj (.mk (op S))) : Sheaf (J.over S) (Type v') :=
  X.presheaf.sheafHom J x y

/-- The sections of the Isom sheaf over `T : Over S` are the isomorphisms between the pullbacks
of `x` and `y` to `T`. -/
noncomputable def isomEquiv (x y : X.presheaf.obj (.mk (op S))) (T : Over S) :
    (X.isom x y).obj.obj (op T) ≃
      ((X.presheaf.map T.hom.op.toLoc).toFunctor.obj x ≅
        (X.presheaf.map T.hom.op.toLoc).toFunctor.obj y) where
  toFun (φ : _ ⟶ _) := asIso φ
  invFun e := e.hom
  left_inv _ := rfl
  right_inv _ := Iso.ext rfl

variable {X} (x y : X.presheaf.obj (.mk (op S))) (T : Over S)

@[simp]
lemma isomEquiv_apply_hom (φ : (X.isom x y).obj.obj (op T)) :
    (X.isomEquiv x y T φ).hom = φ :=
  rfl

@[simp]
lemma isomEquiv_symm_apply
    (e : (X.presheaf.map T.hom.op.toLoc).toFunctor.obj x ≅
      (X.presheaf.map T.hom.op.toLoc).toFunctor.obj y) :
    (X.isomEquiv x y T).symm e = e.hom :=
  rfl

end Isom

end CategoryTheory.StackInGroupoids
