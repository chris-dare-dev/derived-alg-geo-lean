/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Canonical
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism

/-!
# Representable stacks on subcanonical sites

`StackInGroupoids.representable J X` is the discrete stack of `yoneda.obj X`
for a subcanonical topology `J`. `StackInGroupoids.representableMap` induces
its morphisms by postcomposition, and `StackInGroupoids.representable_ofLE`
identifies the constructions after restriction to a coarser subcanonical
topology. The stack property is the existing sheaf-to-stack construction
applied to subcanonicity; no new descent hypothesis is supplied.
-/

namespace CategoryTheory

open Opposite

noncomputable section

universe v u

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-- The stack represented by `X` on a subcanonical site is the discrete stack
of `yoneda.obj X`, constructed by `stackInGroupoidsOfSheaf`.

Its fibres belong to `Cat.{v, v}` because `yoneda.obj X` is `Type v`-valued.
After #1631, #1637 generalizes this construction in place to independent fibre
universes, preserving the names `StackInGroupoids.representable` and
`StackInGroupoids.representableMap`. -/
def representable (X : C) : StackInGroupoids C J :=
  stackInGroupoidsOfSheaf J (yoneda.obj X)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))

/-- A morphism induces `StackInGroupoids.representableMap` by postcomposition
on each fibre of the corresponding representable stacks. -/
def representableMap {X Y : C} (f : X ⟶ Y) :
    StackMorphism (representable J X) (representable J Y) :=
  discreteMap _ _ (yoneda.map f)

/-- The component functors of `StackInGroupoids.representableMap` act by
postcomposition, definitionally. -/
@[simp]
theorem representableMap_app_obj {X Y T : C} (f : X ⟶ Y) (g : T ⟶ X) :
    ((representableMap J f).app T).obj (Discrete.mk g) = Discrete.mk (g ≫ f) :=
  rfl

/-- `StackInGroupoids.representable` is unchanged by restriction along an
inequality between subcanonical topologies: `StackInGroupoids.ofLE` changes
only its descent proof. -/
theorem representable_ofLE {J₁ J₂ : GrothendieckTopology C}
    [J₁.Subcanonical] [J₂.Subcanonical] (h : J₁ ≤ J₂) (X : C) :
    (representable J₂ X).ofLE h = representable J₁ X :=
  rfl

end StackInGroupoids

end

end CategoryTheory
