/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids

/-!
# Morphisms and pointwise-represented fibers of stacks in groupoids

Stack morphisms, their fiber categories, and pointwise representability by an
object of an arbitrary site are generic category theory.  Geometric properties
of the representing morphism remain in the corresponding geometric consumer
layer.

## Main definitions

* `StackMorphism` — a strong transformation between the underlying
  pseudofunctors, with `StackMorphism.app`, `StackMorphism.pullbackIso`,
  `StackMorphism.id`, `StackMorphism.comp` and `StackMorphism.Modification`.
* `StackMorphism.FiberCategory` — the groupoid fiber over a test object and a
  target object.
* `StackMorphism.PointwiseFiberRepresentation` — a representing object and,
  for each test object separately, an equivalence with the fiber.
* `StackMorphism.IsPointwiseRepresentable` — every fiber has a
  `PointwiseFiberRepresentation`.

## Main results

None; this file only defines the vocabulary.

## Implementation notes

Pointwise representability chooses an equivalence with the fiber for each test
object separately, with no compatibility along maps of test objects.  The
docstring of `StackMorphism.PointwiseFiberRepresentation` explains why that is
weaker than representability of the 2-fibre product, and gives a non-smooth
morphism that is pointwise smooth and surjective.

## References

* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4)

## Tags

stack in groupoids, stack morphism, fiber category, pointwise representability
-/

namespace CategoryTheory

open Bicategory Opposite

noncomputable section

universe v w u

/-- A morphism of stacks is a strong transformation between their underlying
pseudofunctors.  Pullback naturality, identities, and composition are supplied
by Mathlib's pseudofunctor API. -/
abbrev StackMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (F G : StackInGroupoids C J) :=
  Pseudofunctor.StrongTrans F.presheaf G.presheaf

namespace StackMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G H I : StackInGroupoids C J}

open scoped Pseudofunctor.StrongTrans

/-- The functor induced by a stack morphism on the fiber over `S`. -/
abbrev app (f : StackMorphism F G) (S : C) :
    Functor (F.presheaf.obj (.mk (op S)))
      (G.presheaf.obj (.mk (op S))) :=
  (Pseudofunctor.StrongTrans.app f (.mk (op S))).toFunctor

/-- The pseudonatural pullback comparison of a stack morphism along a site
morphism. -/
abbrev pullbackIso (f : StackMorphism F G) {S T : C} (g : T ⟶ S) :
    (F.presheaf.map g.op.toLoc).toFunctor ⋙ f.app T ≅
      f.app S ⋙ (G.presheaf.map g.op.toLoc).toFunctor :=
  Cat.Hom.toNatIso (f.naturality g.op.toLoc)

/-- The identity stack morphism, including its pseudonaturality coherence. -/
abbrev id (F : StackInGroupoids C J) : StackMorphism F F :=
  Pseudofunctor.StrongTrans.id F.presheaf

/-- Composition of stack morphisms. -/
abbrev comp (f : StackMorphism F G) (g : StackMorphism G H) :
    StackMorphism F H :=
  Pseudofunctor.StrongTrans.vcomp f g

/-- A 2-morphism between stack morphisms is a modification. -/
abbrev Modification (f g : StackMorphism F G) :=
  Pseudofunctor.StrongTrans.Modification f g

/-- The groupoid fiber of a stack morphism over a test object and a chosen
target object. -/
abbrev FiberCategory (f : StackMorphism F G) {S : C}
    (y : G.presheaf.obj (.mk (op S))) (T : Over S) :=
  Core (StructuredArrow
    ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
    (f.app T.left))

/-- A representation of one fibre of a stack morphism, pointwise in the test
object: an object `representing` over `S` and, for each test object `T`
separately, an equivalence `Discrete (T ⟶ representing) ≌ f.FiberCategory y T`.

Nothing relates `fiberEquivalence T` to `fiberEquivalence T'` along a map
`T' ⟶ T`, as the `homEquiv_comp` field of Mathlib's `Functor.RepresentableBy`
would. So this is weaker than representability of the 2-fibre product (Stacks
Project, Tag 02Y4). For an infinite field `k`, the Hom-sets from any `k`-scheme
`T` to `X = Spec k[ε]/(ε²) ×ₖ 𝔸¹` and to `𝔸¹` have the same cardinality, namely
that of `Γ(T, 𝒪_T)`. Bijections chosen test object by test object therefore make
the stack morphism induced by `X ⟶ Spec k` `IsPointwiseSmoothSurjective`, with
the pullback of `𝔸¹` as representing object, although `X ⟶ Spec k` is not
smooth. Representability natural in the test object is not defined here. -/
structure PointwiseFiberRepresentation (f : StackMorphism F G) {S : C}
    (y : G.presheaf.obj (.mk (op S))) where
  /-- The representing object over `S`. -/
  representing : Over S
  /-- The comparison at the test object `T` alone; nothing ties it to the
  comparison at another test object. -/
  fiberEquivalence (T : Over S) :
    Discrete (T ⟶ representing) ≌ f.FiberCategory y T

/-- A stack morphism is pointwise representable when every fiber over a test
object has a `PointwiseFiberRepresentation`. That structure's docstring explains
why this is weaker than representability by the 2-fibre product. -/
class IsPointwiseRepresentable (f : StackMorphism F G) : Prop where
  representation {S : C} (y : G.presheaf.obj (.mk (op S))) :
    Nonempty (f.PointwiseFiberRepresentation y)

end StackMorphism

end


end CategoryTheory
