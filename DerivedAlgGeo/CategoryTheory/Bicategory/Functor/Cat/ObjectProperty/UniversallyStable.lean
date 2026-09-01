/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty

/-!
# Universally stable object properties of pseudofunctors

For an object property `P` on a Cat-valued pseudofunctor `F`, this file
defines the subproperty consisting of objects whose image along every
outgoing morphism again satisfies `P`. This universally stable closure is
preserved by every transition by construction; the proof uses the compositor
of `F`, so Mathlib's `Pseudofunctor.ObjectProperty.fullsubcategory` turns it
into an actual replete sub-pseudofunctor.

This is the repository's generic subprestack root. A geometric locus should
supply an object property and the relevant preservation theorem instead of
defining a second subprestack carrier in its consumer directory.
-/

namespace CategoryTheory.Pseudofunctor.ObjectProperty

open CategoryTheory.Bicategory

universe w v v' u u'

variable {B : Type u} [Bicategory.{w, v} B]
variable {F : Pseudofunctor B Cat.{v', u'}} (P : F.ObjectProperty)

/-- The objects satisfying `P` after every base change represented by an
outgoing morphism in the source bicategory. -/
def universallyStable : F.ObjectProperty where
  prop X M := ∀ (Y : B) (f : X ⟶ Y),
    P.prop Y ((F.map f).toFunctor.obj M)

instance universallyStable_isClosedUnderIsomorphisms
    [P.IsClosedUnderIsomorphisms] :
    (universallyStable P).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := {
    of_iso := by
      intro M N e hM Y f
      exact (P.prop Y).prop_of_iso ((F.map f).toFunctor.mapIso e) (hM Y f) }

instance universallyStable_isClosedUnderMapObj
    [P.IsClosedUnderIsomorphisms] :
    (universallyStable P).IsClosedUnderMapObj where
  map_obj hM f Z g :=
    (P.prop Z).prop_of_iso
      ((Cat.Hom.toNatIso (F.mapComp f g)).app _) (hM Z (f ≫ g))

/-- A universally stable object satisfies the original property before base
change. The comparison is the unit isomorphism of the pseudofunctor. -/
theorem universallyStable_le_self [P.IsClosedUnderIsomorphisms]
    (X : B) : (universallyStable P).prop X ≤ P.prop X := by
  intro M hM
  exact (P.prop X).prop_of_iso
    ((Cat.Hom.toNatIso (F.mapId X)).app M) (hM X (𝟙 X))

/-- If `P` is already preserved by every transition, every `P`-object is
universally stable. -/
theorem le_universallyStable [P.IsClosedUnderMapObj]
    (X : B) : P.prop X ≤ (universallyStable P).prop X := by
  intro M hM Y f
  exact P.map_obj hM f

/-- A transition-stable property agrees fiberwise with its universally stable
closure. -/
theorem universallyStable_eq_self [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderMapObj] (X : B) :
    (universallyStable P).prop X = P.prop X :=
  le_antisymm (universallyStable_le_self P X) (le_universallyStable P X)

end CategoryTheory.Pseudofunctor.ObjectProperty
