/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import DerivedAlgGeo.CategoryTheory.Sites.Descent.IsStack

/-!
# Stacks in groupoids

This file packages Mathlib's stack condition together with the additional
groupoid-valued requirement used in algebraic geometry.  Covers and Čech
descent are the existing `Sieve`, `Presieve`, and `Pseudofunctor.DescentData`
objects: this layer does not replace them with parallel definitions.

## Main definitions

* `CategoryTheory.StackInGroupoids`: a pseudofunctor `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}`
  with groupoid fibers and effective descent for a Grothendieck topology.
* `CategoryTheory.StackInGroupoids.Cover`: an explicitly indexed covering family, with
  its category of Čech descent data `CategoryTheory.StackInGroupoids.CechDescent`.
* `CategoryTheory.StackInGroupoids.ofLE`: restriction to a coarser topology.
* `CategoryTheory.StackInGroupoids.ofEquivalence`: transport along a strong
  transformation whose components are equivalences of categories.

## Main results

* `CategoryTheory.StackInGroupoids.cechDescentEquivalence`: every fiber is equivalent to
  the Čech descent data of every covering family.
* `CategoryTheory.Pseudofunctor.IsStack.of_le`: effective descent for a finer topology
  gives effective descent for a coarser one.

## Implementation notes

The construction is owned by `CategoryTheory/Sites`: it is generic in a
category and a Grothendieck topology and imports no algebraic geometry.  The
declarations use the matching `CategoryTheory` namespace.

`StackInGroupoids` deliberately contains no algebraicity, representability,
boundedness, or finiteness assertion.  The only conditions are groupoid-valued
fibers and effective descent for a chosen Grothendieck topology.  The fibers
live in `Cat.{v', u'}` with independent universes, as in Mathlib's
`Pseudofunctor.IsStack`, and the carrier states no relation between them.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)

## Tags

stack, stack in groupoids, descent, Grothendieck topology
-/

namespace CategoryTheory

open CategoryTheory
open CategoryTheory.Bicategory
open Opposite

noncomputable section

universe t v' v u' u

/-- A groupoid-valued pseudofunctor satisfying effective descent for `J`.

The fibers lie in `Cat.{v', u'}`: `v'` is the universe of their morphisms and `u'` the
universe of their objects.  The two are independent of each other and of `C`, as in
Mathlib's `Pseudofunctor.IsStack`.  The discrete stack of a `Type w`-valued sheaf has
fibers in `Cat.{w, w}`, and a representable stack has fibers in `Cat.{v, v}`; placing
them in other fiber universes is a separate universe lift, not a condition on this
structure. -/
structure StackInGroupoids (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  /-- The contravariant groupoid-valued pseudofunctor. -/
  presheaf : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}
  /-- Every fiber is a groupoid. -/
  fiberIsGroupoid (X : LocallyDiscrete Cᵒᵖ) : IsGroupoid (presheaf.obj X)
  /-- Objects and morphisms satisfy effective descent for `J`. -/
  isStack : presheaf.IsStack J

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

instance presheaf_obj_isGroupoid
    (F : StackInGroupoids C J) (X : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid (F.presheaf.obj X) :=
  F.fiberIsGroupoid X

instance presheaf_isStack (F : StackInGroupoids C J) :
    F.presheaf.IsStack J :=
  F.isStack

/-- An explicitly indexed covering family for a Grothendieck topology. -/
structure Cover (S : C) where
  /-- The indexing type of the covering family. -/
  index : Type t
  /-- Schemes or site objects in the covering family. -/
  obj : index → C
  /-- The covering arrows. -/
  hom (i : index) : obj i ⟶ S
  /-- The arrows generate a covering sieve. -/
  mem : Sieve.ofArrows obj hom ∈ J S

/-- The category of Čech descent data for a covering family. -/
abbrev CechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :=
  F.presheaf.DescentData U.hom

/-- Restrict an object and its morphisms to Čech descent data. -/
abbrev toCechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :=
  F.presheaf.toDescentData U.hom

/-- The stack condition identifies a fiber with the category of Čech descent
data for every covering family. -/
def cechDescentEquivalence (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :
    F.presheaf.obj (.mk (op S)) ≌ F.CechDescent U := by
  letI := F.presheaf.isEquivalence_toDescentData U.hom U.mem
  exact (F.toCechDescent U).asEquivalence

/-- Morphisms satisfy descent: restriction to a cover is fully faithful. -/
def fullyFaithfulToCechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :
    (F.toCechDescent U).FullyFaithful :=
  F.presheaf.fullyFaithfulToDescentData U.hom U.mem

/-- Objects satisfy effective descent: every Čech descent object comes from an
object over the base, up to isomorphism. -/
theorem essSurjToCechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :
    (F.toCechDescent U).EssSurj := by
  letI := F.presheaf.isEquivalence_toDescentData U.hom U.mem
  infer_instance

end StackInGroupoids

/-! ## Refining the Grothendieck topology

Effective descent is antitone in the topology, and only in that direction.
Every `J₁`-covering sieve is a `J₂`-covering sieve when `J₁ ≤ J₂`, so a stack
for the finer topology is a stack for the coarser one.  The converse is false
and nothing below asserts it: descent for a coarse topology says nothing about
the covers the finer topology adds.  A consumer that needs the finer level has
to prove it there. -/

/-- Effective descent for a finer topology gives effective descent for every
coarser topology.  This is the only implication between the two conditions;
there is no reverse transport. -/
theorem Pseudofunctor.IsStack.of_le {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) [F.IsStack J₂] :
    F.IsStack J₁ :=
  Pseudofunctor.IsStack.of_isStackFor fun _ R hR ↦ F.isStackFor' R (h _ hR)

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] {J₁ J₂ : GrothendieckTopology C}

/-- Restrict a stack in groupoids along `J₁ ≤ J₂` to the coarser topology.
The pseudofunctor and its fibers are untouched; only the descent condition is
weakened, so this loses information and cannot be inverted. -/
def ofLE (h : J₁ ≤ J₂) (F : StackInGroupoids C J₂) : StackInGroupoids C J₁ where
  presheaf := F.presheaf
  fiberIsGroupoid := F.fiberIsGroupoid
  isStack :=
    letI := F.isStack
    Pseudofunctor.IsStack.of_le h

@[simp]
theorem ofLE_presheaf (h : J₁ ≤ J₂) (F : StackInGroupoids C J₂) :
    (F.ofLE h).presheaf = F.presheaf :=
  rfl

/-- A covering family for a coarser topology is a covering family for a finer
one, with the same index type and the same arrows. -/
@[simps index obj hom]
def Cover.ofLE (h : J₁ ≤ J₂) {S : C} (U : Cover.{t} (J := J₁) S) :
    Cover.{t} (J := J₂) S where
  index := U.index
  obj := U.obj
  hom := U.hom
  mem := h _ U.mem

end StackInGroupoids

/-! ## Transport along equivalences -/

open scoped Pseudofunctor.StrongTrans in
/-- Transport a stack in groupoids along a strong transformation whose components are
equivalences of categories.  The stack condition transfers by
`CategoryTheory.Pseudofunctor.isStack_iff_of_isEquivalence`.  Each target fiber is a
groupoid because the inverse of the component equivalence reflects isomorphisms into a
groupoid. -/
def StackInGroupoids.ofEquivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (F : StackInGroupoids C J)
    (G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (α : F.presheaf ⟶ G)
    [∀ X, (α.app X).toFunctor.IsEquivalence] : StackInGroupoids C J where
  presheaf := G
  fiberIsGroupoid X := isGroupoid_of_reflects_iso (α.app X).toFunctor.inv
  isStack := (Pseudofunctor.isStack_iff_of_isEquivalence α J).1 F.isStack

end

end CategoryTheory
