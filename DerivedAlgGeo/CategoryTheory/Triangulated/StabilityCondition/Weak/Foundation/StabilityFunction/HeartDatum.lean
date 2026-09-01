/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# The class datum of a heart

`ClassDatum` (`Basic.lean`) is parameterised by the only two things that vary
between the abelian and the ambient theory of a charge: *which objects the
positivity condition speaks about*, and *which group carries their classes*.
Its docstring says so — "the abelian and ambient theories are two
instantiations of it" — but `Basic.lean` supplies only the abelian one,
`abelianDatum`. This file supplies the ambient one.

`heartDatum t` reads: the relevant objects are the nonzero objects of
`t.heart`, and their classes live in the ambient `K₀ C`. With it,
`StabilityFunctionOn` and `WeakStabilityFunctionOn` cover the §14 heart
theory, which previously carried its own pair of structures with the two
half-planes written out by hand.

## The typeclass cost is nil

`K₀` is defined for a `Pretriangulated` category (`GrothendieckGroup/Basic.lean`),
so nothing here needs `IsTriangulated`. That matters: #760 recorded the open
question that deriving the ambient theory through `K₀Ab.toAmbient` *would*
require `IsTriangulated` in `Weak/Basic/Definitions.lean`, a file that uses it
zero times, and so would strictly weaken the base of the tree. Instantiating
`ClassDatum` a second time needs neither `toAmbient` nor `IsTriangulated`, so
the question does not arise rather than being answered.

## Main definitions

* `heartDatum` — the ambient class datum of a t-structure heart.
-/

noncomputable section

universe v u

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The class datum of the heart of a t-structure**: the relevant objects
are the nonzero objects of `t.heart`, and the class of an object is its class
in the ambient `K₀ C`.

This is the ambient counterpart of `abelianDatum`, and the second
instantiation of `ClassDatum` that `Basic.lean` was written to admit. -/
def heartDatum (t : TStructure C) : ClassDatum C (K₀ C) where
  Relevant E := t.heart E ∧ ¬IsZero E
  cl := K₀.of C

@[simp]
theorem heartDatum_cl (t : TStructure C) (E : C) :
    (heartDatum t).cl E = K₀.of C E := rfl

@[simp]
theorem heartDatum_relevant (t : TStructure C) (E : C) :
    (heartDatum t).Relevant E ↔ (t.heart E ∧ ¬IsZero E) := Iff.rfl

end CategoryTheory.Triangulated
