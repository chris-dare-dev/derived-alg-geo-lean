/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Additive equivalence on morphisms of a fully faithful functor

An additive fully faithful functor identifies hom groups as additive groups.
The data-based form uses Mathlib's chosen inverse.

## Main definitions

* `CategoryTheory.Functor.mapAddEquiv` packages the additive map on morphisms
  as an equivalence when the functor is full and faithful.
* `CategoryTheory.Functor.homAddEquiv` takes explicit fully faithful data.

## Main results

Both equivalences have forward map `Functor.map`.

## Implementation notes

The data-based equivalence extends `FullyFaithful.homEquiv` and adds
`Functor.map_add`. The class-based version specializes it.

## References

Mathlib's `Preadditive/AdditiveFunctor.lean` and `Functor/FullyFaithful.lean`
at pin `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

additive functor, fully faithful functor
-/

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]

/-- An additive functor's fully faithful data induces an additive equivalence
on hom groups, with the supplied inverse from `FullyFaithful.homEquiv`. -/
noncomputable def homAddEquiv (hF : F.FullyFaithful) (X Y : C) :
    (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) :=
  { hF.homEquiv with map_add' := fun _ _ => F.map_add }

variable [F.Full] [F.Faithful]
/-- The map on hom groups of an additive fully faithful functor. -/
noncomputable def mapAddEquiv (X Y : C) :
    (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) :=
  F.homAddEquiv (Functor.FullyFaithful.ofFullyFaithful F) X Y

end CategoryTheory.Functor
