/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic

/-!
# Dg enhancements

`dg-enhancements-e6`. An *enhancement* of an ordinary category `T` is a
pretriangulated dg category together with an equivalence `H⁰ A ≌ T`. The point
of the notion is that structure carried on `A` can be pushed across the
equivalence and read off on `T`; this file starts that transport with the zero
object, and defines the structure that later transports are stated against.

## What is transported here, and what is not

`H⁰` of a pretriangulated dg category has a zero object: `IsPretriangulated`
asks for an object with `dgId Z = 0`, and in a preadditive category that is
exactly `IsZero Z`. So `HasZeroObject (H0 C)` is immediate, and it is the first
clause of a `Pretriangulated` structure.

The shift is not here. `IsPretriangulated.exists_shift` gives, for each `X` and
`n`, *some* `Y` with *some* witness — an existential, not a choice — and
`HasShift (H0 C) ℤ` needs a functor together with `shiftFunctorZero` and
`shiftFunctorAdd` coherence. Getting from one to the other is a construction
with real content, not a repackaging, and it is tracked separately rather than
smuggled in behind a `Nonempty.some`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u v' u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits

section Transport

variable {C : Type u} [DGCategory.{v} C]

/-- An object with zero dg identity is a zero object of `H⁰`. The ascription is
written `show H0 C from Z` rather than `(Z : H0 C)`: the latter reads the
category off `Z`'s own type and looks for `Category C`, which does not exist. -/
lemma H0.isZero_of_dgId_eq_zero {Z : C} (hZ : dgId Z = 0) :
    IsZero (show H0 C from Z) := by
  rw [IsZero.iff_id_eq_zero]
  show (QuotientAddGroup.mk (⟨dgId Z, dgId_cocycle Z⟩ : cocycles Z Z)) = 0
  rw [show (⟨dgId Z, dgId_cocycle Z⟩ : cocycles Z Z) = 0 from Subtype.ext hZ]
  exact QuotientAddGroup.mk_zero _

/-- `H⁰` of a pretriangulated dg category has a zero object. The first clause of
a `Pretriangulated` structure, and the only one this file transports. -/
instance H0.hasZeroObject [IsPretriangulated C] : HasZeroObject (H0 C) := by
  obtain ⟨Z, hZ⟩ := IsPretriangulated.exists_zero (C := C)
  exact (H0.isZero_of_dgId_eq_zero hZ).hasZeroObject

end Transport

set_option linter.checkUnivs false in
/-- A dg enhancement of an ordinary category `T`: a pretriangulated dg category
whose `H⁰` is equivalent to `T`.

The dg category is bundled rather than a parameter because the interesting
statements quantify over enhancements of a fixed `T` — uniqueness of
enhancements, in `dg-enhancements-e15`, is a statement about two inhabitants of
this type.

`u` and `v` occur only together because `DGCategory.{v}` fixes the universe of
the Hom-complexes' abelian groups while `u` fixes the objects, and the
structure's own universe is their `max`. That is what the encoding is, so the
`checkUnivs` linter is turned off here rather than the structure being
contorted to satisfy it. -/
structure Enhancement (T : Type u') [Category.{v'} T] where
  /-- The enhancing dg category. -/
  dgCat : Type u
  /-- Its dg structure. -/
  [isDGCategory : DGCategory.{v} dgCat]
  /-- It is pretriangulated, so its `H⁰` is where a triangulated structure can
  land. -/
  [isPretriangulated : IsPretriangulated dgCat]
  /-- The comparison with `T`. -/
  equiv : H0 dgCat ≌ T

namespace Enhancement

attribute [instance] isDGCategory isPretriangulated

variable {T : Type u'} [Category.{v'} T]

/-- An enhanced category has a zero object: `H⁰` of the enhancing dg category
has one, and the equivalence carries it across.

Mathlib has no `HasZeroObject` transport along an equivalence at the pin, so
this goes the long way round: the image is zero because its image under the
*inverse* is zero, and `IsZero.of_full_of_faithful_of_isZero` reflects that
back. -/
lemma hasZeroObject (E : Enhancement.{v, u} T) : HasZeroObject T := by
  obtain ⟨Z, hZ⟩ := IsPretriangulated.exists_zero (C := E.dgCat)
  refine IsZero.hasZeroObject (X := E.equiv.functor.obj (show H0 E.dgCat from Z)) ?_
  refine IsZero.of_full_of_faithful_of_isZero E.equiv.inverse _ ?_
  exact (E.equiv.unitIso.app _).isZero_iff.mp
    (H0.isZero_of_dgId_eq_zero (C := E.dgCat) hZ)

end Enhancement

end CategoryTheory
