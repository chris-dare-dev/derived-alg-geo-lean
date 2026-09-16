/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic

/-!
# The zero object of `H⁰`

`dg-enhancements-e6`. The first clause of a `Pretriangulated` structure on `H⁰`
of a pretriangulated dg category, stated before any external category is chosen.

`IsPretriangulated` asks for an object with `dgId Z = 0`, and in a preadditive
category that is exactly `IsZero Z`. So `HasZeroObject (H0 C)` is immediate.

## Why this is here and not with the enhancement

Nothing below mentions an ordinary category, an equivalence, or a triangulated
target: the statements are about `H⁰ C` for a pretriangulated dg category `C`
alone. Under the owner map of `docs/architecture/cutover-ledger.md` row 15 that
makes `Algebra/Homology/DGCategory/` their definition owner, and
`CategoryTheory/Triangulated/DGEnhancement/Basic.lean` -- which consumes
`H0.hasZeroObject` to give an enhanced category a zero object -- their consumer.
The dependency runs one way, and the intrinsic side imports no enhancement
module.

## The shift is not here

`IsPretriangulated.exists_shift` gives, for each `X` and `n`, *some* `Y` with
*some* witness -- an existential, not a choice -- and `HasShift (H0 C) ℤ` needs a
functor together with `shiftFunctorZero` and `shiftFunctorAdd` coherence. Getting
from one to the other is a construction with real content, not a repackaging; it
is `H0/Shift.lean`, and it is not smuggled in behind a `Nonempty.some`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits

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

end CategoryTheory
