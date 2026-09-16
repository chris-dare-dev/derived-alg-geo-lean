/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Basic

/-!
# Dg enhancements: the underlying H⁰ presentation

`dg-enhancements-e6`. `Enhancement` is a pretriangulated dg category together
with an equivalence `H⁰ A ≌ T` for an ordinary category `T`. Structure carried
on `A` can be pushed across that equivalence and read off on `T`; this file
starts that transport with the zero object.

## `Enhancement` is an H⁰ presentation, not the literature's enhancement

Read the name as *underlying H⁰ presentation*: `T` is presented as the `H⁰` of a
dg category, and nothing more is claimed. Bondal--Kapranov and Lunts--Orlov take
`T` to be *triangulated* and require the comparison to be an *exact* equivalence.
Neither is a field here -- `T` is an arbitrary `Category`, and `equiv` is a plain
equivalence with no `CommShift` and no preservation of distinguished triangles.

The exact notion is the separate refinement `Enhancement.Exact` in
`DGEnhancement/Exact.lean`, which carries the two compatibilities as data. It is
data, not a theorem: nothing here or there proves that a presentation admits one.
For the only inhabitant, `Cdg.enhancement`, exactness *is* proved -- as an
equality of the two `Set (Triangle _)` (`Cdg.seam_distinguishedTriangles_eq`)
together with a `Functor.CommShift ℤ` on the seam (`Cdg.h0FunctorCommShift`), in
`Algebra/Homology/HomotopyCategory/DGEnhancement/`, and `Cdg.enhancementExact`
packages the two.

**The consequence to keep in view.** Nothing proved from this structure today is
in doubt. But a statement that quantifies over `Enhancement` is not the
literature's statement when read here. Uniqueness of enhancements
(`dg-enhancements-e15`) is the case that matters: over a bare equivalence of
underlying categories it is false, since two dg categories can have equivalent
`H⁰` as plain categories without being quasi-equivalent. When that lane is
written, the statement must quantify over `Enhancement.Exact`. No declaration in
this repository asserts uniqueness of enhancements in either form, and this file
does not authorize one.

## What is transported here, and what is not

`HasZeroObject (H0 C)` is intrinsic to the dg category and belongs to the
definition owner: it is `H0.hasZeroObject` in
`Algebra/Homology/DGCategory/Pretriangulated/H0/Basic.lean`. What is here is the
half that needs `T` and the equivalence -- `Enhancement.hasZeroObject` -- which
is the shape of every transport in this subtree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u v' u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits

set_option linter.checkUnivs false in
/-- A dg enhancement of an ordinary category `T`: a pretriangulated dg category
whose `H⁰` is equivalent to `T`.

`equiv` is a plain equivalence and `T` is a plain category, so this is the
*underlying H⁰ presentation* of `T`; the literature asks for a triangulated `T`
and an exact comparison, which is the refinement `Enhancement.Exact`. See the
module docstring for why the clause is carried outside the structure and what it
costs.

The dg category is bundled rather than a parameter because the interesting
statements quantify over enhancements of a fixed `T` -- uniqueness of
enhancements, in `dg-enhancements-e15`, is a statement about two inhabitants of
this type, and is not proved anywhere in this repository.

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
