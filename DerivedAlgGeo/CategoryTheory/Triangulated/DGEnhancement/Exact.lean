/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Triangle
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Basic

/-!
# Exact enhancements, as a refinement of the H⁰ presentation

`Enhancement` is an *underlying H⁰ presentation*: an equivalence `H⁰ A ≌ T` with
`T` an arbitrary category and no compatibility asked of the comparison.
Bondal--Kapranov and Lunts--Orlov mean something stronger by "enhancement": `T`
is triangulated and the comparison is *exact*. This file is that refinement.

## What the refinement carries, and what it does not prove

`Enhancement.Exact E` is **data supplied about `E`**, in two fields:

* `commShift`, a `Functor.CommShift ℤ` on `E.equiv.functor` -- without it
  `Functor.mapTriangle` does not exist and "the image of a triangle" is not even
  a well-formed phrase;
* `isTriangulated`, a `Functor.IsTriangulated` -- the comparison sends
  distinguished triangles of `H⁰ E.dgCat` to distinguished triangles of `T`.

Both are the ordinary Mathlib classes. Neither is a `Bool`, a flag, or a field
whose inhabitation is asserted rather than constructed: supplying
`Enhancement.Exact E` means supplying a `CommShift` structure and discharging
`Functor.IsTriangulated`'s proof obligation. **No instance of this structure is
produced here, and none is produced for a general `E` anywhere.** The one
inhabitant is `Cdg.enhancementExact` in
`Algebra/Homology/HomotopyCategory/DGEnhancement/Agreement.lean`, where both
fields come from theorems about the complexes model (`Cdg.h0FunctorCommShift`
and `Cdg.h0FunctorIsTriangulated`) rather than from a hypothesis.

The seam and exactness obligations themselves belong to `#854` and `#855`. This
file packages the comparison truthfully; it discharges nothing on their behalf.

## Why a carrier rather than two loose hypotheses

The two classes already travel together wherever exactness is needed:
`Enhancement.coneTriangleFunctor_obj_distinguished` in
`DGEnhancement/H0/ConeFunctor.lean` and the enhanced-kernel cone family in
`Triangulated/FourierMukai/KernelCone.lean` are two independent consumers
spelling out the same pair by hand. The named consumer of the bundle is
`Enhancement.Exact.coneTriangle_mem_distTriang`, in the first of those files.

Naming the pair is what lets a statement say "exact enhancement" and mean it,
which is the distinction `dg-enhancements-e15` will need: uniqueness of
enhancements is false over bare `Enhancement`, and is **not** asserted here or
anywhere else in this repository, in either strength.

Consumers that need only the shift comparison keep taking
`[e.equiv.functor.CommShift ℤ]` alone. Requiring the bundle where only half of it
is used would strengthen those hypotheses, which a placement change may not do.

## The fields are not instances

`Exact` is a structure, not a class, and neither field is registered as an
instance. As instances they would be tried against every `Functor.CommShift` and
`Functor.IsTriangulated` goal in the library and matched by unifying
`?E.equiv.functor` with an arbitrary functor, which is the shape of instance that
makes typeclass search expensive everywhere. `Exact.mapTriangle` below is the
bundled form consumers reach for; a proof that needs the raw classes writes
`letI := h.commShift` and `letI := h.isTriangulated`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u v' u'

namespace CategoryTheory

open Limits Pretriangulated

namespace Enhancement

variable {T : Type u'} [Category.{v'} T] [HasZeroObject T] [Preadditive T]
  [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- The compatibility data refining an H⁰ presentation of a triangulated `T` to
an **exact enhancement** of it: the comparison commutes with the shift, and it
carries distinguished triangles to distinguished triangles.

This is supplied data. Constructing a term means constructing a `CommShift`
structure and proving `Functor.IsTriangulated`; nothing in this repository
produces one for a general `E`. See the module docstring. -/
structure Exact (E : Enhancement.{v, u} T) where
  /-- The comparison commutes with the shift. Without this `mapTriangle` does
  not exist, so it is an instance-implicit field: the exactness field's own
  statement needs it in scope. -/
  [commShift : E.equiv.functor.CommShift ℤ]
  /-- The comparison is exact: it carries the dg cone triangles of
  `H⁰ E.dgCat` to distinguished triangles of `T`. -/
  isTriangulated : E.equiv.functor.IsTriangulated

namespace Exact

variable {E : Enhancement.{v, u} T}

/-- The triangle functor of an exact enhancement: the comparison's action on
triangles, using the `CommShift` the refinement carries.

`Functor.mapTriangle` needs a `CommShift` instance, and `Enhancement` supplies
none -- that is exactly the gap `Exact` fills. Bundling the functor here is what
lets the two statements below be ordinary propositions instead of propositions
under a `letI`. -/
noncomputable def mapTriangle (h : E.Exact) :
    Triangle (H0 E.dgCat) ⥤ Triangle T :=
  letI := h.commShift
  E.equiv.functor.mapTriangle

/-- The image of a distinguished triangle of `H⁰` under an exact enhancement is
distinguished. The content is `Functor.map_distinguished`; this is the name a
consumer holding the refinement reaches for without unbundling it. -/
theorem mapTriangle_obj_mem_distTriang (h : E.Exact) (S : Triangle (H0 E.dgCat))
    (hS : S ∈ distTriang (H0 E.dgCat)) :
    h.mapTriangle.obj S ∈ distTriang T := by
  letI := h.commShift
  letI := h.isTriangulated
  exact E.equiv.functor.map_distinguished S hS

/-- An exact enhancement *detects* distinguished triangles as well as preserving
them, because the comparison is an equivalence and so fully faithful.

This is the direction that makes the refinement worth bundling, and it is not
available from `Enhancement` alone. It is why "an ordinary equivalence
`H⁰ C ≌ T`" and "an exact enhancement of triangulated `T`" are different
statements rather than two spellings of one. -/
theorem mapTriangle_obj_mem_distTriang_iff (h : E.Exact) (S : Triangle (H0 E.dgCat)) :
    h.mapTriangle.obj S ∈ distTriang T ↔ S ∈ distTriang (H0 E.dgCat) := by
  letI := h.commShift
  letI := h.isTriangulated
  exact E.equiv.functor.map_distinguished_iff S

end Exact

end Enhancement

end CategoryTheory
