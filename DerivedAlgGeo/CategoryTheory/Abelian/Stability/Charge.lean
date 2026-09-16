/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Analysis.Complex.HalfPlane
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Charges, and positivity relative to a class datum

A charge condition needs to know two things about a setting: which objects it
speaks about, and which abelian group carries their classes. `ClassDatum` makes
those the parameters, so the abelian and the ambient theories are one structure
at two data rather than two structures with the same fields.

Nothing here is categorical. `ClassDatum O G` quantifies over an arbitrary `O`
and an arbitrary `AddCommGroup G`; the half-planes are subsets of `ℂ`; and the
two structures carry a `G →+ ℂ` and a positivity proof. The instantiations live
with the settings they instantiate at -- `abelianDatum` beside `K₀Ab`,
`heartDatum` beside `K₀`.

## Placement

This is the **neutral core** of the MO1.08 owner map: the class datum and the
additive charge, which an abelian category is enough to use and which nothing
triangulated is needed to state. It has two independent consumers, which is
what earns it a file of its own rather than a block inside one of them --
`Abelian/Stability/Basic.lean` instantiates it at `abelianDatum`, and
`Triangulated/StabilityCondition/Weak/Foundation/HeartDatum.lean` instantiates
it at the heart of a t-structure.

It sat at the root of `CategoryTheory/` from #760 until 2026-09-02 -- the
review of the Mathlib-mesh restructure observed that this promoted
stability-specific support to a subject root it does not own -- and then below
`Triangulated/StabilityCondition/Weak/` until MO1.08 (#1319). What the second
move repaired is that the file was placed beside one of its two consumers, so
the other had to reach for it through the triangulated tree.

The five upper-half-plane facts (`semiClosedUpperHalfPlane`,
`closedUpperHalfPlane`, and their three lemmas) left this file in MO1.13
(#1324) and now live at `DerivedAlgGeo/Analysis/Complex/HalfPlane.lean`, which
this file imports. They had to move: the Euclidean core of the
mass-subadditivity proof states half-plane memberships, and that core is
required to be importable with no category theory and no stability. Their
declaration names and their `CategoryTheory` namespace are unchanged, because a
namespace change would rename declarations and the immutable review payloads
the `exe/RestateHistoricalNames.lean` bridge protects must keep resolving. They
remain an upstream candidate for `Mathlib/Analysis/Complex/UpperHalfPlane/`.
-/

noncomputable section

universe u v

open Complex Real

namespace CategoryTheory

/-- **What a positivity condition needs to know about a category.**

A charge condition speaks about *some* objects (the nonzero ones, or the nonzero
ones lying in a heart) and reads their class in *some* abelian group.  Those two
choices are the only thing that varies between the abelian-category theory and
the ambient/t-structure theory, so they are the parameters.

Making this a parameter rather than baking `K₀Ab` in is what stops the two
theories being two structures with the same fields: they are one structure at two
class data. -/
structure ClassDatum (O : Type*) (G : Type*) [AddCommGroup G] where
  /-- The objects the positivity condition speaks about. -/
  Relevant : O → Prop
  /-- The class of an object. -/
  cl : O → G

variable {O : Type*} {G : Type*} [AddCommGroup G]

/-- A charge is positive for `D` into `P` when every relevant object's class has
charge in `P`. -/
def IsPositive (D : ClassDatum O G) (P : Set ℂ) (Z : G →+ ℂ) : Prop :=
  ∀ E : O, D.Relevant E → Z (D.cl E) ∈ P

/-- **Strict positivity** — the half-plane that excludes `0`. -/
abbrev IsStabilityCharge (D : ClassDatum O G) (Z : G →+ ℂ) : Prop :=
  IsPositive D semiClosedUpperHalfPlane Z

/-- **Weak positivity** — the same with `0` allowed on the real axis. -/
abbrev IsWeakStabilityCharge (D : ClassDatum O G) (Z : G →+ ℂ) : Prop :=
  IsPositive D closedUpperHalfPlane Z

/-- **Strict implies weak**, once and for every class datum. -/
theorem IsStabilityCharge.weak {D : ClassDatum O G} {Z : G →+ ℂ}
    (h : IsStabilityCharge D Z) : IsWeakStabilityCharge D Z :=
  fun E hE ↦ semiClosedUpperHalfPlane_subset_closed (h E hE)

end CategoryTheory
