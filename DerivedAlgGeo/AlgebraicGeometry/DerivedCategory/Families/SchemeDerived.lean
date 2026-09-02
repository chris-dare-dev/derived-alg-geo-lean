/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Basic
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ResidueFiber

/-!
# Derived categories attached to scheme fibers

The core specialization of Mathlib's generic derived category to `X.Modules`
lives in `AlgebraicGeometry.DerivedCategory.Basic`. This file evaluates those
categories on scheme base changes and their residue-field fibers and records
objectwise realizations of scheme-indexed triangulated families.

These are derived categories of all sheaves of modules.  No bounded coherent
or perfect subcategory is identified here.  Moreover, the construction is
objectwise: no derived pullback functor, base-change coherence, geometric
slicing witness, relative HN structure, openness, boundedness, moduli result,
or conclusion of Theorem 22.2 of arXiv:1902.08184v4 is asserted.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u w

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The concrete derived category attached to a scheme base change. -/
abbrev DerivedFiber (T : SchemeBaseChange S) :=
  SchemeDerivedCategory T.left

/-- The concrete bounded derived category attached to a scheme base change. -/
abbrev BoundedDerivedFiber (T : SchemeBaseChange S) :=
  SchemeBoundedDerivedCategory T.left

/-- The concrete derived category over the residue-field scheme at `x`. -/
abbrev ResidueDerivedFiber (T : SchemeBaseChange S) (x : T.left) :=
  (T.residue x).DerivedFiber

/-- The concrete bounded derived category over the residue-field scheme at
`x`. -/
abbrev ResidueBoundedDerivedFiber (T : SchemeBaseChange S) (x : T.left) :=
  (T.residue x).BoundedDerivedFiber

theorem residueDerivedFiber_eq (T : SchemeBaseChange S) (x : T.left) :
    T.ResidueDerivedFiber x =
      SchemeDerivedCategory (Spec (T.left.residueField x)) :=
  rfl

theorem residueBoundedDerivedFiber_eq (T : SchemeBaseChange S) (x : T.left) :
    T.ResidueBoundedDerivedFiber x =
      SchemeBoundedDerivedCategory (Spec (T.left.residueField x)) :=
  rfl

end SchemeBaseChange

namespace SchemeTriangulatedFiberFamily

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)

/-- Objectwise identification of a supplied triangulated family with the
concrete derived categories of module sheaves.  This records no compatibility
between the equivalences and the supplied pullback functors. -/
structure DerivedRealization where
  /-- Equivalence between each supplied fiber and the concrete derived
  category on its underlying scheme. -/
  fiberEquivalence (T : SchemeBaseChange S) : F.Fiber T ≌ T.DerivedFiber

/-- Objectwise identification of a supplied triangulated family with the
concrete bounded derived categories of module sheaves.  Derived pullback and
its coherence remain additional data. -/
structure BoundedDerivedRealization where
  /-- Equivalence between each supplied fiber and the concrete bounded
  derived category on its underlying scheme. -/
  fiberEquivalence (T : SchemeBaseChange S) :
    F.Fiber T ≌ T.BoundedDerivedFiber

namespace DerivedRealization

variable {F}

/-- A derived realization specializes to the actual residue-field derived
category at every point. -/
def residueFiberEquivalence (R : F.DerivedRealization)
    (T : SchemeBaseChange S) (x : T.left) :
    F.ResidueFiber T x ≌ T.ResidueDerivedFiber x :=
  R.fiberEquivalence (T.residue x)

end DerivedRealization

namespace BoundedDerivedRealization

variable {F}

/-- A bounded derived realization specializes to the actual bounded derived
category of the residue-field scheme at every point. -/
def residueFiberEquivalence (R : F.BoundedDerivedRealization)
    (T : SchemeBaseChange S) (x : T.left) :
    F.ResidueFiber T x ≌ T.ResidueBoundedDerivedFiber x :=
  R.fiberEquivalence (T.residue x)

end BoundedDerivedRealization

end SchemeTriangulatedFiberFamily

end


end AlgebraicGeometry.DerivedCategory.Families
