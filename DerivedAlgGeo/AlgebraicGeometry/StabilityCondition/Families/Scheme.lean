/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.Families.BaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families.Basic

/-!
# Scheme-facing stability-in-families interfaces

This file introduces the first geometric types in the families layer.  Base
changes of a scheme `S` are actual objects of Mathlib's category `Over S`, and
the three topological probes are instantiated on actual schemes with their
Zariski topology.

The categorical family remains supplied by a client: this file does not
construct derived categories or derived pullback functors.  It also does not
construct pre-stability conditions, geometric preimage/HN witnesses, a
Dedekind-scheme recognizer, openness or boundedness theorems, moduli spaces, or
the conclusion of Theorem 22.2 of arXiv:1902.08184v4.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u v w

/-- The category of scheme-valued base changes over a fixed scheme. -/
abbrev SchemeBaseChange (S : Scheme.{u}) := Over S

/-- An abstract triangulated category over every scheme base change of `S`.
The fibers and pullback functors are explicit client data. -/
abbrev SchemeTriangulatedFiberFamily (S : Scheme.{u}) :=
  TriangulatedFiberFamily (B := SchemeBaseChange S)

namespace SchemeTriangulatedFiberFamily

/-- The constant triangulated family on the category of schemes over `S`. -/
def constant (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] : SchemeTriangulatedFiberFamily S :=
  TriangulatedFiberFamily.constant (SchemeBaseChange S) C

end SchemeTriangulatedFiberFamily

/-- A charge probe on the underlying Zariski space of an actual scheme. -/
def ChargeProbe.ofScheme (X : Scheme.{u}) {A : Type v} (value : X → A) :
    ChargeProbe A where
  Point := X
  topology := inferInstance
  value := value

@[simp]
theorem ChargeProbe.ofScheme_isLocallyConstant_iff
    (X : Scheme.{u}) {A : Type v} (value : X → A) :
    (ChargeProbe.ofScheme X value).IsLocallyConstant ↔
      _root_.IsLocallyConstant value :=
  Iff.rfl

/-- An openness probe on the underlying Zariski space of an actual scheme. -/
def OpenLocusProbe.ofScheme (X : Scheme.{u}) (locus : Set X) :
    OpenLocusProbe where
  Point := X
  topology := inferInstance
  locus := locus

@[simp]
theorem OpenLocusProbe.ofScheme_isOpen_iff
    (X : Scheme.{u}) (locus : Set X) :
    (OpenLocusProbe.ofScheme X locus).IsOpen ↔ _root_.IsOpen locus :=
  Iff.rfl

/-- A generic-semistability probe on the underlying Zariski space of an
actual scheme. -/
def GenericSemistabilityProbe.ofScheme
    (X : Scheme.{u}) (genericPoint : X) (semistableLocus : Set X) :
    GenericSemistabilityProbe where
  Point := X
  topology := inferInstance
  genericPoint := genericPoint
  semistableLocus := semistableLocus

@[simp]
theorem GenericSemistabilityProbe.ofScheme_isGenericallyOpen_iff
    (X : Scheme.{u}) (genericPoint : X) (semistableLocus : Set X) :
    (GenericSemistabilityProbe.ofScheme X genericPoint
      semistableLocus).IsGenericallyOpen ↔
      genericPoint ∈ semistableLocus →
        ∃ U : Set X, _root_.IsOpen U ∧ genericPoint ∈ U ∧ U ⊆ semistableLocus :=
  Iff.rfl

end

end CategoryTheory.Triangulated.StabilityCondition.Families
