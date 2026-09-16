/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Basic
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Charge
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Cutoff
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.HNPolygon
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.HarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.PhaseGeometry
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.PhaseMonotone
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.SimpleCharge
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Slope
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.SlopeCutoff
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.SlopeThreshold
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Splitting
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Subobject
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Truncation
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Uniqueness
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak

/-!
# Stability functions on an abelian category

A stability function is an additive charge from the Grothendieck group of an
abelian category into a half-plane of `ℂ`, together with the phase order,
semistability and Harder--Narasimhan theory it determines. The subject needs an
abelian category and nothing more: no shift, no distinguished triangle, no
t-structure, no heart, and no scheme.

## The four owners

* **Definition owner** -- this subtree. `Basic.lean` defines `StabilityFunctionOn`
  and `WeakStabilityFunctionOn` over a `ClassDatum`; `HarderNarasimhan.lean` and
  `Weak/HarderNarasimhan.lean` own the filtrations; `Uniqueness/` owns the
  maximal-destabilizing and subobject-lattice arguments the filtrations rest on.
* **Neutral core** -- `Charge.lean`. `ClassDatum` and `IsPositive` quantify over
  an arbitrary object type and an arbitrary `AddCommGroup`, so they are upstream
  of the abelian theory as well as of the triangulated one.
* **Application adapters** -- `Triangulated/StabilityCondition/Weak/Foundation/HeartDatum.lean`
  instantiates `ClassDatum` at the heart of a t-structure, and the rest of
  `Triangulated/StabilityCondition/` reconstructs triangulated stability from
  it. `AlgebraicGeometry/Stability/Slope/` instantiates the weak slope theory at
  `Coh X`.
* **Comparison owner** -- `AlgebraicGeometry/Stability/Comparison.lean`, for the
  geometric theories; the weak/strong comparison is internal to this subtree.

## Weak is a child, and the dependency still runs upward

`Weak/` holds the variant in which the charge may vanish. As with
`MetricSpace/Pseudo/` in Mathlib, the directory is named for the canonical
concept and the weakened one is its adjective-named child, while the import
direction is the reverse: `Slope.lean` imports `Weak/Slope.lean`. That nesting
is not a defect and MO1.08 did not reverse it.

## Placement

This subtree was `Triangulated/StabilityCondition/Weak/Foundation/StabilityFunction/`
until MO1.08 (#1319), where an independently abelian subject was owned by the
triangulated theory it is a foundation for. No declaration was renamed by the
move: fully qualified names stay in `CategoryTheory.Triangulated`, which reads
oddly here and is accepted rather than repaired, per decision 1 of the MO1 owner
map in `docs/architecture/cutover-ledger.md`.
-/
