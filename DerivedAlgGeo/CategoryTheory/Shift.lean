/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Shift.CommShift
import DerivedAlgGeo.CategoryTheory.Shift.FunctorCategory

/-! # Shifts

Extensions of Mathlib's `CategoryTheory/Shift/`: the pointwise shift a functor
category inherits from its target, and the commutation of the evaluation
functors with it.  A two-variable `CommShift₂` can be projected explicitly
to either functor-valued `CommShift`, with evaluation-agreement theorems and no
global projection instances.
-/
