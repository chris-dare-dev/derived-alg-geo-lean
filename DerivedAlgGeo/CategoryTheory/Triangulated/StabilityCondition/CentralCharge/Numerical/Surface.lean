/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compressed surface charge coordinates

This module owns the three real coordinates and the real and imaginary parts
of the `(s,t)` surface charge.  It contains no wall equation or geometric
realization.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

/-- A compressed numerical surface class `(r, c, d)`. -/
abbrev NumClass : Type := ℝ × ℝ × ℝ

namespace NumClass

/-- The rank coordinate. -/
def rk (v : NumClass) : ℝ := v.1

/-- The degree coordinate. -/
def deg (v : NumClass) : ℝ := v.2.1

/-- The integrated second Chern-character coordinate. -/
def ch2 (v : NumClass) : ℝ := v.2.2

end NumClass

open NumClass

/-- The real part of the twisted surface charge at `(s,t)`. -/
noncomputable def reZ (s t : ℝ) (v : NumClass) : ℝ :=
  -v.ch2 + s * v.deg - (s ^ 2 / 2) * v.rk + (t ^ 2 / 2) * v.rk

/-- The imaginary part of the twisted surface charge at `(s,t)`. -/
def imZ (s t : ℝ) (v : NumClass) : ℝ := t * (v.deg - s * v.rk)


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
