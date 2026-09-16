/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Analysis.Complex
import DerivedAlgGeo.Analysis.Convex

/-! # Analysis

Neutral analysis on the complex plane: the upper half-planes and their
argument geometry, and the Euclidean theory of finite polygonal paths.

Nothing below this root imports a category, a stability condition or a scheme.
The subject was added in MO1.13 (#1324) -- the conscious act rule 6 of
`scripts/check_layering.py` requires for a new top-level directory -- because
the Euclidean perimeter comparison at the heart of mass subadditivity has no
owner in the pinned Mathlib revision: it has no polygonal-chain length and no
perimeter of any kind. `Analysis` rather than `Geometry` is the name because
the convexity API these files consume, `convexHull`, is owned at that revision
by `Mathlib/Analysis/Convex/Hull.lean`.
-/
