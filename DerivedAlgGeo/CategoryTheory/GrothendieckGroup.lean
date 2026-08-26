/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Presentation
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian

/-!
# Grothendieck groups by presentation

`GrothendieckPresentation` is generic in its generator and relation types — it
mentions no category at all — and `K₀Ab` instantiates it at the short exact
sequences of an abelian category.

Neither file uses anything triangulated, which is why they live here rather than
under `Triangulated/`.  The triangulated instantiation `K₀`, built on
distinguished triangles, stays at `Triangulated/GrothendieckGroup/` where it
belongs.
-/
