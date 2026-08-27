/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory.H0Triangle
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic

/-!
# The Grothendieck group of a pretriangulated dg category

`K₀` is defined once, at `GrothendieckPresentation`, and instantiated at the
distinguished triangles of a pretriangulated category
(`Triangulated/GrothendieckGroup/Basic.lean`). A pretriangulated dg category is
not itself pretriangulated — its `H⁰` is, by `H0.pretriangulated`
(`H0Triangle.lean`, `dg-enhancements-e6`). So the dg Grothendieck group needs no
new construction: it is the existing one at `H0 C`.

That is the whole content of this file, and it is the point. The dg layer has
carried `H0.pretriangulated` since e6 without any downstream declaration using
it; `K₀dg` is the first, and it is three lines because the tower was already
built to admit it.

## Why not a new presentation

A dg category has no distinguished triangles of its own — a dg cone is
functorial, and the triangulated structure appears only after passing to `H⁰`,
where the choice of cone stops mattering up to isomorphism. Writing a separate
`GrothendieckPresentation` on dg objects would either reproduce
`distinguishedTriangles C` (which is what `H0`'s instance already quotients by)
or quotient by something finer, which would not be the Grothendieck group of the
homotopy category. Neither is wanted.

## Main definitions

* `K₀dg` — the Grothendieck group of a pretriangulated dg category.
* `K₀dg.of` — the class of a dg object.
-/

noncomputable section

universe v u

namespace CategoryTheory.DGCategory

open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Pretriangulated

variable (C : Type u) [DGCategory.{v} C] [IsPretriangulated C]

/-- **The Grothendieck group of a pretriangulated dg category**: the
Grothendieck group of its homotopy category `H⁰`.

This is `K₀` at the `Pretriangulated (H0 C)` instance, not a new construction. -/
abbrev K₀dg : Type _ := K₀ (H0 C)

variable {C}

/-- The class of a dg object in `K₀dg`, through its image in `H⁰`. -/
def K₀dg.of (X : C) : K₀dg C :=
  K₀.of (H0 C) (show H0 C from X)

@[simp]
theorem K₀dg.of_eq (X : C) : K₀dg.of X = K₀.of (H0 C) (show H0 C from X) := rfl

/-- A distinguished triangle of `H⁰` gives the defining relation, inherited
from `K₀`. -/
theorem K₀dg.of_triangle (T : Pretriangulated.Triangle (H0 C))
    (hT : T ∈ distTriang (H0 C)) :
    K₀.of (H0 C) T.obj₂ = K₀.of (H0 C) T.obj₁ + K₀.of (H0 C) T.obj₃ :=
  K₀.of_triangle (H0 C) T hT

end CategoryTheory.DGCategory
