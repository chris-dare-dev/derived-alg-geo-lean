/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Exactness
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Epimorphisms of module sheaves, from local preimages

`epi_of_pointwise_preimages` is the criterion the rest of this repository reaches for whenever a
map of module sheaves has to be shown surjective: it is enough that every section, near every
point, has a preimage on some smaller open.

## What it adds, and what it does not

**Most of this was already in the tree.** `SheafOfModules.epi_of_isLocallySurjective`
(`Modules/Affine/Exactness.lean`) takes `Presheaf.IsLocallySurjective J` for a map of sheaves of
modules over an arbitrary site and returns `Epi`, and its docstring already names Serre's
surjection as the intended use. This lemma does **not** reprove that; it delegates to it.

What is added is the entry point: on `Opens X`, `Presheaf.IsLocallySurjective` is exactly the
pointwise statement, because `Opens.mem_grothendieckTopology` is `rfl` — so a caller who has local
preimages at points, which is what a chart-by-chart argument actually produces, can hand them over
directly. That step is `TopCat.Presheaf.isLocallySurjective_iff`, and it is the whole of the proof
below.

`Divisors/Effective.lean` runs the entire chain inline for one specific quotient map, and
hand-rolls the faithfulness of the forgetful functor while doing so — Mathlib's
`instance : (toSheaf.{v} R).Faithful` already provides it. That file is left alone here; folding it
onto this lemma is a separate cleanup.

## What it is *not*

There is no covering family and no `GrothendieckTopology.over` anywhere. A chart-by-chart argument
does not need `isLocallySurjective_of_coversTop`: the charts enter when the caller *chooses* which
open to work inside, at a point it has already been handed, and the hypothesis below is stated so
that choice is all the caller has to make. That is why the criterion is pointwise rather than
indexed by a cover.

`epi_of_isLocallySurjective`'s docstring anticipates the other route — combining it with
`isLocallySurjective_of_coversTop` to "check a map of module sheaves is an epimorphism chart by
chart". That route works, and it is not the shortest one: assembling the covering family is
avoidable, and this lemma is what avoids it.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **A map of module sheaves with local preimages is an epimorphism.**

If every section `t` of `G` over every open `U`, and every point `x ∈ U`, admits an open
`x ∈ V ≤ U` and a section of `F` over `V` mapping to `t|_V`, then `φ` is epi.

The hypothesis is deliberately pointwise. A caller arguing chart by chart is handed the point
first and picks the chart containing it, so no covering family has to be assembled and no
`GrothendieckTopology.over` appears. -/
theorem epi_of_pointwise_preimages {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ (U : X.Opens) (t : Γ(G, U)) (x : X), x ∈ U →
      ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ ∃ s : Γ(F, V),
        Scheme.Modules.Hom.app φ V s = G.presheaf.map (homOfLE hV).op t) :
    Epi φ := by
  refine SheafOfModules.epi_of_isLocallySurjective φ ?_
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    obtain ⟨V, hV, hxV, s, hs⟩ := h U t x hx
    exact ⟨V, hV, ⟨s, hs⟩, hxV⟩
  exact hls

end AlgebraicGeometry.Scheme.Modules
