/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Covering the terminal object of an open-set site

`GrothendieckTopology.CoversTop` is the hypothesis every local-to-global statement on a site
takes. On the open-set site of a topological space it is implied by the far more familiar
condition that the family's supremum is `⊤`, and on `Spec R` that condition is in turn implied
by the purely algebraic one that the defining elements generate the unit ideal. This file
supplies both bridges.

## Main results

* `TopCat.Opens.grothendieckTopology_coversTop` — a family of opens with `⨆ i, U i = ⊤` covers
  the terminal object.
The `Spec R` companion, `AlgebraicGeometry.basicOpen_coversTop_of_span_eq_top`, lives in
`AlgebraicGeometry/Spec/CoversTop.lean`. It used to live here, which made a `Topology` module
import `Mathlib.AlgebraicGeometry.Scheme` — a layer-0 subject reaching into geometry.

## Why this is its own file

`grothendieckTopology_coversTop` previously lived in
`DerivedAlgGeo/AlgebraicGeometry/Modules/Coherent/Descent/Locality.lean`. It is a statement about
topological spaces with no reference to coherence, sheaves of modules, or schemes, and its position
there made it unreachable from the lower-level topology and algebraic-geometry infrastructure
without creating an import cycle.

That was a live constraint rather than an aesthetic one — the remaining half of the affine
comparison theorem (issue #46) needs `basicOpen_coversTop_of_span_eq_top` in
`AlgebraicGeometry/Modules/Coherent/Affine/Comparison.lean`, which is exactly where the old
placement blocked it. Moving the lemma into the topology domain keeps the dependency direction
explicit.

## Where the second one is used

Quasi-compactness of `Spec R` produces a *finite* subfamily of basic opens covering it, and
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` turns that into `Ideal.span (Set.range g) = ⊤`. So the
shape a local-to-global argument actually has in hand is the algebraic condition, and
`basicOpen_coversTop_of_span_eq_top` is what converts it back into something the site machinery
(`SheafOfModules.IsFinitePresentation.of_coversTop`, `QuasicoherentData.coversTop`) accepts.

These declarations are maintained by DerivedAlgGeo. Their Mathlib-style namespaces express the
mathematical owner of the API and ease replacement by equivalent upstream declarations; they
do not imply any commitment to submit or merge them into Mathlib.
-/

universe u v

open CategoryTheory TopologicalSpace

namespace TopCat.Opens

variable {X : TopCat.{u}} {I : Type v}

/-- A family of open sets whose supremum is `⊤` covers the terminal object of the open-set
site. -/
lemma grothendieckTopology_coversTop
    (U : I → TopologicalSpace.Opens X) (hU : ⨆ i, U i = ⊤) :
    (_root_.Opens.grothendieckTopology X).CoversTop U := by
  intro V x hxV
  have hxTop : x ∈ (⊤ : TopologicalSpace.Opens X) := by simp
  rw [← hU, TopologicalSpace.Opens.mem_iSup] at hxTop
  obtain ⟨i, hxi⟩ := hxTop
  exact ⟨U i ⊓ V, homOfLE inf_le_right, ⟨i, ⟨homOfLE inf_le_left⟩⟩, hxi, hxV⟩

end TopCat.Opens
