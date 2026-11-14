/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Covering the terminal object of an open-set site

`CategoryTheory.GrothendieckTopology.CoversTop` is the site-theoretic form of a covering family.
For the open-set site of a topological space, an open family whose supremum is `⊤` covers the
terminal object. On a prime spectrum, the separate lemma
`PrimeSpectrum.coversTop_basicOpen_of_span_eq_top` translates
the algebraic criterion that a family generates the unit ideal.

## Main definitions

This file introduces no carrier, class, or instance.

## Main results

* `TopCat.Opens.grothendieckTopology_coversTop` — a family of opens with `⨆ i, U i = ⊤` covers
  the terminal object.
* `PrimeSpectrum.coversTop_basicOpen_of_span_eq_top` — in
  `RingTheory/Spectrum/Prime/CoversTop.lean`, a unit-ideal generating family gives a cover of the
  prime spectrum by basic opens.

## Implementation notes

### Why this is its own file

`TopCat.Opens.grothendieckTopology_coversTop` is a statement about topological spaces with no
reference to coherence, sheaves of modules, or schemes. It lives with the open-set site so that
the lower-level topology and algebraic-geometry infrastructure can reach it without an import
cycle, which a home beside the coherent-sheaf descent results would create.

The general topological bridge stays independent of schemes. Its prime-spectrum specialization
lives with `PrimeSpectrum.basicOpen`, under `RingTheory/Spectrum/Prime/`, and assumes only a
commutative semiring; it is not part of the affine module comparison.

## References

Mathlib's `CategoryTheory.GrothendieckTopology.CoversTop` and `Opens.grothendieckTopology`.

## Tags

Grothendieck topology, open cover, terminal object, site of opens
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
