/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Category.TopCat.Opens.CoversTop
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Basic opens cover `Spec R`

The bridge from the algebraic side of quasi-compactness — a family with
`Ideal.span (Set.range g) = ⊤` — to the `CoversTop` hypothesis the site
machinery takes.

## Why it is here and not in `Topology/`

It was in `Topology/Category/TopCat/Opens/CoversTop.lean`, beside the pure-topology lemma it is
built from. That made a layer-0 `Topology` module import
`Mathlib.AlgebraicGeometry.Scheme`: a subject that must stay independent of
geometry reaching directly into it. `scripts/check_layering.py` did not catch it
because its `Mathlib.AlgebraicGeometry` check fired only for `CategoryTheory`,
so the subjects *below* `CategoryTheory` — the ones that should be most
restricted — were unchecked. That guard is widened in the same change.

The topology half stays where it was; only the half that genuinely mentions
`Spec` moved.
-/

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {I : Type v}

/-- **Basic opens whose defining elements generate the unit ideal cover `Spec R`.**

This is the bridge from the algebraic side of quasi-compactness — a finite family with
`Ideal.span (Set.range g) = ⊤` — to the `CoversTop` hypothesis that the site machinery takes. -/
lemma basicOpen_coversTop_of_span_eq_top (g : I → R)
    (hg : Ideal.span (Set.range g) = ⊤) :
    (_root_.Opens.grothendieckTopology (Spec R)).CoversTop
      (fun i => PrimeSpectrum.basicOpen (g i)) :=
  TopCat.Opens.grothendieckTopology_coversTop _
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hg)

end AlgebraicGeometry
