/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Category.TopCat.Opens.CoversTop
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Covering the prime spectrum by basic opens

The Zariski-open family `D(g i)` covers `Spec R` exactly when the elements `g i` generate the
unit ideal. This translates the algebraic criterion for a cover into `CoversTop`, used by
Grothendieck-topology arguments.
-/

universe u v

open CategoryTheory TopologicalSpace

namespace PrimeSpectrum

/-- Basic opens defined by a family generating the unit ideal cover the prime spectrum.

The algebraic criterion `Ideal.span (Set.range g) = ⊤` is equivalent to the opens having supremum
`⊤`; a topological open cover then gives a covering family on the open-set site. -/
lemma basicOpen_coversTop_of_span_eq_top {R : Type u} [CommSemiring R] {I : Type v}
    (g : I → R) (hg : Ideal.span (Set.range g) = ⊤) :
    (_root_.Opens.grothendieckTopology (TopCat.of (PrimeSpectrum R))).CoversTop
      (fun i => PrimeSpectrum.basicOpen (g i)) :=
  TopCat.Opens.grothendieckTopology_coversTop _
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hg)

end PrimeSpectrum
