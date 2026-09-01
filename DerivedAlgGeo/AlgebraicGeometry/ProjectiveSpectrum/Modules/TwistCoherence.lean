/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Finiteness

/-!
# Coherence of the integer twists

Quasi-coherence of `O(d)` is proved in
`DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Finiteness` by trivializing the twist on the
degree-one charts. Coherence follows the same route and for the same reason: coherence is local,
the degree-one charts cover when `A` is generated in degree one, and on such a chart `O(d)` is
isomorphic to the structure sheaf, which is coherent.

The restriction to degree-one charts is not an artifact. On a chart `D₊(f)` with `deg f = m` the
twist `O(d)` is trivial only when `m ∣ d`, so no comparison on charts of every positive degree
is available and `AffineComparisonData` for `intShift 𝒜 d` cannot be asked for.
-/

universe u

open CategoryTheory

open GradedModule

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- On a degree-one chart, an integer twist is isomorphic to the structure sheaf. -/
noncomputable def intShiftOverSelfIso (f : 𝒜 1) (d : ℤ) :
    (associatedSheaf 𝒜 (intShift 𝒜 d)).over
        (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange ≅
      (associatedSheaf 𝒜 𝒜).over
        (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange :=
  intShiftOverIso 𝒜 f.2 d (standardAway_degreeOne_opensRange_le 𝒜 f) ≪≫
    (SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝒜).ringCatSheaf
      (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange).mapIso (intShiftZeroIso 𝒜)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Every integer twist is coherent** as soon as degree-one elements generate `A` over `𝒜 0`.

This is the hypothesis quasi-coherence already takes, unchanged. -/
theorem intShift_isCoherent {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 (intShift 𝒜 d)) := by
  apply SheafOfModules.IsFinitePresentation.of_coversTop
    (associatedSheaf 𝒜 (intShift 𝒜 d))
    (fun i => (standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange)
    (degreeOneCharts_coversTop 𝒜 g hg)
  intro i
  exact SheafOfModules.IsFinitePresentation.of_iso.{u}
    (intShiftOverSelfIso 𝒜 (g i) d).symm
    (SheafOfModules.IsFinitePresentation.over
      (associatedSheaf_self_isCoherent 𝒜) _)

end AlgebraicGeometry.Proj
