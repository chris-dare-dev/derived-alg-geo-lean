/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistCoherence
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistingSheaf
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic

/-!
# The twisting sheaf is invertible

`O(d)` on `Proj 𝒜` is a locally free rank-one sheaf as soon as degree-one elements generate `A`
over `𝒜 0`. This is the hypothesis quasi-coherence and coherence already take, unchanged.

## Why this file exists, and the route it fixes

`#584` asks for the twist `F(d) = F ⊗ O(d)` of an arbitrary module sheaf on `Proj`. The sheafified
tensor product in `Modules/Tensor/Basic.lean` is stated for a **locally free rank-one** factor — its
comparison maps are inverted by sheafification only there, and its associator needs the outer
factors invertible. So `F(d)` cannot be built at all until `O(d)` is known to be invertible, and
the issue left the route open between:

* proving invertibility first, then tensoring; or
* avoiding the tensor entirely, since `associatedSheaf 𝒜 (intShift 𝓜 d)` already *is* the twist
  of an associated sheaf.

**This file takes the first route, and the reason is that the second does not reach the
statement `#570` needs.** The graded-shift description covers associated sheaves only, while
`#570` surjects onto an *arbitrary* coherent `F`; identifying every coherent sheaf on `Proj` with
an associated sheaf is Serre's theorem, which is downstream rather than available. The graded
shift is kept as the computational special case — the Čech lane computes with it and needs no
tensor — and the comparison between the two descriptions is what deliverable 4 of `#584` asks for.

## Why it is short

Nothing here is new mathematics; the local triviality was built already, for a different
conclusion. `TwistCoherence.lean` needed exactly the same charts to prove `O(d)` coherent, so
`intShiftOverSelfIso` — the twist is isomorphic to the structure sheaf over a degree-one chart, at
either sign of `d` — is on hand. Invertibility is that isomorphism composed with
`associatedSheafSelfIso` and handed to `IsInvertible.of_trivializations`, over the cover
`degreeOneCharts_coversTop` already supplies.

## The degree-one hypothesis is not an artifact

`TwistCoherence.lean` records why, and the same applies here: on a chart `D₊(f)` with `deg f = m`,
`O(d)` is trivial only when `m ∣ d`. There is no trivialization on charts of arbitrary positive
degree to be had, so the generating family must be taken in degree one.
-/

universe u

open CategoryTheory

open GradedModule

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- On a degree-one chart, the twisting sheaf is isomorphic to the unit module.

The `Iso.refl` is `SheafOfModules.overUnitIso`, inlined rather than imported: the unit of a
slice and the slice of the unit are the same object, and naming it here would cost the whole
`CoherentSheaf.Abelian.Extensions` import for a `rfl`. -/
noncomputable def twistingSheafOverUnitIso (f : 𝒜 1) (d : ℤ) :
    SheafOfModules.unit
      ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.over
        (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange) ≅
      (show SheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf from
        twistingSheaf 𝒜 d).over
        (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange :=
  Iso.refl _ ≪≫
    ((SheafOfModules.overFunctor _ _).mapIso (associatedSheafSelfIso 𝒜)).symm ≪≫
      (intShiftOverSelfIso 𝒜 f d).symm

/-- **The twisting sheaf `O(d)` is invertible**, at either sign of `d`, as soon as degree-one
elements generate `A` over `𝒜 0`.

This is what makes `Modules/Tensor/Basic.lean` applicable to `O(d)`, and hence what lets `F(d)` be
defined for an arbitrary module sheaf `F`. The hypothesis is the one coherence already takes. -/
theorem twistingSheaf_isInvertible {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf from
        twistingSheaf 𝒜 d) := by
  apply SheafOfModules.IsInvertible.of_trivializations
    (fun i => (standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange)
    (degreeOneCharts_coversTop 𝒜 g hg)
  intro i
  exact twistingSheafOverUnitIso 𝒜 (g i) d

/-- **On a degree-one chart, the twist is the sheaf itself.**

`F(d) = F ⊗ O(d)` restricted to `D₊(f)` for `f` of degree one is just `F`
restricted there, because `O(d)` is trivial on that chart
(`twistingSheafOverUnitIso`) and tensoring with a trivialized factor does
nothing to the restriction (`tensorOverIsoOfTrivializationRight`).

`F` is **arbitrary** — not an associated sheaf, not coherent, not even
quasi-coherent. This is the passage `#585` needs: the per-chart sections that
`ChartExtension.lean` produces live on different sheaves, one per chart, and
this is what carries each of them into the single sheaf `F(d)`. -/
noncomputable def tensorTwistOverChartIso (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    (f : 𝒜 1) (d : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.tensorObj F (twistingSheaf 𝒜 d)).over
        (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange ≅
      F.over (standardAway 𝒜 (degreeOneStandardChart 𝒜 f)).opensRange :=
  AlgebraicGeometry.Scheme.Modules.tensorOverIsoOfTrivializationRight F
    (twistingSheaf 𝒜 d) _ (twistingSheafOverUnitIso 𝒜 f d)

end AlgebraicGeometry.Proj
