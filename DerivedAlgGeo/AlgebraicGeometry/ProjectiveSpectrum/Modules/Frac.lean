/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.BasicOpenLemmas

/-!
# The fraction `a / b`, at a point and as a section

Two definitions and the degree fact they need. `frac` is the degree-zero fraction at a point of
`D₊(b)`; `fracSection` is the same fraction as a section of the structure sheaf over an open inside
`D₊(b)`, which is well defined because the fraction is *fixed* — the `IsFraction` witness is the
open itself and restriction does not move it.

## Why they are named rather than written inline

As an anonymous `HomogeneousLocalization.mk` the denominator submonoid is a metavariable when the
term appears under a `•`, and `Submonoid.pow_mem _ hx n` will not elaborate. Naming the fraction
pins the submonoid. The section-level one has the matching problem one level up: written inline the
value elaborates at the `⋙ forget Ab` type of the unit's sections, where the scalar action does not
synthesize.

## Why this file sits so early

`#825`. `fracPow` and `fracPowSection` — the case `a = fⁿ`, `b = gⁿ` — were written first, in
`TwistBridge.lean` and `ChartUnitTwist.lean`, and the general `frac` and `fracSection` came later
in `FracSection.lean`, which imports both. So the general definitions sat *downstream* of their own
special cases, and the two were bridged by `rfl` lemmas instead of one being defined from the
other. Hoisting the general pair above the special ones is what lets the special ones be
definitions rather than duplicates.
-/

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜

/-- A degree-one element raised to `n` has degree `n`. -/
theorem pow_mem_deg {a : A} (ha : a ∈ 𝒜 1) (m : ℕ) : a ^ m ∈ 𝒜 m := by
  simpa using SetLike.pow_mem_graded m ha

/-- **The degree-zero fraction `a / b` at a point of `D₊(b)`**, for `a` and `b` of the same
degree. -/
def frac {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 b) :
    HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl :=
  HomogeneousLocalization.mk { deg := k, num := ⟨a, ha⟩, den := ⟨b, hb⟩, den_mem := hx }

/-- **`a / b` as a section of the structure sheaf over an open inside `D₊(b)`.**

Pointwise `frac`, which is a fixed fraction, so the `IsFraction` witness is the open itself and
restriction does not move it. -/
def fracSection {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U) :=
  ⟨fun x => frac 𝒜 ha hb (hU x.2),
   fun x => ⟨U, x.2, 𝟙 _, k, ⟨a, ha⟩, ⟨b, hb⟩, fun y => hU y.2, fun _ => rfl⟩⟩

end AlgebraicGeometry.Proj
