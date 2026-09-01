/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Frac
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistSection

/-!
# `fⁿ` on a degree-one chart is `(f / g)ⁿ`

The bridge between `#585`'s two halves. `ChartExtension.lean` clears a power of `f / g` on the
chart through `g`; `TwistSection.lean` multiplies by the global section `fⁿ` of `O(n)`. This file
says those are the same thing, so the halves meet with **no correction factor**.

## Why this comes before the glue, not after

The chart step produces, for each chart `gᵢ`, a section over `D₊(gᵢ)` obtained by clearing
`(f / gᵢ)ⁿ` — a *different* scalar on each chart. Those sections are not sections of any one sheaf,
so there is nothing to glue yet. Twisting is what makes them comparable: each becomes a section of
`F(n)`, and `F(n)` is one sheaf. So the bridge is a precondition for gluing rather than a
finishing step, which is the opposite of the order the obvious reading of `#585` suggests.

## The computation

`intShiftZeroLinearEquiv_apply_mk` fed the constant fraction `fⁿ / 1` at `d = n` gives
`d.toNat = n` and `(-d).toNat = 0`, hence `fⁿ · g⁰` over `1 · gⁿ`. Cleaning that to `fⁿ / gⁿ` is
`DegreeZeroLocalization.ext` and `simp`: the `deg` fields differ (`0 + n` against `n`) and it does
not matter, because the embedding into `LocalizedModule` reads only numerator and denominator.

`fⁿ / gⁿ` is `(HomogeneousLocalization.Away.isLocalizationElem hg hf) ^ n` — exactly the scalar
`exists_pow_smul_eq_res_chart` clears.

## The section level is a one-liner

Both `sectionOfMem` and the chart trivialization are defined pointwise, so
`intShiftSectionLinearEquivOn_sectionOfMem` is the fibre statement applied at `hU x.2` and nothing
else. The same thing happened in `#584`'s `chartModuleTwistSectionEquiv_sectionTwistMul`: in this
construction, lifting from fibres to sections is free, and the cost is always in the fraction
identity underneath.

## Scope

The scalar identity, at a localization and on sections. The glue — one `n` across a finite cover
of degree-one charts, a second exponent for the overlaps, and the assembly of the twisted local
sections into a global section of `F(N)` — is not here; it is
`Proj/Modules/Glue.lean`'s `exists_globalSection_twistBy`.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜] (S : Submonoid A)

/-- **The chart trivialization sends the global section `fⁿ` of `O(n)` to the fraction
`fⁿ / gⁿ`.**

`fⁿ / gⁿ` is `(f / g)ⁿ`, which is exactly the scalar the chart extension step clears — so the two
halves of `#585` meet with no correction factor. -/
theorem intShiftZeroLinearEquiv_constFraction {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hgS : g ∈ S) (n : ℕ) :
    DegreeZeroLocalization.intShiftZeroLinearEquiv 𝒜 hg (n : ℤ) hgS
        (DegreeZeroLocalization.mk
          { deg := 0
            num := ⟨f ^ n, mem_intShift_zero_of_mem 𝒜 n
              (by simpa using SetLike.pow_mem_graded n hf)⟩
            den := ⟨1, SetLike.one_mem_graded 𝒜⟩
            den_mem := S.one_mem }) =
      DegreeZeroLocalization.mk
        { deg := n
          num := ⟨f ^ n, (mem_intShift_zero_iff 𝒜 n (f ^ n)).mpr
            (by simpa using SetLike.pow_mem_graded n hf)⟩
          den := ⟨g ^ n, by simpa using SetLike.pow_mem_graded n hg⟩
          den_mem := S.pow_mem hgS n } := by
  rw [DegreeZeroLocalization.intShiftZeroLinearEquiv_apply_mk]
  apply DegreeZeroLocalization.ext
  simp [NumDenSameDeg.embedding]

section Sections

local notation3 "X" => ProjectiveSpectrum.top 𝒜

/-- **The bridge on sections**: over an open inside `D₊(g)`, trivializing the global section `fⁿ`
of `O(n)` gives the fraction `fⁿ / gⁿ` at every point. -/
theorem intShiftSectionLinearEquivOn_sectionOfMem {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) (n : ℕ) (x : U) :
    (intShiftSectionLinearEquivOn 𝒜 hg (n : ℤ) hU
        (sectionOfMem 𝒜 𝒜 U n (by simpa using SetLike.pow_mem_graded n hf))).1 x =
      DegreeZeroLocalization.mk
        { deg := n
          num := ⟨f ^ n, (mem_intShift_zero_iff 𝒜 n (f ^ n)).mpr
            (by simpa using SetLike.pow_mem_graded n hf)⟩
          den := ⟨g ^ n, by simpa using SetLike.pow_mem_graded n hg⟩
          den_mem := Submonoid.pow_mem _ (hU x.2) n } :=
  intShiftZeroLinearEquiv_constFraction 𝒜 _ hf hg (hU x.2) n

/-- The degree-zero fraction `fⁿ / gⁿ` at a point of `D₊(g)`.

`frac` at `a = fⁿ`, `b = gⁿ`, both of degree `n`. `#825` made this a definition rather than a
second `HomogeneousLocalization.mk` with a `rfl` lemma bridging the two. -/
noncomputable def fracPow {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (n : ℕ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 g) :
    HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl :=
  frac 𝒜 (pow_mem_deg 𝒜 hf n) (pow_mem_deg 𝒜 hg n) (basicOpen_le_basicOpen_pow 𝒜 g n hx)

/-- **Rescaling the section `gⁿ` of `O(n)` by `fⁿ/gⁿ` gives the section `fⁿ`.**

`(fⁿ/gⁿ) · (gⁿ/1) = fⁿ/1`, at every point of an open inside `D₊(g)`.

This is the identity that makes the per-chart extensions of `#585` glue, on the
route that never trivializes: taking the section of `F(n)` over `D₊(g)` to be
`twistBy gⁿ` applied to the chart extension, its restriction to `D₊(g) ⊓ D₊(f)`
is `twistBy gⁿ` of `(f/g)ⁿ • s`, and this says that is `twistBy fⁿ` of `s` —
the same object for every chart, so agreement is immediate and no transition
function appears. -/
theorem fracPow_smul_sectionOfMem {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (n : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) (x : U) :
    fracPow 𝒜 hf hg n (hU x.2) •
        (sectionOfMem 𝒜 𝒜 U n (by simpa using SetLike.pow_mem_graded n hg)).1 x =
      (sectionOfMem 𝒜 𝒜 U n (by simpa using SetLike.pow_mem_graded n hf)).1 x := by
  rw [sectionOfMem_apply, sectionOfMem_apply, fracPow, frac, DegreeZeroLocalization.mk_smul_mk]
  apply DegreeZeroLocalization.ext
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding, smul_eq_mul, mul_one]
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩

end Sections

end AlgebraicGeometry.Proj
