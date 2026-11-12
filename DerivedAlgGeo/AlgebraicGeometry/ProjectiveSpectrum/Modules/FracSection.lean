/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistApp
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Frac
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.BasicOpenLemmas

/-!
# Degree-zero fractions with an arbitrary numerator, and the twist comparison they give

`TwistBridge.lean` and `ChartUnitTwist.lean` carry the fraction `fⁿ / gⁿ` for `f` and `g` of
degree one. The gluing in the section-extension lemma `exists_globalSection_twistBy` needs the same
statements for an arbitrary pair of homogeneous elements of the same degree --
`fᵐ gᵢⁿ / gᵢ^{n+m}` appears the moment the extension exponent and the agreement exponent are
allowed to differ, and no power of a single element has that shape.

## Main definitions

This file introduces no new definitions; `frac` and `fracSection` are in `Frac.lean`.

## Main results

* `AlgebraicGeometry.Proj.pow_mem_smul`, `AlgebraicGeometry.Proj.pow_mem_mul`: a power lands in
  the degree its exponent multiplies, in the two spellings the glue compares.
* `AlgebraicGeometry.Proj.frac_eq`, `AlgebraicGeometry.Proj.fracSection_eq`: two fractions with the
  same value are equal, whatever degrees they are written in.
* `AlgebraicGeometry.Proj.frac_pow`, `AlgebraicGeometry.Proj.fracSection_mul`: powers and products
  of fractions.
* `AlgebraicGeometry.Proj.fracSection_mul_fracSection_symm`: `a / b` and `b / a` are inverse.
* `AlgebraicGeometry.Proj.frac_smul_sectionOfMem`,
  `AlgebraicGeometry.Proj.fracSection_smul_sectionOfMem`: rescaling the section `b` of `O(k)` by
  `a / b` gives the section `a`.
* `AlgebraicGeometry.Proj.twistBy_app_eq_smul'`: over an open inside `D₊(b)`, twisting a section by
  `a` is twisting it by `b` and scaling by `a / b`.

## Notation

`X` is local notation for the underlying space `ProjectiveSpectrum.top 𝒜`.

## Implementation notes

### The fractions and the comparison

`frac` is `a / b` at a point of `D₊(b)`, for `a b ∈ 𝒜 k`; `fracSection` is the section of the
structure sheaf it defines over any open inside `D₊(b)`. `fracPow` and `fracPowSection` are the
special case `a = fⁿ`, `b = gⁿ`, defined from them, so nothing has to be transported between the
two spellings.

`twistBy_app_eq_smul'` is the comparison the glue consumes: over an open inside `D₊(b)`, twisting a
section by `a` is twisting it by `b` and scaling by `a / b`. Its case `a = fⁿ`, `b = gⁿ` is the
degree-one comparison.

### Why this is not just a generalisation for its own sake

The two exponents the section-extension lemma carries are independent: `n` extends a section
across each chart, `m` forces agreement on the pairwise overlaps, and the section that finally
glues is `twistBy (fᵐ gᵢⁿ)` of the chart extension. Comparing two such across an overlap needs
`a / b` with `a = fᵐ gⱼⁿ` and `b = gᵢ^{n+m}`, which is a genuine two-element fraction.

### Scope

Fractions and the twist comparison. No chart, no cover, no gluing.

## References

Mathlib's `SetLike.pow_mem_graded` and `Localization.r_iff_exists`, and
`AlgebraicGeometry.Scheme.Modules.smul_tmulSection`.

## Tags

projective spectrum, homogeneous localization, twisting sheaf, fraction
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜

/-- **A power lands in the degree its exponent multiplies.**

`SetLike.pow_mem_graded` states the degree as `d • e`; the gluing meets it as `e • d`, because the
numerator of `HomogeneousLocalization.Away.isLocalizationElem hg hf` is a power of `f` sitting in
the degree that `g`'s exponent produces. -/
theorem pow_mem_smul {a : A} {e : ℕ} (ha : a ∈ 𝒜 e) (d : ℕ) : a ^ d ∈ 𝒜 (e • d) := by
  simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d ha

/-- **The same, with the degree written as a product.**

`pow_mem_smul` is the spelling the localization elements produce; this is the spelling a twist
degree is stated in, and the glue needs both because it compares one against the other. The
degree-one case is `Frac.pow_mem_deg`. -/
theorem pow_mem_mul {a : A} {e : ℕ} (ha : a ∈ 𝒜 e) (d : ℕ) : a ^ d ∈ 𝒜 (e * d) := by
  simpa [smul_eq_mul] using pow_mem_smul 𝒜 ha d

/-- **Two fractions with the same value are the same element**, whatever degrees they are written
in.

The workhorse for the gluing's bookkeeping: the exponents that reach the glue are built by different
routes -- `(f ^ d) ^ n` from a chart's distinguished element, `f ^ (d * n)` from a twist -- and this
identifies them without transporting a degree. -/
theorem frac_eq {a b a' b' : A} {k k' : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    (ha' : a' ∈ 𝒜 k') (hb' : b' ∈ 𝒜 k') {x : ProjectiveSpectrum 𝒜}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 b) (hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒜 b')
    (h : a * b' = a' * b) : frac 𝒜 ha hb hx = frac 𝒜 ha' hb' hx' := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simpa [mul_comm] using h⟩

/-- **The same, on sections.** -/
theorem fracSection_eq {a b a' b' : A} {k k' : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    (ha' : a' ∈ 𝒜 k') (hb' : b' ∈ 𝒜 k') {U : Opens X}
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) (hU' : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b')
    (h : a * b' = a' * b) : fracSection 𝒜 ha hb hU = fracSection 𝒜 ha' hb' hU' :=
  Subtype.ext (funext fun x => frac_eq 𝒜 ha hb ha' hb' (hU x.2) (hU' x.2) h)

/-- **A power of a fraction is the fraction of the powers.** -/
theorem frac_pow {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k) (n : ℕ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 b)
    (hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒜 (b ^ n)) :
    frac 𝒜 ha hb hx ^ n = frac 𝒜 (pow_mem_smul 𝒜 ha n) (pow_mem_smul 𝒜 hb n) hx' := by
  apply HomogeneousLocalization.val_injective
  simp [frac, HomogeneousLocalization.val_pow, Localization.mk_pow]

/-- **Fractions multiply componentwise.** -/
theorem fracSection_mul {a b a' b' : A} {k k' : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    (ha' : a' ∈ 𝒜 k') (hb' : b' ∈ 𝒜 k') {U : Opens X}
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) (hU' : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b')
    (hUU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 (b * b')) :
    fracSection 𝒜 ha hb hU * fracSection 𝒜 ha' hb' hU'
      = fracSection 𝒜 (SetLike.mul_mem_graded ha ha') (SetLike.mul_mem_graded hb hb') hUU :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **`a / b` and `b / a` are inverse to each other**, over an open inside both `D₊(a)` and
`D₊(b)`.

Serre's global generation inverts the chart scalar `(f / gᵉ)ⁿ` on `D₊(g) ⊓ D₊(f)`: the extension
lemma produces `(f / gᵉ)ⁿ • u` as a restriction of a global section, and this is what recovers
`u` itself as a combination of the chart's generators. The product is `fracSection_mul`, and
`(a b) / (b a) = 1 / 1` is one `Localization.r_iff_exists` with witness `1`. -/
theorem fracSection_mul_fracSection_symm {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {U : Opens X} (hUb : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b)
    (hUa : U ≤ ProjectiveSpectrum.basicOpen 𝒜 a) :
    fracSection 𝒜 ha hb hUb * fracSection 𝒜 hb ha hUa = 1 := by
  rw [fracSection_mul 𝒜 ha hb hb ha hUb hUa (le_basicOpen_mul 𝒜 hUb hUa)]
  refine Subtype.ext (funext fun x => ?_)
  show frac 𝒜 _ _ _ = 1
  apply HomogeneousLocalization.val_injective
  rw [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Rescaling the section `b` of `O(k)` by `a / b` gives the section `a`**, at every point of an
open inside `D₊(b)`.

The general form of `fracPow_smul_sectionOfMem`, and the identity that makes two chart extensions
with *different* exponents comparable. -/
theorem frac_smul_sectionOfMem {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) (x : U) :
    frac 𝒜 ha hb (hU x.2) • (sectionOfMem 𝒜 𝒜 U k hb).1 x
      = (sectionOfMem 𝒜 𝒜 U k ha).1 x := by
  rw [sectionOfMem_apply, sectionOfMem_apply, frac, DegreeZeroLocalization.mk_smul_mk]
  apply DegreeZeroLocalization.ext
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding, smul_eq_mul, mul_one]
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩

/-- **The same on sections rather than at a point.** -/
theorem fracSection_smul_sectionOfMem {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) :
    fracSection 𝒜 ha hb hU • sectionOfMem 𝒜 𝒜 U k hb = sectionOfMem 𝒜 𝒜 U k ha := by
  apply section_ext
  funext x
  exact frac_smul_sectionOfMem 𝒜 ha hb hU x

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **The overlap comparison for two homogeneous elements of the same degree.**

Over an open inside `D₊(b)`, twisting a section by `a` is twisting it by `b` and scaling by
`a / b`.

The scalar is ascribed at `Γ(Proj 𝒜, U)`: written bare it elaborates at the structure sheaf's own
section type, where the action on the twist's sections does not synthesize. -/
theorem twistBy_app_eq_smul' {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    (F : (Proj 𝒜).Modules) {U : Opens X}
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) (t : Γ(F, U)) :
    ((twistBy 𝒜 k ha F).val.app (op U)).hom t
      = (show Γ(Proj 𝒜, U) from fracSection 𝒜 ha hb hU) •
        ((twistBy 𝒜 k hb F).val.app (op U)).hom t := by
  rw [twistBy_app, twistBy_app]
  have h1 := Scheme.Modules.smul_tmulSection F (twistingSheaf 𝒜 (k : ℤ)) (op U)
    (show Γ(Proj 𝒜, U) from fracSection 𝒜 ha hb hU) t (sectionOfMem 𝒜 𝒜 U k hb)
  have h2 := fracSection_smul_sectionOfMem 𝒜 ha hb hU
  exact (h1.trans (congrArg
    (Scheme.Modules.tmulSection F (twistingSheaf 𝒜 (k : ℤ)) (op U) t) h2)).symm

end AlgebraicGeometry.Proj
