/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistApp
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.Frac
import DerivedAlgGeo.AlgebraicGeometry.Proj.BasicOpenLemmas

/-!
# Degree-zero fractions with an arbitrary numerator, and the twist comparison they give

`TwistBridge.lean` and `TwistApp.lean` carry the fraction `fⁿ / gⁿ` for `f` and `g` of degree one.
`#585`'s glue needs the same statements for an arbitrary pair of homogeneous elements of the same
degree -- `fᵐ gᵢⁿ / gᵢ^{n+m}` appears the moment the extension exponent and the agreement exponent
are allowed to differ, and no power of a single element has that shape.

## What is here

`frac` is `a / b` at a point of `D₊(b)`, for `a b ∈ 𝒜 k`; `fracSection` is the section of the
structure sheaf it defines over any open inside `D₊(b)`. `fracPow` and `fracPowSection` are the
special case `a = fⁿ`, `b = gⁿ`, and the two `..._eq_fracPow...` lemmas record that -- by `rfl`,
so nothing has to be transported between the two spellings.

`twistBy_app_eq_smul'` is the comparison the glue consumes: over an open inside `D₊(b)`, twisting a
section by `a` is twisting it by `b` and scaling by `a / b`. The degree-one case was its
`a = fⁿ`, `b = gⁿ` case.

## Why this is not just a generalisation for its own sake

The two exponents `#585` carries are independent: `n` extends a section across each chart, `m`
forces agreement on the pairwise overlaps, and the section that finally glues is
`twistBy (fᵐ gᵢⁿ)` of the chart extension. Comparing two such across an overlap needs `a / b` with
`a = fᵐ gⱼⁿ` and `b = gᵢ^{n+m}`, which is a genuine two-element fraction.

## Scope

Fractions and the twist comparison. No chart, no cover, no gluing.
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

`SetLike.pow_mem_graded` states the degree as `d • e`; `#585` meets it as `e • d`, because the
numerator of `HomogeneousLocalization.Away.isLocalizationElem hg hf` is a power of `f` sitting in
the degree that `g`'s exponent produces. -/
theorem pow_mem_smul {a : A} {e : ℕ} (ha : a ∈ 𝒜 e) (d : ℕ) : a ^ d ∈ 𝒜 (e • d) := by
  simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d ha

/-- **The same, with the degree written as a product.**

`pow_mem_smul` is the spelling the localization elements produce; this is the spelling a twist
degree is stated in, and `#823` needs both because the glue compares one against the other. The
degree-one case is `Frac.pow_mem_deg`. -/
theorem pow_mem_mul {a : A} {e : ℕ} (ha : a ∈ 𝒜 e) (d : ℕ) : a ^ d ∈ 𝒜 (e * d) := by
  simpa [smul_eq_mul] using pow_mem_smul 𝒜 ha d

/-- **Two fractions with the same value are the same element**, whatever degrees they are written
in.

The workhorse for `#585`'s bookkeeping: the exponents that reach the glue are built by different
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

/-- **The overlap comparison for two homogeneous elements of the same degree.**

Over an open inside `D₊(b)`, twisting a section by `a` is twisting it by `b` and scaling by
`a / b`. The case `a = fⁿ`, `b = gⁿ` was stated separately in `TwistApp.lean` until `#825`; it had
no consumer once this one existed.

The scalar is ascribed at `Γ(Proj 𝒜, U)` for the reason recorded there: written bare it elaborates
at the structure sheaf's own section type, where the action on the twist's sections does not
synthesize. -/
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
