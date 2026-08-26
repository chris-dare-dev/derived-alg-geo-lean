/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ChartUnitTwist

/-!
# What `twistBy` does to a section, and the comparison between two charts

`#585`'s glue has to compare the sections that two charts produce. Everything up to here compares
*morphisms*; this file is where the comparison finally happens on sections, which is the form the
chart-extension half speaks in.

## Why this can be said at all now

`twistBy` is `ρ.inv ≫ tensorHom (𝟙 F) (unitToTwist _)`, and until recently **nothing in the tree
said what any part of that does to a section** — `tensorObj`, `tensorHom` and the unitors were used
at the morphism level only. `Scheme.Modules.tensorUnitRight_inv_tensorHom_app` supplies exactly
that shape, and `twistBy_app` is it plus `unitToTwist_app_one`.

## The comparison, and what it avoids

`twistBy_app_eq_smul` says: over an open inside `D₊(g)`, twisting a section by `fⁿ` is twisting by
`gⁿ` and scaling by `fⁿ/gⁿ`. That is the overlap agreement `#585` needs, and it is stated **on
`Proj 𝒜` directly** — no restriction functor appears.

That matters. The morphism-level route (`chartUnitToTwist_eq`, `chartTwistBy_eq`) works on the open
subscheme, and turning its conclusion back into a statement about sections of `F(n)` on `Proj`
would need restriction to commute with the sheafified tensor product. No such compatibility exists,
in this repository or in Mathlib. Carrying the comparison on sections from the start avoids needing
it.

The proof is three rewrites and no geometry: `twistBy_app` on both sides, `smul_tmulSection` to
push the scalar onto the twist factor, and step A (`fracPow_smul_sectionOfMem`, lifted to sections
here) to finish. The geometry was all spent earlier.

## Scope

The section-level comparison. The cover, the single exponent across it, and the gluing itself are
not here.
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜

/-- **What `twistBy` does to a section: it is the pure tensor with `a / 1`.**

The section-level counterpart of `unitToTwist_app_one`, one tensor up. Without it `twistBy` is
opaque at every use site, exactly as `unitToTwist` was before that lemma. -/
theorem twistBy_app (m : ℕ) {a : A} (ha : a ∈ 𝒜 m)
    (F : (Proj 𝒜).Modules) (U : (Proj 𝒜).Opensᵒᵖ) (t : Γ(F, U.unop)) :
    ((twistBy 𝒜 m ha F).val.app U).hom t
      = Scheme.Modules.tmulSection F (twistingSheaf 𝒜 (m : ℤ)) U t
          (sectionOfMem 𝒜 𝒜 U.unop m ha) := by
  rw [twistBy, Scheme.Modules.tensorUnitRight_inv_tensorHom_app]
  exact congrArg (Scheme.Modules.tmulSection F (twistingSheaf 𝒜 (m : ℤ)) U t)
    (unitToTwist_app_one 𝒜 𝒜 m ha U.unop)

/-- **Step A, on sections rather than at a point.**

`fracPow_smul_sectionOfMem` is pointwise; both sides here are sections of the twist, and the
associated sheaf's module structure is pointwise, so this is that lemma under `section_ext`.

No transport appears, unlike the morphism-level route: this is the `Proj` action throughout, not a
restricted one, so `Scheme.Modules.restrict_smul_eq` is not needed. -/
theorem fracPowSection_smul_sectionOfMem {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (n : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    fracPowSection 𝒜 hf hg n hU • sectionOfMem 𝒜 𝒜 U n (pow_mem_deg 𝒜 hg n)
      = sectionOfMem 𝒜 𝒜 U n (pow_mem_deg 𝒜 hf n) := by
  apply section_ext
  funext x
  exact fracPow_smul_sectionOfMem 𝒜 hf hg n hU x

/-- **The overlap comparison: over `D₊(g)`, twisting by `fⁿ` is twisting by `gⁿ` and scaling.**

The agreement `#585`'s glue needs, on sections and on `Proj 𝒜` itself — no restriction functor and
no chart. Carrying it here rather than through the open subscheme is what avoids needing
restriction to commute with the sheafified tensor, which nothing provides.

The scalar is ascribed at `Γ(Proj 𝒜, U)`: written bare it elaborates at the structure sheaf's own
section type, where the action on the twist's sections does not synthesize. That ascription leaves
residue in the goal which stops `rw` matching, so the last two steps are `have` and `exact`. -/
theorem twistBy_app_eq_smul {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (n : ℕ)
    (F : (Proj 𝒜).Modules) {U : Opens X}
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) (t : Γ(F, U)) :
    ((twistBy 𝒜 n (pow_mem_deg 𝒜 hf n) F).val.app (op U)).hom t
      = (show Γ(Proj 𝒜, U) from fracPowSection 𝒜 hf hg n hU) •
        ((twistBy 𝒜 n (pow_mem_deg 𝒜 hg n) F).val.app (op U)).hom t := by
  rw [twistBy_app, twistBy_app]
  have h1 := Scheme.Modules.smul_tmulSection F (twistingSheaf 𝒜 (n : ℤ)) (op U)
    (show Γ(Proj 𝒜, U) from fracPowSection 𝒜 hf hg n hU) t
    (sectionOfMem 𝒜 𝒜 U n (pow_mem_deg 𝒜 hg n))
  have h2 := fracPowSection_smul_sectionOfMem 𝒜 hf hg n hU
  exact (h1.trans (congrArg
    (Scheme.Modules.tmulSection F (twistingSheaf 𝒜 (n : ℤ)) (op U) t) h2)).symm

end AlgebraicGeometry.Proj
