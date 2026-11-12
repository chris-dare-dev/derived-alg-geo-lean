/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.ChartUnitTwist

/-!
# What `twistBy` does to a section

`twistBy` is `ρ.inv ≫ tensorHom (𝟙 F) (unitToTwist _)`, and `twistBy_app` says what it does to a
section: it is the pure tensor of the section with `a / 1`.
`Scheme.Modules.tensorUnitRight_inv_tensorHom_app` supplies exactly that shape at the level of
sections, and `twistBy_app` is it plus `unitToTwist_app_one`. Without it `twistBy` is opaque at
every use site.

## Main definitions

This file introduces no new definitions.

## Main results

* `AlgebraicGeometry.Proj.twistBy_app`: `twistBy` sends a section `t` to the pure tensor of `t`
  with `a / 1`.

## Notation

`X` is local notation for the underlying space `ProjectiveSpectrum.top 𝒜`.

## Implementation notes

### The overlap comparison is stated on `Proj 𝒜`

The overlap comparison — over an open inside `D₊(b)`, twisting a section by `a` is twisting by `b`
and scaling by `a / b` — is `FracSection.twistBy_app_eq_smul'`, which is built on `twistBy_app`
and is what the gluing in `exists_globalSection_twistBy` consumes. It is stated **on `Proj 𝒜`
directly**, with no restriction functor. The morphism-level route (`chartUnitToTwist_eq`,
`chartTwistBy_eq`) works on the open subscheme, and turning its conclusion back into a statement
about sections of `F(n)` on `Proj` would need restriction to commute with the sheafified tensor
product. No such compatibility exists, here or in Mathlib.

### Scope

One lemma: what `twistBy` does to a section. The comparison between charts is
`FracSection.twistBy_app_eq_smul'`; the cover, the single exponent across it, and the gluing are
further downstream still.

## References

`AlgebraicGeometry.Scheme.Modules.tensorUnitRight_inv_tensorHom_app` and
`AlgebraicGeometry.Proj.unitToTwist_app_one`.

## Tags

projective spectrum, twisting sheaf, tensor product, sections
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **What `twistBy` does to a section: it is the pure tensor with `a / 1`.**

The section-level counterpart of `unitToTwist_app_one`, one tensor up. Without it `twistBy` is
opaque at every use site, exactly as `unitToTwist` is without that lemma. -/
theorem twistBy_app (m : ℕ) {a : A} (ha : a ∈ 𝒜 m)
    (F : (Proj 𝒜).Modules) (U : (Proj 𝒜).Opensᵒᵖ) (t : Γ(F, U.unop)) :
    ((twistBy 𝒜 m ha F).val.app U).hom t
      = Scheme.Modules.tmulSection F (twistingSheaf 𝒜 (m : ℤ)) U t
          (sectionOfMem 𝒜 𝒜 U.unop m ha) := by
  rw [twistBy, Scheme.Modules.tensorUnitRight_inv_tensorHom_app]
  exact congrArg (Scheme.Modules.tmulSection F (twistingSheaf 𝒜 (m : ℤ)) U t)
    (unitToTwist_app_one 𝒜 𝒜 m ha U.unop)

end AlgebraicGeometry.Proj
