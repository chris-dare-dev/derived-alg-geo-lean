/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.ChartUnitTwist

/-!
# What `twistBy` does to a section

`twistBy` is `ρ.inv ≫ tensorHom (𝟙 F) (unitToTwist _)`, and for a long time **nothing in the tree
said what any part of that does to a section** — `tensorObj`, `tensorHom` and the unitors were used
at the morphism level only. `Scheme.Modules.tensorUnitRight_inv_tensorHom_app` supplies exactly
that shape, and `twistBy_app` is it plus `unitToTwist_app_one`. Without it `twistBy` is opaque at
every use site.

## What used to be here

The overlap comparison — over an open inside `D₊(g)`, twisting a section by `fⁿ` is twisting by
`gⁿ` and scaling by `fⁿ/gⁿ` — was stated here first, at `f, g` of degree one, together with the
step-A lemma it needed. `FracSection.twistBy_app_eq_smul'` then proved the same thing for any two
homogeneous elements of the same degree, and that is what `#585`'s glue actually consumes. The
degree-one pair survived with no consumer until `#825` removed it.

What made the degree-one version worth writing is preserved in the general one: it is stated **on
`Proj 𝒜` directly**, with no restriction functor. The morphism-level route
(`chartUnitToTwist_eq`, `chartTwistBy_eq`) works on the open subscheme, and turning its conclusion
back into a statement about sections of `F(n)` on `Proj` would need restriction to commute with the
sheafified tensor product. No such compatibility exists, here or in Mathlib.

## Scope

One lemma: what `twistBy` does to a section. The comparison between charts is
`FracSection.twistBy_app_eq_smul'`; the cover, the single exponent across it, and the gluing are
further downstream still.
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

end AlgebraicGeometry.Proj
