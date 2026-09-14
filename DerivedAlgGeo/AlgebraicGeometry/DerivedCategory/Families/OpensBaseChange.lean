/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.Scheme
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Opens of the base as base changes of it

Section 4 of arXiv:1902.08184 quantifies `S`-locality over the quasi-compact
opens `U ⊆ S`: a t-structure on `𝒟` is `S`-local when each such `U` carries a
t-structure on `𝒟_U` making restriction t-exact. The repository indexes base
change by `SchemeBaseChange S = Over S`, so before that quantifier can be
written an open has to be an object of `Over S`.

It already is, and nothing needs constructing. Mathlib's `Scheme.Opens.toScheme`
makes an open into a scheme and `Scheme.Opens.ι` is its immersion into the
ambient one, so `Over.mk U.ι` is the base change. This file names that, records
the two projections as `rfl`, and identifies the top open with the identity base
change -- the object at which `𝒟_U` is `𝒟` itself.

No quasi-compactness hypothesis appears here. Which opens `S`-locality ranges
over is the quantifier's business, not the index's, and an arbitrary open is a
base change whether or not it is quasi-compact.
-/

noncomputable section

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- An open of the base, as a scheme over the base.

This is the object `𝒟_U` is the base change to: the quantifier in `S`-locality
ranges over the quasi-compact ones among these. -/
abbrev opensBaseChange (U : S.Opens) : SchemeBaseChange S :=
  Over.mk U.ι

@[simp]
theorem opensBaseChange_left (U : S.Opens) :
    (opensBaseChange U).left = U.toScheme :=
  rfl

@[simp]
theorem opensBaseChange_hom (U : S.Opens) :
    (opensBaseChange U).hom = U.ι :=
  rfl

end AlgebraicGeometry.DerivedCategory.Families
