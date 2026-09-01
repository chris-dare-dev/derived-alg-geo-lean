/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Basic
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant

/-!
# The structure sheaf as a coherent sheaf

`O_X` is a coherent sheaf, and this file names the resulting object of `Coh X`.
It is a two-line definition, but it needs a home: coherence of `O_X` is
`LineBundleData.isCoherent` applied to `LineBundleData.unit`, so the fact lives
in `Divisors/`, while the category it lands in lives in `CoherentSheaf/`.

The coherent derived-category owner imports this module and uses this same
object as the canonical degree-zero perfect object. Keeping the coherent sheaf
here avoids making ordinary coherent-sheaf consumers depend on triangulated
generators or t-structures.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- The structure sheaf `O_X`, regarded as an object of `Coh X`.

Coherence is `Scheme.Modules.LineBundleData.isCoherent` for the unit line
bundle; no noetherian or finiteness hypothesis on `X` is needed, because an
invertible sheaf is of finite presentation outright. -/
noncomputable def structureSheafCoh (X : Scheme.{u}) : Coh X :=
  ⟨(Modules.LineBundleData.unit X).line,
    (Modules.LineBundleData.unit X).isCoherent⟩

@[simp]
theorem structureSheafCoh_obj (X : Scheme.{u}) :
    (structureSheafCoh X).obj = (Modules.LineBundleData.unit X).line :=
  rfl

/-- The underlying module sheaf of `structureSheafCoh` is the unit of the
tensor product, which is what makes it the *structure* sheaf rather than some
other invertible sheaf. -/
theorem structureSheafCoh_obj_eq_unit (X : Scheme.{u}) :
    (structureSheafCoh X).obj = SheafOfModules.unit X.ringCatSheaf :=
  rfl

end Scheme

namespace Scheme.Modules.LineBundleData

variable {X : Scheme.{u}}

/-- Two line bundles have the same Picard-group element exactly when their
underlying sheaves are isomorphic.

`toPic_eq_of_iso` is the forward direction alone. The converse is what a
triviality hypothesis stated in `Pic` has to be unpacked through, so both are
worth having; the recorded tensor inverses play no part, which is why this is
an `iff` and not merely an implication. -/
theorem toPic_eq_iff (L M : LineBundleData X) :
    L.toPic = M.toPic ↔ Nonempty (L.line ≅ M.line) := by
  rw [← Units.val_inj, coe_toPic, coe_toPic]
  exact PicardClass.mk_eq_mk_iff _ _

/-- The structure sheaf is the identity of the Picard group. -/
@[simp]
theorem unit_toPic (X : Scheme.{u}) : (unit X).toPic = 1 := by
  rw [← Units.val_inj, coe_toPic, Pic.coe_one]
  rfl

end Scheme.Modules.LineBundleData

end AlgebraicGeometry
