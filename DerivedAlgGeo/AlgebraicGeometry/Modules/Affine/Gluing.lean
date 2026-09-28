/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.BasicOpen
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.OpenImmersion

/-!
# Affine-comparison bridges retained after the gluing proof moved upstream

Mathlib v4.32.1 contains the full quasi-coherent affine comparison as
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`, with its finite-cover
presentation argument in `AlgebraicGeometry/Modules/Tilde.lean`. This file retains local bridges
and does not reprove that comparison.

Only two local bridges remain:

* the linear equivalence identifying sections of a restriction to `Spec R[1/g]` with sections
  over `D(g)`, used by the finite-generation argument; and
* stable wrappers connecting the upstream comparison instance to DerivedAlgGeo's localization and
  explicit-quasi-coherent-data APIs.

No gluing theorem is duplicated here.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open _root_.PrimeSpectrum

variable {R : CommRingCat.{u}}

/-- The canonical open immersion `Spec R[1/g] ⟶ Spec R`. -/
noncomputable def basicOpenSpecMap (g : R) :
    Spec (.of (Localization.Away g)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))

instance (g : R) : IsOpenImmersion (basicOpenSpecMap g) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway g

/-- The range of `Spec R[1/g] ⟶ Spec R` is `D(g)`. -/
lemma basicOpenSpecMap_opensRange (g : R) :
    (basicOpenSpecMap g).opensRange = PrimeSpectrum.basicOpen g := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away g) g

/-- The image of the top open under the canonical open immersion is `D(g)`. -/
private lemma basicOpenSpecMap_image_top (g : R) :
    basicOpenSpecMap g ''ᵁ ⊤ = PrimeSpectrum.basicOpen g := by
  rw [Scheme.Hom.image_top_eq_opensRange, basicOpenSpecMap_opensRange]

private lemma restrictBasicOpen_smul (M : (Spec R).Modules) (g : R)
    (r : R)
    (x : (modulesSpecToSheaf.obj (M.restrict (basicOpenSpecMap g))).presheaf.obj (op ⊤)) :
    (algebraMap R (Localization.Away g) r) • x =
      r • (show (modulesSpecToSheaf.obj M).presheaf.obj
        (op (basicOpenSpecMap g ''ᵁ ⊤)) from x) := by
  change (M.restrictAppIso (basicOpenSpecMap g) ⊤).hom
      (algebraMap R (Localization.Away g) r • x) =
    r • (M.restrictAppIso (basicOpenSpecMap g) ⊤).hom x
  exact restrictAppIso_smul_Spec (M := M)
    (CommRingCat.ofHom (algebraMap R (Localization.Away g))) r x

/-- Identify sections of the restriction to `Spec R[1/g]` over its top open with sections of
the original sheaf over `D(g)`, after restricting scalars to `R`. -/
noncomputable def restrictBasicOpenTopLinearEquiv (M : (Spec R).Modules) (g : R) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away g))).obj
        ((modulesSpecToSheaf.obj
          (M.restrict (basicOpenSpecMap g))).presheaf.obj (op ⊤)) ≃ₗ[R]
      (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen g)) := by
  let e := ((modulesSpecToSheaf.obj M).presheaf.mapIso
    (eqToIso (basicOpenSpecMap_image_top (R := R) g)).op).symm
  refine
    { toFun := e.hom
      invFun := e.inv
      left_inv := fun x => Iso.hom_inv_id_apply e x
      right_inv := fun x => Iso.inv_hom_id_apply e x
      map_add' := fun x y => e.hom.hom.map_add x y
      map_smul' := ?_ }
  intro r x
  change e.hom.hom (algebraMap R (Localization.Away g) r • x) = _
  calc
    _ = e.hom.hom (r • (show (modulesSpecToSheaf.obj M).presheaf.obj
        (op (basicOpenSpecMap g ''ᵁ ⊤)) from x)) :=
      congrArg e.hom.hom (restrictBasicOpen_smul M g r x)
    _ = _ := e.hom.hom.map_smul r _

/-- For a quasi-coherent sheaf on an affine scheme, restriction to every basic open is the
corresponding module localization. -/
theorem isLocalizedModule_basicOpenRestriction_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom :=
  M.isLocalizedModule_basicOpenRestriction_of_isIso f

/-- Explicit quasi-coherent presentation data suffices for the upstream affine comparison. -/
theorem isIso_fromTildeΓ_of_quasicoherentData
    (M : (Spec R).Modules) (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    IsIso M.fromTildeΓ := by
  letI : M.IsQuasicoherent := q.isQuasicoherent
  infer_instance

end AlgebraicGeometry.Scheme.Modules
