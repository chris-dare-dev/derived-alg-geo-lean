import DerivedAlgGeo.AlgebraicGeometry.Modules.Tilde

/-! # Tilde basic-open range audit and direct clients -/

open CategoryTheory AlgebraicGeometry Opposite _root_.PrimeSpectrum

universe u

#print axioms AlgebraicGeometry.tilde.localized'_range_eq_range_map_basicOpen

-- The owner leaf alone supplies the range statement for an arbitrary map.
example (R : CommRingCat.{u}) (K M : ModuleCat.{u} R)
    (g : K ⟶ M) (r : R) :
    let S := Submonoid.powers r
    let U := basicOpen r
    let fK := (tilde.toOpen K U).hom
    let fM := (tilde.toOpen M U).hom
    letI : IsLocalizedModule S fK := by
      exact inferInstanceAs (IsLocalizedModule.Away r
        (tilde.toOpen K (basicOpen r)).hom)
    letI : IsLocalizedModule S fM := by
      exact inferInstanceAs (IsLocalizedModule.Away r
        (tilde.toOpen M (basicOpen r)).hom)
    letI : Module (Localization.Away r) _ := IsLocalizedModule.module S fK
    letI : IsScalarTower R (Localization.Away r) _ :=
      IsLocalizedModule.isScalarTower_module S fK
    letI : Module (Localization.Away r) _ := IsLocalizedModule.module S fM
    letI : IsScalarTower R (Localization.Away r) _ :=
      IsLocalizedModule.isScalarTower_module S fM
    let h := ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op U)).hom
    g.hom.range.localized' (Localization.Away r) S fM =
      (h.extendScalarsOfIsLocalization S (Localization.Away r)).range :=
  tilde.localized'_range_eq_range_map_basicOpen R K M g r

-- In particular, the source can be the subtype of a submodule, without
-- requiring Noetherianity or finiteness of that submodule.
#check fun (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (N : Submodule R M) (r : R) =>
  tilde.localized'_range_eq_range_map_basicOpen R (ModuleCat.of R N) M
    (ModuleCat.ofHom N.subtype) r
