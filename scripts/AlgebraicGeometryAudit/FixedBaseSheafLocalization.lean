import DerivedAlgGeo.AlgebraicGeometry.Modules.FixedBaseSheafLocalization

/-! # SF11 localized two-open section limit audit -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

#print axioms AlgebraicGeometry.localizedFixedBaseSectionsTwoOpenLimit

-- This is the genuine fixed-base section cone, localized objectwise.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U V : Y.Opens) (S : Submonoid R) :
    IsLimit ((ModuleCat.localizedModuleFunctor S).mapCone
      (TopCat.Sheaf.interUnionPullbackCone
        ((modulesToFixedBaseSheaf Y φ).obj M) U V)) :=
  localizedFixedBaseSectionsTwoOpenLimit Y φ M U V S

-- The localized cone point is the localization of sections on the union,
-- not an independently supplied base-changed section module.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U V : Y.Opens) (S : Submonoid R) :
    ((ModuleCat.localizedModuleFunctor S).mapCone
      (TopCat.Sheaf.interUnionPullbackCone
        ((modulesToFixedBaseSheaf Y φ).obj M) U V)).pt =
      (ModuleCat.localizedModuleFunctor S).obj
        ((fixedBaseSectionsFunctor Y φ (U ⊔ V)).obj M) :=
  rfl

end
