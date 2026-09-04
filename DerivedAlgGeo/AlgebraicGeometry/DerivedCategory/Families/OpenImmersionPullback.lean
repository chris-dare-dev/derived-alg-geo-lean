/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback

/-!
# Exact pullback along open immersions

Mathlib identifies module-sheaf pullback along an open immersion with
restriction and proves that restriction commutes with stalks.  Combining
that comparison with the stalkwise-to-global criterion from
`Families.FlatPullback` proves that pullback along every open immersion is
exact.  Consequently its ordinary module pullback descends to the concrete
derived fibers without an additional exactness hypothesis.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

/-- After forgetting the local-ring action, pullback followed by a stalk
along an open immersion is the ordinary stalk at the image point. -/
def openImmersionPullbackStalkForgetIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x) :=
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (moduleStalkForgetIso X x) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (CategoryTheory.Functor.associator (SheafOfModules.toSheaf X.ringCatSheaf)
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
      (Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ≪≫
    (CategoryTheory.Functor.associator (Scheme.Modules.restrictFunctor f)
      (Scheme.Modules.toPresheaf X)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).symm ≪≫
    Scheme.Modules.restrictStalkNatIso f x

/-- Pullback along an open immersion, followed by any module-stalk functor,
preserves finite limits. -/
theorem openImmersionPullbackStalk_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    PreservesFiniteLimits
      (Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) := by
  let forgetX :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let forgetY :=
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f x))) AddCommGrpCat.{u}
  have hStalk : PreservesFiniteLimits (moduleStalkFunctor Y (f x)) :=
    moduleStalkFunctor_preservesFiniteLimits Y (f x)
  have hForget : PreservesFiniteLimits forgetY := inferInstance
  have hStalkForget : PreservesFiniteLimits
      (moduleStalkFunctor Y (f x) ⋙ forgetY) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hStalk hForget
  let e : moduleStalkFunctor Y (f x) ⋙ forgetY ≅
      Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x) :=
    moduleStalkForgetIso Y (f x) ≪≫
      (CategoryTheory.Functor.associator (SheafOfModules.toSheaf Y.ringCatSheaf)
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y)
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x))).symm
  have hRight : PreservesFiniteLimits
      (Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e hStalkForget
  have hComposite : PreservesFiniteLimits
      ((Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) ⋙ forgetX) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (openImmersionPullbackStalkForgetIso f x).symm hRight
  letI := hComposite
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) forgetX

/-- Module-sheaf pullback along an open immersion preserves finite limits. -/
theorem openImmersionModulePullback_preservesFiniteLimits
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : PreservesFiniteLimits (modulePullback f) :=
  preservesFiniteLimits_of_stalkwise (modulePullback f)
    (openImmersionPullbackStalk_preservesFiniteLimits f.left)

/-- Pullback along an open immersion of scheme base changes is exact. -/
theorem isExactPullback_of_isOpenImmersion
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : IsExactPullback f := by
  letI : PreservesFiniteLimits (modulePullback f) :=
    openImmersionModulePullback_preservesFiniteLimits f
  exact IsExactPullback.of_preservesFiniteLimits f

/-- Exact pullback along open immersions is available to the derived
pullback API without a caller-supplied exactness instance. -/
instance (priority := 900) isExactPullbackOfIsOpenImmersion
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : IsExactPullback f :=
  isExactPullback_of_isOpenImmersion f

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
