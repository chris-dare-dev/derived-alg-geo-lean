/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.LeftDerivedPullback

/-!
# Exact pullback along open immersions

Mathlib identifies module-sheaf pullback along an open immersion with
restriction and proves that restriction commutes with stalks.  Combining
that comparison with the stalkwise-to-global criterion from
`Families.FlatPullback` proves that pullback along every open immersion is
exact.  Consequently its ordinary module pullback descends to the concrete
derived fibers without an additional exactness hypothesis.

Mathlib also identifies restriction after module-sheaf pushforward with the
identity.  Applying that counit degreewise gives every complex on the open
subscheme an extension to the ambient scheme.  After localization this proves
that derived pullback along an open immersion is essentially surjective; no
exactness of pushforward is needed for this objectwise extension argument.
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

/-! ## Essential surjectivity -/

/-- Pushforward followed by pullback along an open immersion is naturally
isomorphic to the identity on module sheaves.  The point is that pullback is
restriction in this case, and Mathlib's restriction--pushforward adjunction
has invertible counit. -/
def openImmersionModulePullbackPushforwardIso
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] :
    modulePushforward f ⋙ modulePullback f ≅ 𝟭 T.left.Modules :=
  (Functor.isoWhiskerLeft (modulePushforward f)
      (Scheme.Modules.restrictFunctorIsoPullback f.left)).symm ≪≫
    Scheme.Modules.restrictFunctorAdjCounitIso f.left

/-- Extend a complex on an open subscheme termwise by module-sheaf
pushforward.  Pushforward need not be exact: this functor is used only to
choose an ambient representative whose pullback is the original complex. -/
abbrev openImmersionComplexExtension
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U) :
    CochainComplex T.left.Modules ℤ ⥤ CochainComplex U.left.Modules ℤ :=
  (modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Pulling back the termwise extension of a complex from an open subscheme
recovers that complex. -/
def openImmersionComplexPullbackExtensionIso
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] :
    openImmersionComplexExtension f ⋙ complexPullback f ≅
      𝟭 (CochainComplex T.left.Modules ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (openImmersionModulePullbackPushforwardIso f) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso T.left.Modules (ComplexShape.up ℤ)

/-- Derived pullback along an open immersion is essentially surjective.

For a derived object on the open subscheme, choose a complex representative,
extend it termwise by pushforward, and use the restriction--pushforward
counit after applying the derived localization. -/
noncomputable instance derivedPullback_essSurj_of_isOpenImmersion
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : (derivedPullback f).EssSurj where
  mem_essImage E := by
    let K := (SchemeDerivedCategory.Q T.left).objPreimage E
    let extension := (openImmersionComplexExtension f).obj K
    refine ⟨(SchemeDerivedCategory.Q U.left).obj extension, ⟨?_⟩⟩
    exact (derivedPullbackFactors f).app extension ≪≫
      (SchemeDerivedCategory.Q T.left).mapIso
        ((openImmersionComplexPullbackExtensionIso f).app K) ≪≫
      (SchemeDerivedCategory.Q T.left).objObjPreimageIso E

/-- Every genuine left-derived pullback along an open immersion is
essentially surjective.  Uniqueness of left-derived functors identifies it
with the exact model above. -/
noncomputable instance LeftDerivedPullback.essSurj_of_isOpenImmersion
    {S : Scheme.{u}} {T U : SchemeBaseChange S} {f : T ⟶ U}
    (P : LeftDerivedPullback f) [IsOpenImmersion f.left] : P.functor.EssSurj := by
  letI : (derivedPullback f).EssSurj :=
    derivedPullback_essSurj_of_isOpenImmersion f
  exact Functor.essSurj_of_iso P.exactComparison.symm

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
