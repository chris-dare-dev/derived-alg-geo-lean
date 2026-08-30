/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.LeftDerivedPullback

/-!
# Functorial resolutions for arbitrary derived pullback

This file isolates the concrete resolution data sufficient to construct
left-derived pullback along a scheme morphism. A
`PullbackAcyclicResolution f` consists of a functorial replacement of every
complex, a componentwise quasi-isomorphism from the replacement to the
original complex, and a proof that pullback followed by localization inverts
quasi-isomorphisms between the replacements.

The resulting functor on the derived categories is constructed by the
universal property of localization. The comparison with ordinary pullback is
then proved to have Mathlib's left-derived universal property; it is not
stored as an additional assumption.

K-flat resolutions are intended to provide the main geometric inhabitants of
this interface. Keeping the condition in terms of the exact functor that must
invert quasi-isomorphisms also permits narrower supported constructions.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry Limits

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

/-- A functorial resolution on which pullback along `f` preserves
quasi-isomorphisms.

The comparison points from the resolution to the original complex, as for a
K-flat replacement. The last field is the operational acyclicity condition:
after resolving, ordinary pullback descends through the source derived
localization. -/
structure PullbackAcyclicResolution (f : T ⟶ U) where
  /-- Functorial replacement of complexes on the source of pullback. -/
  resolution : CochainComplex U.left.Modules ℤ ⥤
    CochainComplex U.left.Modules ℤ
  /-- Comparison from the replacement to the original complex. -/
  comparison : resolution ⟶ 𝟭 _
  /-- Every comparison component is a quasi-isomorphism. -/
  comparison_quasiIso (K : CochainComplex U.left.Modules ℤ) :
    HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)
      (comparison.app K)
  /-- Pullback of resolved complexes sends every quasi-isomorphism to an
  isomorphism after localization on the target scheme. -/
  pullback_inverts :
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)).IsInvertedBy
      (resolution ⋙ complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
  /-- Pulling back the comparison of an already resolved complex gives an
  isomorphism after target localization. This is the idempotence condition
  on the acyclic replacement that makes the comparison universal. -/
  resolved_comparison_isIso (K : CochainComplex U.left.Modules ℤ) :
    IsIso ((complexPullback f ⋙ SchemeDerivedCategory.Q T.left).map
      (comparison.app (resolution.obj K)))

namespace PullbackAcyclicResolution

variable {S : Scheme.{u}} {T U : SchemeBaseChange S} {f : T ⟶ U}

/-- For exact pullback, the identity functor on complexes is already a
pullback-acyclic resolution. This is the normalization case against which
genuinely derived resolutions can be compared. -/
def ofExact (f : T ⟶ U) [IsExactPullback f] :
    PullbackAcyclicResolution f where
  resolution := 𝟭 (CochainComplex U.left.Modules ℤ)
  comparison := 𝟙 (𝟭 (CochainComplex U.left.Modules ℤ))
  comparison_quasiIso K := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  pullback_inverts := by
    intro K L g hg
    change IsIso ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map g))
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    rw [HomologicalComplex.mem_quasiIso_iff] at hg ⊢
    letI := hg
    infer_instance
  resolved_comparison_isIso K := by
    simp only [CategoryTheory.Functor.id_obj, NatTrans.id_app, CategoryTheory.Functor.comp_map,
      CategoryTheory.Functor.map_id]
    exact IsIso.id _

/-- The functor on derived categories obtained by resolving, pulling back, and
using the universal property of localization. -/
def derivedFunctor (R : PullbackAcyclicResolution f) :
    U.DerivedFiber ⥤ T.DerivedFiber :=
  Localization.lift
    (R.resolution ⋙ complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
    R.pullback_inverts (SchemeDerivedCategory.Q U.left)

/-- The localization factorization for resolved pullback. -/
def derivedFactors (R : PullbackAcyclicResolution f) :
    SchemeDerivedCategory.Q U.left ⋙ R.derivedFunctor ≅
      R.resolution ⋙ complexPullback f ⋙ SchemeDerivedCategory.Q T.left :=
  Localization.fac
    (R.resolution ⋙ complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
    R.pullback_inverts (SchemeDerivedCategory.Q U.left)

/-- A resolution becomes naturally isomorphic to the identity after source
localization. -/
def localizationComparison (R : PullbackAcyclicResolution f) :
    R.resolution ⋙ SchemeDerivedCategory.Q U.left ≅
      SchemeDerivedCategory.Q U.left := by
  refine NatIso.ofComponents
    (fun K ↦ by
      exact @CategoryTheory.asIso _ _ _ _ _
        (Localization.inverts (SchemeDerivedCategory.Q U.left)
          (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
          (R.comparison.app K) (R.comparison_quasiIso K))) ?_
  intro K L g
  change (SchemeDerivedCategory.Q U.left).map (R.resolution.map g) ≫
      (SchemeDerivedCategory.Q U.left).map (R.comparison.app L) =
    (SchemeDerivedCategory.Q U.left).map (R.comparison.app K) ≫
      (SchemeDerivedCategory.Q U.left).map g
  have hc : R.resolution.map g ≫ R.comparison.app L =
      R.comparison.app K ≫ g := by
    simpa only [CategoryTheory.Functor.id_map] using! R.comparison.naturality g
  simpa only [← CategoryTheory.Functor.map_comp] using! congrArg
    (fun k ↦ (SchemeDerivedCategory.Q U.left).map k)
    hc

/-- The comparison from resolved derived pullback to ordinary pullback. -/
def counit (R : PullbackAcyclicResolution f) :
    SchemeDerivedCategory.Q U.left ⋙ R.derivedFunctor ⟶
      complexPullback f ⋙ SchemeDerivedCategory.Q T.left :=
  R.derivedFactors.hom ≫
    CategoryTheory.Functor.whiskerRight R.comparison
      (complexPullback f ⋙ SchemeDerivedCategory.Q T.left)

private abbrev ordinaryPullback (f : T ⟶ U) :=
  complexPullback f ⋙ SchemeDerivedCategory.Q T.left

/-- The two ways of comparing a double resolution with a single resolution:
first compare the outer resolution. -/
def outerComparisonIso (R : PullbackAcyclicResolution f) :
    R.resolution ⋙ R.resolution ⋙ ordinaryPullback f ≅
      R.resolution ⋙ ordinaryPullback f := by
  refine NatIso.ofComponents
    (fun K ↦ by
      exact @CategoryTheory.asIso _ _ _ _ _
        (R.resolved_comparison_isIso K)) ?_
  intro K L g
  change (ordinaryPullback f).map (R.resolution.map (R.resolution.map g)) ≫
      (ordinaryPullback f).map (R.comparison.app (R.resolution.obj L)) =
    (ordinaryPullback f).map (R.comparison.app (R.resolution.obj K)) ≫
      (ordinaryPullback f).map (R.resolution.map g)
  have hc : R.resolution.map (R.resolution.map g) ≫
      R.comparison.app (R.resolution.obj L) =
    R.comparison.app (R.resolution.obj K) ≫ R.resolution.map g := by
    simpa only [CategoryTheory.Functor.id_map] using!
      R.comparison.naturality (R.resolution.map g)
  simpa only [← CategoryTheory.Functor.map_comp] using!
    congrArg (fun k ↦ (ordinaryPullback f).map k)
      hc

/-- The two ways of comparing a double resolution with a single resolution:
first map the inner comparison through the outer resolution. -/
def innerComparisonIso (R : PullbackAcyclicResolution f) :
    R.resolution ⋙ R.resolution ⋙ ordinaryPullback f ≅
      R.resolution ⋙ ordinaryPullback f := by
  refine NatIso.ofComponents
    (fun K ↦ by
      exact @CategoryTheory.asIso _ _ _ _ _
        (R.pullback_inverts (R.comparison.app K)
          (R.comparison_quasiIso K))) ?_
  intro K L g
  change (ordinaryPullback f).map (R.resolution.map (R.resolution.map g)) ≫
      (ordinaryPullback f).map (R.resolution.map (R.comparison.app L)) =
    (ordinaryPullback f).map (R.resolution.map (R.comparison.app K)) ≫
      (ordinaryPullback f).map (R.resolution.map g)
  have hc : R.resolution.map g ≫ R.comparison.app L =
      R.comparison.app K ≫ g := by
    simpa only [CategoryTheory.Functor.id_map] using! R.comparison.naturality g
  simpa only [← CategoryTheory.Functor.map_comp] using!
    congrArg (fun k ↦ (ordinaryPullback f).map (R.resolution.map k))
      hc

/-- The comparison defining resolved derived pullback is invertible on an
already resolved complex. -/
instance counit_app_resolution_isIso (R : PullbackAcyclicResolution f)
    (K : CochainComplex U.left.Modules ℤ) :
    IsIso (R.counit.app (R.resolution.obj K)) := by
  change IsIso (R.derivedFactors.hom.app (R.resolution.obj K) ≫
    (ordinaryPullback f).map
      (R.comparison.app (R.resolution.obj K)))
  exact IsIso.comp_isIso' (by infer_instance)
    (R.resolved_comparison_isIso K)

/-- The lift before descending it through source localization. Its middle
two factors compare the two canonical maps from a double resolution to a
single resolution. -/
def whiskeredLift (R : PullbackAcyclicResolution f)
    (G : U.DerivedFiber ⥤ T.DerivedFiber)
    (β : SchemeDerivedCategory.Q U.left ⋙ G ⟶ ordinaryPullback f) :
    SchemeDerivedCategory.Q U.left ⋙ G ⟶
      SchemeDerivedCategory.Q U.left ⋙ R.derivedFunctor :=
  (CategoryTheory.Functor.isoWhiskerRight R.localizationComparison G).inv ≫
    (CategoryTheory.Functor.associator R.resolution (SchemeDerivedCategory.Q U.left) G).hom ≫
    CategoryTheory.Functor.whiskerLeft R.resolution β ≫
    R.outerComparisonIso.inv ≫
    R.innerComparisonIso.hom ≫
    R.derivedFactors.inv

/-- The universal lift induced by a pullback-acyclic resolution. -/
def lift (R : PullbackAcyclicResolution f)
    (G : U.DerivedFiber ⥤ T.DerivedFiber)
    (β : SchemeDerivedCategory.Q U.left ⋙ G ⟶ ordinaryPullback f) :
    G ⟶ R.derivedFunctor := by
  letI := Localization.full_whiskeringLeft
    (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    T.DerivedFiber
  exact ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj
    (SchemeDerivedCategory.Q U.left)).preimage (R.whiskeredLift G β)

@[reassoc]
lemma whiskerLeft_lift (R : PullbackAcyclicResolution f)
    (G : U.DerivedFiber ⥤ T.DerivedFiber)
    (β : SchemeDerivedCategory.Q U.left ⋙ G ⟶ ordinaryPullback f) :
    CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left) (R.lift G β) =
      R.whiskeredLift G β := by
  letI := Localization.full_whiskeringLeft
    (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    T.DerivedFiber
  apply ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj
    (SchemeDerivedCategory.Q U.left)).map_preimage

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma whiskeredLift_fac (R : PullbackAcyclicResolution f)
    (G : U.DerivedFiber ⥤ T.DerivedFiber)
    (β : SchemeDerivedCategory.Q U.left ⋙ G ⟶ ordinaryPullback f) :
    R.whiskeredLift G β ≫ R.counit = β := by
  ext K
  change (R.whiskeredLift G β).app K ≫ R.counit.app K = β.app K
  apply (cancel_epi (G.map (R.localizationComparison.hom.app K))).mp
  have hβ : G.map ((SchemeDerivedCategory.Q U.left).map
      (R.comparison.app K)) ≫ β.app K =
      β.app (R.resolution.obj K) ≫
        (ordinaryPullback f).map (R.comparison.app K) := by
    simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_obj] using!
      β.naturality (R.comparison.app K)
  have hc : R.resolution.map (R.comparison.app K) ≫ R.comparison.app K =
      R.comparison.app (R.resolution.obj K) ≫ R.comparison.app K := by
    simpa only [CategoryTheory.Functor.id_map] using!
      R.comparison.naturality (R.comparison.app K)
  have hFc : (ordinaryPullback f).map
        (R.resolution.map (R.comparison.app K)) ≫
      (ordinaryPullback f).map (R.comparison.app K) =
    (ordinaryPullback f).map
        (R.comparison.app (R.resolution.obj K)) ≫
      (ordinaryPullback f).map (R.comparison.app K) := by
    simpa only [← CategoryTheory.Functor.map_comp] using! congrArg
      (fun k ↦ (ordinaryPullback f).map k) hc
  have hmiddle : @CategoryTheory.inv _ _ _ _ _
        (R.resolved_comparison_isIso K) ≫
      (ordinaryPullback f).map (R.resolution.map (R.comparison.app K)) ≫
      (ordinaryPullback f).map (R.comparison.app K) =
    (ordinaryPullback f).map (R.comparison.app K) := by
    rw [hFc]
    simp
  have hloc : G.map (R.localizationComparison.hom.app K) ≫
      (R.whiskeredLift G β).app K =
    β.app (R.resolution.obj K) ≫ R.outerComparisonIso.inv.app K ≫
      R.innerComparisonIso.hom.app K ≫ R.derivedFactors.inv.app K := by
    have hG : G.map (R.localizationComparison.hom.app K) ≫
        G.map (R.localizationComparison.inv.app K) = 𝟙 _ := by
      rw [← G.map_comp, R.localizationComparison.hom_inv_id_app, G.map_id]
    dsimp [whiskeredLift]
    rw [← Category.assoc, hG, Category.id_comp]
    simp
  have hcounit : R.derivedFactors.inv.app K ≫ R.counit.app K =
      (ordinaryPullback f).map (R.comparison.app K) := by
    dsimp [counit]
    simp
  have hrest : R.outerComparisonIso.inv.app K ≫
      R.innerComparisonIso.hom.app K ≫
        (ordinaryPullback f).map (R.comparison.app K) =
      (ordinaryPullback f).map (R.comparison.app K) := by
    simpa only [outerComparisonIso, innerComparisonIso,
      Category.assoc] using! hmiddle
  have hlocCounit :
      G.map (R.localizationComparison.hom.app K) ≫
          ((R.whiskeredLift G β).app K ≫ R.counit.app K) =
        (β.app (R.resolution.obj K) ≫ R.outerComparisonIso.inv.app K ≫
          R.innerComparisonIso.hom.app K ≫ R.derivedFactors.inv.app K) ≫
          R.counit.app K := by
    simpa only [Category.assoc] using! congrArg
      (fun k ↦ k ≫ R.counit.app K) hloc
  rw [hlocCounit]
  simp only [Category.assoc, hcounit, hrest]
  simpa only [localizationComparison, CategoryTheory.asIso_hom] using! hβ.symm

@[reassoc]
lemma lift_fac (R : PullbackAcyclicResolution f)
    (G : U.DerivedFiber ⥤ T.DerivedFiber)
    (β : SchemeDerivedCategory.Q U.left ⋙ G ⟶ ordinaryPullback f) :
    CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left) (R.lift G β) ≫
      R.counit = β := by
  rw [R.whiskerLeft_lift, R.whiskeredLift_fac]

lemma counit_hom_ext (R : PullbackAcyclicResolution f)
    (G : U.DerivedFiber ⥤ T.DerivedFiber) (γ₁ γ₂ : G ⟶ R.derivedFunctor)
    (hγ : CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left) γ₁ ≫ R.counit =
      CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left) γ₂ ≫ R.counit) :
    γ₁ = γ₂ := by
  letI := Localization.faithful_whiskeringLeft
    (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    T.DerivedFiber
  apply ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj
    (SchemeDerivedCategory.Q U.left)).map_injective
  ext K
  change γ₁.app ((SchemeDerivedCategory.Q U.left).obj K) =
    γ₂.app ((SchemeDerivedCategory.Q U.left).obj K)
  rw [← cancel_epi (G.map (R.localizationComparison.hom.app K))]
  rw [γ₁.naturality, γ₂.naturality]
  rw [cancel_mono (R.derivedFunctor.map
    (R.localizationComparison.hom.app K))]
  change γ₁.app ((SchemeDerivedCategory.Q U.left).obj
      (R.resolution.obj K)) =
    γ₂.app ((SchemeDerivedCategory.Q U.left).obj (R.resolution.obj K))
  apply (cancel_mono (R.counit.app (R.resolution.obj K))).mp
  simpa only [NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app] using!
    NatTrans.congr_app hγ (R.resolution.obj K)

/-- A pullback-acyclic resolution constructs the genuine left-derived
pullback universal property. -/
theorem isLeftDerived (R : PullbackAcyclicResolution f) :
    R.derivedFunctor.IsLeftDerivedFunctor R.counit
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)) where
  isRightKanExtension := by
    refine ⟨⟨?_⟩⟩
    refine IsTerminal.ofUniqueHom (fun E ↦
      CostructuredArrow.homMk (R.lift E.left E.hom) (R.lift_fac E.left E.hom)) ?_
    intro E m
    apply CostructuredArrow.hom_ext
    apply R.counit_hom_ext
    exact (CostructuredArrow.w m).trans (R.lift_fac E.left E.hom).symm

/-- Package a functorial pullback-acyclic resolution as the arbitrary
left-derived pullback interface used by the relative-perfect moduli theory. -/
def toLeftDerivedPullback (R : PullbackAcyclicResolution f) :
    LeftDerivedPullback f where
  functor := R.derivedFunctor
  counit := R.counit
  isLeftDerived := R.isLeftDerived

/-- The functor obtained from the identity resolution for exact pullback is
canonically isomorphic to Mathlib's exact derived functor. -/
def exactComparison (f : T ⟶ U) [IsExactPullback f] :
    (ofExact f).derivedFunctor ≅ derivedPullback f :=
  (ofExact f).toLeftDerivedPullback.exactComparison

/-- The exact comparison intertwines the two transformations to ordinary
degreewise pullback. -/
@[reassoc]
lemma exactComparison_hom_counit (f : T ⟶ U) [IsExactPullback f] :
    CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left)
        (exactComparison f).hom ≫
      (derivedPullbackFactors f).hom =
        (ofExact f).counit := by
  letI : (derivedPullback f).IsLeftDerivedFunctor
      (derivedPullbackFactors f).hom
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)) :=
    (LeftDerivedPullback.ofExact f).isLeftDerived
  change CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left)
      (CategoryTheory.Functor.leftDerivedNatTrans (ofExact f).derivedFunctor
        (derivedPullback f) (ofExact f).counit
        (derivedPullbackFactors f).hom
        (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
        (𝟙 (complexPullback f ⋙ SchemeDerivedCategory.Q T.left))) ≫
    (derivedPullbackFactors f).hom = (ofExact f).counit
  simpa only [Category.comp_id] using
    (CategoryTheory.Functor.leftDerivedNatTrans_fac
      (ofExact f).derivedFunctor (derivedPullback f)
      (ofExact f).counit (derivedPullbackFactors f).hom
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
      (𝟙 (complexPullback f ⋙ SchemeDerivedCategory.Q T.left)))

end PullbackAcyclicResolution

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
