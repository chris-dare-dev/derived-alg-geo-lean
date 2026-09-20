/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Unbounded

/-!
# A left-derived tensor interface on scheme-module complexes

This module owns the localization-facing interface for the unbounded tensor product.  It does not
assert a monoidal structure on either complexes or the derived category.

There are two tempting routes which are deliberately recorded here as dead ends.  First,
`MorphismProperty.IsMonoidal W` (see
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:44`) requires whiskering every
`W`-morphism on the left by every object.  For quasi-isomorphisms this is false: tensoring the
quasi-isomorphism `[𝒪 →ˢ 𝒪] → 𝒪/s` with `𝒪/s` produces homology in two degrees.  Thus
`IsMonoidal quasiIso` is neither proved nor carried as a field here; K-flat replacement exists
precisely because this naive localization-descent route is unavailable.  In particular, the
dependent `functorMonoidalOfComp` route (`Localization/Monoidal/Functor.lean:134`) is unavailable
too, since it requires a monoidal localized functor.

Second, `HomologicalComplex.monoidalCategory`
(`Mathlib/Algebra/Homology/Monoidal.lean:274-281`) requires
`[∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]`.  For `I = ℤ` this asks for
coproducts over countably infinite anti-diagonals, whereas `Coh X` has only finite biproducts.
Mathlib's worked example in that file is `ChainComplex D ℕ`, whose anti-diagonals are finite;
there is no ℤ-indexed instance at this pin.  Accordingly no declaration below asserts either
of those dead routes.

`TensorAcyclicResolution` is a tensor-specific interface around the already-existing generic
K-flat localization construction.  Its two resolved-comparison fields are intentional: a
generic two-sided K-flat replacement proves the localized bifunctor, but does not by itself make
the comparison for an arbitrary fixed, non-K-flat factor invertible after resolving only the
other factor.  The missing comparison is therefore a hypothesis, not a marker or an axiom.
-/

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The complexes used by the unbounded scheme tensor interface. -/
abbrev SchemeTensorComplex (X : Scheme.{u}) := CochainComplex X.Modules ℤ

/-- The quasi-isomorphisms used by the unbounded scheme tensor interface. -/
abbrev SchemeTensorQuasiIso (X : Scheme.{u}) :
    MorphismProperty (SchemeTensorComplex X) :=
  HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)

/-- A tensor-acyclic replacement of complexes of `𝒪_X`-modules.

The first four fields are the functorial replacement, its quasi-isomorphic comparison, and the
two-sided localization-inversion datum needed by `Localization.lift₂`.  The last two fields are
the one-sided acyclicity needed for the two fixed-argument left-derived universal properties.
They are stronger than the generic `KFlatResolution` fields in exactly the place where a fixed
arbitrary tensor factor need not preserve quasi-isomorphisms. -/
structure TensorAcyclicResolution (X : Scheme.{u}) where
  /-- Functorial replacement of complexes. -/
  resolution : SchemeTensorComplex X ⥤ SchemeTensorComplex X
  /-- Comparison from the replacement to the original complex. -/
  comparison : resolution ⟶ 𝟭 (SchemeTensorComplex X)
  /-- Every comparison component is a quasi-isomorphism. -/
  comparison_quasiIso (K : SchemeTensorComplex X) :
    SchemeTensorQuasiIso X (comparison.app K)
  /-- Resolving both inputs makes total tensor invert quasi-isomorphisms after localization. -/
  tensor_inverts :
    MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
      (resolution ⋙ Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringLeft _ _ _).obj resolution ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))
  /-- The comparison is acyclic for a fixed first argument after resolving the second twice. -/
  left_resolved_comparison_isIso (K L : SchemeTensorComplex X) :
    IsIso ((SchemeDerivedCategory.Q X).map
      (((Scheme.Modules.totalTensor X).map (comparison.app K)).app
          (resolution.obj (resolution.obj L)) ≫
        ((Scheme.Modules.totalTensor X).obj K).map
          (comparison.app (resolution.obj L))))
  /-- The comparison is acyclic for a fixed second argument after resolving the first. -/
  right_resolved_comparison_isIso (K L : SchemeTensorComplex X) :
    IsIso ((SchemeDerivedCategory.Q X).map
      (((Scheme.Modules.totalTensor X).map (comparison.app (resolution.obj K))).app
          (resolution.obj L) ≫
        ((Scheme.Modules.totalTensor X).obj (resolution.obj K)).map
          (comparison.app L)))

namespace TensorAcyclicResolution

variable {X : Scheme.{u}}

/-- The resolved tensor functor belonging to an acyclic resolution. -/
def resolvedTensor (R : TensorAcyclicResolution X) :
    SchemeTensorComplex X ⥤ SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
  R.resolution ⋙ Scheme.Modules.totalTensor X ⋙
    (Functor.whiskeringLeft _ _ _).obj R.resolution ⋙
    (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)

/-- The comparison component with the identity functor normalized. -/
def comparisonApp (R : TensorAcyclicResolution X) (K : SchemeTensorComplex X) :
    R.resolution.obj K ⟶ K :=
  R.comparison.app K

/-- Naturality of the normalized replacement-to-identity comparison. -/
@[reassoc]
lemma comparisonApp_naturality (R : TensorAcyclicResolution X)
    {K L : SchemeTensorComplex X} (f : K ⟶ L) :
    R.resolution.map f ≫ R.comparisonApp L = R.comparisonApp K ≫ f := by
  simpa only [comparisonApp, Functor.id_obj, Functor.id_map] using R.comparison.naturality f

/-- The comparison from resolved total tensor to ordinary total tensor followed by localization. -/
def resolvedTensorComparison (R : TensorAcyclicResolution X) :
    R.resolvedTensor ⟶
      Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X) where
  app K :=
    { app := fun L ↦ (SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
            (R.resolution.obj L) ≫
          ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp L))
      naturality := fun {L M} f ↦ by
        change (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).obj (R.resolution.obj K)).map
                (R.resolution.map f)) ≫
            (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
                  (R.resolution.obj M) ≫
                ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp M)) =
          (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
                  (R.resolution.obj L) ≫
                ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp L)) ≫
            (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).obj K).map f)
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        simp only [Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp]
        rw [R.comparisonApp_naturality] }
  naturality {K L} f := by
    ext M
    change (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map (R.resolution.map f)).app
              (R.resolution.obj M)) ≫
        (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map (R.comparisonApp L)).app
              (R.resolution.obj M) ≫
            ((Scheme.Modules.totalTensor X).obj L).map (R.comparisonApp M)) =
      (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
              (R.resolution.obj M) ≫
            ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp M)) ≫
        (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map f).app M)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
      R.comparisonApp_naturality]
    simp only [Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [(Scheme.Modules.totalTensor X).map f |>.naturality]

/-- The bifunctor on the derived category obtained by resolving both variables. -/
def derivedTensor (R : TensorAcyclicResolution X) :
    SchemeDerivedCategory X ⥤ SchemeDerivedCategory X ⥤ SchemeDerivedCategory X :=
  Localization.lift₂ R.resolvedTensor R.tensor_inverts
    (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X)

/-- Pulling the derived tensor back to complexes recovers the resolved tensor. -/
def derivedTensorFactors (R : TensorAcyclicResolution X) :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
          R.derivedTensor ≅ R.resolvedTensor := by
  change
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
        (Localization.lift₂ R.resolvedTensor R.tensor_inverts
          (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X)) ≅ R.resolvedTensor
  exact Localization.Lifting₂.iso (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X)
    (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X) R.resolvedTensor
    (Localization.lift₂ R.resolvedTensor R.tensor_inverts
      (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X))

/-- The counit from the localized derived tensor to degreewise total tensor. -/
def counit (R : TensorAcyclicResolution X) :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
          R.derivedTensor ⟶
      Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X) :=
  R.derivedTensorFactors.hom ≫ R.resolvedTensorComparison

/-- The localization comparison induced by the quasi-isomorphic replacement. -/
private def localizationComparison (R : TensorAcyclicResolution X) :
    R.resolution ⋙ SchemeDerivedCategory.Q X ≅ SchemeDerivedCategory.Q X := by
  refine NatIso.ofComponents
    (fun K ↦ by
      exact @CategoryTheory.asIso _ _ _ _ _
        (Localization.inverts (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X)
          (R.comparison.app K) (R.comparison_quasiIso K))) ?_
  intro K L f
  change (SchemeDerivedCategory.Q X).map (R.resolution.map f) ≫
      (SchemeDerivedCategory.Q X).map (R.comparison.app L) =
    (SchemeDerivedCategory.Q X).map (R.comparison.app K) ≫
      (SchemeDerivedCategory.Q X).map f
  have hc : R.resolution.map f ≫ R.comparison.app L =
      R.comparison.app K ≫ f := by
    simpa only [Functor.id_map] using! R.comparison.naturality f
  simpa only [← Functor.map_comp] using!
    congrArg (fun k ↦ (SchemeDerivedCategory.Q X).map k) hc

private def resolvedCounitIso (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K))) :
    R.resolution ⋙ (SchemeDerivedCategory.Q X) ⋙ G ≅ R.resolution ⋙ F := by
  refine NatIso.ofComponents
    (fun K ↦ @CategoryTheory.asIso _ _ _ _ _ (hα K)) ?_
  intro K L f
  change (SchemeDerivedCategory.Q X ⋙ G).map (R.resolution.map f) ≫
      α.app (R.resolution.obj L) =
    α.app (R.resolution.obj K) ≫ F.map (R.resolution.map f)
  exact α.naturality (R.resolution.map f)

private def whiskeredLift (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    (SchemeDerivedCategory.Q X) ⋙ H ⟶ (SchemeDerivedCategory.Q X) ⋙ G :=
  (Functor.isoWhiskerRight (localizationComparison R) H).inv ≫
    (Functor.associator R.resolution (SchemeDerivedCategory.Q X) H).hom ≫
    Functor.whiskerLeft R.resolution β ≫
    (resolvedCounitIso R α hα).inv ≫
    (Functor.isoWhiskerRight (localizationComparison R) G).hom

private def lift (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) : H ⟶ G := by
  letI := Localization.full_whiskeringLeft
    (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X) (SchemeDerivedCategory X)
  exact ((Functor.whiskeringLeft _ _ _).obj (SchemeDerivedCategory.Q X)).preimage
    (whiskeredLift R α hα H β)

@[reassoc]
private lemma whiskerLeft_lift (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    Functor.whiskerLeft (SchemeDerivedCategory.Q X) (lift R α hα H β) =
      whiskeredLift R α hα H β := by
  letI := Localization.full_whiskeringLeft
    (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X) (SchemeDerivedCategory X)
  apply ((Functor.whiskeringLeft _ _ _).obj (SchemeDerivedCategory.Q X)).map_preimage

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma whiskeredLift_fac (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    whiskeredLift R α hα H β ≫ α = β := by
  ext K
  change (whiskeredLift R α hα H β).app K ≫ α.app K = β.app K
  apply (cancel_epi (H.map ((localizationComparison R).hom.app K))).mp
  have hβ : H.map ((SchemeDerivedCategory.Q X).map (R.comparison.app K)) ≫
      β.app K = β.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simpa only [Functor.comp_map, Functor.id_obj] using!
      β.naturality (R.comparison.app K)
  have hα' : G.map ((SchemeDerivedCategory.Q X).map (R.comparison.app K)) ≫
      α.app K = α.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simpa only [Functor.comp_map, Functor.id_obj] using!
      α.naturality (R.comparison.app K)
  have hH : H.map ((localizationComparison R).hom.app K) ≫
      H.map ((localizationComparison R).inv.app K) = 𝟙 _ := by
    rw [← H.map_comp, (localizationComparison R).hom_inv_id_app, H.map_id]
  have hloc : H.map ((localizationComparison R).hom.app K) ≫
      (whiskeredLift R α hα H β).app K =
        β.app (R.resolution.obj K) ≫
          (resolvedCounitIso R α hα).inv.app K ≫
            G.map ((localizationComparison R).hom.app K) := by
    dsimp [whiskeredLift]
    rw [← Category.assoc, hH, Category.id_comp]
    simp
  have hlocComparison :
      G.map ((localizationComparison R).hom.app K) ≫ α.app K =
        α.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simpa only [localizationComparison, NatIso.ofComponents_hom_app,
      CategoryTheory.asIso_hom,
      Functor.comp_obj] using hα'
  have hcounit :
      (resolvedCounitIso R α hα).inv.app K ≫ α.app (R.resolution.obj K) = 𝟙 _ := by
    dsimp [resolvedCounitIso]
    simp
  have hlocα :
      H.map ((localizationComparison R).hom.app K) ≫
          ((whiskeredLift R α hα H β).app K ≫ α.app K) =
        (β.app (R.resolution.obj K) ≫
          (resolvedCounitIso R α hα).inv.app K ≫
            G.map ((localizationComparison R).hom.app K)) ≫ α.app K := by
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ α.app K) hloc
  have hrest :
      (β.app (R.resolution.obj K) ≫
        (resolvedCounitIso R α hα).inv.app K ≫
          G.map ((localizationComparison R).hom.app K)) ≫ α.app K =
        β.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simp only [Category.assoc]
    rw [hlocComparison]
    rw [← Category.assoc ((resolvedCounitIso R α hα).inv.app K)
      (α.app (R.resolution.obj K)) (F.map (R.comparison.app K))]
    rw [hcounit, Category.id_comp]
  rw [hlocα, hrest]
  simpa only [localizationComparison, NatIso.ofComponents_hom_app,
    CategoryTheory.asIso_hom,
    Functor.comp_obj] using hβ.symm

@[reassoc]
private lemma lift_fac (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    Functor.whiskerLeft (SchemeDerivedCategory.Q X) (lift R α hα H β) ≫ α = β := by
  rw [whiskerLeft_lift, whiskeredLift_fac]

private lemma counit_hom_ext (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (γ₁ γ₂ : H ⟶ G)
    (hγ : Functor.whiskerLeft (SchemeDerivedCategory.Q X) γ₁ ≫ α =
      Functor.whiskerLeft (SchemeDerivedCategory.Q X) γ₂ ≫ α) :
    γ₁ = γ₂ := by
  letI := Localization.faithful_whiskeringLeft
    (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X) (SchemeDerivedCategory X)
  apply ((Functor.whiskeringLeft _ _ _).obj (SchemeDerivedCategory.Q X)).map_injective
  ext K
  change γ₁.app ((SchemeDerivedCategory.Q X).obj K) =
    γ₂.app ((SchemeDerivedCategory.Q X).obj K)
  rw [← cancel_epi (H.map ((localizationComparison R).hom.app K))]
  rw [γ₁.naturality, γ₂.naturality]
  rw [cancel_mono (G.map ((localizationComparison R).hom.app K))]
  change γ₁.app ((SchemeDerivedCategory.Q X).obj (R.resolution.obj K)) =
    γ₂.app ((SchemeDerivedCategory.Q X).obj (R.resolution.obj K))
  apply (cancel_mono (α.app (R.resolution.obj K))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using!
    NatTrans.congr_app hγ (R.resolution.obj K)

/-- The fixed-argument universal property supplied by a resolved counit. -/
private theorem isLeftDerived_of_resolved (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K))) :
    G.IsLeftDerivedFunctor α (SchemeTensorQuasiIso X) where
  isRightKanExtension := by
    refine ⟨⟨?_⟩⟩
    refine IsTerminal.ofUniqueHom (fun E ↦
      CostructuredArrow.homMk (lift R α hα E.left E.hom)
        (lift_fac R α hα E.left E.hom)) ?_
    intro E m
    apply CostructuredArrow.hom_ext
    apply counit_hom_ext R α hα
    exact (CostructuredArrow.w m).trans (lift_fac R α hα E.left E.hom).symm

end TensorAcyclicResolution

/-- A genuine bifunctorial left-derived tensor on the unbounded scheme-derived category.

The two universal-property fields are deliberately indexed by complexes representing the fixed
argument.  This makes the comparison against the actual degreewise tensor visible and prevents
an unrelated bifunctor from satisfying the interface. -/
structure LeftDerivedTensor (X : Scheme.{u}) where
  /-- The derived tensor bifunctor. -/
  functor : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X ⥤ SchemeDerivedCategory X
  /-- Comparison from localization followed by the derived tensor to degreewise total tensor. -/
  counit :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj functor ⟶
      Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)
  /-- The fixed-first-argument left-derived universal property. -/
  isLeftDerived_left (K : SchemeTensorComplex X) :
    (functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
      (counit.app K) (SchemeTensorQuasiIso X)
  /-- The fixed-second-argument left-derived universal property. -/
  isLeftDerived_right (L : SchemeTensorComplex X) :
    (functor.flip.obj ((SchemeDerivedCategory.Q X).obj L)).IsLeftDerivedFunctor
      (counit.flipApp L) (SchemeTensorQuasiIso X)

namespace TensorAcyclicResolution

variable {X : Scheme.{u}}

/-- A tensor-acyclic resolution constructs the bifunctor and proves both fixed-argument
universal properties. -/
def toLeftDerivedTensor (R : TensorAcyclicResolution X) : LeftDerivedTensor X where
  functor := R.derivedTensor
  counit := R.counit
  isLeftDerived_left K := by
    refine isLeftDerived_of_resolved R (R.counit.app K) ?_
    intro L
    change IsIso
      (((R.derivedTensorFactors.hom.app K).app (R.resolution.obj L)) ≫
        (R.resolvedTensorComparison.app K).app (R.resolution.obj L))
    haveI : IsIso ((R.derivedTensorFactors.hom.app K).app (R.resolution.obj L)) := by
      infer_instance
    haveI : IsIso ((R.resolvedTensorComparison.app K).app (R.resolution.obj L)) := by
      change IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map (R.comparison.app K)).app
            (R.resolution.obj (R.resolution.obj L)) ≫
          ((Scheme.Modules.totalTensor X).obj K).map
            (R.comparison.app (R.resolution.obj L))))
      exact R.left_resolved_comparison_isIso K L
    infer_instance
  isLeftDerived_right L := by
    let α : SchemeDerivedCategory.Q X ⋙
        R.derivedTensor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ⟶
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)).flip.obj L := by
      exact R.counit.flipApp L
    refine isLeftDerived_of_resolved R α ?_
    intro K
    change IsIso ((R.counit.app (R.resolution.obj K)).app L)
    change IsIso
      (((R.derivedTensorFactors.hom.app (R.resolution.obj K)).app L) ≫
        (R.resolvedTensorComparison.app (R.resolution.obj K)).app L)
    haveI : IsIso ((R.derivedTensorFactors.hom.app (R.resolution.obj K)).app L) := by
      infer_instance
    haveI : IsIso ((R.resolvedTensorComparison.app (R.resolution.obj K)).app L) := by
      change IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map
            (R.comparison.app (R.resolution.obj K))).app (R.resolution.obj L) ≫
          ((Scheme.Modules.totalTensor X).obj (R.resolution.obj K)).map
            (R.comparison.app L)))
      exact R.right_resolved_comparison_isIso K L
    infer_instance

end TensorAcyclicResolution

namespace LeftDerivedTensor

variable {X : Scheme.{u}}

/-- The canonical comparison of two left-derived tensors, for a fixed complex representative. -/
noncomputable def leftDerivedUnique (P Q : LeftDerivedTensor X)
    (K : SchemeTensorComplex X) :
    P.functor.obj ((SchemeDerivedCategory.Q X).obj K) ≅
      Q.functor.obj ((SchemeDerivedCategory.Q X).obj K) := by
  let F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
    (Scheme.Modules.totalTensor X).obj K ⋙ SchemeDerivedCategory.Q X
  let αP : SchemeDerivedCategory.Q X ⋙
      P.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact P.counit.app K
  let αQ : SchemeDerivedCategory.Q X ⋙
      Q.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact Q.counit.app K
  letI :
      (P.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αP (SchemeTensorQuasiIso X) := by
    exact P.isLeftDerived_left K
  letI :
      (Q.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αQ (SchemeTensorQuasiIso X) := by
    exact Q.isLeftDerived_left K
  exact CategoryTheory.Functor.leftDerivedUnique
    (Q.functor.obj ((SchemeDerivedCategory.Q X).obj K))
    (P.functor.obj ((SchemeDerivedCategory.Q X).obj K))
    αP αQ (SchemeTensorQuasiIso X)

/-- The analogous comparison after fixing the second argument. -/
noncomputable def leftDerivedUnique_flip (P Q : LeftDerivedTensor X)
    (L : SchemeTensorComplex X) :
    P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ≅
      Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) := by
  let F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
    (Scheme.Modules.totalTensor X ⋙
      (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)).flip.obj L
  let αP : SchemeDerivedCategory.Q X ⋙
      P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ⟶ F := by
    exact P.counit.flipApp L
  let αQ : SchemeDerivedCategory.Q X ⋙
      Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ⟶ F := by
    exact Q.counit.flipApp L
  letI :
      (P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L)).IsLeftDerivedFunctor
        αP (SchemeTensorQuasiIso X) := by
    exact P.isLeftDerived_right L
  letI :
      (Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L)).IsLeftDerivedFunctor
        αQ (SchemeTensorQuasiIso X) := by
    exact Q.isLeftDerived_right L
  exact CategoryTheory.Functor.leftDerivedUnique
    (Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L))
    (P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L))
    αP αQ (SchemeTensorQuasiIso X)

end LeftDerivedTensor

namespace TensorAcyclicResolution

variable {X : Scheme.{u}}

/-- The identity resolution is available only when the supplied tensor already inverts both
variables' quasi-isomorphisms after localization. -/
def ofExact (X : Scheme.{u})
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))) :
    TensorAcyclicResolution X where
  resolution := 𝟭 (SchemeTensorComplex X)
  comparison := 𝟙 (𝟭 (SchemeTensorComplex X))
  comparison_quasiIso K := by
    change HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ) (𝟙 _)
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  tensor_inverts := by
    change MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
      (Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))
    exact hTensor
  left_resolved_comparison_isIso K L := by
    simp only [Functor.id_obj, NatTrans.id_app]
    infer_instance
  right_resolved_comparison_isIso K L := by
    simp only [Functor.id_obj, NatTrans.id_app]
    infer_instance

/-- Compatibility name for the exact identity resolution. -/
abbrev identity (X : Scheme.{u})
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))) :
    TensorAcyclicResolution X :=
  ofExact X hTensor

/-- Adapt the generic `SchemeKFlatResolution`.  The explicit left acyclicity hypothesis is the
additional comparison that generic K-flatness does not provide for an arbitrary fixed factor. -/
def ofKFlat (R : SchemeKFlatResolution X)
    (hleft : ∀ K L : SchemeTensorComplex X,
      IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map (R.comparison.app K)).app
            (R.resolution.obj (R.resolution.obj L)) ≫
          ((Scheme.Modules.totalTensor X).obj K).map
            (R.comparison.app (R.resolution.obj L))))) :
    TensorAcyclicResolution X where
  resolution := R.resolution
  comparison := R.comparison
  comparison_quasiIso := R.comparison_quasiIso
  tensor_inverts := by
    simpa only [resolvedTensor, CategoryTheory.KFlatResolution.resolvedTensor] using
      R.resolvedTensor_inverts
  left_resolved_comparison_isIso := hleft
  right_resolved_comparison_isIso K L := by
    haveI h₁ : IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map
            (R.comparison.app (R.resolution.obj K))).app
          (R.resolution.obj L))) := by
      change IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).flip.obj (R.resolution.obj L)).map
          (R.comparison.app (R.resolution.obj K))))
      exact (R.isKFlat L).tensorRight_inverts _
        (R.comparison_quasiIso (R.resolution.obj K))
    haveI h₂ : IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).obj (R.resolution.obj K)).map
          (R.comparison.app L))) :=
      (R.isKFlat K).tensorLeft_inverts
        (R.comparison.app L) (R.comparison_quasiIso L)
    change IsIso ((SchemeDerivedCategory.Q X).map (_ ≫ _))
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' h₁ h₂

/-- A general resolution and the exact identity construction agree by the fixed-argument
`Functor.leftDerivedUnique` comparison. -/
noncomputable def exactComparison (R : TensorAcyclicResolution X)
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)))
    (K : SchemeTensorComplex X) :
    R.toLeftDerivedTensor.functor.obj ((SchemeDerivedCategory.Q X).obj K) ≅
      (ofExact X hTensor).toLeftDerivedTensor.functor.obj
        ((SchemeDerivedCategory.Q X).obj K) :=
  LeftDerivedTensor.leftDerivedUnique R.toLeftDerivedTensor
    (ofExact X hTensor).toLeftDerivedTensor K

end TensorAcyclicResolution

end

end AlgebraicGeometry.DerivedCategory
