/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredTotalComplexAdjacent
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The Cech bicomplex of an injective resolution

Given a cover-shaped family `U` and an injective resolution `I` of an abelian sheaf `F`, this
file constructs the classical cohomological bicomplex

`C^{p,q} = Cech^p(U, I^q)`.

The Cech direction is the first direction and the resolution direction is the second.  We also
retain the augmentation induced by `F ⟶ I⁰`, and instantiate the column-filtered total-complex
spectral sequence constructed in
`DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredTotalComplex`.

The site here is a general `C : Type u` with `Category.{v} C`, and at the pinned Mathlib revision
abelian sheaves over such a site carry no `EnoughInjectives` instance.  Accordingly, the
construction takes an explicit `InjectiveResolution F`; it does not install its existence as an
axiom or typeclass.  The obstruction is smallness alone: over a small site Mathlib does derive
enough injectives, and
`DerivedAlgGeo.CategoryTheory.Sites.Cech.SmallSiteResolution` discharges the resolution
argument there.
-/

universe w vA uA a v u

open CategoryTheory Category Limits

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

noncomputable instance evalOp_additive
    {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A] :
    (evalOp.{w} C A).Additive where
  map_add := by
    intro X₀ Y₀ f g
    ext X
    apply Pi.hom_ext
    intro i
    dsimp [evalOp]
    rw [Pi.map_π, Preadditive.comp_add]
    symm
    let f' := fun j ↦ f.app (Opposite.op (X.unop.obj j))
    let g' := fun j ↦ g.app (Opposite.op (X.unop.obj j))
    exact (Preadditive.add_comp _ _ _ (Pi.map f') (Pi.map g') (Pi.π _ i)).trans (by
      simp [f', g'])

end CategoryTheory.Limits.FormalCoproduct

namespace CategoryTheory

variable {B D A : Type*} [Category* B] [Category* D] [Category* A] [Preadditive A]

instance whiskeringLeft_obj_additive (F : B ⥤ D) :
    ((Functor.whiskeringLeft B D A).obj F).Additive where
  map_add := by
    intros
    rfl

end CategoryTheory

namespace AlgebraicTopology

variable {A : Type a} [Category A] [Preadditive A]

instance cosimplicialObject_preadditive : Preadditive (CosimplicialObject A) := by
  dsimp only [CosimplicialObject]
  exact CategoryTheory.functorCategoryPreadditive

instance alternatingCofaceMapComplex_additive :
    (alternatingCofaceMapComplex A).Additive where
  map_add := by
    intros
    ext n
    rfl

end AlgebraicTopology

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

noncomputable instance cech_evalOp_additive :
    (Limits.FormalCoproduct.evalOp.{a} C AddCommGrpCat.{a}).Additive :=
  Limits.FormalCoproduct.evalOp_additive

instance cech_whiskeringLeft_additive
    (E : SimplicialObject (Limits.FormalCoproduct.{a} C)) :
    ((Functor.whiskeringLeft SimplexCategory
      (Limits.FormalCoproduct.{a} C)ᵒᵖ AddCommGrpCat.{a}).obj E.rightOp).Additive where
  map_add := by
    intros
    rfl

noncomputable instance cech_cosimplicialObjectFunctor_additive
    (E : SimplicialObject (Limits.FormalCoproduct.{a} C)) :
    (Limits.FormalCoproduct.cosimplicialObjectFunctor
      (A := AddCommGrpCat.{a}) E).Additive := by
  dsimp [Limits.FormalCoproduct.cosimplicialObjectFunctor]
  letI : (Limits.FormalCoproduct.evalOp.{a} C AddCommGrpCat.{a}).Additive :=
    cech_evalOp_additive
  letI : ((Functor.whiskeringLeft SimplexCategory
      (Limits.FormalCoproduct.{a} C)ᵒᵖ AddCommGrpCat.{a}).obj E.rightOp).Additive :=
    cech_whiskeringLeft_additive E
  constructor
  intro X Y f g
  change ((Functor.whiskeringLeft SimplexCategory
      (Limits.FormalCoproduct.{a} C)ᵒᵖ AddCommGrpCat.{a}).obj E.rightOp).map
        ((Limits.FormalCoproduct.evalOp.{a} C AddCommGrpCat.{a}).map (f + g)) = _
  rw [(Limits.FormalCoproduct.evalOp.{a} C AddCommGrpCat.{a}).map_add,
    ((Functor.whiskeringLeft SimplexCategory
      (Limits.FormalCoproduct.{a} C)ᵒᵖ AddCommGrpCat.{a}).obj E.rightOp).map_add]
  rfl

noncomputable instance cechComplexFunctor_additive (U : index → C) :
    (cechComplexFunctor (A := AddCommGrpCat.{a}) U).Additive := by
  dsimp [cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor]
  infer_instance

/-- Apply the Cech complex to the underlying presheaf of an abelian sheaf and extend its
`ℕ`-grading by zero to a `ℤ`-grading. -/
noncomputable def cechCochainFunctorInt (U : index → C) :
    Sheaf J AddCommGrpCat.{a} ⥤ CochainComplex AddCommGrpCat.{a} ℤ :=
  sheafToPresheaf J AddCommGrpCat.{a} ⋙
    cechComplexFunctor U ⋙
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{a})

noncomputable instance cechCochainFunctorInt_additive (U : index → C) :
    (cechCochainFunctorInt (J := J) U).Additive := by
  dsimp only [cechCochainFunctorInt]
  infer_instance

/-- Before flipping the two directions, applying the Cech-complex functor to an injective
resolution gives a complex in the resolution degree whose values are Cech complexes. -/
noncomputable def cechResolutionBicomplexUnflipped
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    HomologicalComplex₂ AddCommGrpCat.{a} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    I.cochainComplex

/-- The Cech bicomplex `C^{p,q} = Cech^p(U, I^q)`, with Cech degree first and resolution
degree second. -/
noncomputable def cechInjectiveBicomplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    HomologicalComplex₂ AddCommGrpCat.{a} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.flip (cechResolutionBicomplexUnflipped U I)

/-- The componentwise identification expressing the defining formula
`C^{p,q} = Cech^p(U, I^q)`. -/
noncomputable def cechInjectiveBicomplexXXIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F)
    (p q : ℤ) :
    ((cechInjectiveBicomplex U I).X p).X q ≅
      ((cechCochainFunctorInt U).obj (I.cochainComplex.X q)).X p :=
  Iso.refl _

/-- The bicomplex obtained from the Cech complex of `F`, placed in resolution degree zero.
It is the source of `cechInjectiveBicomplexAugmentation`. -/
noncomputable def cechInjectiveBicomplexAugmentationSource
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) :
    HomologicalComplex₂ AddCommGrpCat.{a} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.flip
    (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F))

/-- The augmentation of the Cech bicomplex induced by the injective-resolution map
`F ⟶ I⁰`. -/
noncomputable def cechInjectiveBicomplexAugmentation
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    cechInjectiveBicomplexAugmentationSource U F ⟶ cechInjectiveBicomplex U I :=
  (HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι')

/-- The total cochain complex of the Cech bicomplex.  Its cohomology is the intended abutment of
the column-filtration spectral sequence. -/
noncomputable def cechInjectiveTotalComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{a} ℤ :=
  (cechInjectiveBicomplex U I).total (ComplexShape.up ℤ)

/-- The canonical map from filtration stage `p` into the total Cech complex. -/
noncomputable def cechInjectiveFilteredToTotal
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) (p : ℤ) :
    (HomologicalComplex₂.columnFilteredTotalComplex
      (cechInjectiveBicomplex U I)).obj p ⟶ cechInjectiveTotalComplex U I :=
  HomologicalComplex₂.columnFilteredTotalι (cechInjectiveBicomplex U I) p

/-- The filtration-stage maps to the total Cech complex, packaged with their compatibility. -/
noncomputable def cechInjectiveFilteredToTotalNat
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    HomologicalComplex₂.columnFilteredTotalComplex (cechInjectiveBicomplex U I) ⟶
      (Functor.const ℤ).obj (cechInjectiveTotalComplex U I) :=
  HomologicalComplex₂.columnFilteredTotalιNat (cechInjectiveBicomplex U I)

/-- The abelian spectral object associated to the column-filtered Cech total complex. -/
noncomputable def cechInjectiveSpectralObject
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    Abelian.SpectralObject AddCommGrpCat.{a} ℤ :=
  HomologicalComplex₂.columnFilteredTotalSpectralObject (cechInjectiveBicomplex U I)

/-- The `E₂` cohomological spectral sequence of the Cech bicomplex of an explicit injective
resolution. -/
noncomputable def cechInjectiveSpectralSequence
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    SpectralSequence AddCommGrpCat.{a}
      (fun r ↦ ComplexShape.up' (⟨r - 1, 2 - r⟩ : ℤ × ℤ)) 2 :=
  (cechInjectiveSpectralObject U I).spectralSequence
    Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt

/-- The formal initial-page computation: an object on page `2` is the homology of the adjacent
filtration layer selected by the stages `-p - 1 ≤ -p`. -/
noncomputable def cechInjectiveInitialPageXIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F)
    (p q : ℤ) :
    ((cechInjectiveSpectralSequence U I).page 2).X (p, q) ≅
      ((cechInjectiveSpectralObject U I).H (p + q)).obj
        (ComposableArrows.mk₁ (homOfLE (show
          HomologicalComplex₂.columnFiltrationIndex (p + 1) ≤
            HomologicalComplex₂.columnFiltrationIndex p by
              simp [HomologicalComplex₂.columnFiltrationIndex]))) :=
  (cechInjectiveSpectralObject U I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt (p, q)
      (HomologicalComplex₂.columnFiltrationIndex (p + 1))
      (HomologicalComplex₂.columnFiltrationIndex p) (by
        dsimp [Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt,
          HomologicalComplex₂.columnFiltrationIndex]
        omega)
      (by simp [HomologicalComplex₂.columnFiltrationIndex]) (p + q) rfl

/-- The adjacent filtered-total mapping cone contributing Cech column `p` to the initial page. -/
noncomputable def cechInjectiveAdjacentLayerComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F)
    (p : ℤ) : CochainComplex AddCommGrpCat.{a} ℤ :=
  HomologicalComplex₂.columnFilteredAdjacentLayerComplex
    (cechInjectiveBicomplex U I) p

/-- The spectral object's adjacent-layer term is ordinary homology of the corresponding mapping
cone. -/
noncomputable def cechInjectiveAdjacentLayerHomologyIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F)
    (p q : ℤ) :
    ((cechInjectiveSpectralObject U I).H (p + q)).obj
        (ComposableArrows.mk₁ (homOfLE (show
          HomologicalComplex₂.columnFiltrationIndex (p + 1) ≤
            HomologicalComplex₂.columnFiltrationIndex p by
              simp [HomologicalComplex₂.columnFiltrationIndex]))) ≅
      (cechInjectiveAdjacentLayerComplex U I p).homology (p + q) := by
  dsimp [cechInjectiveSpectralObject,
    HomologicalComplex₂.columnFilteredTotalSpectralObject,
    HomotopyCategory.filteredComplexSpectralObject,
    CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor,
    HomotopyCategory.spectralObjectMappingCone,
    HomotopyCategory.composableArrowsFunctor,
    cechInjectiveAdjacentLayerComplex,
    HomologicalComplex₂.columnFilteredAdjacentLayerComplex]
  change ((HomotopyCategory.quotient AddCommGrpCat.{a} (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor AddCommGrpCat.{a}
        (ComplexShape.up ℤ) (p + q)).obj
      (cechInjectiveAdjacentLayerComplex U I p)) ≅ _
  exact (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{a}
    (ComplexShape.up ℤ) (p + q)).app _

/-- The initial page of the column-filtration spectral sequence is vertical homology of the fixed
Cech column: `E₂^{p,q} ≅ H^q(C^{p,*})`. -/
noncomputable def cechInjectiveInitialPageColumnHomologyIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F)
    (p q : ℤ) :
    ((cechInjectiveSpectralSequence U I).page 2).X (p, q) ≅
      ((cechInjectiveBicomplex U I).X p).homology q :=
  cechInjectiveInitialPageXIso U I p q ≪≫
    cechInjectiveAdjacentLayerHomologyIso U I p q ≪≫
    HomologicalComplex₂.columnFilteredAdjacentLayerHomologyIso
      (cechInjectiveBicomplex U I) p (p + q) ≪≫
    (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{a}
      (-p) (p + q) q (by omega)).app ((cechInjectiveBicomplex U I).X p)

end CategoryTheory.Sheaf
