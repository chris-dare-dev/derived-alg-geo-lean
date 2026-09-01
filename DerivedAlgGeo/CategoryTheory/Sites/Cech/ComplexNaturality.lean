/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.GlobalComparison
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.InjectiveResolutionNaturality
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.ExtendHomologyNaturality
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.TotalFlipNaturality

/-!
# The Čech comparison as a construction on complexes of sheaves

Every step of the Čech-to-derived comparison built in
`DerivedAlgGeo.CategoryTheory.Sites.Cech.GlobalComparison` reads its injective
resolution `I` only through the cochain complex `I.cochainComplex`. This file makes that
dependence explicit: each construction is restated for an arbitrary cochain complex of sheaves,
agreeing with the original by definition, and each is shown to commute with an arbitrary
morphism of such complexes.

This is the content that the bare `Nonempty (_ ≃+ _)` form of the comparison cannot supply.
A `k`-action on cohomology arrives as the map induced by a single endomorphism of the sheaf,
so `k`-linearity of the comparison is exactly the statement that the comparison commutes with
the maps induced by that endomorphism — which is what the naturality squares below record.
-/

universe h a u

open CategoryTheory Category Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf

set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

/-- Sections over `X`, applied degreewise to a cochain complex of sheaves. -/
noncomputable abbrev sectionsComplexUnlifted (X : C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    CochainComplex AddCommGrpCat.{a} ℤ :=
  ((sectionsAtFunctorUnlifted X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The Čech bicomplex `C^{p,q} = Čech^p(U, K^q)` of a cochain complex of sheaves. -/
noncomputable abbrev cechBicomplexOfComplex (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{a} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.flip
    (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The injective Čech bicomplex reads its resolution only through the underlying complex. -/
lemma cechInjectiveBicomplex_eq_cechBicomplexOfComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    cechInjectiveBicomplex U I = cechBicomplexOfComplex U I.cochainComplex :=
  rfl

omit [HasFiniteProducts C] in
/-- The sections complex of an injective resolution reads it only through the underlying
complex. -/
lemma injectiveResolutionSectionsComplexUnlifted_eq
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplexUnlifted X I =
      sectionsComplexUnlifted X I.cochainComplex :=
  rfl

variable {K L : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ}

/-- A morphism of cochain complexes of sheaves induces a morphism of Čech bicomplexes. -/
noncomputable abbrev cechBicomplexMap (U : index → C) (Φ : K ⟶ L) :
    cechBicomplexOfComplex U K ⟶ cechBicomplexOfComplex U L :=
  (HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).map Φ)

/-- A morphism of cochain complexes of sheaves induces a morphism of sections complexes. -/
noncomputable abbrev sectionsComplexMap (X : C) (Φ : K ⟶ L) :
    sectionsComplexUnlifted X K ⟶ sectionsComplexUnlifted X L :=
  ((sectionsAtFunctorUnlifted X).mapHomologicalComplex (ComplexShape.up ℤ)).map Φ

/-- Global sections of a complex of sheaves map to its degree-zero Čech column. -/
noncomputable def sectionsToCechZeroColumn
    {T : C} (hT : IsTerminal T) (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    sectionsComplexUnlifted T K ⟶ (cechBicomplexOfComplex U K).X 0 where
  f q := globalSectionsToCechZeroInt hT U (K.X q)
  comm' q r _ := globalSectionsToCechZeroInt_naturality hT U (K.d q r)

/-- The degree-zero Čech column map of an injective resolution reads it only through the
underlying complex. -/
lemma injectiveResolutionSectionsToCechZeroColumn_eq
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsToCechZeroColumn hT U I =
      sectionsToCechZeroColumn hT U I.cochainComplex :=
  rfl

/-- The degree-zero Čech column map commutes with an arbitrary morphism of complexes. -/
lemma sectionsToCechZeroColumn_naturality
    {T : C} (hT : IsTerminal T) (U : index → C) (Φ : K ⟶ L) :
    sectionsComplexMap T Φ ≫ sectionsToCechZeroColumn hT U L =
      sectionsToCechZeroColumn hT U K ≫ (cechBicomplexMap U Φ).f 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact (globalSectionsToCechZeroInt_naturality hT U (Φ.f q)).symm

/-- The augmented row map from the global-sections complex, placed in Čech degree zero, to the
full Čech bicomplex of a cochain complex of sheaves. -/
noncomputable def sectionsToCechBicomplexMap
    {T : C} (hT : IsTerminal T) (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    HomologicalComplex₂.singleZeroBicomplex (sectionsComplexUnlifted T K) ⟶
      cechBicomplexOfComplex U K := by
  let A := sectionsComplexUnlifted T K
  let g := sectionsToCechZeroColumn hT U (index := index) K
  refine HomologicalComplex₂.homMk (fun pq ↦
    if hp : pq.1 = 0 then
      (HomologicalComplex₂.singleZeroXIso A pq.1 hp).hom.f pq.2 ≫ g.f pq.2 ≫
        (HomologicalComplex₂.XXIsoOfEq AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (cechBicomplexOfComplex U K) hp.symm rfl).hom
    else 0) ?_ ?_
  · intro p p' q hpp
    by_cases hp : p = 0
    · subst p
      have hp' : p' = 1 := by
        change 0 + 1 = p' at hpp
        omega
      subst p'
      simp only [dif_pos True.intro, dif_neg (by omega : ¬ (0 + 1 = (0 : ℤ))),
        comp_zero]
      rw [Category.assoc]
      change (HomologicalComplex₂.singleZeroXIso A 0 rfl).hom.f q ≫
        (globalSectionsToCechZeroInt hT U (K.X q) ≫
          ((cechCochainFunctorInt U).obj (K.X q)).d 0 1) = 0
      rw [globalSectionsToCechZeroInt_comp_d, comp_zero]
    · simp [hp, HomologicalComplex₂.singleZeroBicomplex]
  · intro p q q' hqq
    by_cases hp : p = 0
    · subst p
      simp only [dif_pos True.intro]
      exact (HomologicalComplex.Hom.comm
        ((HomologicalComplex₂.singleZeroXIso A 0 rfl).hom ≫ g) q q')
    · simp [hp]

/-- The augmented bicomplex map of an injective resolution reads it only through the underlying
complex. -/
lemma globalSectionsToCechBicomplexMap_eq
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    globalSectionsToCechBicomplexMap hT U I =
      sectionsToCechBicomplexMap hT U I.cochainComplex :=
  rfl

/-- The augmented bicomplex map commutes with an arbitrary morphism of complexes. -/
lemma sectionsToCechBicomplexMap_naturality
    {T : C} (hT : IsTerminal T) (U : index → C) (Φ : K ⟶ L) :
    (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{a} ℤ) 0).map
          (sectionsComplexMap T Φ) ≫ sectionsToCechBicomplexMap hT U L =
      sectionsToCechBicomplexMap hT U K ≫ cechBicomplexMap U Φ := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hp : p = 0
  · subst p
    have h := congrArg (fun m : sectionsComplexUnlifted T K ⟶
        (cechBicomplexOfComplex U L).X 0 => m.f q)
      (sectionsToCechZeroColumn_naturality hT U Φ)
    dsimp [sectionsToCechBicomplexMap, HomologicalComplex₂.singleZeroXIso,
      HomologicalComplex₂.XXIsoOfEq] at h ⊢
    have hs : ((CochainComplex.singleFunctor
          (CochainComplex AddCommGrpCat.{a} ℤ) 0).map (sectionsComplexMap T Φ)).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (sectionsComplexUnlifted T K)).hom ≫ sectionsComplexMap T Φ ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (sectionsComplexUnlifted T L)).inv :=
      HomologicalComplex.single_map_f_self (c := ComplexShape.up ℤ) 0 _
    rw [show (((CochainComplex.singleFunctor
        (CochainComplex AddCommGrpCat.{a} ℤ) 0).map (sectionsComplexMap T Φ)).f 0).f q =
          _ from congrArg (fun m => HomologicalComplex.Hom.f m q) hs]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    refine congrArg (fun m => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (sectionsComplexUnlifted T K)).hom.f q ≫ m) ?_
    simpa using h
  · apply IsZero.eq_of_src
    exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) q).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (sectionsComplexUnlifted T K) p hp)

/-- The global-sections complex maps to the Čech total complex of a cochain complex of
sheaves. -/
noncomputable def sectionsToCechTotalMap
    {T : C} (hT : IsTerminal T) (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    sectionsComplexUnlifted T K ⟶
      (cechBicomplexOfComplex U K).total (ComplexShape.up ℤ) :=
  (HomologicalComplex₂.singleZeroTotalIso (sectionsComplexUnlifted T K)).inv ≫
    ((HomologicalComplex₂.singleZeroBicomplex
      (sectionsComplexUnlifted T K)).totalFlipIso (ComplexShape.up ℤ)).inv ≫
    HomologicalComplex₂.total.map
      (HomologicalComplex₂.flipMap (sectionsToCechBicomplexMap hT U K))
      (ComplexShape.up ℤ) ≫
    ((cechBicomplexOfComplex U K).totalFlipIso (ComplexShape.up ℤ)).hom

/-- The comparison into the Čech total complex reads an injective resolution only through the
underlying complex. -/
lemma injectiveResolutionSectionsToCechTotalMap_eq
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsToCechTotalMap hT U I =
      sectionsToCechTotalMap hT U I.cochainComplex :=
  rfl

/-- The comparison into the Čech total complex commutes with an arbitrary morphism of
complexes. -/
lemma sectionsToCechTotalMap_naturality
    {T : C} (hT : IsTerminal T) (U : index → C) (Φ : K ⟶ L) :
    sectionsComplexMap T Φ ≫ sectionsToCechTotalMap hT U L =
      sectionsToCechTotalMap hT U K ≫
        HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ) := by
  dsimp only [sectionsToCechTotalMap]
  have h₁ : sectionsComplexMap T Φ ≫
        (HomologicalComplex₂.singleZeroTotalIso (sectionsComplexUnlifted T L)).inv =
      (HomologicalComplex₂.singleZeroTotalIso (sectionsComplexUnlifted T K)).inv ≫
        HomologicalComplex₂.total.map
          (HomologicalComplex₂.singleZeroBicomplexMap (sectionsComplexMap T Φ))
          (ComplexShape.up ℤ) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq,
      HomologicalComplex₂.singleZeroTotalIso_naturality]
  have h₂ : HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap
            (HomologicalComplex₂.singleZeroBicomplexMap (sectionsComplexMap T Φ)))
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap (sectionsToCechBicomplexMap hT U L))
          (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap (sectionsToCechBicomplexMap hT U K))
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap (cechBicomplexMap U Φ)) (ComplexShape.up ℤ) := by
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    congr 1
    exact ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (sectionsToCechBicomplexMap_naturality hT U Φ) |>.trans
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map_comp _ _))
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc,
    HomologicalComplex₂.totalFlipIso_inv_naturality_assoc, reassoc_of% h₂,
    Category.assoc, HomologicalComplex₂.totalFlipIso_naturality, Category.assoc]

section Augmentation

variable {F G : Sheaf J AddCommGrpCat.{a}}

/-- The bicomplex augmentation induced by an augmentation of a cochain complex of sheaves. -/
noncomputable abbrev cechAugmentationMap (U : index → C)
    (ε : (CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F ⟶ K) :
    cechBicomplexOfComplex U
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F) ⟶
      cechBicomplexOfComplex U K :=
  cechBicomplexMap U ε

/-- The augmentation source of the Čech bicomplex is the Čech bicomplex of the complex
concentrated in degree zero. -/
lemma cechInjectiveBicomplexAugmentationSource_eq (U : index → C)
    (F : Sheaf J AddCommGrpCat.{a}) :
    cechInjectiveBicomplexAugmentationSource U F =
      cechBicomplexOfComplex U
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F) :=
  rfl

/-- The augmentation of the Čech bicomplex of an injective resolution is the augmentation
induced by `I.ι'`. -/
lemma cechInjectiveBicomplexAugmentation_eq (U : index → C) (I : InjectiveResolution F) :
    cechInjectiveBicomplexAugmentation U I = cechAugmentationMap U I.ι' :=
  rfl

/-- The identification of the total complex of the augmentation source with the ordinary Čech
complex is natural in the sheaf. -/
lemma cechInjectiveBicomplexAugmentationSourceTotalIso_naturality
    (U : index → C) (φ : F ⟶ G) :
    HomologicalComplex₂.total.map
          (cechBicomplexMap U
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).map φ))
          (ComplexShape.up ℤ) ≫
        (cechInjectiveBicomplexAugmentationSourceTotalIso U G).hom =
      (cechInjectiveBicomplexAugmentationSourceTotalIso U F).hom ≫
        (cechCochainFunctorInt U).map φ := by
  dsimp only [cechInjectiveBicomplexAugmentationSourceTotalIso, Iso.trans_hom]
  rw [HomologicalComplex₂.totalFlipIso_naturality_assoc]
  simp only [HomologicalComplex₂.total.mapIso_hom, Category.assoc, Iso.app_hom]
  have hnat : ((cechCochainFunctorInt (J := J) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).map φ) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (cechCochainFunctorInt (J := J) U) (ComplexShape.up ℤ) 0).hom.app G =
    (HomologicalComplex.singleMapHomologicalComplex
        (cechCochainFunctorInt (J := J) U) (ComplexShape.up ℤ) 0).hom.app F ≫
      (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{a} ℤ) 0).map
        ((cechCochainFunctorInt U).map φ) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (cechCochainFunctorInt (J := J) U) (ComplexShape.up ℤ) 0).hom.naturality φ
  rw [← HomologicalComplex₂.total.map_comp_assoc, hnat,
    HomologicalComplex₂.total.map_comp_assoc]
  exact congrArg (fun m => (HomologicalComplex₂.totalFlipIso
        (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F))
        (ComplexShape.up ℤ)).hom ≫
      HomologicalComplex₂.total.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (cechCochainFunctorInt (J := J) U) (ComplexShape.up ℤ) 0).hom.app F)
        (ComplexShape.up ℤ) ≫ m)
    (HomologicalComplex₂.singleZeroTotalIso_naturality
      ((cechCochainFunctorInt U).map φ))

omit [HasSheafify J AddCommGrpCat.{a}] in
/-- The induced map of Čech bicomplexes is functorial. -/
lemma cechBicomplexMap_comp (U : index → C) {M : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ}
    (Φ : K ⟶ L) (Ψ : L ⟶ M) :
    cechBicomplexMap U (Φ ≫ Ψ) = cechBicomplexMap U Φ ≫ cechBicomplexMap U Ψ := by
  dsimp only [cechBicomplexMap]
  rw [Functor.map_comp, Functor.map_comp]

/-- Inverse form of `cechInjectiveBicomplexAugmentationSourceTotalIso_naturality`. -/
lemma cechInjectiveBicomplexAugmentationSourceTotalIso_inv_naturality
    (U : index → C) (φ : F ⟶ G) :
    (cechCochainFunctorInt U).map φ ≫
        (cechInjectiveBicomplexAugmentationSourceTotalIso U G).inv =
      (cechInjectiveBicomplexAugmentationSourceTotalIso U F).inv ≫
        HomologicalComplex₂.total.map
          (cechBicomplexMap U
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).map φ))
          (ComplexShape.up ℤ) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq,
    cechInjectiveBicomplexAugmentationSourceTotalIso_naturality]

/-- The comparison from the ordinary Čech complex into the Čech total complex of an augmented
cochain complex of sheaves. -/
noncomputable def cechToTotalMap (U : index → C)
    (ε : (CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F ⟶ K) :
    (cechCochainFunctorInt U).obj F ⟶
      (cechBicomplexOfComplex U K).total (ComplexShape.up ℤ) :=
  (cechInjectiveBicomplexAugmentationSourceTotalIso U F).inv ≫
    HomologicalComplex₂.total.map (cechAugmentationMap U ε) (ComplexShape.up ℤ)

/-- The Čech-to-total comparison of an injective resolution reads it only through the
underlying complex and its augmentation. -/
lemma cechToInjectiveTotalMap_eq (U : index → C) (I : InjectiveResolution F) :
    cechToInjectiveTotalMap U I = cechToTotalMap U I.ι' :=
  rfl

/-- The Čech-to-total comparison commutes with a morphism of augmented complexes. -/
lemma cechToTotalMap_naturality (U : index → C) (φ : F ⟶ G)
    (εF : (CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F ⟶ K)
    (εG : (CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj G ⟶ L)
    (Φ : K ⟶ L)
    (hΦ : εF ≫ Φ =
      (CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).map φ ≫ εG) :
    (cechCochainFunctorInt U).map φ ≫ cechToTotalMap U εG =
      cechToTotalMap U εF ≫
        HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ) := by
  dsimp only [cechToTotalMap, cechAugmentationMap]
  rw [← Category.assoc,
    cechInjectiveBicomplexAugmentationSourceTotalIso_inv_naturality,
    Category.assoc, Category.assoc, ← HomologicalComplex₂.total.map_comp,
    ← HomologicalComplex₂.total.map_comp, ← cechBicomplexMap_comp,
    ← cechBicomplexMap_comp, ← hΦ]

omit [HasSheafify J AddCommGrpCat.{a}] in
/-- The degreewise identification between the integer-extended Čech complex and ordinary Čech
cohomology is natural in the sheaf. -/
lemma cechCochainFunctorIntHomologyIso_naturality
    (U : index → C) (φ : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechCochainFunctorInt U).map φ) (n : ℤ) ≫
        (cechCochainFunctorIntHomologyIso U n).hom =
      (cechCochainFunctorIntHomologyIso U n).hom ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ.hom) n := by
  dsimp only [cechCochainFunctorIntHomologyIso]
  exact HomologicalComplex.extendHomologyIso_naturality
    ((cechComplexFunctor U).map φ.hom) ComplexShape.embeddingUpNat rfl

/-- The universe-lifting identification of sections complexes is natural in the complex. -/
lemma injectiveResolutionSectionsComplexUnliftedIso_naturality
    {X : TopCat.{u}} {T : Opens X} {F₁ F₂ : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I₁ : InjectiveResolution F₁) (I₂ : InjectiveResolution F₂)
    (Φ : I₁.cochainComplex ⟶ I₂.cochainComplex) :
    sectionsComplexMap T Φ ≫ (injectiveResolutionSectionsComplexUnliftedIso I₂).hom =
      (injectiveResolutionSectionsComplexUnliftedIso I₁).hom ≫
        ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (sectionsComplexMap T Φ) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  rfl

omit [HasFiniteProducts C] in
/-- The terminal-object comparison between `H'` and `H` is natural in the sheaf. -/
lemma HPrimeAddEquivH_naturality {T : C} (hT : IsTerminal T)
    [HasExt.{h} (Sheaf J AddCommGrpCat.{a})] (φ : F ⟶ G) (n : ℕ) (x : F.H' n T) :
    HPrimeAddEquivH (J := J) hT G n
        (((cohomologyPresheafFunctor J n).map φ).app (op T) x) =
      Sheaf.H.map φ n (HPrimeAddEquivH (J := J) hT F n x) := by
  have h := congrFun (congrArg (fun m => (ConcreteCategory.hom m : _ → _))
    ((HPrimeNatIsoH (J := J) hT n).hom.naturality φ)) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  show (ConcreteCategory.hom ((HPrimeNatIsoH (J := J) hT n).hom.app G))
      ((ConcreteCategory.hom ((cohomologyPresheafFunctor J n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{h}).obj (op T)).map φ)) x) =
    (ConcreteCategory.hom ((functorH J n).map φ))
      ((ConcreteCategory.hom ((HPrimeNatIsoH (J := J) hT n).hom.app F)) x)
  exact h

end Augmentation

section HomComplexSections

/-- Sections over `X` of a cochain complex of sheaves, lifted to the universe in which
morphisms of sheaves live. -/
noncomputable abbrev sectionsComplexLifted (X : C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    CochainComplex AddCommGrpCat.{max a u} ℤ :=
  ((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (sectionsComplexUnlifted X K)

/-- In each degree, cochains from the free abelian representable sheaf are sections. -/
noncomputable def yonedaHomComplexXIso (X : C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) (n : ℤ) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
        (freeAbelianYonedaSheaf J X)) K).X n ≅
      (sectionsComplexLifted X K).X n :=
  ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := freeAbelianYonedaSheaf J X) (K := K) (zero_add n)).trans
    ((freeAbelianYonedaSheafHomAddEquiv X (K.X n)).trans
      AddEquiv.ulift.symm)).toAddCommGrpIso

omit [HasFiniteProducts C] in
/-- Degreewise, the resolution-specific identification is the general one: the construction
never sees the resolution, only its underlying complex. -/
lemma freeAbelianYonedaHomComplexXIso_eq {F : Sheaf J AddCommGrpCat.{a}}
    (X : C) (I : InjectiveResolution F) (n : ℤ) :
    freeAbelianYonedaHomComplexXIso X I n = yonedaHomComplexXIso X I.cochainComplex n :=
  rfl

/-- The Hom complex from the free abelian representable sheaf is the sections complex. -/
noncomputable def yonedaHomComplexIsoSections (X : C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
        (freeAbelianYonedaSheaf J X)) K ≅
      sectionsComplexLifted X K :=
  HomologicalComplex.Hom.isoOfComponents (yonedaHomComplexXIso X K) (by
    intro i j hij
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro α
    obtain ⟨f, rfl⟩ :=
      CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
        (X := freeAbelianYonedaSheaf J X) (K := K) α i (zero_add i)
    change i + 1 = j at hij
    simp only [CategoryTheory.comp_apply, yonedaHomComplexXIso,
      AddEquiv.toAddCommGrpIso_hom, AddCommGrpCat.ofHom_apply, AddEquiv.coe_trans,
      Function.comp_apply,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    dsimp [sectionsAtFunctorUnlifted]
    simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    change ULift.up
        ((K.d i j).hom.app (op X)
          (freeAbelianYonedaSheafHomAddEquiv X (K.X i) f)) =
      ULift.up
        (freeAbelianYonedaSheafHomAddEquiv X (K.X j)
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
            (CochainComplex.HomComplex.δ i j
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add i)))))
    apply ULift.ext
    change (K.d i j).hom.app (op X)
        (freeAbelianYonedaSheafHomAddEquiv X (K.X i) f) =
      freeAbelianYonedaSheafHomAddEquiv X (K.X j)
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
          (CochainComplex.HomComplex.δ i j
            (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add i))))
    rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
    rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    exact (freeAbelianYonedaSheafHomAddEquiv_comp X f (K.d i j)).symm)

omit [HasFiniteProducts C] in
/-- The same at the level of complexes, which is what the naturality square below is stated
against. -/
lemma freeAbelianYonedaHomComplexIsoSections_eq {F : Sheaf J AddCommGrpCat.{a}}
    (X : C) (I : InjectiveResolution F) :
    freeAbelianYonedaHomComplexIsoSections X I =
      yonedaHomComplexIsoSections X I.cochainComplex :=
  rfl

omit [HasFiniteProducts C] in
/-- Post-composing a cochain out of a single complex with a morphism of complexes. -/
lemma fromSingleMk_comp_ofHom {X : C}
    (K L : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) (n : ℤ)
    (f : freeAbelianYonedaSheaf J X ⟶ K.X n) (Φ : K ⟶ L) :
    (CochainComplex.HomComplex.Cochain.fromSingleMk
        (X := freeAbelianYonedaSheaf J X) f (zero_add n)).comp
        (CochainComplex.HomComplex.Cochain.ofHom Φ) (add_zero n) =
      CochainComplex.HomComplex.Cochain.fromSingleMk (f ≫ Φ.f n) (zero_add n) := by
  ext p q hpq
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = n := by omega
    rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.fromSingleMk_v,
      CochainComplex.HomComplex.Cochain.fromSingleMk_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc]
  · rw [CochainComplex.HomComplex.Cochain.fromSingleMk_v_eq_zero _ (zero_add n) p q hpq hp,
      CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.fromSingleMk_v_eq_zero _ (zero_add n) p q hpq hp,
      Limits.zero_comp]

omit [HasFiniteProducts C] in
/-- The identification of the Hom complex with the sections complex is natural in the
complex. -/
lemma yonedaHomComplexIsoSections_naturality (X : C) (Φ : K ⟶ L) :
    CochainComplex.HomComplex.postcompMap _ Φ ≫ (yonedaHomComplexIsoSections X L).hom =
      (yonedaHomComplexIsoSections X K).hom ≫
        ((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (sectionsComplexMap X Φ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro α
  obtain ⟨f, rfl⟩ :=
    CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
      (X := freeAbelianYonedaSheaf J X) (K := K) α n (zero_add n)
  simp only [HomologicalComplex.comp_f, CategoryTheory.comp_apply,
    HomologicalComplex.Hom.isoOfComponents_hom_f, yonedaHomComplexIsoSections,
    yonedaHomComplexXIso, AddEquiv.toAddCommGrpIso_hom, AddCommGrpCat.ofHom_apply,
    AddEquiv.coe_trans, Function.comp_apply,
    CochainComplex.HomComplex.postcompMap_f_apply,
    fromSingleMk_comp_ofHom,
    CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  apply ULift.ext
  dsimp [sectionsAtFunctorUnlifted]
  simp only [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
    AddEquiv.apply_symm_apply]
  exact freeAbelianYonedaSheafHomAddEquiv_comp X f (Φ.f n)

end HomComplexSections

section HPrime

variable [HasExt.{h} (Sheaf J AddCommGrpCat.{a})] {F G : Sheaf J AddCommGrpCat.{a}}

omit [HasFiniteProducts C] [HasExt.{h} (Sheaf J AddCommGrpCat.{a})] in
/-- The lifted sections complex of an injective resolution reads it only through the underlying
complex. -/
lemma injectiveResolutionSectionsComplex_eq (X : C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplex X I = sectionsComplexLifted X I.cochainComplex :=
  rfl

omit [HasFiniteProducts C] in
/-- The map on `H'` induced by a morphism of sheaves is post-composition in `Ext`. -/
lemma cohomologyPresheafFunctor_map_app_apply (X : C) (φ : F ⟶ G) (n : ℕ) (y : F.H' n X) :
    ((cohomologyPresheafFunctor J n).map φ).app (op X) y =
      y.comp (Abelian.Ext.mk₀ φ) (add_zero n) :=
  rfl

omit [HasFiniteProducts C] in
/-- The identification of the cohomology of the sections of an injective resolution with `H'`
commutes with a morphism of sheaves, once that morphism is lifted to the resolutions. -/
lemma injectiveResolutionSectionsCohomologyAddEquivHPrime_naturality
    (X : C) (φ : F ⟶ G) (I : InjectiveResolution F) (I' : InjectiveResolution G)
    (Φ : I.cochainComplex ⟶ I'.cochainComplex)
    (hΦ : I.ι' ≫ Φ =
      (CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).map φ ≫ I'.ι')
    (n : ℕ) (x : (injectiveResolutionSectionsComplex X I).homology (n : ℤ)) :
    injectiveResolutionSectionsCohomologyAddEquivHPrime X I' n
        (HomologicalComplex.homologyMap
          (((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (sectionsComplexMap X Φ)) (n : ℤ) x) =
      ((cohomologyPresheafFunctor J n).map φ).app (op X)
        (injectiveResolutionSectionsCohomologyAddEquivHPrime X I n x) := by
  -- the Hom-complex identification, in the direction the comparison uses
  have hsq : (freeAbelianYonedaHomComplexIsoSections X I).inv ≫
      CochainComplex.HomComplex.postcompMap _ Φ =
    ((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionsComplexMap X Φ) ≫
      (freeAbelianYonedaHomComplexIsoSections X I').inv := by
    rw [freeAbelianYonedaHomComplexIsoSections_eq,
      freeAbelianYonedaHomComplexIsoSections_eq, Iso.inv_comp_eq, ← Category.assoc,
      Iso.eq_comp_inv, yonedaHomComplexIsoSections_naturality]
  have h1 := ConcreteCategory.congr_hom
    (show HomologicalComplex.homologyMap
          (((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (sectionsComplexMap X Φ)) (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (freeAbelianYonedaHomComplexIsoSections X I').inv (n : ℤ) =
      HomologicalComplex.homologyMap
          (freeAbelianYonedaHomComplexIsoSections X I).inv (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (CochainComplex.HomComplex.postcompMap _ Φ) (n : ℤ) from by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hsq]) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  -- the Ext identification, in the direction the comparison uses
  have h3 : ∀ c : CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
          (freeAbelianYonedaSheaf J X)) I.cochainComplex (n : ℤ),
      I'.extEquivCohomologyClass.symm
          (CochainComplex.HomComplex.CohomologyClass.postcomp Φ c) =
        (I.extEquivCohomologyClass.symm c).comp (Abelian.Ext.mk₀ φ) (add_zero n) := by
    intro c
    refine (I'.extEquivCohomologyClass.symm_apply_eq).2 ?_
    rw [CategoryTheory.InjectiveResolution.extEquivCohomologyClass_naturality
      I I' φ Φ hΦ, Equiv.apply_symm_apply]
  exact (congrArg (fun z ↦ I'.extAddEquivCohomologyClass.symm
        (CochainComplex.HomComplex.homologyAddEquiv _ I'.cochainComplex (n : ℤ) z)) h1).trans
    ((congrArg I'.extAddEquivCohomologyClass.symm
        (CochainComplex.HomComplex.CohomologyClass.homologyAddEquiv_naturality
          _ Φ (n : ℤ) _)).trans (h3 _))

end HPrime



section Comparison

open TopologicalSpace

variable {Y : TopCat.{u}} {T : Opens Y} {ind : Type u}
  {F G : TopCat.Sheaf AddCommGrpCat.{u} Y}

/-- The Čech-to-sections half of the comparison commutes with a morphism of sheaves, once that
morphism is lifted to the resolutions.

Each of the four factors is the homology of an explicit chain map or its inverse, so each
square is the image under `homologyMap` of a square of chain maps proved earlier in this
file. -/
lemma cechToSectionsHomologyIso_hom_naturality
    (hT : IsTerminal T) (U : ind → Opens Y) (φ : F ⟶ G)
    (I : InjectiveResolution F) (I' : InjectiveResolution G)
    (Φ : I.cochainComplex ⟶ I'.cochainComplex)
    (hΦ : I.ι' ≫ Φ =
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{u} Y) 0).map φ ≫ I'.ι')
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} Y))
    (hcover : @IsCechAcyclicCover (Opens Y) _
      (Opens.grothendieckTopology Y) _ hExt ind _ U F)
    (hcover' : @IsCechAcyclicCover (Opens Y) _
      (Opens.grothendieckTopology Y) _ hExt ind _ U G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ.hom) n ≫
        (cechToSectionsHomologyIso hT U I' hExt hcover' n).hom =
      (cechToSectionsHomologyIso hT U I hExt hcover n).hom ≫
        HomologicalComplex.homologyMap
          (((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (sectionsComplexMap T Φ)) (n : ℤ) := by
  letI : QuasiIso (injectiveResolutionSectionsToCechTotalMap hT U I) :=
    injectiveResolutionSectionsToCechTotalMap_quasiIso hT U hcover.1 I
  letI : QuasiIso (injectiveResolutionSectionsToCechTotalMap hT U I') :=
    injectiveResolutionSectionsToCechTotalMap_quasiIso hT U hcover'.1 I'
  letI : QuasiIso (cechToInjectiveTotalMap U I) :=
    @cechToInjectiveTotalMap_quasiIso (Opens Y) _ (Opens.grothendieckTopology Y) _ _
      ind F U I hExt hcover.2
  letI : QuasiIso (cechToInjectiveTotalMap U I') :=
    @cechToInjectiveTotalMap_quasiIso (Opens Y) _ (Opens.grothendieckTopology Y) _ _
      ind G U I' hExt hcover'.2
  -- the underlying squares of chain maps, restated in the local types
  have hs1 : HomologicalComplex.homologyMap ((cechCochainFunctorInt U).map φ) (n : ℤ) ≫
      (cechCochainFunctorIntHomologyIso U n (F := G)).hom =
    (cechCochainFunctorIntHomologyIso U n (F := F)).hom ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ.hom) n :=
    cechCochainFunctorIntHomologyIso_naturality U φ n
  have hs2 : (cechCochainFunctorInt U).map φ ≫ cechToInjectiveTotalMap U I' =
      cechToInjectiveTotalMap U I ≫
        HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ) :=
    cechToTotalMap_naturality U φ I.ι' I'.ι' Φ hΦ
  have hs3 : sectionsComplexMap T Φ ≫ injectiveResolutionSectionsToCechTotalMap hT U I' =
      injectiveResolutionSectionsToCechTotalMap hT U I ≫
        HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ) :=
    sectionsToCechTotalMap_naturality hT U Φ
  have hs4 : sectionsComplexMap T Φ ≫
      (injectiveResolutionSectionsComplexUnliftedIso I').hom =
    (injectiveResolutionSectionsComplexUnliftedIso I).hom ≫
      ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionsComplexMap T Φ) :=
    injectiveResolutionSectionsComplexUnliftedIso_naturality I I' Φ
  -- their images under `homologyMap`
  have S1 : HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ.hom) n ≫
        (cechCochainFunctorIntHomologyIso U n (F := G)).inv =
      (cechCochainFunctorIntHomologyIso U n (F := F)).inv ≫
        HomologicalComplex.homologyMap ((cechCochainFunctorInt U).map φ) (n : ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hs1]
  have S2 : HomologicalComplex.homologyMap ((cechCochainFunctorInt U).map φ) (n : ℤ) ≫
        (isoOfQuasiIsoAt (cechToInjectiveTotalMap U I') (n : ℤ)).hom =
      (isoOfQuasiIsoAt (cechToInjectiveTotalMap U I) (n : ℤ)).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ))
          (n : ℤ) := by
    simp only [isoOfQuasiIsoAt, asIso_hom]
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hs2]
  have S3 : HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ))
          (n : ℤ) ≫
        (isoOfQuasiIsoAt
          (injectiveResolutionSectionsToCechTotalMap hT U I') (n : ℤ)).inv =
      (isoOfQuasiIsoAt
          (injectiveResolutionSectionsToCechTotalMap hT U I) (n : ℤ)).inv ≫
        HomologicalComplex.homologyMap (sectionsComplexMap T Φ) (n : ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    simp only [isoOfQuasiIsoAt, asIso_hom]
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hs3]
  have S4 : HomologicalComplex.homologyMap (sectionsComplexMap T Φ) (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (injectiveResolutionSectionsComplexUnliftedIso I').hom (n : ℤ) =
      HomologicalComplex.homologyMap
          (injectiveResolutionSectionsComplexUnliftedIso I).hom (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (sectionsComplexMap T Φ)) (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hs4]
  dsimp only [cechToSectionsHomologyIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso, cechCohomologyIsoInjectiveTotalHomology]
  rw [← Category.assoc, S1, Category.assoc, Category.assoc, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap
      ((cechCochainFunctorInt U).map φ) (n : ℤ)), S2, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ))
      (n : ℤ)), S3, Category.assoc, S4]
  simp only [Category.assoc]

/-- **The Čech-to-derived comparison commutes with a morphism of sheaves.**

This is what the bare existential form cannot state. A scalar action on cohomology is the map
induced by an endomorphism of the sheaf, so `k`-linearity of the comparison is this square at
`φ = ` multiplication by a scalar, with `Φ` any lift of it to the resolutions.

The `HasExt` witness is passed positionally throughout, for the reason recorded across this
lane: `HasExt.{u}` and `HasExt.{u + 1}` name different groups, and instance search must not be
allowed to choose. -/
theorem cechComparisonAddEquiv_naturality
    (hT : IsTerminal T) (U : ind → Opens Y) (φ : F ⟶ G)
    (I : InjectiveResolution F) (I' : InjectiveResolution G)
    (Φ : I.cochainComplex ⟶ I'.cochainComplex)
    (hΦ : I.ι' ≫ Φ =
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{u} Y) 0).map φ ≫ I'.ι')
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} Y))
    (hcover : @IsCechAcyclicCover (Opens Y) _
      (Opens.grothendieckTopology Y) _ hExt ind _ U F)
    (hcover' : @IsCechAcyclicCover (Opens Y) _
      (Opens.grothendieckTopology Y) _ hExt ind _ U G) (n : ℕ)
    (x : (cechCohomology U F.obj n : AddCommGrpCat.{u})) :
    cechComparisonAddEquiv hT U I' hExt hcover' n
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ.hom) n x) =
      @Sheaf.H.map (Opens Y) _ (Opens.grothendieckTopology Y) _ hExt F G φ n
        (cechComparisonAddEquiv hT U I hExt hcover n x) := by
  have h1 := ConcreteCategory.congr_hom
    (cechToSectionsHomologyIso_hom_naturality hT U φ I I' Φ hΦ hExt hcover hcover' n) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  exact (congrArg (fun z ↦
        @HPrimeAddEquivH (Opens Y) _ (Opens.grothendieckTopology Y) _ hExt T hT G n
          (@injectiveResolutionSectionsCohomologyAddEquivHPrime (Opens Y) _
            (Opens.grothendieckTopology Y) _ hExt G T I' n z)) h1).trans
    ((congrArg (@HPrimeAddEquivH (Opens Y) _ (Opens.grothendieckTopology Y) _ hExt T hT G n)
        (@injectiveResolutionSectionsCohomologyAddEquivHPrime_naturality (Opens Y) _
          (Opens.grothendieckTopology Y) _ hExt F G T φ I I' Φ hΦ n _)).trans
      (@HPrimeAddEquivH_naturality (Opens Y) _ (Opens.grothendieckTopology Y) _ F G T hT
        hExt φ n _))

end Comparison

end CategoryTheory.Sheaf
