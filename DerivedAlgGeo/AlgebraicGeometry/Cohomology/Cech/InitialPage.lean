/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.Comparison
import DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredTotalComplexFirstPageDifferential
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The degree-zero row of the Cech-injective spectral sequence

For an explicit injective resolution `F ⟶ I⁰ ⟶ I¹ ⟶ ⋯`, applying a fixed Cech
cochain term gives an augmented complex that is exact at `I⁰`.  Consequently, the zeroth
vertical homology of the Cech-injective bicomplex is the corresponding term of the ordinary Cech
complex of `F`.

The second half of the file tracks the initial-page differential through the adjacent-column
mapping cones.  It identifies the degree-zero row, including its horizontal differential, with
the integer-extended Cech complex.  The page-to-page homology isomorphism therefore identifies
the following page with Cech cohomology.
-/

universe a v u

open CategoryTheory Category Limits

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

/-- Evaluation of the integer-extended Cech complex in a fixed cochain degree. -/
noncomputable def cechTermFunctorInt (U : index → C) (p : ℤ) :
    Sheaf J AddCommGrpCat.{a} ⥤ AddCommGrpCat.{a} :=
  cechCochainFunctorInt U ⋙
    HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) p

noncomputable instance cechTermFunctorInt_additive (U : index → C) (p : ℤ) :
    (cechTermFunctorInt (J := J) U p).Additive := by
  dsimp [cechTermFunctorInt]
  infer_instance

/-- A nonnegative term of the integer-extended Cech complex is the usual product of sections on
the corresponding finite intersections. -/
noncomputable def cechCochainFunctorIntXIso (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) (p : ℕ) :
    ((cechCochainFunctorInt U).obj G).X (p : ℤ) ≅
      ∏ᶜ fun x : Fin (p + 1) → index =>
        G.obj.obj (Opposite.op (∏ᶜ fun k => U (x k))) := by
  dsimp [cechCochainFunctorInt, cechComplexFunctor,
    Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor]
  let K := AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (Functor.rightOp (Limits.FormalCoproduct.mk index U).cech ⋙
      (Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj G.obj)
  refine K.extendXIso ComplexShape.embeddingUpNat rfl ≪≫ ?_
  exact Iso.refl _

omit [HasSheafify J AddCommGrpCat.{a}] in
@[reassoc]
lemma cechCochainFunctorIntXIso_naturality (U : index → C)
    {G H : Sheaf J AddCommGrpCat.{a}} (f : G ⟶ H) (p : ℕ) :
    (((cechCochainFunctorInt U).map f).f (p : ℤ)) ≫
        (cechCochainFunctorIntXIso U H p).hom =
      (cechCochainFunctorIntXIso U G p).hom ≫
        Limits.Pi.map (fun x : Fin (p + 1) → index =>
          f.hom.app (Opposite.op (∏ᶜ fun k => U (x k)))) := by
  dsimp [cechCochainFunctorIntXIso, cechCochainFunctorInt,
    cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
    (i := p) (i' := (p : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

noncomputable instance cechCochainFunctorInt_map_f_mono
    (U : index → C) {G H : Sheaf J AddCommGrpCat.{a}} (f : G ⟶ H)
    [Mono f] (p : ℕ) : Mono (((cechCochainFunctorInt U).map f).f (p : ℤ)) := by
  apply mono_of_mono_fac (cechCochainFunctorIntXIso_naturality U f p)

/-- The augmentation on a fixed Cech column. -/
noncomputable def cechInjectiveColumnAugmentation
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℤ) :
    (cechInjectiveBicomplexAugmentationSource U F).X p ⟶
      (cechInjectiveBicomplex U I).X p :=
  (cechInjectiveBicomplexAugmentation U I).f p

/-- The first two maps of an injective resolution after taking sections, in its original
`Nat`-graded presentation. -/
noncomputable def sectionsNatAugmentedShortComplex
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    ShortComplex AddCommGrpCat.{a} :=
  (ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1)
    I.ι_f_zero_comp_complex_d).map (sectionsAtFunctorUnlifted X)

/-- The first two maps of an injective resolution after taking sections, in the integer-graded
presentation used by the Cech bicomplex. -/
noncomputable def sectionsIntAugmentedShortComplex
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    ShortComplex AddCommGrpCat.{a} :=
  ShortComplex.mk
    ((sectionsAtFunctorUnlifted X).map (I.ι'.f 0))
    ((sectionsAtFunctorUnlifted X).map (I.cochainComplex.d 0 1)) (by
      rw [← (sectionsAtFunctorUnlifted X).map_comp, I.ι'.comm]
      simp [CochainComplex.singleFunctor])

/-- The integer- and natural-graded augmented section short complexes agree. -/
noncomputable def sectionsAugmentedShortComplexIso
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    sectionsIntAugmentedShortComplex X I ≅
      sectionsNatAugmentedShortComplex X I := by
  let e₀ := I.cochainComplexXIso 0 0 (by simp)
  let e₁ := I.cochainComplexXIso 1 1 (by simp)
  exact ShortComplex.isoMk
    ((sectionsAtFunctorUnlifted X).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F))
    ((sectionsAtFunctorUnlifted X).mapIso e₀)
    ((sectionsAtFunctorUnlifted X).mapIso e₁)
    (by
      dsimp [sectionsIntAugmentedShortComplex,
        sectionsNatAugmentedShortComplex]
      have hι : I.ι'.f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
            I.ι.f 0 ≫ e₀.inv := by
        simpa only [e₀] using I.ι'_f_zero
      rw [hι]
      let A := (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 F).hom
      let S := sectionsAtFunctorUnlifted (J := J) X
      calc
        S.map A ≫ S.map (I.ι.f 0) = S.map (A ≫ I.ι.f 0) :=
          (S.map_comp A (I.ι.f 0)).symm
        _ = S.map ((A ≫ I.ι.f 0 ≫ e₀.inv) ≫ e₀.hom) := by
          congr 1
          simp
        _ = S.map (A ≫ I.ι.f 0 ≫ e₀.inv) ≫ S.map e₀.hom :=
          S.map_comp _ _)
    (by
      dsimp [sectionsIntAugmentedShortComplex,
        sectionsNatAugmentedShortComplex]
      simp only [← (sectionsAtFunctorUnlifted X).map_comp]
      have hd : I.cochainComplex.d 0 1 =
          e₀.hom ≫ I.cocomplex.d 0 1 ≫ e₁.inv := by
        simpa only [e₀, e₁] using I.cochainComplex_d 0 1 0 1 rfl rfl
      rw [hd]
      simp)

omit [HasFiniteProducts C] in
/-- Taking sections preserves exactness at the beginning of an injective resolution. -/
lemma sectionsIntAugmentedShortComplex_exact
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    (sectionsIntAugmentedShortComplex X I).Exact :=
  ShortComplex.exact_of_iso (sectionsAugmentedShortComplexIso X I).symm (by
    letI : PreservesLimitsOfShape WalkingParallelPair
        (sectionsAtFunctorUnlifted (J := J) X) := by
      dsimp [sectionsAtFunctorUnlifted]
      infer_instance
    apply I.exact₀.map_of_mono_of_preservesKernel
    all_goals infer_instance)

/-- Product, over all intersections in a fixed Cech degree, of the augmented section short
complexes. -/
noncomputable def cechAugmentedColumnProductShortComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) : ShortComplex AddCommGrpCat.{a} :=
  ShortComplex.mk
    (Limits.Pi.map (fun x : Fin (p + 1) → index =>
      (sectionsIntAugmentedShortComplex (∏ᶜ fun k => U (x k)) I).f))
    (Limits.Pi.map (fun x : Fin (p + 1) → index =>
      (sectionsIntAugmentedShortComplex (∏ᶜ fun k => U (x k)) I).g)) (by
      apply Limits.Pi.hom_ext
      intro x
      rw [Category.assoc, Limits.Pi.map_π,
        ← Category.assoc, Limits.Pi.map_π]
      rw [Category.assoc,
        (sectionsIntAugmentedShortComplex (∏ᶜ fun k => U (x k)) I).zero]
      simp)

lemma cechAugmentedColumnProductShortComplex_exact
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    (cechAugmentedColumnProductShortComplex U I p).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  let K := fun x : Fin (p + 1) → index =>
    sectionsIntAugmentedShortComplex (∏ᶜ fun k => U (x k)) I
  have hlocal (x : Fin (p + 1) → index) : (K x).Exact :=
    sectionsIntAugmentedShortComplex_exact (∏ᶜ fun k => U (x k)) I
  have hlocal' (x : Fin (p + 1) → index) :
      ∀ (yx : (K x).X₂), (K x).g yx = 0 →
        ∃ zx : (K x).X₁, (K x).f zx = yx := by
    rw [← ShortComplex.ab_exact_iff]
    exact hlocal x
  have hyx (x : Fin (p + 1) → index) :
      (K x).g (Concrete.productEquiv (fun x => (K x).X₂) y x) = 0 := by
    have hx := congrArg
      (fun z => Concrete.productEquiv (fun x => (K x).X₃) z x) hy
    simp only [Concrete.productEquiv_apply_apply] at hx
    dsimp [cechAugmentedColumnProductShortComplex, K] at hx
    change (Pi.π (fun x => (K x).X₃) x)
      ((Limits.Pi.map (fun x => (K x).g)) y) =
        (Pi.π (fun x => (K x).X₃) x) 0 at hx
    have hπ := CategoryTheory.congr_fun
      (Limits.Pi.map_π (fun x => (K x).g) x) y
    simp only [CategoryTheory.comp_apply] at hπ
    rw [hπ] at hx
    rw [Concrete.productEquiv_apply_apply]
    change (K x).g ((Pi.π (fun x => (K x).X₂) x) y) = 0
    simpa only [map_zero] using hx
  choose z hz using fun x => hlocal' x _ (hyx x)
  refine ⟨(Concrete.productEquiv (fun x => (K x).X₁)).symm z, ?_⟩
  apply (Concrete.productEquiv (fun x => (K x).X₂)).injective
  funext x
  simp only [Concrete.productEquiv_apply_apply]
  change ((Limits.Pi.map (fun x => (K x).f) ≫
    Pi.π (fun x => (K x).X₂) x)
      ((Concrete.productEquiv (fun x => (K x).X₁)).symm z)) =
    Pi.π (fun x => (K x).X₂) x y
  rw [Limits.Pi.map_π, CategoryTheory.comp_apply,
    Concrete.productEquiv_symm_apply_π]
  simpa only [Concrete.productEquiv_apply_apply] using hz x

/-- The augmented first two terms in a fixed nonnegative Cech column. -/
noncomputable def cechColumnAugmentationShortComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) : ShortComplex AddCommGrpCat.{a} :=
  ShortComplex.mk
    ((cechInjectiveColumnAugmentation U I (p : ℤ)).f 0)
    (((cechInjectiveBicomplex U I).X (p : ℤ)).d 0 1) (by
      calc
        ((cechInjectiveColumnAugmentation U I (p : ℤ)).f 0) ≫
            ((cechInjectiveBicomplex U I).X (p : ℤ)).d 0 1 =
          ((cechInjectiveBicomplexAugmentationSource U F).X (p : ℤ)).d 0 1 ≫
            ((cechInjectiveColumnAugmentation U I (p : ℤ)).f 1) :=
              (cechInjectiveColumnAugmentation U I (p : ℤ)).comm 0 1
        _ = 0 := by
          have hd :
              ((cechInjectiveBicomplexAugmentationSource U F).X
                (p : ℤ)).d 0 1 = 0 := by
            apply IsZero.eq_of_tgt
            change IsZero (((cechCochainFunctorInt U).obj
              (((CochainComplex.singleFunctor
                (Sheaf J AddCommGrpCat.{a}) 0).obj F).X 1)).X (p : ℤ))
            exact (HomologicalComplex.eval AddCommGrpCat.{a}
              (ComplexShape.up ℤ) (p : ℤ)).map_isZero
                ((cechCochainFunctorInt U).map_isZero
                  (HomologicalComplex.isZero_single_obj_X
                    (ComplexShape.up ℤ) 0 F 1 (by omega)))
          rw [hd, zero_comp])

/-- The fixed-column augmented short complex is the product of the augmented section short
complexes. -/
noncomputable def cechColumnAugmentationShortComplexIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    cechColumnAugmentationShortComplex U I p ≅
      cechAugmentedColumnProductShortComplex U I p :=
  ShortComplex.isoMk
    (cechCochainFunctorIntXIso U
      (((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F).X 0) p)
    (cechInjectiveBicomplexColumnXIso U I p 0)
    (cechInjectiveBicomplexColumnXIso U I p 1)
    (by
      simpa [cechColumnAugmentationShortComplex,
        cechAugmentedColumnProductShortComplex,
        cechInjectiveColumnAugmentation, cechInjectiveBicomplexAugmentation,
        cechInjectiveBicomplexAugmentationSource, cechInjectiveBicomplex,
        cechResolutionBicomplexUnflipped,
        cechInjectiveBicomplexColumnXIso, cechCochainFunctorIntXIso,
        sectionsIntAugmentedShortComplex,
        sectionsAtFunctorUnlifted] using
          (cechCochainFunctorIntXIso_naturality U (I.ι'.f 0) p).symm)
    (by
      simpa [cechColumnAugmentationShortComplex,
        cechAugmentedColumnProductShortComplex,
        sectionsIntAugmentedShortComplex,
        sectionsAtFunctorUnlifted, cechColumnSectionsComplex,
        cechInjectiveBicomplexColumnIsoSectionsComplex] using
        (cechInjectiveBicomplexColumnIsoSectionsComplex U I p).hom.comm 0 1)

lemma cechColumnAugmentationShortComplex_exact
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    (cechColumnAugmentationShortComplex U I p).Exact :=
  ShortComplex.exact_of_iso (cechColumnAugmentationShortComplexIso U I p).symm
    (cechAugmentedColumnProductShortComplex_exact U I p)

lemma cechInjectiveColumnAugmentation_f_zero_mono
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    Mono ((cechInjectiveColumnAugmentation U I (p : ℤ)).f 0) := by
  dsimp [cechInjectiveColumnAugmentation, cechInjectiveBicomplexAugmentation,
    cechInjectiveBicomplexAugmentationSource, cechInjectiveBicomplex,
    cechResolutionBicomplexUnflipped]
  rw [I.ι'_f_zero]
  let e := I.cochainComplexXIso 0 0 (by simp)
  change Mono (((cechCochainFunctorInt U).map
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
      I.ι.f 0 ≫ e.inv)).f (p : ℤ))
  letI : Mono (I.ι.f 0) := by infer_instance
  have h₁ : Mono (I.ι.f 0 ≫ e.inv) := mono_comp (I.ι.f 0) e.inv
  have h₂ : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
      I.ι.f 0 ≫ e.inv) :=
    @mono_comp _ _ _ _ _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
      (by infer_instance) (I.ι.f 0 ≫ e.inv) h₁
  letI := h₂
  exact cechCochainFunctorInt_map_f_mono U _ p

lemma cechAugmentationSourceColumn_d_neg_one_zero
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (p : ℕ) :
    ((cechInjectiveBicomplexAugmentationSource U F).X (p : ℤ)).d (-1) 0 = 0 := by
  apply IsZero.eq_of_src
  change IsZero (((cechCochainFunctorInt U).obj
    (((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F).X (-1))).X
      (p : ℤ))
  exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) (p : ℤ)).map_isZero
    ((cechCochainFunctorInt U).map_isZero
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 F (-1) (by omega)))

lemma cechInjectiveColumn_d_neg_one_zero
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    ((cechInjectiveBicomplex U I).X (p : ℤ)).d (-1) 0 = 0 := by
  apply IsZero.eq_of_src
  change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X (-1))).X (p : ℤ))
  exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) (p : ℤ)).map_isZero
    ((cechCochainFunctorInt U).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by omega)))

/-- The augmentation is a quasi-isomorphism in vertical degree zero in every nonnegative Cech
degree. -/
noncomputable instance cechInjectiveColumnAugmentation_quasiIsoAt_zero
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    QuasiIsoAt (cechInjectiveColumnAugmentation U I (p : ℤ)) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.quasiIso_iff_of_zeros]
  · constructor
    · exact cechColumnAugmentationShortComplex_exact U I p
    · exact cechInjectiveColumnAugmentation_f_zero_mono U I p
  · exact cechAugmentationSourceColumn_d_neg_one_zero U p
  · apply IsZero.eq_of_tgt
    change IsZero (((cechCochainFunctorInt U).obj
      (((CochainComplex.singleFunctor
        (Sheaf J AddCommGrpCat.{a}) 0).obj F).X 1)).X (p : ℤ))
    exact (HomologicalComplex.eval AddCommGrpCat.{a}
      (ComplexShape.up ℤ) (p : ℤ)).map_isZero
        ((cechCochainFunctorInt U).map_isZero
          (HomologicalComplex.isZero_single_obj_X
            (ComplexShape.up ℤ) 0 F 1 (by omega)))
  · exact cechInjectiveColumn_d_neg_one_zero U I p

/-- Zeroth vertical homology of the augmentation source and the injective bicomplex agree. -/
noncomputable def cechInjectiveColumnAugmentationHomologyIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    ((cechInjectiveBicomplexAugmentationSource U F).X (p : ℤ)).homology 0 ≅
      ((cechInjectiveBicomplex U I).X (p : ℤ)).homology 0 :=
  isoOfQuasiIsoAt (cechInjectiveColumnAugmentation U I (p : ℤ)) 0

/-- A column of the augmentation source is the single complex concentrated in vertical degree
zero on the corresponding term of the integer-extended Cech complex. -/
noncomputable def cechAugmentationSourceColumnIsoSingle
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) (p : ℤ) :
    (cechInjectiveBicomplexAugmentationSource U F).X p ≅
      (CochainComplex.singleFunctor AddCommGrpCat.{a} 0).obj
        (((cechCochainFunctorInt U).obj F).X p) := by
  change (((cechTermFunctorInt U p).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj F)) ≅ _
  exact (HomologicalComplex.singleMapHomologicalComplex
    (cechTermFunctorInt U p) (ComplexShape.up ℤ) 0).app F

/-- Zeroth homology of an augmentation-source column is its ordinary Cech term. -/
noncomputable def cechAugmentationSourceColumnHomologyIso
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) (p : ℤ) :
    ((cechInjectiveBicomplexAugmentationSource U F).X p).homology 0 ≅
      ((cechCochainFunctorInt U).obj F).X p :=
  HomologicalComplex.homologyMapIso
      (cechAugmentationSourceColumnIsoSingle U F p) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) 0 (((cechCochainFunctorInt U).obj F).X p)

/-- The degree-zero row of the initial Cech-injective page has the same objects as the ordinary
Cech complex. -/
noncomputable def cechInjectiveInitialPageZeroRowXIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    ((cechInjectiveSpectralSequence U I).page 2).X ((p : ℤ), 0) ≅
      ((cechCochainFunctorInt U).obj F).X (p : ℤ) :=
  cechInjectiveInitialPageColumnHomologyIso U I (p : ℤ) 0 ≪≫
    (cechInjectiveColumnAugmentationHomologyIso U I p).symm ≪≫
    cechAugmentationSourceColumnHomologyIso U F (p : ℤ)

/-- The horizontal differential on the augmentation source is the ordinary Cech differential
under the single-complex identifications of its columns. -/
lemma cechAugmentationSourceColumn_d_square (U : index → C)
    (F : Sheaf J AddCommGrpCat.{a}) (p : ℤ) :
    (cechInjectiveBicomplexAugmentationSource U F).d p (p + 1) ≫
        (cechAugmentationSourceColumnIsoSingle U F (p + 1)).hom =
      (cechAugmentationSourceColumnIsoSingle U F p).hom ≫
        (CochainComplex.singleFunctor AddCommGrpCat.{a} 0).map
          (((cechCochainFunctorInt U).obj F).d p (p + 1)) := by
  apply HomologicalComplex.Hom.ext
  funext q
  dsimp [cechAugmentationSourceColumnIsoSingle,
    cechInjectiveBicomplexAugmentationSource,
    cechTermFunctorInt, HomologicalComplex₂.flip]
  by_cases hq : q = 0
  · subst q
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    erw [HomologicalComplex.single_map_f_self]
    let m := (cechCochainFunctorInt U).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
    let e₀ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (((cechCochainFunctorInt U).obj F).X p)
    let e₁ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (((cechCochainFunctorInt U).obj F).X (p + 1))
    let d := ((cechCochainFunctorInt U).obj F).d p (p + 1)
    let d₀ := ((cechCochainFunctorInt U).obj
      (((CochainComplex.singleFunctor
        (Sheaf J AddCommGrpCat.{a}) 0).obj F).X 0)).d p (p + 1)
    change (d₀ ≫ m.f (p + 1)) ≫ e₁.inv =
      (m.f p ≫ e₀.inv) ≫ (e₀.hom ≫ d ≫ e₁.inv)
    calc
      _ = (m.f p ≫ d) ≫ e₁.inv :=
        congrArg (fun z ↦ z ≫ e₁.inv) (m.comm p (p + 1)).symm
      _ = _ := by
        rw [Category.assoc, Category.assoc, e₀.inv_hom_id_assoc]
  · apply IsZero.eq_of_src
    change IsZero (((cechCochainFunctorInt U).obj
      (((CochainComplex.singleFunctor
        (Sheaf J AddCommGrpCat.{a}) 0).obj F).X q)).X p)
    exact (HomologicalComplex.eval AddCommGrpCat.{a}
      (ComplexShape.up ℤ) p).map_isZero
        ((cechCochainFunctorInt U).map_isZero
          (HomologicalComplex.isZero_single_obj_X
            (ComplexShape.up ℤ) 0 F q hq))

/-- On zeroth homology, the augmentation-source horizontal map is the ordinary Cech
differential. -/
lemma cechAugmentationSourceColumnHomologyIso_naturality (U : index → C)
    (F : Sheaf J AddCommGrpCat.{a}) (p : ℤ) :
    HomologicalComplex.homologyMap
        ((cechInjectiveBicomplexAugmentationSource U F).d p (p + 1)) 0 ≫
      (cechAugmentationSourceColumnHomologyIso U F (p + 1)).hom =
    (cechAugmentationSourceColumnHomologyIso U F p).hom ≫
      ((cechCochainFunctorInt U).obj F).d p (p + 1) := by
  let e₀ := cechAugmentationSourceColumnIsoSingle U F p
  let e₁ := cechAugmentationSourceColumnIsoSingle U F (p + 1)
  let d := ((cechCochainFunctorInt U).obj F).d p (p + 1)
  let s := (CochainComplex.singleFunctor AddCommGrpCat.{a} 0).map d
  have hs : (cechInjectiveBicomplexAugmentationSource U F).d p (p + 1) ≫
      e₁.hom = e₀.hom ≫ s := cechAugmentationSourceColumn_d_square U F p
  have hh : HomologicalComplex.homologyMap
        ((cechInjectiveBicomplexAugmentationSource U F).d p (p + 1)) 0 ≫
      HomologicalComplex.homologyMap e₁.hom 0 =
      HomologicalComplex.homologyMap e₀.hom 0 ≫
        HomologicalComplex.homologyMap s 0 := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, hs]
  change HomologicalComplex.homologyMap
        ((cechInjectiveBicomplexAugmentationSource U F).d p (p + 1)) 0 ≫
      HomologicalComplex.homologyMap e₁.hom 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) 0 _).hom =
    HomologicalComplex.homologyMap e₀.hom 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) 0 _).hom ≫ d
  rw [reassoc_of% hh]
  let h₀ := HomologicalComplex.homologyMap e₀.hom 0
  let u := HomologicalComplex.homologyMap s 0
  let e := (HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 (((cechCochainFunctorInt U).obj F).X (p + 1))).hom
  let e' := (HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 (((cechCochainFunctorInt U).obj F).X p)).hom
  change h₀ ≫ u ≫ e = h₀ ≫ e' ≫ d
  calc
    _ = h₀ ≫ (u ≫ e) := Category.assoc _ _ _
    _ = h₀ ≫ (e' ≫ d) := congrArg (fun z ↦ h₀ ≫ z)
      (HomologicalComplex.singleObjHomologySelfIso_hom_naturality
        (ComplexShape.up ℤ) 0 d)
    _ = _ := (Category.assoc _ _ _).symm

/-- The augmentation isomorphisms intertwine the horizontal maps on zeroth vertical
homology. -/
lemma cechInjectiveColumnAugmentationHomologyIso_horizontal
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    HomologicalComplex.homologyMap
        ((cechInjectiveBicomplex U I).d (p : ℤ) (p + 1)) 0 ≫
      (cechInjectiveColumnAugmentationHomologyIso U I (p + 1)).inv =
    (cechInjectiveColumnAugmentationHomologyIso U I p).inv ≫
      HomologicalComplex.homologyMap
        ((cechInjectiveBicomplexAugmentationSource U F).d
          (p : ℤ) (p + 1)) 0 := by
  let e₀ := cechInjectiveColumnAugmentationHomologyIso U I p
  let e₁ := cechInjectiveColumnAugmentationHomologyIso U I (p + 1)
  let d₀ := (cechInjectiveBicomplexAugmentationSource U F).d
    (p : ℤ) (p + 1)
  let d₁ := (cechInjectiveBicomplex U I).d (p : ℤ) (p + 1)
  have hh : e₀.hom ≫ HomologicalComplex.homologyMap d₁ 0 =
      HomologicalComplex.homologyMap d₀ 0 ≫ e₁.hom := by
    change HomologicalComplex.homologyMap
        (cechInjectiveColumnAugmentation U I (p : ℤ)) 0 ≫
      HomologicalComplex.homologyMap d₁ 0 =
      HomologicalComplex.homologyMap d₀ 0 ≫
        HomologicalComplex.homologyMap
          (cechInjectiveColumnAugmentation U I (p + 1 : ℤ)) 0
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    congr 1
    exact (cechInjectiveBicomplexAugmentation U I).comm
      (p : ℤ) (p + 1)
  rw [← cancel_epi e₀.hom]
  calc
    e₀.hom ≫ HomologicalComplex.homologyMap d₁ 0 ≫ e₁.inv =
        (e₀.hom ≫ HomologicalComplex.homologyMap d₁ 0) ≫ e₁.inv :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap d₀ 0 ≫ e₁.hom) ≫ e₁.inv :=
      congrArg (fun z ↦ z ≫ e₁.inv) hh
    _ = HomologicalComplex.homologyMap d₀ 0 := by
      calc
        _ = HomologicalComplex.homologyMap d₀ 0 ≫ (e₁.hom ≫ e₁.inv) :=
          Category.assoc _ _ _
        _ = HomologicalComplex.homologyMap d₀ 0 ≫ 𝟙 _ :=
          congrArg (fun z ↦ HomologicalComplex.homologyMap d₀ 0 ≫ z)
            e₁.hom_inv_id
        _ = _ := Category.comp_id _
    _ = e₀.hom ≫ e₀.inv ≫ HomologicalComplex.homologyMap d₀ 0 := by
      calc
        _ = 𝟙 _ ≫ HomologicalComplex.homologyMap d₀ 0 :=
          (Category.id_comp _).symm
        _ = (e₀.hom ≫ e₀.inv) ≫
            HomologicalComplex.homologyMap d₀ 0 :=
          congrArg (fun z ↦ z ≫ HomologicalComplex.homologyMap d₀ 0)
            e₀.hom_inv_id.symm
        _ = _ := Category.assoc _ _ _

/-- The first differential on the degree-zero row of the Cech-injective spectral sequence is
the ordinary Cech differential. -/
lemma cechInjectiveInitialPageZeroRow_d
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    ((cechInjectiveSpectralSequence U I).page 2).d
        ((p : ℤ), 0) ((p + 1 : ℕ), 0) ≫
      (cechInjectiveInitialPageZeroRowXIso U I (p + 1)).hom =
    (cechInjectiveInitialPageZeroRowXIso U I p).hom ≫
      ((cechCochainFunctorInt U).obj F).d (p : ℤ) (p + 1) := by
  dsimp [cechInjectiveInitialPageZeroRowXIso]
  have hd := HomologicalComplex₂.columnFilteredInitialPage_d_eq_horizontalHomologyMap
    (cechInjectiveBicomplex U I) (p : ℤ) 0
  change ((cechInjectiveSpectralSequence U I).page 2).d
      ((p : ℤ), 0) ((p : ℤ) + 1, 0) ≫
        (cechInjectiveInitialPageColumnHomologyIso U I ((p : ℤ) + 1) 0).hom =
      (cechInjectiveInitialPageColumnHomologyIso U I (p : ℤ) 0).hom ≫
        HomologicalComplex.homologyMap
          ((cechInjectiveBicomplex U I).d (p : ℤ) (p + 1)) 0 at hd
  rw [reassoc_of% hd]
  change (cechInjectiveInitialPageColumnHomologyIso U I (p : ℤ) 0).hom ≫
      HomologicalComplex.homologyMap
        ((cechInjectiveBicomplex U I).d (p : ℤ) (p + 1)) 0 ≫
      (cechInjectiveColumnAugmentationHomologyIso U I (p + 1)).inv ≫
      (cechAugmentationSourceColumnHomologyIso U F (p + 1)).hom =
    (cechInjectiveInitialPageColumnHomologyIso U I (p : ℤ) 0).hom ≫
      (cechInjectiveColumnAugmentationHomologyIso U I p).inv ≫
      (cechAugmentationSourceColumnHomologyIso U F p).hom ≫
      ((cechCochainFunctorInt U).obj F).d (p : ℤ) (p + 1)
  rw [cancel_epi
    (cechInjectiveInitialPageColumnHomologyIso U I (p : ℤ) 0).hom]
  rw [reassoc_of% cechInjectiveColumnAugmentationHomologyIso_horizontal U I p]
  let e := (cechInjectiveColumnAugmentationHomologyIso U I p).inv
  let h := HomologicalComplex.homologyMap
    ((cechInjectiveBicomplexAugmentationSource U F).d
      (p : ℤ) (p + 1)) 0
  let t := (cechAugmentationSourceColumnHomologyIso U F (p + 1)).hom
  let s := (cechAugmentationSourceColumnHomologyIso U F (p : ℤ)).hom
  let d := ((cechCochainFunctorInt U).obj F).d (p : ℤ) (p + 1)
  have hs : h ≫ t = s ≫ d :=
    cechAugmentationSourceColumnHomologyIso_naturality U F (p : ℤ)
  change (e ≫ h) ≫ t = e ≫ s ≫ d
  calc
    _ = e ≫ (h ≫ t) := Category.assoc _ _ _
    _ = e ≫ (s ≫ d) := congrArg (fun z ↦ e ≫ z) hs
    _ = _ := (Category.assoc _ _ _).symm

/-- The embedding of the integer-graded degree-zero row into the bidegrees of the initial
spectral-sequence page. -/
noncomputable def cechInitialPageZeroRowEmbedding :
    (ComplexShape.up ℤ).Embedding
      ((fun r : ℤ ↦ ComplexShape.up'
        (⟨r - 1, 2 - r⟩ : ℤ × ℤ)) 2) :=
  ComplexShape.Embedding.mk'
    (ComplexShape.up ℤ)
    ((fun r : ℤ ↦ ComplexShape.up'
      (⟨r - 1, 2 - r⟩ : ℤ × ℤ)) 2)
    (fun p ↦ (p, 0)) (by
      intro p q h
      simpa using congrArg (fun z : ℤ × ℤ ↦ z.1) h)
    (by
      intro p q
      simp [ComplexShape.up_Rel, ComplexShape.up'_Rel])

instance : cechInitialPageZeroRowEmbedding.IsRelIff := by
  dsimp [cechInitialPageZeroRowEmbedding]
  infer_instance

/-- The degree-zero row of the initial Cech-injective page, with its inherited horizontal
differential. -/
noncomputable def cechInjectiveInitialPageZeroRow
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) : CochainComplex AddCommGrpCat.{a} ℤ :=
  ((cechInjectiveSpectralSequence U I).page 2).restriction
    cechInitialPageZeroRowEmbedding

/-- Initial-page entries in a negative Cech degree vanish. -/
lemma isZero_cechInjectiveInitialPage_of_negative_cech_degree
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p q : ℤ) (hp : p < 0) :
    IsZero (((cechInjectiveSpectralSequence U I).page 2).X (p, q)) := by
  have hz : IsZero (((cechInjectiveBicomplex U I).X p).homology q) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X q)).X p)
    dsimp [cechCochainFunctorInt]
    apply HomologicalComplex.isZero_extend_X
    intro n hn
    dsimp [ComplexShape.embeddingUpNat] at hn
    omega
  exact IsZero.of_iso hz
    (cechInjectiveInitialPageColumnHomologyIso U I p q)

/-- Every object of the integer-graded degree-zero row is the corresponding object of the
integer-extended ordinary Cech complex. -/
noncomputable def cechInjectiveInitialPageZeroRowXIsoInt
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℤ) :
    (cechInjectiveInitialPageZeroRow U I).X p ≅
      ((cechCochainFunctorInt U).obj F).X p := by
  by_cases hp : 0 ≤ p
  · rw [← Int.toNat_of_nonneg hp]
    exact cechInjectiveInitialPageZeroRowXIso U I p.toNat
  · exact IsZero.iso
      (isZero_cechInjectiveInitialPage_of_negative_cech_degree U I p 0 (by omega))
      (by
        dsimp [cechCochainFunctorInt]
        apply HomologicalComplex.isZero_extend_X
        intro n hn
        dsimp [ComplexShape.embeddingUpNat] at hn
        omega)

/-- The degree-zero row of the initial page, including its differential, is the ordinary Cech
complex extended by zero from natural to integer degrees. -/
noncomputable def cechInjectiveInitialPageZeroRowIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) :
    cechInjectiveInitialPageZeroRow U I ≅ (cechCochainFunctorInt U).obj F :=
  HomologicalComplex.Hom.isoOfComponents
    (cechInjectiveInitialPageZeroRowXIsoInt U I) (by
      intro p q hpq
      have hpq' : q = p + 1 := by
        simpa [ComplexShape.up_Rel] using hpq.symm
      subst q
      by_cases hp : 0 ≤ p
      · rw [← Int.toNat_of_nonneg hp]
        dsimp [cechInjectiveInitialPageZeroRow,
          cechInitialPageZeroRowEmbedding,
          cechInjectiveInitialPageZeroRowXIsoInt]
        exact (cechInjectiveInitialPageZeroRow_d U I p.toNat).symm
      · apply IsZero.eq_of_src
        exact isZero_cechInjectiveInitialPage_of_negative_cech_degree
          U I p 0 (by omega))

/-- The page following the initial Cech-injective page is ordinary Cech cohomology along the
degree-zero row. -/
noncomputable def cechInjectiveFollowingPageCechCohomologyIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℕ) :
    ((cechInjectiveSpectralSequence U I).page 3).X ((p : ℤ), 0) ≅
      cechCohomology U F.obj p :=
  ((cechInjectiveSpectralSequence U I).iso 2 3 ((p : ℤ), 0)).symm ≪≫
    (((cechInjectiveSpectralSequence U I).page 2).restrictionHomologyIso
      cechInitialPageZeroRowEmbedding
      ((p : ℤ) - 1) (p : ℤ) ((p : ℤ) + 1)
      (by simp) (by simp) rfl rfl rfl (by
        apply ComplexShape.prev_eq'
        simp [cechInitialPageZeroRowEmbedding, ComplexShape.up'_Rel]) (by
        apply ComplexShape.next_eq'
        simp [cechInitialPageZeroRowEmbedding, ComplexShape.up'_Rel])).symm ≪≫
    HomologicalComplex.homologyMapIso
      (cechInjectiveInitialPageZeroRowIso U I) (p : ℤ) ≪≫
    ((cechComplexFunctor U).obj F.obj).extendHomologyIso
      ComplexShape.embeddingUpNat rfl

end CategoryTheory.Sheaf
