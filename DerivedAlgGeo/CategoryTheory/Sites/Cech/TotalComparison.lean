/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.InitialPage
import DerivedAlgGeo.CategoryTheory.SpectralSequence.TotalQuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# The Cech-to-total comparison

This file proves the first-quadrant comparison theorem for the Cech bicomplex of an explicit
injective resolution.  If the sheaf is acyclic on every nonempty finite intersection in the
Cech nerve, the augmentation from its ordinary Cech complex to the total injective Cech complex
is a quasi-isomorphism.
-/

universe h a u

open CategoryTheory Category Limits

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

private lemma isZero_cechAugmentationSourceColumn_homology_of_ne_zero
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((cechInjectiveBicomplexAugmentationSource U F).X p).homology q) := by
  exact IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) 0 (((cechCochainFunctorInt U).obj F).X p) q hq)
    (HomologicalComplex.homologyMapIso
      (cechAugmentationSourceColumnIsoSingle U F p) q)

private lemma isZero_cechInjectiveColumn_homology_of_neg
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) (p : ℤ) (q : ℤ) (hq : q < 0) :
    IsZero (((cechInjectiveBicomplex U I).X p).homology q) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X q)).X p)
  exact (HomologicalComplex.eval AddCommGrpCat.{a}
    (ComplexShape.up ℤ) p).map_isZero
      ((cechCochainFunctorInt U).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 q hq))

/-- Under local Cech acyclicity, the augmentation of every nonnegative Cech column is a
quasi-isomorphism. -/
lemma cechInjectiveColumnAugmentation_quasiIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]
    (hacyclic : IsCechAcyclicFor U F) (p : ℕ) :
    QuasiIso (cechInjectiveColumnAugmentation U I (p : ℤ)) := by
  rw [quasiIso_iff]
  intro q
  by_cases hq₀ : q = 0
  · subst q
    infer_instance
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hsource := isZero_cechAugmentationSourceColumn_homology_of_ne_zero
    U F (p : ℤ) q hq₀
  by_cases hq : q < 0
  · exact IsZero.isIso hsource
      (isZero_cechInjectiveColumn_homology_of_neg U I (p : ℤ) q hq) _
  · have hqpos : 0 < q := by omega
    let n : ℕ := q.toNat
    have hn : (n : ℤ) = q := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (by omega)]
    have htarget : IsZero (((cechInjectiveBicomplex U I).X (p : ℤ)).homology q) := by
      rw [← hn]
      exact (cechInjectiveBicomplexColumn_exactAt_of_isCechAcyclicFor
        U I hacyclic p n (by omega)).isZero_homology
    exact IsZero.isIso hsource htarget _

omit [HasSheafify J AddCommGrpCat.{a}] in
private lemma isZero_cechCochainFunctorInt_X_of_neg
    (U : index → C) (G : Sheaf J AddCommGrpCat.{a}) (p : ℤ) (hp : p < 0) :
    IsZero (((cechCochainFunctorInt U).obj G).X p) := by
  dsimp [cechCochainFunctorInt]
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  dsimp [ComplexShape.embeddingUpNat] at hn
  omega

/-- The augmentation source is supported in nonnegative vertical degrees. -/
lemma cechInjectiveBicomplexAugmentationSource_verticallyConnective
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) :
    HomologicalComplex₂.IsVerticallyConnective
      (cechInjectiveBicomplexAugmentationSource U F) := by
  intro p q hq
  change IsZero (((cechCochainFunctorInt U).obj
    (((CochainComplex.singleFunctor
      (Sheaf J AddCommGrpCat.{a}) 0).obj F).X q)).X p)
  exact (HomologicalComplex.eval AddCommGrpCat.{a}
    (ComplexShape.up ℤ) p).map_isZero
      ((cechCochainFunctorInt U).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 F q (by omega)))

/-- The augmentation source is supported in nonnegative Cech degrees. -/
lemma cechInjectiveBicomplexAugmentationSource_horizontallyConnective
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) :
    HomologicalComplex₂.IsHorizontallyConnective
      (cechInjectiveBicomplexAugmentationSource U F) := by
  intro p q hp
  change IsZero (((cechCochainFunctorInt U).obj
    (((CochainComplex.singleFunctor
      (Sheaf J AddCommGrpCat.{a}) 0).obj F).X q)).X p)
  exact isZero_cechCochainFunctorInt_X_of_neg U _ p hp

/-- The injective Cech bicomplex is supported in nonnegative resolution degrees. -/
lemma cechInjectiveBicomplex_verticallyConnective
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) :
    HomologicalComplex₂.IsVerticallyConnective
      (cechInjectiveBicomplex U I) := by
  intro p q hq
  change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X q)).X p)
  exact (HomologicalComplex.eval AddCommGrpCat.{a}
    (ComplexShape.up ℤ) p).map_isZero
      ((cechCochainFunctorInt U).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 q hq))

/-- The injective Cech bicomplex is supported in nonnegative Cech degrees. -/
lemma cechInjectiveBicomplex_horizontallyConnective
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) :
    HomologicalComplex₂.IsHorizontallyConnective
      (cechInjectiveBicomplex U I) := by
  intro p q hp
  change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X q)).X p)
  exact isZero_cechCochainFunctorInt_X_of_neg U _ p hp

/-- Under local Cech acyclicity, the total augmentation is a quasi-isomorphism. -/
lemma cechInjectiveBicomplexAugmentation_total_quasiIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]
    (hacyclic : IsCechAcyclicFor U F) :
    QuasiIso (HomologicalComplex₂.total.map
      (cechInjectiveBicomplexAugmentation U I) (ComplexShape.up ℤ)) := by
  apply HomologicalComplex₂.totalMap_quasiIso
  · exact cechInjectiveBicomplexAugmentationSource_verticallyConnective U F
  · exact cechInjectiveBicomplex_verticallyConnective U I
  · exact cechInjectiveBicomplexAugmentationSource_horizontallyConnective U F
  · exact cechInjectiveBicomplex_horizontallyConnective U I
  · intro p
    exact cechInjectiveColumnAugmentation_quasiIso U I hacyclic p

/-- The total of the Cech complex placed in vertical degree zero is canonically the ordinary
integer-extended Cech complex. -/
noncomputable def cechInjectiveBicomplexAugmentationSourceTotalIso
    (U : index → C) (F : Sheaf J AddCommGrpCat.{a}) :
    (cechInjectiveBicomplexAugmentationSource U F).total (ComplexShape.up ℤ) ≅
      (cechCochainFunctorInt U).obj F :=
  let K : HomologicalComplex₂ AddCommGrpCat.{a}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((cechCochainFunctorInt U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (Sheaf J AddCommGrpCat.{a}) 0).obj F)
  K.totalFlipIso (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.total.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (cechCochainFunctorInt U) (ComplexShape.up ℤ) 0).app F)
      (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.singleZeroTotalIso ((cechCochainFunctorInt U).obj F)

/-- The comparison map from the ordinary Cech complex to the total Cech complex of an
explicit injective resolution. -/
noncomputable def cechToInjectiveTotalMap
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) :
    (cechCochainFunctorInt U).obj F ⟶ cechInjectiveTotalComplex U I :=
  (cechInjectiveBicomplexAugmentationSourceTotalIso U F).inv ≫
    HomologicalComplex₂.total.map
      (cechInjectiveBicomplexAugmentation U I) (ComplexShape.up ℤ)

/-- On a Cech-acyclic family, the comparison from the ordinary Cech complex to the injective
Cech total complex is a quasi-isomorphism. -/
lemma cechToInjectiveTotalMap_quasiIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]
    (hacyclic : IsCechAcyclicFor U F) :
    QuasiIso (cechToInjectiveTotalMap U I) := by
  letI : QuasiIso
      (HomologicalComplex₂.total.map
        (cechInjectiveBicomplexAugmentation U I) (ComplexShape.up ℤ)) :=
    cechInjectiveBicomplexAugmentation_total_quasiIso U I hacyclic
  dsimp [cechToInjectiveTotalMap]
  infer_instance

/-- Degreewise homology comparison between the ordinary Cech complex and the injective Cech
total complex on a Cech-acyclic family. -/
noncomputable def cechCohomologyIsoInjectiveTotalHomology
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C)
    (I : InjectiveResolution F) [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]
    (hacyclic : IsCechAcyclicFor U F) (n : ℤ) :
    ((cechCochainFunctorInt U).obj F).homology n ≅
      (cechInjectiveTotalComplex U I).homology n := by
  letI : QuasiIso (cechToInjectiveTotalMap U I) :=
    cechToInjectiveTotalMap_quasiIso U I hacyclic
  exact isoOfQuasiIsoAt (cechToInjectiveTotalMap U I) n

end CategoryTheory.Sheaf
