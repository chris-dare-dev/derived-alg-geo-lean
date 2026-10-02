/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Degree-zero homology of the bounded-below right-derived functor

For an additive functor between abelian categories with enough injectives,
Mathlib constructs a bounded-below right-derived functor and its universal
unit. An injective resolution shows that the unit induces an isomorphism on
H⁰ of a strictly nonnegative complex when the functor preserves the input's
outgoing degree-zero kernel and those of nonnegative injective resolutions
equipped with a quasi-isomorphism from that input. The degree-zero single
case needs only its resolution-kernel condition.

This is a pointwise comparison. Naturality of the resulting objectwise
isomorphism and geometric identifications are separate.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusHomologyZeroSingleIso`:
  the pointwise comparison with the underived functor.
* `CategoryTheory.Functor.rightDerivedFunctorPlusHomologyZeroSingleIsoOfPreservesFiniteLimits`:
  a finite-limit-preserving specialization.

## Main results

* `CategoryTheory.Functor.isIso_homologyZero_map_rightDerivedFunctorPlusUnit_of_isStrictlyGE_zero`:
  the H⁰ unit is invertible on a nonnegative complex under local kernels.
* `CategoryTheory.Functor.isIso_homologyZero_map_rightDerivedFunctorPlusUnit_single`:
  the degree-zero single specialization.

## Implementation notes

The resolution is strictly nonnegative and termwise injective. Zero incoming
differentials reduce H⁰ preservation to outgoing-kernel preservation. Unit
naturality transfers invertibility from the injective resolution.

## References

* Mathlib `Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`
  and `DerivabilityStructureInjectives.lean` at pin
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

right-derived functor, bounded-below derived category, degree-zero homology
-/

namespace CategoryTheory.Functor

open Category Limits

universe u v

variable {C : Type u} {D : Type v}
  [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- Unit naturality transports H⁰ invertibility across an injective resolution. -/
private theorem isIso_homologyZero_unit_of_resolution
    (K J : HomotopyCategory.Plus C) (w : K ⟶ J)
    (hw : (HomotopyCategory.Plus.quasiIso C) w)
    [∀ n : ℤ, Injective (J.obj.as.X n)]
    [IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map w))] :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app K)) := by
  let H := DerivedCategory.Plus.homologyFunctor D 0
  let α := F.rightDerivedFunctorPlusUnit
  have hJ : IsIso (α.app J) := inferInstance
  have hwQ : IsIso (DerivedCategory.Plus.Qh.map w) :=
    Localization.inverts DerivedCategory.Plus.Qh _ _ hw
  have hwR : IsIso ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map w) := by
    change IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map w))
    infer_instance
  have hnat := α.naturality w
  have hnatH := congrArg H.map hnat
  simp only [H.map_comp] at hnatH
  have hcomp : IsIso (H.map (α.app K) ≫
      H.map ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map w)) := by
    rw [← hnatH]
    letI := hJ
    infer_instance
  have hright : IsIso (H.map ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map w)) := by
    letI := hwR
    infer_instance
  letI := hright
  have hunit : IsIso (H.map (α.app K)) :=
    (isIso_comp_right_iff _ _).mp hcomp
  simpa only [H, α] using hunit


omit [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] [F.Additive] in
/-- Zero incoming differentials identify degree-zero left homology with
outgoing kernels. Their preservation carries a local quasi-isomorphism to H⁰. -/
private lemma isIso_homologyMap_of_zero_incoming
    [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]
    (K L : CochainComplex C ℤ) (φ : K ⟶ L)
    (hK : (K.sc 0).f = 0) (hL : (L.sc 0).f = 0)
    [K.HasHomology 0] [L.HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).HasHomology 0]
    [QuasiIsoAt φ 0]
    [PreservesLimit (parallelPair (K.sc 0).g 0) F]
    [PreservesLimit (parallelPair (L.sc 0).g 0) F] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
  haveI : F.PreservesLeftHomologyOf (K.sc 0) :=
    F.preservesLeftHomology_of_zero_f (K.sc 0) hK
  haveI : F.PreservesLeftHomologyOf (L.sc 0) :=
    F.preservesLeftHomology_of_zero_f (L.sc 0) hL
  haveI : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map φ) := by
    exact (inferInstance : QuasiIsoAt φ 0).quasiIso
  haveI : (F.mapShortComplex.obj
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).obj K)).HasHomology := by
    change (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc 0).HasHomology
    infer_instance
  haveI : (F.mapShortComplex.obj
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).obj L)).HasHomology := by
    change (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).sc 0).HasHomology
    infer_instance
  haveI hmap : ShortComplex.QuasiIso
      (F.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map φ)) :=
    ShortComplex.quasiIso_map_of_preservesLeftHomology F
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map φ)
  change IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) 0).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)))
  have heq :
      (HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) 0).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) =
      F.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map φ) := by
    ext <;> rfl
  rw [heq]
  exact hmap.isIso


/-- The localization–homology comparison identifies the plus derived-category
H⁰ map with ordinary homology of a displayed complex morphism. -/
private lemma isIso_homologyZero_plusQ_map_of_homologyMap
    {K L : CochainComplex.Plus D} (ψ : K ⟶ L)
    [IsIso (HomologicalComplex.homologyMap ψ.hom 0)] :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Q.map ψ)) := by
  change IsIso ((DerivedCategory.homologyFunctor D 0).map
    (DerivedCategory.Q.map ψ.hom))
  change IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor D 0).map ψ.hom)
  rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D 0) ψ.hom]
  change IsIso (HomologicalComplex.homologyMap ψ.hom 0)
  infer_instance

/-- Resolve the input by a strictly nonnegative complex of injectives.
Preservation of the input's outgoing kernel and the kernels in its chosen
resolution makes the mapped resolution an H⁰ isomorphism; unit naturality
then transfers invertibility to the input. -/
theorem isIso_homologyZero_map_rightDerivedFunctorPlusUnit_of_isStrictlyGE_zero
    (K : CochainComplex.Plus C) [K.obj.IsStrictlyGE 0]
    (hK : PreservesLimit (parallelPair (K.obj.sc 0).g 0) F)
    (hResKernel : ∀ (L : CochainComplex.Plus (InjectiveObject C)) [L.obj.IsStrictlyGE 0],
      (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L) →
      CochainComplex.Plus.quasiIso C i → PreservesLimit (parallelPair
        (((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj.sc 0).g 0) F) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient C).obj K))) := by
  obtain ⟨L, hL, i, hi⟩ :=
    CochainComplex.Plus.exists_quasiIso_injective K 0
  let J := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let w : (HomotopyCategory.Plus.quotient C).obj K ⟶
      (HomotopyCategory.Plus.quotient C).obj J :=
    (HomotopyCategory.Plus.quotient C).map i
  have hw : (HomotopyCategory.Plus.quasiIso C) w := by
    change HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map i.hom)
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact hi
  haveI hJ : J.obj.IsStrictlyGE 0 := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj) 0
    rwa [CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff]
  haveI hi' : QuasiIso i.hom := by
    exact hi
  letI : PreservesLimit (parallelPair (K.obj.sc 0).g 0) F := hK
  letI : L.obj.IsStrictlyGE 0 := hL
  letI : PreservesLimit (parallelPair (J.obj.sc 0).g 0) F := hResKernel L i hi
  have hzK : (K.obj.sc 0).f = 0 := by
    change K.obj.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    exact (K.obj.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _
  have hzJ : (J.obj.sc 0).f = 0 := by
    change J.obj.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    exact (J.obj.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _
  haveI hmap : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom) 0) :=
    isIso_homologyMap_of_zero_incoming F K.obj J.obj i.hom hzK hzJ
  have hmapPlus : IsIso (HomologicalComplex.homologyMap
      (F.mapCochainComplexPlus.map i).hom 0) := by
    change IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom) 0)
    exact hmap
  have hplus : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i))) := by
    letI := hmapPlus
    exact isIso_homologyZero_plusQ_map_of_homologyMap _
  have hsource : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map w)) := by
    change IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i)))
    exact hplus
  exact isIso_homologyZero_unit_of_resolution F _ _ w hw

/-- For a degree-zero single, the source outgoing differential is zero and
its kernel is automatically preserved. Only kernels in resolutions receiving
a quasi-isomorphism from this single remain as premises. -/
theorem isIso_homologyZero_map_rightDerivedFunctorPlusUnit_single (X : C)
    (hResKernel : ∀ (L : CochainComplex.Plus (InjectiveObject C)) [L.obj.IsStrictlyGE 0],
      (i : (⟨(CochainComplex.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩ :
        CochainComplex.Plus C) ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L) →
      CochainComplex.Plus.quasiIso C i → PreservesLimit (parallelPair
        (((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj.sc 0).g 0) F) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X))) := by
  let K : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩
  haveI : K.obj.IsStrictlyGE 0 := inferInstance
  have hK : PreservesLimit (parallelPair (K.obj.sc 0).g 0) F := by
    apply Limits.preservesKernel_zero'
    simp [K]
    rfl
  have h :=
    isIso_homologyZero_map_rightDerivedFunctorPlusUnit_of_isStrictlyGE_zero F K hK hResKernel
  change IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X))) at h
  exact h

/-- Normalize the source of the derived unit by composing the localization–
homology, mapped-single, and single-object homology comparisons. -/
private noncomputable def sourceH0SingleIso (X : C) :
    (DerivedCategory.Plus.homologyFunctor D 0).obj
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X)) ≅ F.obj X := by
  let M := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CochainComplex.singleFunctor C 0).obj X)
  let t := (DerivedCategory.homologyFunctorFactors D 0).app M
  let m := (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).mapIso
    ((F.mapCochainComplexSingleFunctor 0).app X)
  let s := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj X)
  exact t ≪≫ m ≪≫ s

/-- Invert H⁰ of the derived unit on this single, then compose with the
canonical source comparison to `F.obj X`. This packages a pointwise
isomorphism; naturality in `X` remains separate. -/
noncomputable def rightDerivedFunctorPlusHomologyZeroSingleIso (X : C)
    (hResKernel : ∀ (L : CochainComplex.Plus (InjectiveObject C)) [L.obj.IsStrictlyGE 0],
      (i : (⟨(CochainComplex.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩ :
        CochainComplex.Plus C) ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L) →
      CochainComplex.Plus.quasiIso C i → PreservesLimit (parallelPair
        (((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj.sc 0).g 0) F) :
    (DerivedCategory.Plus.homologyFunctor D 0).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      F.obj X := by
  let K := (HomotopyCategory.Plus.singleFunctor C 0).obj X
  let H := DerivedCategory.Plus.homologyFunctor D 0
  let α := F.rightDerivedFunctorPlusUnit
  haveI : IsIso (H.map (α.app K)) :=
    isIso_homologyZero_map_rightDerivedFunctorPlusUnit_single F X hResKernel
  let e := (asIso (H.map (α.app K))).symm
  exact e ≪≫ sourceH0SingleIso F X


/-- Finite-limit preservation supplies every outgoing kernel condition
required by the pointwise single-object comparison. -/
noncomputable def rightDerivedFunctorPlusHomologyZeroSingleIsoOfPreservesFiniteLimits
    (X : C) [PreservesFiniteLimits F] :
    (DerivedCategory.Plus.homologyFunctor D 0).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      F.obj X :=
  F.rightDerivedFunctorPlusHomologyZeroSingleIso X (fun _ _ _ => inferInstance)

end CategoryTheory.Functor
