/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Adjunction
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopowerFunctor
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearEvaluation
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearHomFunctor

/-!
# The scalar-linear copower--Hom dg adjunction

In a `k`-linear dg category with scalar-linear copowers, the selected copower
functor `- ⊗ E` is left dg adjoint to the linear Hom-complex functor
`Hom(E, -)`.  The unit is the universal chain map of the selected copower and
the counit is exactly the existing scalar-linear evaluation transformation.

Both triangle identities hold strictly in the dg categories.  This file does
not use pretriangulatedness, cones, finiteness, or a model of `Perf(k)`, and it
makes no sphericality or equivalence claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u w

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable (k : Type w) [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

namespace LinearEvaluationData

/-- The selected scalar-linear evaluation functor is the composite of the
linear Hom-complex functor with the selected copower functor. -/
theorem ofHasLinearCopowers_functor_eq (E : C) :
    (ofHasLinearCopowers k E).functor =
      (DGLinear.homFunctor k E).comp (linearCopowerFunctor k E) :=
  rfl

end LinearEvaluationData

private noncomputable def linearCopowerAdjunctionUnit (E : C) :
    DGFunctor.HomogeneousNatTrans (DGFunctor.id (Cdg (ModuleCat.{v} k)))
      ((linearCopowerFunctor k E).comp (DGLinear.homFunctor k E)) 0 :=
  ⟨fun K => CochainComplex.HomComplex.Cochain.ofHom
      (linearCopowerIsLinearCopower (Cdg.of _ K) E).univ,
    by
      intro K L p r hpr hrp γ
      rw [zero_mul, Int.negOnePow_zero, one_smul]
      obtain rfl : r = p := by omega
      dsimp only [DGFunctor.id, DGFunctor.comp, linearCopowerFunctor,
        DGLinear.homFunctor, DGFunctor.HomogeneousNatTrans.app]
      rw [Cdg.dgComp_eq, Cdg.dgComp_eq]
      change γ.comp
          (CochainComplex.HomComplex.Cochain.ofHom
            (linearCopowerIsLinearCopower (Cdg.of _ L) E).univ) hpr =
        (CochainComplex.HomComplex.Cochain.ofHom
          (linearCopowerIsLinearCopower (Cdg.of _ K) E).univ).comp
          (DGLinear.postcompCochain k E r
            ((linearCopowerIsLinearCopower (Cdg.of _ K) E).coefficientMap
              (linearCopowerIsLinearCopower (Cdg.of _ L) E) r γ)) hrp
      apply CochainComplex.HomComplex.Cochain.ext
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [CochainComplex.HomComplex.Cochain.comp_v,
        CochainComplex.HomComplex.Cochain.comp_v,
        CochainComplex.HomComplex.Cochain.ofHom_v,
        CochainComplex.HomComplex.Cochain.ofHom_v]
      dsimp only [DGLinear.postcompCochain]
      change
        (linearCopowerIsLinearCopower (Cdg.of _ L) E).univ.f j
            ((γ.v i j hij).hom x) =
          dgComp i r j hij
            ((linearCopowerIsLinearCopower (Cdg.of _ K) E).univ.f i x)
            ((linearCopowerIsLinearCopower (Cdg.of _ K) E).coefficientMap
              (linearCopowerIsLinearCopower (Cdg.of _ L) E) r γ)
      exact (IsLinearCopowerOf.univ_comp_coefficientMap
        (linearCopowerIsLinearCopower (Cdg.of _ K) E)
        (linearCopowerIsLinearCopower (Cdg.of _ L) E) r γ i j hij x).symm
      all_goals omega⟩

private lemma linearCopowerAdjunctionUnit_isClosed (E : C) :
    DGFunctor.HomogeneousNatTrans.IsClosed
      (linearCopowerAdjunctionUnit k E) := by
  ext K
  change CochainComplex.HomComplex.δ 0 1
      (CochainComplex.HomComplex.Cochain.ofHom
        (linearCopowerIsLinearCopower (Cdg.of _ K) E).univ) = 0
  exact CochainComplex.HomComplex.δ_ofHom _

/-- The selected scalar-linear copower functor is left dg adjoint to the
linear Hom-complex functor. -/
noncomputable def linearCopowerAdjunction (E : C) :
    DGAdjunction (linearCopowerFunctor k E) (DGLinear.homFunctor k E) where
  unit := linearCopowerAdjunctionUnit k E
  counit := (LinearEvaluationData.ofHasLinearCopowers k E).evaluation
  unit_isClosed := linearCopowerAdjunctionUnit_isClosed k E
  counit_isClosed :=
    (LinearEvaluationData.ofHasLinearCopowers k E).evaluation_isClosed
  left_triangle K := by
    let ZK := linearCopowerObj (Cdg.of _ K) E
    let tK := linearCopowerIsLinearCopower (Cdg.of _ K) E
    let V := LinearEvaluationData.ofHasLinearCopowers k E
    refine tK.lift_unique (fun i j hij x => ?_)
    obtain rfl : j = i := by omega
    change
      dgComp j 0 j (by omega) (tK.univ.f j x)
          (dgComp 0 0 0 (by omega)
            (tK.coefficientMap (V.isLinearCopower ZK) 0
              (CochainComplex.HomComplex.Cochain.ofHom tK.univ))
            (V.evalHom ZK)) =
        dgComp j 0 j (by omega) (tK.univ.f j x) (dgId ZK)
    rw [← dgComp_assoc j 0 0 j 0 j (by omega) (by omega) (by omega),
      tK.univ_comp_coefficientMap,
      CochainComplex.HomComplex.Cochain.ofHom_v,
      V.univ_comp_evalHom, dgComp_id]
  right_triangle Y := by
    let V := LinearEvaluationData.ofHasLinearCopowers k E
    dsimp only [linearCopowerAdjunctionUnit,
      LinearEvaluationData.evaluation, DGFunctor.HomogeneousNatTrans.app,
      DGLinear.homFunctor, DGFunctor.comp]
    rw [Cdg.dgComp_eq, Cdg.dgId_eq]
    change
      (CochainComplex.HomComplex.Cochain.ofHom
        (linearCopowerIsLinearCopower
          (DGLinear.homComplex k E Y) E).univ).comp
        (DGLinear.postcompCochain k E 0
          ((LinearEvaluationData.ofHasLinearCopowers k E).evalHom Y))
        (by omega) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (DGLinear.homComplex k E Y))
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    obtain rfl : j = i := by omega
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rw [CochainComplex.HomComplex.Cochain.comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    dsimp only [DGLinear.postcompCochain]
    change dgComp j 0 j (by omega)
        ((V.isLinearCopower Y).univ.f j g) (V.evalHom Y) = g
    exact V.univ_comp_evalHom Y j g
    all_goals omega

/-- The unit component of the scalar-linear copower--Hom dg adjunction is the
universal chain map of the selected copower. -/
theorem linearCopowerAdjunction_unit_app (E : C)
    (K : Cdg (ModuleCat.{v} k)) :
    DGFunctor.HomogeneousNatTrans.app (linearCopowerAdjunction k E).unit K =
      CochainComplex.HomComplex.Cochain.ofHom
        (linearCopowerIsLinearCopower (Cdg.of _ K) E).univ :=
  rfl

/-- The counit of the scalar-linear copower--Hom dg adjunction is exactly the
selected scalar-linear evaluation transformation. -/
theorem linearCopowerAdjunction_counit (E : C) :
    (linearCopowerAdjunction k E).counit =
      (LinearEvaluationData.ofHasLinearCopowers k E).evaluation :=
  rfl

/-- Because the adjunction reuses the existing evaluation transformation, its
counit component reduces definitionally to the selected representing lift of
the identity cochain. -/
theorem linearCopowerAdjunction_counit_app (E Y : C) :
    DGFunctor.HomogeneousNatTrans.app (linearCopowerAdjunction k E).counit Y =
      (LinearEvaluationData.ofHasLinearCopowers k E).evalHom Y :=
  rfl

end CategoryTheory
