/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.FreeYonedaKFlat
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.LeftDerivedTensor
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Stalk
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.StalkQuasiIso
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Pullback of quasi-isomorphisms between K-flat scheme-module complexes

Arbitrary scheme pullback preserves a quasi-isomorphism between complexes
whose right tensor functors invert quasi-isomorphisms. K-flatness supplies
these two hypotheses. The argument uses the free-Yoneda K-flat resolution,
exactness and detection of quasi-isomorphisms at module stalks, and the
fixed-left ordinary tensor/stalk natural isomorphism.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.quasiIso_pullback_of_tensorRight_inverts`
  uses only the right tensor-inversion halves of K-flatness.

## Main results

* `AlgebraicGeometry.Scheme.Modules.quasiIso_pullback_of_isKFlat` specializes
  this to K-flat complexes.

## Implementation notes

The generic functor and scalar-change transports below are private proof
helpers. No derived pullback functor is asserted in this file.

## References

`AlgebraicGeometry.Scheme.Modules.pullback` is the pinned Mathlib functor.
The fixed-left tensor and stalk comparisons used here are existing repository
results, combined with the canonical free-Yoneda K-flat resolution.

## Tags

scheme module, pullback, K-flat complex, quasi-isomorphism
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
noncomputable section
universe u v w
attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor_additive

private theorem qiso_congr_natIso
    {C : Type u} [Category C] [HasZeroMorphisms C]
    {D : Type v} [Category D] [Abelian D]
    (F G : C ⥤ D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G) {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (h : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  let em := NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
  have hFi : IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  have hcomp : IsIso (DerivedCategory.Q.map (em.hom.app K) ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
    rw [← Functor.map_comp, ← em.hom.naturality g, Functor.map_comp]
    infer_instance
  have hGi : IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :=
    (isIso_comp_left_iff _ _).mp hcomp
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hGi

private theorem quasiIso_tensorLeft_of_tensorRight_inverts
    (Y : Scheme.{u})
    {K L : CochainComplex Y.Modules ℤ} (g : K ⟶ L)
    (hg : HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ) g)
    (hK : (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((Scheme.Modules.totalTensor Y).flip.obj K ⋙ DerivedCategory.Q))
    (hL : (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((Scheme.Modules.totalTensor Y).flip.obj L ⋙ DerivedCategory.Q))
    (M : Y.Modules) :
    QuasiIso (((Scheme.Modules.tensorLeftFunctor M).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := by
  let R := AlgebraicGeometry.DerivedCategory.freeYonedaSchemeKFlatResolution Y
  let F := (Scheme.Modules.totalTensor Y).obj
    (AlgebraicGeometry.DerivedCategory.singleComplex Y M)
  let G := (Scheme.Modules.tensorLeftFunctor M).mapHomologicalComplex (ComplexShape.up ℤ)
  let e : F ≅ G := AlgebraicGeometry.DerivedCategory.singleLeftTensorIso Y M
  have hF : IsIso ((AlgebraicGeometry.DerivedCategory.SchemeDerivedCategory.Q Y).map (F.map g)) :=
    R.isIso_Q_map_tensorLeft_of_inverts hK hL g hg
      (AlgebraicGeometry.DerivedCategory.singleComplex Y M)
  have hcomp : IsIso
      ((AlgebraicGeometry.DerivedCategory.SchemeDerivedCategory.Q Y).map (e.hom.app K) ≫
        (AlgebraicGeometry.DerivedCategory.SchemeDerivedCategory.Q Y).map (G.map g)) := by
    rw [← Functor.map_comp, ← e.hom.naturality g, Functor.map_comp]
    infer_instance
  have hG : IsIso ((AlgebraicGeometry.DerivedCategory.SchemeDerivedCategory.Q Y).map (G.map g)) :=
    (isIso_comp_left_iff _ _).mp hcomp
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  change IsIso (DerivedCategory.Q.map (G.map g)) at hG
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hG

private theorem qiso_restrictScalars_reflect
    {R S : Type u} [Ring R] [Ring S] (r : R →+* S)
    {ι : Type w} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} S) c} (g : K ⟶ L)
    (h : QuasiIso (((ModuleCat.restrictScalars r).mapHomologicalComplex
      c).map g)) : QuasiIso g := by
  letI : (ModuleCat.restrictScalars r).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (ModuleCat.restrictScalars r).PreservesHomology :=
    { preservesKernels := fun _ => inferInstance,
      preservesCokernels := fun _ => inferInstance }
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology g
    (ModuleCat.restrictScalars r)).1 h

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along any scheme morphism preserves a quasi-isomorphism when
both source complexes invert quasi-isomorphisms under tensor in the right slot.
The proof tests after stalks, realizes the needed stalk module by a sheaf, and
uses the ordinary fixed-left tensor/stalk comparison. -/
theorem quasiIso_pullback_of_tensorRight_inverts
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ} (g : K ⟶ L)
    (hg : HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ) g)
    (hK : (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((Scheme.Modules.totalTensor Y).flip.obj K ⋙ DerivedCategory.Q))
    (hL : (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((Scheme.Modules.totalTensor Y).flip.obj L ⋙ DerivedCategory.Q)) :
    QuasiIso (((Scheme.Modules.pullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := by
  apply (Scheme.Modules.quasiIso_iff_stalkwise X _).2
  intro x
  let r := (f.stalkMap x).hom
  let N : ModuleCat.{u} (Y.presheaf.stalk (f x)) :=
    (ModuleCat.restrictScalars r).obj (ModuleCat.of _ (X.presheaf.stalk x))
  obtain ⟨M, ⟨eM⟩⟩ := Scheme.Modules.exists_sheaf_with_stalk Y (f x) N
  let stY := Scheme.Modules.moduleStalkFunctor Y (f x)
  let stX := Scheme.Modules.moduleStalkFunctor X x
  let gy := (stY.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  have hM : QuasiIso (((tensorLeft M).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) :=
    quasiIso_tensorLeft_of_tensorRight_inverts Y g hg hK hL M
  letI : stY.PreservesHomology := Scheme.Modules.moduleStalkFunctor_preservesHomology Y (f x)
  have hMst : QuasiIso ((stY.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
    letI : QuasiIso (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).map g) := hM
    infer_instance
  have hMst' : QuasiIso
      (((tensorLeft M ⋙ stY).mapHomologicalComplex (ComplexShape.up ℤ)).map g) := hMst
  have hst : QuasiIso
      (((stY ⋙ tensorLeft (stY.obj M)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) :=
    qiso_congr_natIso _ _ (Scheme.Modules.fixedLeftTensorStalkIso Y (f x) M).symm g hMst'
  have hst' : QuasiIso (((tensorLeft (stY.obj M)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map gy) := hst
  have hN : QuasiIso (((tensorLeft N).mapHomologicalComplex
      (ComplexShape.up ℤ)).map gy) :=
    qiso_congr_natIso _ _ ((curriedTensor (ModuleCat.{u} (Y.presheaf.stalk (f x)))).mapIso eM)
      gy hst'
  have hRestr : QuasiIso (((ModuleCat.restrictScalars r).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
      (((ModuleCat.extendScalars r).mapHomologicalComplex (ComplexShape.up ℤ)).map gy)) := by
    change QuasiIso
      ((((ModuleCat.extendScalars r ⋙ ModuleCat.restrictScalars r).mapHomologicalComplex
        (ComplexShape.up ℤ)).map gy))
    exact hN
  have hExt : QuasiIso (((ModuleCat.extendScalars r).mapHomologicalComplex
      (ComplexShape.up ℤ)).map gy) :=
    qiso_restrictScalars_reflect r _ hRestr
  have hExt' : QuasiIso (((stY ⋙ ModuleCat.extendScalars r).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := hExt
  have hPull : QuasiIso (((Scheme.Modules.pullback f ⋙ stX).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) :=
    qiso_congr_natIso _ _ (Scheme.Modules.pullbackStalkIso f x).symm g hExt'
  exact hPull


/-- K-flatness supplies the right tensor-inversion hypotheses at both
endpoints, so the stronger pullback criterion applies using only those halves
of the K-flatness assumptions. -/
theorem quasiIso_pullback_of_isKFlat
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ} (g : K ⟶ L)
    (hg : HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ) g)
    (hK : CochainComplex.IsKFlat (Scheme.Modules.totalTensor Y) K)
    (hL : CochainComplex.IsKFlat (Scheme.Modules.totalTensor Y) L) :
    QuasiIso (((Scheme.Modules.pullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) :=
  quasiIso_pullback_of_tensorRight_inverts f g hg hK.2 hL.2

end AlgebraicGeometry.Scheme.Modules
end
