/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms detected by module stalks

Module stalks preserve homology. A map of complexes of scheme-module sheaves
is a quasi-isomorphism precisely when it is so at every module stalk.

## Main definitions

The existing `AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor` is the only
stalk functor used here.

## Main results

`AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor_preservesHomology` and
`AlgebraicGeometry.Scheme.Modules.quasiIso_iff_stalkwise` provide
the exactness and detection statements.

## Implementation notes

Additivity follows from finite-product preservation. Kernels and cokernels
are preserved by finite-limit and parallel-pair-colimit preservation.

## References

The proof uses Mathlib's homology-preservation criterion and the existing
joint isomorphism reflection theorem for module stalks.

## Tags

module stalk, quasi-isomorphism, homology
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The local-ring module stalk functor is additive. -/
theorem moduleStalkFunctor_additive (X : Scheme.{u}) (x : X) :
    (moduleStalkFunctor X x).Additive := by
  letI := moduleStalkFunctor_preservesFiniteLimits X x
  exact Functor.additive_of_preserves_binary_products _

attribute [local instance] moduleStalkFunctor_additive

/-- Module stalks preserve parallel-pair colimits. -/
theorem moduleStalkFunctor_preservesParallelPairColimits
    (X : Scheme.{u}) (x : X) :
    PreservesColimitsOfShape WalkingParallelPair (moduleStalkFunctor X x) := by
  let forgetModule := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let α := 𝟙 X.ringCatSheaf.obj
  letI : PreservesColimitsOfShape WalkingParallelPair
      (PresheafOfModules.sheafification α ⋙ SheafOfModules.toSheaf X.ringCatSheaf) := by
    exact inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  have hF : PreservesColimitsOfShape WalkingParallelPair
      (SheafOfModules.toSheaf X.ringCatSheaf) :=
    (PresheafOfModules.sheafificationAdjunction α).preservesColimitsOfShape_of_comp_left
      (K := WalkingParallelPair) (SheafOfModules.toSheaf X.ringCatSheaf)
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hG : PreservesColimitsOfShape WalkingParallelPair G := inferInstance
  have hFG : PreservesColimitsOfShape WalkingParallelPair
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙ G) :=
    @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _
      (SheafOfModules.toSheaf X.ringCatSheaf) G hF hG
  letI : PreservesColimitsOfShape WalkingParallelPair
      (moduleStalkFunctor X x ⋙ forgetModule) :=
    (preservesColimitsOfShape_iff_of_natIso (moduleStalkForgetIso X x)).mpr hFG
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (moduleStalkFunctor X x) forgetModule

/-- Taking a local-ring module stalk preserves homology. -/
theorem moduleStalkFunctor_preservesHomology (X : Scheme.{u}) (x : X) :
    (moduleStalkFunctor X x).PreservesHomology := by
  letI := moduleStalkFunctor_additive X x
  letI := moduleStalkFunctor_preservesFiniteLimits X x
  letI := moduleStalkFunctor_preservesParallelPairColimits X x
  exact { preservesKernels := fun _ => inferInstance,
          preservesCokernels := fun _ => inferInstance }

attribute [local instance] moduleStalkFunctor_preservesHomology
  HasDerivedCategory.standard

/-- Quasi-isomorphisms of complexes of scheme-module sheaves are detected at
all local-ring module stalks. -/
theorem quasiIso_iff_stalkwise (X : Scheme.{u})
    {K L : CochainComplex X.Modules ℤ} (g : K ⟶ L) :
    QuasiIso g ↔ ∀ x : X, QuasiIso
      (((moduleStalkFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) := by
  constructor
  · intro h x
    letI := h
    infer_instance
  · intro h
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    letI : ∀ x : X, IsIso ((moduleStalkFunctor X x).map
        (HomologicalComplex.homologyMap g n)) := by
      intro x
      let F := moduleStalkFunctor X x
      let φ := (HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) n).map g
      letI := h x
      have hi : IsIso ((F.mapShortComplex ⋙ ShortComplex.homologyFunctor _).map φ) := by
        exact (quasiIsoAt_iff_isIso_homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) n).mp inferInstance
      exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso F) φ).mp hi
    exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).isIso _

end AlgebraicGeometry.Scheme.Modules
