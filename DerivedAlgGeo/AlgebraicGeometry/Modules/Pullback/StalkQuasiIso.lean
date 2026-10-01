/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

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

universe u v

/-- Additivity follows from finite-product preservation, without computing
with stalk representatives. -/
theorem moduleStalkFunctor_additive (X : Scheme.{u}) (x : X) :
    (moduleStalkFunctor X x).Additive := by
  letI := moduleStalkFunctor_preservesFiniteLimits X x
  exact Functor.additive_of_preserves_binary_products _

attribute [local instance] moduleStalkFunctor_additive

/-- Coequalizer preservation is a specialization of the small-colimit theorem
for the existing module-stalk functor. -/
theorem moduleStalkFunctor_preservesParallelPairColimits
    (X : Scheme.{u}) (x : X) :
    PreservesColimitsOfShape WalkingParallelPair (moduleStalkFunctor X x) := by
  letI := moduleStalkFunctor_preservesFiniteColimits X x
  infer_instance

/-- Finite limits supply kernels and coequalizers supply cokernels, giving
preservation of homology by module stalks. -/
theorem moduleStalkFunctor_preservesHomology (X : Scheme.{u}) (x : X) :
    (moduleStalkFunctor X x).PreservesHomology := by
  letI := moduleStalkFunctor_additive X x
  letI := moduleStalkFunctor_preservesFiniteLimits X x
  letI := moduleStalkFunctor_preservesParallelPairColimits X x
  exact { preservesKernels := fun _ => inferInstance,
          preservesCokernels := fun _ => inferInstance }

attribute [local instance] moduleStalkFunctor_preservesHomology
  HasDerivedCategory.standard

/-- Apply the pinned jointly-reflecting exact-functor criterion to all module
stalks. This detects quasi-isomorphisms for every complex shape. -/
theorem quasiIso_iff_stalkwise (X : Scheme.{u})
    {ι : Type v} {c : ComplexShape ι} {K L : HomologicalComplex X.Modules c}
    (g : K ⟶ L) :
    QuasiIso g ↔ ∀ x : X, QuasiIso
      (((moduleStalkFunctor X x).mapHomologicalComplex c).map g) := by
  letI (x : X) := moduleStalkFunctor_preservesFiniteLimits X x
  letI (x : X) :=
    (moduleStalkFunctor X x).preservesFiniteColimits_of_preservesHomology
  exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).quasiIso_iff g

end AlgebraicGeometry.Scheme.Modules
