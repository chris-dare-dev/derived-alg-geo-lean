/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ModuleCat.LinearDual
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Exact linear duality on modules over a field

Over a field, algebraic linear duality sends a module `V` to
`Vᵛ = Hom(V, k)`.  The contravariant additive functor is defined in
`CategoryTheory/ModuleCat/LinearDual.lean`; this file proves that it is exact:
it takes short exact sequences to short exact sequences and preserves finite
limits and colimits.  Its derived lift is
`Algebra/Homology/DerivedCategory/LinearDual.lean`.
-/


universe u

open CategoryTheory

namespace ModuleCat

variable (k : Type u) [Field k]

/-- Linear duality reverses a short exact sequence of vector spaces to a short
exact sequence. -/
theorem linearDualFunctor_map_shortExact
    (S : ShortComplex ((ModuleCat.{u + 1} k)ᵒᵖ)) (hS : S.ShortExact) :
    (S.map (linearDualFunctor.{u, u + 1} k)).ShortExact := by
  have hU : S.unop.ShortExact := hS.unop
  refine
    { exact := ?_
      mono_f := ?_
      epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range S.f.unop.hom.dualMap =
      LinearMap.ker S.g.unop.hom.dualMap
    have hRange := hU.exact.moduleCat_range_eq_ker
    change LinearMap.range S.g.unop.hom =
      LinearMap.ker S.f.unop.hom at hRange
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range, hRange]
  · rw [ModuleCat.mono_iff_injective]
    change Function.Injective S.f.unop.hom.dualMap
    rw [LinearMap.dualMap_injective_iff]
    exact hU.moduleCat_surjective_g
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective S.g.unop.hom.dualMap
    rw [LinearMap.dualMap_surjective_iff]
    exact hU.moduleCat_injective_f

/-- Exactness of algebraic linear duality, in the form Mathlib's
derived-functor construction consumes. -/
theorem linearDualFunctor_preservesFiniteLimits_and_colimits :
    CategoryTheory.Limits.PreservesFiniteLimits
        (linearDualFunctor.{u, u + 1} k) ∧
      CategoryTheory.Limits.PreservesFiniteColimits
        (linearDualFunctor.{u, u + 1} k) :=
  (CategoryTheory.Functor.exact_tfae
    (linearDualFunctor.{u, u + 1} k)).out 0 3 |>.mp
    fun (S : ShortComplex ((ModuleCat.{u + 1} k)ᵒᵖ)) hS ↦
      linearDualFunctor_map_shortExact k S hS

/-- Linear duality preserves finite limits, being exact. -/
theorem linearDualFunctor_preservesFiniteLimits :
    CategoryTheory.Limits.PreservesFiniteLimits
      (linearDualFunctor.{u, u + 1} k) :=
  (linearDualFunctor_preservesFiniteLimits_and_colimits k).1

/-- Linear duality preserves finite colimits, being exact. -/
theorem linearDualFunctor_preservesFiniteColimits :
    CategoryTheory.Limits.PreservesFiniteColimits
      (linearDualFunctor.{u, u + 1} k) :=
  (linearDualFunctor_preservesFiniteLimits_and_colimits k).2

noncomputable instance :
    CategoryTheory.Limits.PreservesFiniteLimits
      (linearDualFunctor.{u, u + 1} k) :=
  linearDualFunctor_preservesFiniteLimits k

noncomputable instance :
    CategoryTheory.Limits.PreservesFiniteColimits
      (linearDualFunctor.{u, u + 1} k) :=
  linearDualFunctor_preservesFiniteColimits k

end ModuleCat
