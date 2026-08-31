/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Opposite
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Exact linear duality and its derived lift

Over a field, algebraic linear duality sends a module `V` to
`Vᵛ = Hom(V, k)`. This file bundles that construction as a contravariant
additive functor, proves that it takes short exact sequences to short exact
sequences, and therefore constructs its functor on derived categories.

To use this lift from the opposite of a derived category, a client supplies
the generic `CategoryTheory.DerivedCategory.OppositeComparison`. The resulting
derived linear-dual functors are categorical infrastructure; geometric Serre
duality imports them as consumers.
-/

universe u

open CategoryTheory

namespace ModuleCat

variable (k : Type u) [Field k]

/-- Algebraic linear dual, viewed as a contravariant functor on `k`-modules. -/
noncomputable def linearDualFunctor :
    (ModuleCat.{u + 1} k)ᵒᵖ ⥤ ModuleCat.{u + 1} k where
  obj V := ModuleCat.of k (Module.Dual k V.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id V := by
    apply ModuleCat.hom_ext
    exact LinearMap.dualMap_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.dualMap_comp_dualMap g.unop.hom f.unop.hom

@[simp]
theorem linearDualFunctor_obj (V : (ModuleCat.{u + 1} k)ᵒᵖ) :
    (linearDualFunctor k).obj V = ModuleCat.of k (Module.Dual k V.unop) :=
  rfl

@[simp]
theorem linearDualFunctor_map {V W : (ModuleCat.{u + 1} k)ᵒᵖ} (f : V ⟶ W) :
    (linearDualFunctor k).map f = ModuleCat.ofHom f.unop.hom.dualMap :=
  rfl

noncomputable instance : (linearDualFunctor k).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change (show Module.Dual k X.unop from φ) (f.unop.hom x + g.unop.hom x) =
      (show Module.Dual k X.unop from φ) (f.unop.hom x) +
        (show Module.Dual k X.unop from φ) (g.unop.hom x)
    exact map_add (show Module.Dual k X.unop from φ) _ _

/-- Linear duality reverses a short exact sequence of vector spaces to a short
exact sequence. -/
theorem linearDualFunctor_map_shortExact
    (S : ShortComplex ((ModuleCat.{u + 1} k)ᵒᵖ)) (hS : S.ShortExact) :
    (S.map (linearDualFunctor k)).ShortExact := by
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
    CategoryTheory.Limits.PreservesFiniteLimits (linearDualFunctor k) ∧
      CategoryTheory.Limits.PreservesFiniteColimits (linearDualFunctor k) :=
  (CategoryTheory.Functor.exact_tfae (linearDualFunctor k)).out 0 3 |>.mp
    fun (S : ShortComplex ((ModuleCat.{u + 1} k)ᵒᵖ)) hS ↦
      linearDualFunctor_map_shortExact k S hS

/-- Linear duality preserves finite limits, being exact. -/
theorem linearDualFunctor_preservesFiniteLimits :
    CategoryTheory.Limits.PreservesFiniteLimits (linearDualFunctor k) :=
  (linearDualFunctor_preservesFiniteLimits_and_colimits k).1

/-- Linear duality preserves finite colimits, being exact. -/
theorem linearDualFunctor_preservesFiniteColimits :
    CategoryTheory.Limits.PreservesFiniteColimits (linearDualFunctor k) :=
  (linearDualFunctor_preservesFiniteLimits_and_colimits k).2

noncomputable instance :
    CategoryTheory.Limits.PreservesFiniteLimits (linearDualFunctor k) :=
  linearDualFunctor_preservesFiniteLimits k

noncomputable instance :
    CategoryTheory.Limits.PreservesFiniteColimits (linearDualFunctor k) :=
  linearDualFunctor_preservesFiniteColimits k

/-- The canonical derived-category localization for modules over a field. -/
noncomputable instance moduleHasDerivedCategory :
    HasDerivedCategory (ModuleCat.{u + 1} k) :=
  HasDerivedCategory.standard _

/-- The canonical derived-category localization for the opposite category of
modules over a field. -/
noncomputable instance oppositeModuleHasDerivedCategory :
    HasDerivedCategory ((ModuleCat.{u + 1} k)ᵒᵖ) :=
  HasDerivedCategory.standard _

/-- The derived functor induced by exact algebraic linear duality. Its source
is the derived category of the opposite abelian category. -/
noncomputable def derivedLinearDualFunctor :
    DerivedCategory ((ModuleCat.{u + 1} k)ᵒᵖ) ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  (linearDualFunctor k).mapDerivedCategory

/-- Algebraic derived linear duality as a functor from the opposite derived
category, once the explicit opposite/derived comparison is supplied. -/
noncomputable def derivedLinearDualFromOpposite
    (B : CategoryTheory.DerivedCategory.OppositeComparison
      (ModuleCat.{u + 1} k)) :
    (DerivedCategory (ModuleCat.{u + 1} k))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  B.equivalence.functor ⋙ derivedLinearDualFunctor k

/-- Derived linear duality followed by a cohomological shift. -/
noncomputable def derivedLinearDualShift
    (B : CategoryTheory.DerivedCategory.OppositeComparison
      (ModuleCat.{u + 1} k)) (n : ℤ) :
    (DerivedCategory (ModuleCat.{u + 1} k))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  derivedLinearDualFromOpposite k B ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{u + 1} k)) n

end ModuleCat
