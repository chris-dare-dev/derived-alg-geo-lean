/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.LineBundleExtLinear
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveVariety

/-!
# Finiteness and amplitude of Ext from a line bundle

For a projectively presented variety, the linear comparison

`Extⁿ_{X.Modules}(L, N) ≃ₗ[k] Hⁿ(X, L⁻¹ ⊗ N)`

transports both halves of Serre finiteness: every degree is finite-dimensional, and the Ext groups
vanish above the finite-affine-cover cohomological bound of the coherent inverse twist. Thus the
natural-number finrank support is finite.

These results concern Ext in `X.Modules` with a line-bundle source. They do not claim Ext
finiteness for arbitrary coherent sources and do not compare with Ext internal to `Coh X`.

## Main results

* `ProjectivePresentation.module_finite_lineBundleExt` proves degreewise finite-dimensionality;
* `ProjectivePresentation.lineBundleExt_subsingleton_of_bound_lt` gives the explicit amplitude;
* `ProjectivePresentation.lineBundleExt_finrankSupport_finite` packages finite support.
-/

universe u

open CategoryTheory Abelian
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePresentation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.hasExt_of_hasDerivedCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))]

/-- Ext in `X.Modules` from a line bundle to a coherent module sheaf is finite-dimensional in
every nonnegative degree on a projectively presented variety. -/
theorem module_finite_lineBundleExt (P : ProjectivePresentation k X)
    [Nontrivial P.index] (L : Scheme.Modules.LineBundleData X) (N : X.Modules)
    (hN : Scheme.Modules.IsCoherent X N) (n : ℕ) :
    Module.Finite k (Ext.{u + 1} L.line N n) := by
  let T : Coh X :=
    ⟨Scheme.Modules.tensorObj L.inverse N,
      Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible L.inverse N hN⟩
  letI : Module.Finite k ((Cohomology.linearCoherentH k X n).obj T) :=
    P.module_finite_linearCoherentH n T
  exact Module.Finite.equiv
    (L.extLineLinearEquivCoherentH (k := k) N hN n).symm

variable [IsVariety k X]

/-- Ext from `L` to `N` vanishes strictly above the cohomological bound of
`L⁻¹ ⊗ N`. -/
theorem lineBundleExt_subsingleton_of_bound_lt (P : ProjectivePresentation k X)
    [Nontrivial P.index] (L : Scheme.Modules.LineBundleData X) (N : X.Modules)
    (hN : Scheme.Modules.IsCoherent X N) (n : ℕ)
    (hn : (P.finiteCohomology (k := k)).bound
      ⟨Scheme.Modules.tensorObj L.inverse N,
        Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible
          L.inverse N hN⟩ < n) :
    Subsingleton (Ext.{u + 1} L.line N n) := by
  let T : Coh X :=
    ⟨Scheme.Modules.tensorObj L.inverse N,
      Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible L.inverse N hN⟩
  haveI : Subsingleton ((Cohomology.linearCoherentH k X n).obj T) :=
    (P.finiteCohomology (k := k)).vanishesAbove T n hn
  exact (L.extLineLinearEquivCoherentH (k := k) N hN n).toEquiv.subsingleton

/-- The finrank support of ambient Ext from a line bundle lies below the cohomological bound of
the coherent inverse twist. -/
theorem lineBundleExt_finrankSupport_subset_range (P : ProjectivePresentation k X)
    [Nontrivial P.index] (L : Scheme.Modules.LineBundleData X) (N : X.Modules)
    (hN : Scheme.Modules.IsCoherent X N) :
    Function.support (fun n : ℕ ↦
      (Module.finrank k (Ext.{u + 1} L.line N n) : ℤ)) ⊆
      (Finset.range
        ((P.finiteCohomology (k := k)).bound
          ⟨Scheme.Modules.tensorObj L.inverse N,
            Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible
              L.inverse N hN⟩ + 1) : Set ℕ) := by
  intro n hn
  have hn_le : n ≤ (P.finiteCohomology (k := k)).bound
      ⟨Scheme.Modules.tensorObj L.inverse N,
        Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible
          L.inverse N hN⟩ := by
    by_contra h
    haveI : Subsingleton (Ext.{u + 1} L.line N n) :=
      P.lineBundleExt_subsingleton_of_bound_lt (k := k) L N hN n (Nat.lt_of_not_ge h)
    rw [Function.mem_support] at hn
    apply hn
    exact_mod_cast Module.finrank_zero_of_subsingleton
  simpa using Nat.lt_succ_of_le hn_le

/-- Only finitely many nonnegative Ext degrees from `L` to `N` have nonzero finrank. -/
theorem lineBundleExt_finrankSupport_finite (P : ProjectivePresentation k X)
    [Nontrivial P.index] (L : Scheme.Modules.LineBundleData X) (N : X.Modules)
    (hN : Scheme.Modules.IsCoherent X N) :
    (Function.support fun n : ℕ ↦
      (Module.finrank k (Ext.{u + 1} L.line N n) : ℤ)).Finite :=
  (Finset.finite_toSet _).subset
    (P.lineBundleExt_finrankSupport_subset_range (k := k) L N hN)

end AlgebraicGeometry.ProjectivePresentation
