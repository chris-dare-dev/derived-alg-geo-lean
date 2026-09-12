/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExtLinear
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundleLinear
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.Adjunction

/-!
# Ext from a line bundle as coherent cohomology

Tensoring by an explicitly invertible module sheaf is an exact autoequivalence. Its derived Ext
adjunction, followed by the linear unit-Ext/cohomology comparison, identifies

`Extⁿ_{X.Modules}(L, N) ≃ₗ[k] Hⁿ(X, L⁻¹ ⊗ N)`.

For a coherent `N`, invertible tensor preserves finite presentation, so the cohomology target is
canonically an object of `Coh X`. This is entirely an ambient-module-sheaf theorem: it does not
identify Ext in `Coh X` with Ext in `X.Modules`, and therefore does not discharge the separate
`CoherentExtComparison` obligation.

## Main result

* `LineBundleData.extLineLinearEquivCoherentH` is the base-field-linear comparison for a coherent
  target.
-/

universe u

open CategoryTheory MonoidalCategory Abelian
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.LineBundleData

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.hasExt_of_hasDerivedCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))]

private noncomputable instance tensorLeftEquivalenceFunctorAdditive
    (L : LineBundleData X) : L.tensorLeftEquivalence.functor.Additive := by
  change (tensorLeft L.line).Additive
  infer_instance

private noncomputable instance tensorLeftEquivalenceInverseAdditive
    (L : LineBundleData X) : L.tensorLeftEquivalence.inverse.Additive := by
  change (tensorLeft L.inverse).Additive
  infer_instance

private noncomputable instance tensorLeftEquivalenceFunctorLinear
    (L : LineBundleData X) : L.tensorLeftEquivalence.functor.Linear k := by
  change (tensorLeft L.line).Linear k
  infer_instance

private noncomputable instance tensorLeftEquivalenceInverseLinear
    (L : LineBundleData X) : L.tensorLeftEquivalence.inverse.Linear k := by
  change (tensorLeft L.inverse).Linear k
  infer_instance

/-- **Ext from a line bundle is the cohomology of the inverse twist.**

The first equivalence replaces `L` by `L ⊗ 𝒪_X`, the second is derived Ext transport across the
exact tensor autoequivalence, and the third is the linear unit-Ext/cohomology comparison. -/
noncomputable def extLineLinearEquivCoherentH (L : LineBundleData X) (N : X.Modules)
    (hN : IsCoherent X N) (n : ℕ) :
    Ext.{u + 1} L.line N n ≃ₗ[k]
      (Cohomology.linearCoherentH k X n).obj
        ⟨tensorObj L.inverse N,
          isFinitePresentation_tensorObj_left_of_isInvertible L.inverse N hN⟩ :=
  (Ext.precompLinearEquiv (S := k) (tensorUnitRightIso L.line) N n).trans
    ((extAdjunctionLinearEquiv (S := k) L.tensorLeftEquivalence.toAdjunction
      (AlgebraicGeometry.Scheme.Modules.unit X) N n).trans
      (extUnitLinearEquivCoherentH
        ⟨tensorObj L.inverse N,
          isFinitePresentation_tensorObj_left_of_isInvertible L.inverse N hN⟩ n))

end AlgebraicGeometry.Scheme.Modules.LineBundleData
