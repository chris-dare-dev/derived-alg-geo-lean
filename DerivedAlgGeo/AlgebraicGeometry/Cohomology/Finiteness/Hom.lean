/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveVariety
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundleLinear

/-!
# Finiteness of Hom from a line bundle

This file gives the honest reduction from Serre finiteness to finite-dimensional Hom spaces with
a line-bundle source. The linear comparison

`Hom(L, N) ≃ₗ[k] Γ(X, L⁻¹ ⊗ N)`

transports finite-dimensionality from coherent `H⁰`. Tensoring by the invertible sheaf `L⁻¹`
preserves finite presentation, so a coherent target `N` supplies the required coherent tensor
without an extra geometric premise.

## Main results

* `LineBundleData.module_finite_hom_of_finiteHZero` isolates the formal transport from finite
  coherent `H⁰` to finite Hom;
* `ProjectivePresentation.module_finite_lineBundleHom` supplies tensor coherence and the `H⁰`
  input from a coherent target and projective Serre finiteness.
-/

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.LineBundleData

/-- Finite-dimensional `H⁰` of the coherent tensor `L⁻¹ ⊗ N` implies that `Hom(L, N)` is
finite-dimensional. -/
theorem module_finite_hom_of_finiteHZero {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))]
    (L : LineBundleData Y) (N : Y.Modules)
    (hTensor : IsCoherent Y (tensorObj L.inverse N))
    (hHZero : Module.Finite k
      ((Cohomology.linearCoherentH k Y 0).obj
        ⟨tensorObj L.inverse N, hTensor⟩)) :
    Module.Finite k (L.line ⟶ N) := by
  let T : Coh Y := ⟨tensorObj L.inverse N, hTensor⟩
  have hSections := Cohomology.module_finite_linearGlobalSectionsObj Y T hHZero
  have hObj : ((Coh.ι Y).obj T) = tensorObj L.inverse N := rfl
  rw [hObj] at hSections
  letI : Module.Finite k
      (Cohomology.linearGlobalSectionsObj (k := k) Y (tensorObj L.inverse N)) := by
    exact hSections
  exact Module.Finite.equiv (L.lineHomTopLinearEquivOver Y N).symm

end AlgebraicGeometry.Scheme.Modules.LineBundleData

namespace AlgebraicGeometry.ProjectivePresentation

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))]

/-- Hom from a line bundle to a coherent module sheaf on a projectively presented variety is
finite-dimensional. -/
theorem module_finite_lineBundleHom (P : ProjectivePresentation k X)
    [Nontrivial P.index] (L : Scheme.Modules.LineBundleData X) (N : X.Modules)
    (hN : Scheme.Modules.IsCoherent X N) :
    Module.Finite k (L.line ⟶ N) := by
  have hTensor : Scheme.Modules.IsCoherent X
      (Scheme.Modules.tensorObj L.inverse N) :=
    Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible
      L.inverse N hN
  exact L.module_finite_hom_of_finiteHZero X N hTensor
    (P.module_finite_linearCoherentH 0
      ⟨Scheme.Modules.tensorObj L.inverse N, hTensor⟩)

end AlgebraicGeometry.ProjectivePresentation
