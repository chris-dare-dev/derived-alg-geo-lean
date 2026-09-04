/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal

/-!
# Monoidal comparisons for scheme-module pullback

The sheafified tensor product is the canonical monoidal structure on all scheme-module sheaves.
Consequently, strong monoidality of Mathlib's existing `pullback f` functor is expressed by the
standard `Functor.Monoidal` class, not by a parallel repository-specific capability or carrier.

At the current Mathlib pin the strong-monoidal instance itself is an external input. This module
names its two standard comparison isomorphisms so line bundles, determinants, Picard classes, and
the projection-formula lane can share one API while the construction of that instance is pursued.
-/

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable section

/-- The tensor comparison supplied by a standard strong-monoidal structure on module pullback. -/
noncomputable def pullbackTensorIso (f : X ⟶ Y) [(pullback f).Monoidal]
    (M N : Y.Modules) :
    tensorObj ((pullback f).obj M) ((pullback f).obj N) ≅
      (pullback f).obj (tensorObj M N) := by
  change (pullback f).obj M ⊗ (pullback f).obj N ≅
    (pullback f).obj (M ⊗ N)
  exact Functor.Monoidal.μIso (pullback f) M N

/-- The unit comparison supplied by a standard strong-monoidal structure on module pullback. -/
noncomputable def pullbackUnitIso (f : X ⟶ Y) [(pullback f).Monoidal] :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  change (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules
  exact (Functor.Monoidal.εIso (pullback f)).symm

end

end AlgebraicGeometry.Scheme.Modules
