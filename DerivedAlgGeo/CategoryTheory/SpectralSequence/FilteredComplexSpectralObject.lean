/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-!
# The spectral object of a filtered complex

Mathlib constructs a triangulated spectral object from mapping cones and observes that
precomposing it with a functor into cochain complexes produces the spectral object associated to
a filtered complex. The remaining bridge applies a homological functor to obtain a spectral
object in an abelian category.

This file supplies that bridge for an arbitrary homological functor and then specializes it to
homology on the homotopy category.  Thus a filtration
`K : ι ⥤ CochainComplex C ℤ` canonically produces an
`Abelian.SpectralObject C ι`, which Mathlib assembles into a spectral sequence.
-/

namespace CategoryTheory

open ComposableArrows Limits Pretriangulated

namespace Triangulated

namespace SpectralObject

variable {D A ι : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Category* A] [Abelian A] [Category* ι]

/-- Applying a homological functor, in every shifted degree, to a triangulated spectral object
produces a spectral object in the target abelian category. -/
noncomputable def mapHomologicalFunctor (X : SpectralObject D ι) (F : D ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ hn₁ :=
    { app T := F.homologySequenceδ (X.ω₂.obj T) n₀ n₁ hn₁
      naturality T T' φ :=
        F.homologySequenceδ_naturality (X.ω₂.obj T) (X.ω₂.obj T') (X.ω₂.map φ)
          n₀ n₁ hn₁ }
  exact₁' n₀ n₁ hn₁ T :=
    (F.homologySequence_exact₁ (X.ω₂.obj T) (X.ω₂_obj_distinguished T)
      n₀ n₁ hn₁).exact_toComposableArrows
  exact₂' n T :=
    (F.homologySequence_exact₂ (X.ω₂.obj T) (X.ω₂_obj_distinguished T)
      n).exact_toComposableArrows
  exact₃' n₀ n₁ hn₁ T :=
    (F.homologySequence_exact₃ (X.ω₂.obj T) (X.ω₂_obj_distinguished T)
      n₀ n₁ hn₁).exact_toComposableArrows

end SpectralObject

end Triangulated

end CategoryTheory

namespace HomotopyCategory

open CategoryTheory

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]

/-- The abelian spectral object associated to a filtered cochain complex
`K : ι ⥤ CochainComplex C ℤ`. -/
noncomputable def filteredComplexSpectralObject (K : ι ⥤ CochainComplex C ℤ) :
    CategoryTheory.Abelian.SpectralObject C ι :=
  ((spectralObjectMappingCone C).precomp K).mapHomologicalFunctor
    (homologyFunctor C (ComplexShape.up ℤ) 0)

end HomotopyCategory
