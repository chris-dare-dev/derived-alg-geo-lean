/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The spectral object of a filtered complex

Mathlib constructs a triangulated spectral object from mapping cones and observes that
precomposing it with a functor into cochain complexes produces the spectral object associated to
a filtered complex. The remaining bridge applies a homological functor to obtain a spectral
object in an abelian category.

Mathlib (since v4.35) supplies that bridge for an arbitrary homological functor as
`CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor`; this file specializes it to
homology on the homotopy category.  Thus a filtration
`K : ι ⥤ CochainComplex C ℤ` canonically produces an
`Abelian.SpectralObject C ι`, which Mathlib assembles into a spectral sequence.

## Main definitions

* `HomotopyCategory.filteredComplexSpectralObject`: the abelian spectral object of a filtered
  cochain complex.

## Main results

* None beyond the definition: its properties are those of Mathlib's spectral objects.

## Implementation notes

Until the Lean/Mathlib v4.35 bump this file also defined
`CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor`; Mathlib now provides it
under the same name and shape, so the local copy was removed.

## References

* Mathlib `CategoryTheory/Triangulated/SpectralObject.lean` and
  `Algebra/Homology/HomotopyCategory/SpectralObject.lean`.

## Tags

spectral object, spectral sequence, filtered complex, homological functor
-/

-- `CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor`, formerly defined here, is
-- upstream in Mathlib since v4.35 (`Mathlib/CategoryTheory/Triangulated/SpectralObject.lean`).

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
