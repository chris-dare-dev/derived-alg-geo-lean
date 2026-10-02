/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyHomotopy

/-!
# Degree-zero Hom-complex classes and derived-category morphisms

For a K-projective source, degree-zero cohomology classes of the Hom complex
identify additively with morphisms in the derived category. This compares
Hom-sets; it does not construct an internal derived-Hom object.
The dual comparison uses a K-injective target.

## Main definitions

* `CochainComplex.HomComplex.CohomologyClass.derivedCategoryHomAddEquiv`
  uses a K-projective source.
* `CochainComplex.HomComplex.CohomologyClass.derivedCategoryHomAddEquivOfKInjective`
  uses a K-injective target.

## Main results

Both comparisons preserve addition and identify degree-zero classes with
ordinary derived-category morphisms.

## Implementation notes

The neutral `CochainComplex.HomComplex.cohomologyClassHomotopyAddEquiv`
owns zero-shift normalization. Mathlib's bijectivity of localization maps
then uses the relevant K-projective or K-injective hypothesis.

## References

Mathlib's `HomComplexCohomology.lean`, `KProjective.lean`, and
`KInjective.lean` at pin `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

Hom complex, derived category, K-projective, K-injective
-/

open CategoryTheory

namespace CochainComplex.HomComplex.CohomologyClass

universe u v

/-- Degree-zero Hom-complex classes are derived-category morphisms when the
source complex is K-projective. The equivalence is additive; no scalar-linearity
or base-change compatibility is asserted. -/
noncomputable def derivedCategoryHomAddEquiv
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [K.IsKProjective] :
    CohomologyClass K L 0 ≃+
      ((DerivedCategory.Qh).obj ((HomotopyCategory.quotient C (.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh).obj ((HomotopyCategory.quotient C (.up ℤ)).obj L)) := by
  let Kₕ := (HomotopyCategory.quotient C (.up ℤ)).obj K
  let Lₕ := (HomotopyCategory.quotient C (.up ℤ)).obj L
  let e₂ : (Kₕ ⟶ Lₕ) ≃+
      ((DerivedCategory.Qh).obj Kₕ ⟶ (DerivedCategory.Qh).obj Lₕ) :=
    AddEquiv.ofBijective (Functor.mapAddHom DerivedCategory.Qh)
      (CochainComplex.IsKProjective.Qh_map_bijective K Lₕ)
  exact (CochainComplex.HomComplex.cohomologyClassHomotopyAddEquiv K L).trans e₂

/-- Degree-zero Hom-complex classes are derived-category morphisms when the
target complex is K-injective. This is the target-side counterpart of
`CochainComplex.HomComplex.CohomologyClass.derivedCategoryHomAddEquiv`;
no K-projectivity of the source is needed. -/
noncomputable def derivedCategoryHomAddEquivOfKInjective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] :
    CohomologyClass K L 0 ≃+
      ((DerivedCategory.Qh).obj ((HomotopyCategory.quotient C (.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh).obj ((HomotopyCategory.quotient C (.up ℤ)).obj L)) := by
  let Kₕ := (HomotopyCategory.quotient C (.up ℤ)).obj K
  let Lₕ := (HomotopyCategory.quotient C (.up ℤ)).obj L
  let e₂ : (Kₕ ⟶ Lₕ) ≃+
      ((DerivedCategory.Qh).obj Kₕ ⟶ (DerivedCategory.Qh).obj Lₕ) :=
    AddEquiv.ofBijective (Functor.mapAddHom DerivedCategory.Qh)
      (CochainComplex.IsKInjective.Qh_map_bijective Kₕ L)
  exact (CochainComplex.HomComplex.cohomologyClassHomotopyAddEquiv K L).trans e₂

end CochainComplex.HomComplex.CohomologyClass
