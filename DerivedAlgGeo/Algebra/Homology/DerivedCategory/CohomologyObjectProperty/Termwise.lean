/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty

/-!
# Cohomology membership from terms of a complex

A property of objects closed under kernels and cokernels passes from the
adjacent terms of a complex to its homology. Closure under isomorphisms then
transports this membership to the corresponding object of the derived category.
The result applies to unbounded complexes without extension closure.

## Main definitions

This file introduces no new carrier, class, or instance.

## Main results

* `DerivedCategory.cohomologyIn_Q_obj_of_termwise` places the localization of
  a termwise-property complex in the existing cohomology object property.

## Implementation notes

The cycle object is a kernel of the outgoing differential. Homology is a
cokernel of the map from the predecessor term to cycles. The private helpers
use only the three adjacent terms; the public theorem uses every term and the
canonical derived homology comparison.

## References

The proof uses Mathlib's `HomologicalComplex.cyclesIsKernel`,
`HomologicalComplex.homologyIsCokernel`, and
`DerivedCategory.homologyFunctorFactors` at the pinned Mathlib revision.

## Tags

Derived category; homology; object property.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

universe t v u w

private lemma cycles_property_of_terms {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {ι : Type t} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsClosedUnderKernels]
    (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    (hi : P (K.X i)) (hn : P (K.X (c.next i))) : P (K.cycles i) := by
  exact P.prop_of_isLimit_kernelFork (K.cyclesIsKernel i (c.next i) rfl) hi hn

private lemma homology_property_of_terms {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {ι : Type t} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    (hp : P (K.X (c.prev i))) (hi : P (K.X i))
    (hn : P (K.X (c.next i))) : P (K.homology i) := by
  exact P.prop_of_isColimit_cokernelCofork (K.homologyIsCokernel (c.prev i) i rfl)
    hp (cycles_property_of_terms P K i hi hn)

/-- Kernel closure gives the cycles property and cokernel closure gives the
homology property. The derived homology factorization transports this to
`cohomologyIn P` after localization; extension closure is unnecessary. -/
theorem cohomologyIn_Q_obj_of_termwise {A : Type u} [Category.{v} A]
    [Abelian A] [HasDerivedCategory.{w} A] (P : ObjectProperty A)
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderIsomorphisms]
    (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i)) :
    cohomologyIn P (Q.obj K) := by
  intro i
  exact P.prop_of_iso ((homologyFunctorFactors A i).app K).symm
    (homology_property_of_terms P K i (hK _) (hK _) (hK _))

end DerivedCategory
