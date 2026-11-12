/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.FiberProduct
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Transport

/-!
# Cat-valued pseudofunctors

Extensions of Mathlib's `CategoryTheory/Bicategory/Functor/Cat/`, where
`Pseudofunctor.ObjectProperty` is defined. Declarations use Mathlib's
`CategoryTheory.Pseudofunctor` namespace.

## Main definitions

This umbrella introduces no definitions. It exports:

* `Cat/ObjectProperty.lean`: replete and restriction-stable fiberwise loci and
  their full subpseudofunctors, with the universally stable closure
  `Pseudofunctor.ObjectProperty.universallyStable`;
* `Cat/Transport.lean`: transport of a Cat-valued pseudofunctor presentation
  through objectwise equivalences, `Pseudofunctor.equivalenceTransportFunctor`
  with its compositor and unitor;
* `Cat/FiberProduct.lean`: the 2-fibre product `Pseudofunctor.fiberProduct` of
  pseudofunctors on a locally discrete base, fibrewise Mathlib's categorical
  pullback, with its projections, lifts, the relative diagonal and the
  terminal pseudofunctor.

## Main results

The transported compositors satisfy the pseudofunctor coherence equations
(`Pseudofunctor.equivalenceTransport_associativity` and the two unitality
theorems), and the lift into a 2-fibre product recovers its 2-commutative
square (`Pseudofunctor.fiberProduct.lift_comm`).

## Implementation notes

Each child extends Mathlib's Cat-valued pseudofunctor API at its definition
site; none introduces a new carrier.

## References

The 2-fibre product follows the Stacks Project, Tags 02X9 and 02XI; the
children cite their sources.

## Tags

pseudofunctor, Cat, object property, 2-fibre product
-/
