/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Core
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.FiberProduct
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Transport
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ULift
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Yoneda

/-!
# Cat-valued pseudofunctors

Extensions of Mathlib's `CategoryTheory/Bicategory/Functor/Cat/`, where
`Pseudofunctor.ObjectProperty` is defined. Declarations use Mathlib's
`CategoryTheory.Pseudofunctor` namespace.

## Main definitions

This umbrella introduces no definitions. It exports:

* `Cat/Core.lean`: the core `Pseudofunctor.core` of a pseudofunctor on a locally
  discrete base, fibrewise the maximal groupoid, with its inclusion
  `Pseudofunctor.coreι`;
* `Cat/ObjectProperty.lean`: replete and restriction-stable fiberwise loci and
  their full subpseudofunctors, with the universally stable closure
  `Pseudofunctor.ObjectProperty.universallyStable`, the restriction
  `Pseudofunctor.ObjectProperty.core` to the core, and the inclusions
  `Pseudofunctor.ObjectProperty.ιOfLE`;
* `Cat/Transport.lean`: transport of a Cat-valued pseudofunctor presentation
  through objectwise equivalences, `Pseudofunctor.equivalenceTransportFunctor`
  with its compositor and unitor;
* `Cat/ULift.lean`: the universe lift `Pseudofunctor.ulift` of a pseudofunctor on a locally
  discrete base, with fibres `ULiftHom (ULift (F.obj X))`, built by that transport;
* `Cat/FiberProduct.lean`: the 2-fibre product `Pseudofunctor.fiberProduct` of
  pseudofunctors on a locally discrete base, fibrewise Mathlib's categorical
  pullback, with its projections, lifts, the relative diagonal and the
  terminal pseudofunctor;
* `Cat/Yoneda.lean`: the representable pseudofunctor `Pseudofunctor.representable`
  of an object, in the universes of `Pseudofunctor.ulift`, and the strong
  transformation `Pseudofunctor.ofObj` attached to an object of a fibre.

## Main results

The transported compositors satisfy the pseudofunctor coherence equations
(`Pseudofunctor.equivalenceTransport_associativity` and the two unitality
theorems), the lift into a 2-fibre product recovers its 2-commutative
square (`Pseudofunctor.fiberProduct.lift_comm`), and evaluation at the
universal point is the 2-Yoneda equivalence `Pseudofunctor.yonedaEquivalence`.

## Implementation notes

Each child extends Mathlib's Cat-valued pseudofunctor API at its definition
site; none introduces a new carrier.

## References

The 2-fibre product follows the Stacks Project, Tags 02X9 and 02XI, and the
2-Yoneda lemma Tag 004B; the children cite their sources.

## Tags

pseudofunctor, Cat, object property, core, 2-fibre product, 2-Yoneda lemma
-/
