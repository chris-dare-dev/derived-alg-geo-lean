/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Homotopy.FiniteCohomologyPresentation
import DerivedAlgGeo.Algebra.Homology.Homotopy.ModuleCatFormality

/-!
# Finite cohomology presentations from finite support

Over a division ring, this file composes the generic finite-support comparison
between zero-differential homology models with the noncanonical formality
equivalence to construct a `FiniteCohomologyPresentation`.

The support witness is explicit and the recorded finite set need not be
minimal.  No boundedness, finite-dimensionality, naturality, or
quasi-isomorphism invariance is inferred.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory Limits

namespace CochainComplex

namespace FiniteCohomologyPresentation

variable {k : Type u} [DivisionRing k]

/-- A finite-support witness constructs a finite cohomology presentation for
a complex of vector spaces.  The underlying formality equivalence remains
noncanonical; the finite-support comparison itself uses only the categorical
zero-differential models. -/
noncomputable def ofFiniteSupport
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (degrees : Finset ℤ)
    (hSupport : ∀ i, i ∉ degrees → IsZero (K.homology i)) :
    FiniteCohomologyPresentation K where
  degrees := degrees
  homotopyEquiv :=
    (homotopyEquivHomologyModel K).trans <|
      HomotopyEquiv.ofIso
        (homologyModelIsoFiniteCohomologyModel K degrees hSupport)

@[simp]
lemma ofFiniteSupport_degrees
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (degrees : Finset ℤ)
    (hSupport : ∀ i, i ∉ degrees → IsZero (K.homology i)) :
    (ofFiniteSupport K degrees hSupport).degrees = degrees :=
  rfl

end FiniteCohomologyPresentation

end CochainComplex
