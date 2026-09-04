/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.UniversallyStable

/-!
# Object properties and subprestacks of pseudofunctors

Mathlib's `Pseudofunctor.ObjectProperty` is the canonical carrier for a
fiberwise locus. Closure under isomorphisms makes the locus replete; closure
under mapped objects makes it a subprestack, represented by
`Pseudofunctor.ObjectProperty.fullsubcategory` and its inclusion `ι`.
-/
