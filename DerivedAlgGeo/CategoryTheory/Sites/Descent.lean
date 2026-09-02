/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism

/-!
# Descent and stacks

Extensions of Mathlib's `CategoryTheory/Sites/Descent/`, where `IsStack` is
defined: stacks in groupoids, discrete stacks from sheaves, stack morphisms,
and site-object representability. `StackInGroupoids.lean` declares the
structure and does not re-export its directory, so this umbrella imports the
children directly.
-/
