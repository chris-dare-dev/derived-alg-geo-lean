/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids

/-!
# Compatibility import for generic stacks in groupoids

The generic definitions are owned by
`DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids`.  This module keeps the
former import path working for algebraic-geometry clients; new generic code
should import the neutral owner directly. It preserves the import surface, not
the retired `AlgebraicGeometry.StackInGroupoids` qualified name.
-/
