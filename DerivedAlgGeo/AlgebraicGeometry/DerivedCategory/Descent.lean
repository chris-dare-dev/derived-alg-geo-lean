/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.TotalSite
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.LevelPushforward
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Functoriality
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Constant
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Augmentation
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Cartesian
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.CechNerve

/-!
# Module sheaves on simplicial schemes and Čech nerves

The total site of a simplicial scheme (Stacks, Section 85.3), its sheaves of
modules, restriction to the levels and its right adjoint, functoriality along
morphisms of simplicial schemes, augmentations towards a scheme, cartesian
objects (Stacks, Section 85.12), and the specialization to the Čech nerve of a
morphism of schemes. Declarations use `AlgebraicGeometry.TotalSite` and
`AlgebraicGeometry.CechNerve`.
-/
