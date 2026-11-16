/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Sites.BigZariski
import DerivedAlgGeo.AlgebraicGeometry.Sites.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Sites.QuasiCompact
import DerivedAlgGeo.AlgebraicGeometry.Sites.StackQuasiCompact

/-! # Grothendieck topologies on schemes

Direct extensions of Mathlib's big Zariski, étale, fppf and fpqc sites, and the criteria for
stacks on them: effective descent along a family is effective descent along the morphism out of
its coproduct, and a Zariski stack is a stack for a quasi-compact topology when it has effective
descent along the single affine covering morphisms.
-/
