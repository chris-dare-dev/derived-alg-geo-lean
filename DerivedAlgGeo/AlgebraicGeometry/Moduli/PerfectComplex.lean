/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Relative
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.AffineFamilyRelativePerfect
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.AffineFamilyRelativePerfectPseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Presheaf
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.BigZariski
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Algebraicity

/-!
# Moduli of perfect complexes

Declarations in this subtree use the geometry-owned `AlgebraicGeometry`
namespace; neutral moduli objects do not belong to a stability namespace.
`Comparison.lean` records the proved arrows between two-term presentation
data, the absolute coherent-derived perfect locus, and its `Dqc` image; it
does not identify those notions with relative perfection over a base.
-/
