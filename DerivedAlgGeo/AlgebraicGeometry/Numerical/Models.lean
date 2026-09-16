import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.DimensionZero
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Fourfold
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.MonogenicRing
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Threefold

/-! # Numerical models

Formal rank--degree--coordinate models: an intersection ring, its grading, a
degree map, Chern and Todd coefficients, and Riemann--Roch. Nothing here
realizes a model in a real divisor space, carries a central charge, or names a
wall; those are the demonstrations of `Numerical/Examples/`, which import this
directory rather than the other way round.

A model is not a scheme. Each module states which hypotheses on an actual
variety its coordinates are a shadow of, and none of them constructs the
variety.
-/
