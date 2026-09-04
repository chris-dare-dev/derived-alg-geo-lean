/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.BogomolovGieseker
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.BMT
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.Slope
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.TwistedChern

/-! # Polarised numerical data

The polarisation and the Mumford slope; the two `H`-discriminants; the twisted
Chern character; and the two supplied inequalities.

The inequalities are not alike. `BogomolovGiesekerData` is true and merely out
of reach here. `BMTData` is **false in general** — it fails on the blow-up of
`ℙ³` at a point — so it can only ever be hypothesised for one threefold at a
time. See `BMT.lean`.
-/
