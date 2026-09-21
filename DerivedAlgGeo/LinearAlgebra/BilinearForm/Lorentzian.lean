/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.Lorentzian.Diagonal
import DerivedAlgGeo.LinearAlgebra.BilinearForm.Lorentzian.TimeCone

/-! # Lorentzian pairings

Structure that follows from a `HodgeDefinite` certificate alone: the splitting
of a vector along a reference vector and its orthogonal complement, the future
cone, and the two inequalities that reverse their Euclidean counterparts.

`Diagonal.lean` supplies the certificate itself for the signature-`(1, k)`
model, at every rank and with no case split, together with the transport
theorem that lets a concrete model inherit it.
-/
