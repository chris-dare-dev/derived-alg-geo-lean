/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Unbounded
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.LeftDerivedTensor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedCoherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedMonoidal
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Coherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Relative

/-!
# Derived tensor products on schemes

The geometry-level owner of derived tensor, in three deliberately separate tiers.

| Tier | Module | What it supplies |
| --- | --- | --- |
| Unbounded | `Tensor/Unbounded.lean` | the K-flat tensor bifunctor on complexes of module sheaves, **constructed** from a supplied resolution |
| Bounded coherent | `Tensor/BoundedCoherent.lean` | `HasDerivedTensor`, a **supplied capability** on `Dᵇ(Coh Z)` with two-slot exactness |
| Bounded coherent, monoidal | `Tensor/Coherent.lean` | `HasCoherentDerivedTensor`, the same capability with full monoidal coherence, mapping one way into the tier above |
| Relative | `Tensor/Relative.lean` | `HasMonoidalDerivedPullback`, compatibility with derived pullback along a morphism |

The tiers are separate because they are not each other's restrictions.  The unbounded
bifunctor does **not** restrict to `Dᵇ(Coh Z)`: that category is not closed under
arbitrary derived tensor on a singular scheme, so the bounded coherent tiers are
contracts a caller discharges rather than theorems proved from the tier above them.

Fourier--Mukai consumes all of this and owns none of it; see
`DerivedCategory/FourierMukai/`.  Declarations in this subtree keep the
`AlgebraicGeometry.DerivedCategory.FourierMukai` namespace they were introduced with, per
the cutover ledger's standing decision that paths move and namespaces do not, except in
`Tensor/Unbounded.lean`, which was already `AlgebraicGeometry.DerivedCategory`.

## References

* `docs/architecture/cutover-ledger.md`, row 10 (#1321).
-/
