/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Unbounded
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.FiniteKFlat
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedAboveKFlat
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.LeftDerivedTensor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedCoherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedMonoidal
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Coherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Relative

/-!
# Derived tensor products on schemes

The geometry-level owner of derived tensor: one localization-facing interface and three
deliberately separate derived-tensor tiers.

## Main definitions

This umbrella introduces no definitions. It exports the scheme-derived tensor
interfaces and their existing constructions.

## Main results

| Interface | Module | What it supplies |
| --- | --- | --- |
| Localization-facing | `Tensor/LeftDerivedTensor.lean` | the bifunctor and fixed-argument universal properties on the unbounded derived category |

| Derived-tensor tier | Module | What it supplies |
| --- | --- | --- |
| Unbounded | `Tensor/Unbounded.lean` | the K-flat tensor bifunctor on complexes of module sheaves, **constructed** from a supplied resolution |
| Bounded coherent | `Tensor/BoundedCoherent.lean` | `AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor`, a **supplied capability** on `Dᵇ(Coh Z)` with two-slot exactness |
| Bounded coherent, monoidal | `Tensor/Coherent.lean` | `AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor`, the same capability with full monoidal coherence, mapping one way into the tier above |

`Tensor/Relative.lean` is the compatibility layer for the bounded coherent tiers, not a fourth
derived-tensor construction: it supplies
`AlgebraicGeometry.DerivedCategory.FourierMukai.HasMonoidalDerivedPullback` for derived pullback along
a morphism.

`Tensor/FiniteKFlat.lean` proves that a finite supported complex with flat
scheme-module terms is K-flat for the existing total tensor.
`Tensor/BoundedAboveKFlat.lean` extends this to strictly bounded-above
flat-term complexes through the lower stupid-truncation colimit.

## Implementation notes

The tiers are separate because they are not each other's restrictions.  The unbounded
bifunctor does **not** restrict to `Dᵇ(Coh Z)`: that category is not closed under
arbitrary derived tensor on a singular scheme, so the bounded coherent tiers are
contracts a caller discharges rather than theorems proved from the tier above them.

Fourier--Mukai consumes all of this and owns none of it; see
`DerivedCategory/FourierMukai/`. The tensor cutover kept the historical
`AlgebraicGeometry.DerivedCategory.FourierMukai` namespace in
`Tensor/BoundedCoherent.lean`, `Tensor/Coherent.lean`, and `Tensor/Relative.lean`.
`Tensor/Unbounded.lean`, `Tensor/LeftDerivedTensor.lean`, and
`Tensor/BoundedMonoidal.lean` use `AlgebraicGeometry.DerivedCategory`.
`Tensor/FiniteKFlat.lean` and `Tensor/BoundedAboveKFlat.lean` use
`AlgebraicGeometry.Scheme.Modules`, the namespace of the total tensor they
specialize. Paths follow ownership without imposing one
namespace on every declaration in the subtree.

## References

* `docs/architecture/cutover-ledger.md`, row 10 (#1321).

## Tags

derived tensor, scheme-module sheaves, K-flat complexes, bounded coherent derived category
-/
