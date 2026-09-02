/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Properties

/-!
# Varieties over a field

A variety over `k` is a scheme with a structure morphism to `Spec k` that is integral and
locally of finite type. This file states that the way Mathlib states every property of a
scheme over a base: the scheme is `X : Scheme`, the structure morphism is the
`X.Over (Spec k)` instance with its notation `X ↘ Spec k`, and "variety" is the
`Prop`-valued class `IsVariety k X` extending Mathlib's `IsIntegral X` and
`LocallyOfFiniteType (X ↘ Spec k)`, exactly as `IsProper` extends its constituents.

There is no bundled a variety over `k` type. A bundle is a second carrier for an object Mathlib
already has, and every API written against it has to be unwrapped before Mathlib's own
results about `X` apply. Consequently:

* an API about a variety takes `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsVariety k X]` and writes `X ↘ Spec (CommRingCat.of k)` for the structure morphism;
* `IsSmoothProperVariety k X` is the conjunction with `Smooth` and `IsProper` of the
  structure morphism, for APIs stated on smooth proper varieties as such; a result that
  needs only smoothness or only properness takes `[Smooth (X ↘ _)]` or
  `[IsProper (X ↘ _)]` alone;
* the namespaces `Variety` and `SmoothProperVariety` name the concepts and hold their
  API, including `SmoothProperVariety.CanonicalSheafData`; they are not the names of
  types.

`NumericalVarietyData n A N` remains the intersection-theoretic quotient used by numerical
arguments; the realization from a variety to it is separate data.
-/

universe u

namespace AlgebraicGeometry

/-- `X` is a variety over `k`: integral, and locally of finite type over `Spec k`.

The base field is an `outParam`: a conclusion such as `IsLocallyNoetherian X` mentions no
`k`, so instance search must be allowed to recover `k` from the `IsVariety` instance in
scope rather than be given it. That is what the bundled a variety over `k` used to do through its
type, and it is the only way an unbundled `X : Scheme` can carry the same instances. -/
class IsVariety (k : outParam (Type u)) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] : Prop
    extends IsIntegral X, LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))

/-- `X` is a smooth proper variety over `k`: a variety whose structure morphism is smooth
and proper. The conjunction is a class, as `IsProper` is, so that an API stated on smooth
proper varieties carries one hypothesis; each constituent is recovered by instance search.
The base is an `outParam` for the reason given at `IsVariety`. -/
class IsSmoothProperVariety (k : outParam (Type u)) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] : Prop
    extends IsVariety k X, Smooth (X ↘ Spec (CommRingCat.of k)),
      IsProper (X ↘ Spec (CommRingCat.of k))

namespace Variety

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- A variety over a field is locally noetherian: the base field is noetherian and the
structure morphism is locally of finite type. -/
noncomputable instance isLocallyNoetherian [IsVariety k X] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))

/-- A proper variety over a field is Noetherian: finite type gives local Noetherianity and
properness gives quasi-compactness over the compact point `Spec k`. -/
noncomputable instance isNoetherian_of_isProper [IsVariety k X]
    [IsProper (X ↘ Spec (CommRingCat.of k))] : IsNoetherian X where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k))

/-- A proper variety over a field is separated as an absolute scheme.

The variety hypothesis contributes nothing to the proof, which uses only properness of the
structure morphism. It is kept because its `outParam` base field is the only way instance
search can recover `k` from the goal `X.IsSeparated`, which mentions no `k`; without it Lean
reports no synthesization order for the instance. -/
@[nolint unusedArguments]
instance isSeparated_of_isProper [IsVariety k X]
    [IsProper (X ↘ Spec (CommRingCat.of k))] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← CategoryTheory.Limits.terminal.comp_from (X ↘ Spec (CommRingCat.of k))]
    infer_instance

end Variety

end AlgebraicGeometry
