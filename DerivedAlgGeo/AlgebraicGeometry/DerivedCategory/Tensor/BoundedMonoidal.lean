/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Subcategory
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent

/-!
# Restricting a monoidal structure from `D(Coh X)` to `Dᵇ(Coh X)`

For a locally Noetherian scheme `X`, a monoidal structure on the unbounded
`D(Coh X)` whose tensor preserves boundedness restricts to `Dᵇ(Coh X)`, and the
inclusion is monoidal. The payoff is that the `MonoidalCategory` parent of
`HasCoherentDerivedTensor` stops being something a caller supplies from
nothing and becomes something a named constructor produces from a strictly
weaker, strictly ambient input.

## The identification that makes this cheap

`SchemeBoundedCoherentDerivedCategory X` is `DerivedCategory.Bounded (Coh X)`,
and that is an `abbrev` for
`(DerivedCategory.TStructure.t (C := Coh X)).bounded.FullSubcategory`
(`Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:207`). So the
bounded coherent derived category **is** a full subcategory on the nose, and
Mathlib's `fullMonoidalSubcategory` and `monoidalι`
(`Mathlib/CategoryTheory/Monoidal/Subcategory.lean:93`, `:101`) apply to it
directly. A reader who misses this will rebuild the associator by hand.

## The hypothesis is an input, and what it means

The closure condition is Mathlib's own class,
`ObjectProperty.IsMonoidal t.bounded`, not a bespoke structure: it is
definitionally `ContainsUnit` plus `TensorLE P P P` (`:64`), both `Prop`, so a
`...Data` wrapper would carry no data. This repository's `...Data` idiom is for
external inputs that carry content, and this is not one.

`TensorLE` here says the derived tensor of two bounded coherent complexes is
bounded. **That is finite Tor-dimension.** On a singular Noetherian scheme
`⊗ᴸ` has unbounded Tor and leaves `Dᵇ(Coh)`, so this hypothesis is exactly the
regularity restriction under which `HasCoherentDerivedTensor` is inhabitable at
all. It is a true, satisfiable statement — not a disguised falsehood — but it
is **supplied here, not proved**. There is no scheme-level regularity predicate
in this tree, which is why the restriction is carried by this class rather than
by an `[IsRegular X]` binder.

## Why a `def` and not an `instance`

`fullMonoidalSubcategory` is already a **global** instance on
`FullSubcategory P`, and `SchemeBoundedCoherentDerivedCategory X` is an
`abbrev` for exactly such a subcategory. `HasCoherentDerivedTensor` extends
`MonoidalCategory (SchemeBoundedCoherentDerivedCategory Z.left)`
(`Tensor/Coherent.lean:78`) and is bound at 68 sites across this library, of
which 15 are in `FourierMukai/KernelAssociativity.lean`. A repo-level instance
producing the same `MonoidalCategory` would therefore be a **third** synthesis
route on one `abbrev`, not a second — the diamond shape that has bitten this
repository before.

The two routes do not collide today, because the inputs below are not in scope
at those binder sites. That is a fact about the current call sites, not a
property of the instance, so it is not a reason to rely on it. Everything here
is a named `def`; a caller that wants the structure names it.

## Placement

`dt-1` (#892) proposed this under
`CategoryTheory.Triangulated.StabilityCondition.Families`. MO1.10 (#1321,
merged as #1363) makes that impossible: rule 17 of `scripts/check_layering.py`
requires every module under `AlgebraicGeometry/DerivedCategory/Tensor` to reach
neither the Fourier--Mukai subtree nor the stability tree, **transitively**,
and the consumer this feeds — `HasCoherentDerivedTensor` — now lives in
`Tensor/Coherent.lean`. So the construction belongs to the `Tensor/` owner, and
the issue's own integration note directs exactly this: coordinate the
path-specific contract with the cutover rather than create a second root.

The namespace is `AlgebraicGeometry.DerivedCategory`. The umbrella's rule is
that *moved* declarations keep the namespace they were introduced with; these
are new, so there is nothing to preserve, and filing them under `FourierMukai`
would assert the coupling MO1.10 removed.

This module sits **below** `Tensor/Coherent.lean` and must not import it: the
point is to feed `HasCoherentDerivedTensor`, not to consume it.

## Not in scope

The three exactness obligations of `HasCoherentDerivedTensor` — `additive`,
`commShift`, `isTriangulated`, now packaged as its `exact` field — belong to
`dt-2`. Where `MonoidalCategory (D(Coh X))` itself comes from belongs to
`dt-3`. Nothing here touches `AlgebraicGeometry/Modules/**` or
`AlgebraicGeometry/CoherentSheaf/**`.

## References

* `Mathlib/CategoryTheory/Monoidal/Subcategory.lean` — the prior art adapted.
* `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:207` — the `abbrev`.
* `docs/architecture/cutover-ledger.md`, row 10 (#1321).
-/

universe u

-- The same local instance the rest of `AlgebraicGeometry/DerivedCategory/`
-- uses; `DerivedCategory.TStructure.t` needs it to mention `Coh X` at all.
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory AlgebraicGeometry

noncomputable section

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The bounded object property on `D(Coh X)`, named.

`SchemeBoundedCoherentDerivedCategory X` is this property's full subcategory,
by `abbrev`. Naming it keeps downstream files from unfolding the chain
`SchemeBoundedCoherentDerivedCategory X → DerivedCategory.Bounded (Coh X) →
t.bounded.FullSubcategory` at every use site. -/
abbrev boundedProperty : ObjectProperty (SchemeCoherentDerivedCategory X) :=
  (DerivedCategory.TStructure.t (C := Coh X)).bounded

/-- The identification, recorded rather than left to a comment: the bounded
coherent derived category is the full subcategory on `boundedProperty`. -/
lemma schemeBoundedCoherentDerivedCategory_eq :
    SchemeBoundedCoherentDerivedCategory X = (boundedProperty X).FullSubcategory :=
  rfl

variable [MonoidalCategory (SchemeCoherentDerivedCategory X)]
  [(boundedProperty X).IsMonoidal]

/-- **The restriction.** A monoidal structure on `D(Coh X)` whose tensor
preserves boundedness gives one on `Dᵇ(Coh X)`.

A `def`, not an `instance`; see the module docstring on why a third synthesis
route on one `abbrev` is not wanted. -/
@[reducible] def boundedMonoidalCategory :
    MonoidalCategory (SchemeBoundedCoherentDerivedCategory X) :=
  ObjectProperty.fullMonoidalSubcategory (boundedProperty X)

/-- The inclusion `Dᵇ(Coh X) ⥤ D(Coh X)`, named locally so downstream files do
not unfold the `abbrev` chain. -/
def boundedTensorι :
    SchemeBoundedCoherentDerivedCategory X ⥤ SchemeCoherentDerivedCategory X :=
  (boundedProperty X).ι

/-- **The inclusion is monoidal.** Mathlib's `monoidalι`, read through the
repo-local names, so a consumer gets the comparison without re-deriving which
full subcategory it is about. -/
@[reducible] def boundedTensorιMonoidal :
    letI := boundedMonoidalCategory X
    (boundedTensorι X).Monoidal :=
  ObjectProperty.monoidalι (boundedProperty X)

/-! ### Acceptance

The construction is reachable **by name**, without class synthesis. That is the
point of shipping `def`s: an `example` that said `inferInstance` here would pass
on Mathlib's global `fullMonoidalSubcategory` alone and would prove nothing
about this file. -/

example : MonoidalCategory (SchemeBoundedCoherentDerivedCategory X) :=
  boundedMonoidalCategory X

example :
    letI := boundedMonoidalCategory X
    (boundedTensorι X).Monoidal :=
  boundedTensorιMonoidal X

end

end AlgebraicGeometry.DerivedCategory
