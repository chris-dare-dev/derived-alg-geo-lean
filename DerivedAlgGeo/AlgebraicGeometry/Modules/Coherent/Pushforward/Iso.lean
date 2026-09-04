/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Descent.Locality
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Iso

/-!
# Pushforward along an isomorphism of schemes

`isCoherent_pushforward_of_iso` : coherence survives `e_*` for `e : X ≅ Y`.

## Why `#572` step 2 needs this

Step 2 wants `ι_* F` coherent for a closed immersion `ι`. `isCoherent_pushforward_of_surjective`
(`Pushforward/Affine.lean`) proves the affine case, but it is stated for `Spec.map φ : Spec S ⟶
Spec R` — a map *of spectra*, not of affine schemes. An affine open cover supplies affine
*schemes*, so the affine case cannot be applied to a cover member without first moving across
`Scheme.isoSpec`. That factorisation is available and cheap,

```
f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv
```

(`Scheme.isoSpec_inv_naturality`), and `Modules.pushforward (g ≫ h)` is
`Modules.pushforward g ⋙ Modules.pushforward h` **by `rfl`** — so the whole step reduces to
knowing that the two outer pushforwards, both along isomorphisms, preserve coherence. That is
what this file supplies, and it was the one missing input.

## The comparison lives one level down

`pushforwardIsoRestrict` (`Modules/Pushforward/Iso.lean`) identifies `e_*` with restriction
along `e⁻¹` by uniqueness of right adjoints; it is stated on all module sheaves and needs
nothing about coherence, which is why it is not here.

Coherence then transfers because restriction along an open immersion already preserves it
(`Modules.IsCoherent.restrict_of_isOpenImmersion`) and an isomorphism is an open immersion.

Nothing here computes what the comparison does to a section, and nothing needs to: the consumer is
a property closed under isomorphism.

## A trap, costing time and not visible in the statement

* **`SheafOfModules.IsFinitePresentation.of_iso` does not pin its universes.** Its
  local-generators universe is unconstrained by the explicit arguments and defaults to `0`, so
  feeding it a `.{u, u, u}` hypothesis is a type mismatch even in tactic mode with the expected
  type present. Use `(Scheme.coherent Y).prop_of_iso`, which is the idiom
  `Pushforward/Affine.lean` already ends with.

## Scope

Isomorphisms only. This says nothing about pushforward along a general morphism, and the closed
immersion of `#572` step 2 is *not* an isomorphism — this is the transport that lets the affine
theorem reach a cover member, not the theorem itself.

## Main results

* `Modules.isCoherent_pushforward_of_iso` — coherence survives `e_*`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- **Coherence survives pushforward along an isomorphism of schemes.**

The transport `#572` step 2 needs in order to apply the affine pushforward theorem, which is
stated about `Spec.map`, to a member of an affine open cover, which is an affine *scheme*. -/
theorem isCoherent_pushforward_of_iso (M : X.Modules) (hM : IsCoherent X M) :
    IsCoherent Y ((pushforward e.hom).obj M) := by
  have h : IsCoherent Y (M.restrict e.inv) :=
    IsCoherent.restrict_of_isOpenImmersion e.inv M hM
  exact (Scheme.coherent Y).prop_of_iso ((pushforwardIsoRestrict e).app M).symm h

end AlgebraicGeometry.Scheme.Modules
