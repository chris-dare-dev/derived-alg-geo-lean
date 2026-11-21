/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Surjectivity along étale surjections

Surjectivity of scheme morphisms is stable under precomposition with étale surjections. This is
`MorphismProperty.RespectsLeft @Surjective (@Etale ⊓ @Surjective)`, one of the two conditions
under which a property measured on étale surjective atlases does not depend on the atlas.

## Main definitions

None.

## Main results

* An instance `MorphismProperty.RespectsLeft @Surjective (@Etale ⊓ @Surjective)`.

## Implementation notes

The other condition, `MorphismProperty.HasOfPrecompProperty @Surjective Q`, is a Mathlib instance
for every `Q`: if `f ≫ g` is surjective then so is `g` (`AlgebraicGeometry.Surjective.of_comp`).

The instance is stated for `@Etale ⊓ @Surjective` rather than for `Q ⊓ @Surjective` with `Q`
arbitrary. Instance search cannot use the general form: matching `Q` against `@Etale` would
assign a term of the bare function type `{X Y : Scheme} → (X ⟶ Y) → Prop` to a variable of type
`MorphismProperty Scheme`, and `MorphismProperty` does not unfold at instance transparency.

## Tags

surjective morphism, étale morphism, scheme
-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

/-- A surjective morphism of schemes stays surjective after precomposition with an étale
surjection. -/
instance : RespectsLeft @Surjective (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}) where
  precomp _ hi _ hf := ⟨hf.1.comp hi.2.1⟩

end AlgebraicGeometry
