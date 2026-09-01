/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Descent.Locality

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

## The argument is adjoint uniqueness, not a computation

`Modules.restrictFunctor e.hom` and `Modules.restrictFunctor e.inv` are mutually inverse: compose
them, collapse with `restrictFunctorComp`, rewrite the composite morphism to an identity, and
finish with `restrictFunctorId`. So `restrictFunctor e.hom` has `restrictFunctor e.inv` as a right
adjoint. It also has `Modules.pushforward e.hom` as one, by `Modules.restrictAdjunction`. Right
adjoints are unique up to isomorphism, and `pushforwardIsoRestrict` is that isomorphism.

Coherence then transfers because restriction along an open immersion already preserves it
(`Modules.IsCoherent.restrict_of_isOpenImmersion`) and an isomorphism is an open immersion.

Nothing here computes what the comparison does to a section, and nothing needs to: the consumer is
a property closed under isomorphism.

## Two traps, both costing time and neither visible in the statement

* **`Equivalence.mk` resolves to the wrong `Equivalence`.** Under `open CategoryTheory` the root
  `Equivalence.mk` — the constructor of the equivalence-relation structure — wins, and the error
  is an inscrutable "expected `∀ (x : ?m), ?m x x`". Write
  `CategoryTheory.Equivalence.mk`. It is also the constructor to want: it takes the two
  isomorphisms and *adjointifies* the unit, so the triangle identity is not an obligation. Giving
  the fields directly to the structure leaves that identity for `aesop`, which does not discharge
  it here.
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

* `Modules.restrictEquiv` — restriction along an isomorphism, as an equivalence.
* `Modules.pushforwardIsoRestrict` — `e_*` is restriction along `e⁻¹`.
* `Modules.isCoherent_pushforward_of_iso` — coherence survives `e_*`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- **Restriction along an isomorphism, as an equivalence of module categories.**

Built with `CategoryTheory.Equivalence.mk` rather than by giving the structure's fields: that
constructor adjointifies the unit, so the triangle identity is discharged for us. See the module
docstring — both halves of that sentence cost time to learn. -/
noncomputable def restrictEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.inv) (restrictFunctor e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫
      restrictFunctorCongr (by simp) ≪≫ restrictFunctorId).symm
    ((restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr (by simp) ≪≫ restrictFunctorId)

/-- **Pushforward along an isomorphism is restriction along its inverse.**

Both are right adjoint to `restrictFunctor e.hom` — the first by `restrictAdjunction`, the second
because `restrictEquiv` makes it half of an equivalence — and right adjoints are unique. -/
noncomputable def pushforwardIsoRestrict :
    pushforward e.hom ≅ restrictFunctor e.inv :=
  (restrictAdjunction e.hom).rightAdjointUniq (restrictEquiv e).symm.toAdjunction

/-- **Coherence survives pushforward along an isomorphism of schemes.**

The transport `#572` step 2 needs in order to apply the affine pushforward theorem, which is
stated about `Spec.map`, to a member of an affine open cover, which is an affine *scheme*. -/
theorem isCoherent_pushforward_of_iso (M : X.Modules) (hM : IsCoherent X M) :
    IsCoherent Y ((pushforward e.hom).obj M) := by
  have h : IsCoherent Y (M.restrict e.inv) :=
    IsCoherent.restrict_of_isOpenImmersion e.inv M hM
  exact (Scheme.coherent Y).prop_of_iso ((pushforwardIsoRestrict e).app M).symm h

end AlgebraicGeometry.Scheme.Modules
