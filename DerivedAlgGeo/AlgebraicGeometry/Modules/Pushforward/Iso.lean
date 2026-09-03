/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pushforward of module sheaves along an isomorphism of schemes

`pushforwardIsoRestrict` : for an isomorphism `e : X ≅ Y`, pushforward along `e.hom` is
restriction along `e.inv`.  This is the transport that lets a statement about `Spec.map` reach
an affine scheme through `Scheme.isoSpec`, and it is stated on all module sheaves because
nothing about it needs coherence or quasi-coherence.

## Main definitions

* `Modules.restrictEquiv` — restriction along an isomorphism, as an equivalence.
* `Modules.pushforwardIsoRestrict` — `e_*` is restriction along `e⁻¹`.

## The argument is adjoint uniqueness, not a computation

`Modules.restrictFunctor e.hom` and `Modules.restrictFunctor e.inv` are mutually inverse: compose
them, collapse with `restrictFunctorComp`, rewrite the composite morphism to an identity, and
finish with `restrictFunctorId`. So `restrictFunctor e.hom` has `restrictFunctor e.inv` as a right
adjoint. It also has `Modules.pushforward e.hom` as one, by `Modules.restrictAdjunction`. Right
adjoints are unique up to isomorphism, and `pushforwardIsoRestrict` is that isomorphism.

Nothing here computes what the comparison does to a section, and nothing needs to: every consumer
so far is a property closed under isomorphism (coherence in
`Coherent/Pushforward/Iso.lean`, quasi-coherence and epimorphisms in `Affine/Epi.lean`).

## A trap not visible in the statement

`Equivalence.mk` resolves to the wrong `Equivalence`. Under `open CategoryTheory` the root
`Equivalence.mk` — the constructor of the equivalence-relation structure — wins, and the error is
an inscrutable "expected `∀ (x : ?m), ?m x x`". Write `CategoryTheory.Equivalence.mk`. It is also
the constructor to want: it takes the two isomorphisms and *adjointifies* the unit, so the
triangle identity is not an obligation. Giving the fields directly to the structure leaves that
identity for `aesop`, which does not discharge it here.
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

end AlgebraicGeometry.Scheme.Modules
