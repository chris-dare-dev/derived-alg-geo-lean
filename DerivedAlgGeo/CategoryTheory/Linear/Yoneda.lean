/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Representability through the linear Yoneda embedding

Three consequences of `linearYoneda` being full and faithful: representing
objects are unique up to a canonical isomorphism, that isomorphism is the one
the presheaf comparison names, and two morphisms agreeing after the embedding
are equal.

None of the three mentions a Serre functor, a shift, or a triangulation; each
is `Functor.preimageIso`, `Functor.map_preimage` or `Functor.map_injective`
against Mathlib's `full_linearYoneda` and `faithful_linearYoneda`. They were
proved that way from the start, and the uniqueness of a Serre functor is only
their first consumer -- a downstream lane needs the representability step on a
functor that is not a Serre functor at all.

## Trap: which variable a Yoneda argument runs in

`Hom(A,B)` is contravariant in `A` and covariant in `B`, and the dual flips
both, so `Dual (A ⟶ B)` is **covariant in `A`** and **contravariant in `B`**.
An argument comparing two objects that represent `B ↦ Dual (A ⟶ B)` therefore
runs in the `B` variable, which is why these are stated on `linearYoneda` and
not on `linearCoyoneda`. In this repository `(linearCoyoneda k C).obj (op X)`
is the *covariant* `Hom(X, −)`, so the same argument run there typechecks
against the opposite functor and proves nothing about the original one.

## Namespace

The declarations keep the `CategoryTheory.SerreFunctor` namespace they were
published under. Their path and their namespace disagree on purpose: the
repository's cutover policy moves paths and preserves fully qualified
declaration names, because a namespace cutover would invalidate the immutable
review payloads `exe/RestateHistoricalNames.lean` exists to protect. See
`docs/architecture/cutover-ledger.md`, finding 05.
-/

universe w v u

open CategoryTheory

namespace CategoryTheory.SerreFunctor

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C]

/-- **Representing objects are unique.** A natural isomorphism of the linear Yoneda presheaves
gives an isomorphism of the representing objects.

Public and `SerreFunctorData`-free on purpose; see the module docstring. This is
`Functor.preimageIso` against Mathlib's `full_linearYoneda` and `faithful_linearYoneda`. -/
noncomputable def isoOfLinearYonedaIso {X Y : C}
    (e : (linearYoneda k C).obj X ≅ (linearYoneda k C).obj Y) : X ≅ Y :=
  (linearYoneda k C).preimageIso e

@[simp]
theorem map_isoOfLinearYonedaIso {X Y : C}
    (e : (linearYoneda k C).obj X ≅ (linearYoneda k C).obj Y) :
    (linearYoneda k C).mapIso (isoOfLinearYonedaIso k C e) = e := by
  ext : 1
  exact (linearYoneda k C).map_preimage e.hom

/-- Two morphisms agreeing after the linear Yoneda embedding are equal. -/
theorem hom_ext_of_linearYoneda {X Y : C} {f g : X ⟶ Y}
    (h : (linearYoneda k C).map f = (linearYoneda k C).map g) : f = g :=
  (linearYoneda k C).map_injective h

end CategoryTheory.SerreFunctor
