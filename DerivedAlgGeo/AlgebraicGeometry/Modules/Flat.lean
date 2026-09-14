/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Flat.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-!
# Flatness of a module sheaf over a morphism

`Scheme.Modules.IsFlatOver p M` says that `M` is flat over the base along
`p : X ⟶ S`, stalkwise: at every point of `X`, the stalk of `M` is flat as a
module over the corresponding stalk of `S`, restricted along the local-ring
map `p` induces.

This is a property of one module sheaf and one morphism. It needs no derived
category, no moduli problem and no perfectness notion, and it is used before
any of them: Tor-amplitude models, geometric fibers and base-change arguments
all ask for flat terms. It lives with `X.Modules` for that reason — the
carrier in its public type is a module sheaf, and `moduleStalkFunctor`, the
only other repository construction it mentions, is the neighbouring
`Modules/Pullback/Stalk.lean`.

It previously sat in `Moduli/PerfectComplex/Relative.lean`, where its first
consumer was; see `docs/architecture/cutover-ledger.md`, finding 11.

## Not a morphism-flatness predicate

`Mathlib.AlgebraicGeometry.Morphisms.Flat` is a different subject: it asks
that the *morphism* be flat, which is this condition for the structure sheaf
alone. Nothing here specializes to or is implied by that class, and no
instance relates them.
-/

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace Scheme

/-- A module sheaf on `X` is flat over `S` when every stalk, restricted along
the local-ring map induced by `p`, is a flat module over the corresponding
stalk of `S`. -/
def Modules.IsFlatOver {X S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) : Prop :=
  ∀ x : X, Module.Flat (S.presheaf.stalk (p x))
    ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((Scheme.Modules.moduleStalkFunctor X x).obj M))

end Scheme

end AlgebraicGeometry
