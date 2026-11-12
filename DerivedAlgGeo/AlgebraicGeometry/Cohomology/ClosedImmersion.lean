/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CohomologyPushforward
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite

/-!
# Cohomology of a coherent sheaf along a closed immersion

`cohCohomologyPushforwardAddEquiv` : `Hⁿ(X, F) ≃+ Hⁿ(Y, ι_* F)` for `ι` a closed immersion of
schemes and `F` coherent on `X`, with `ι_* F` itself coherent. This is the coherent-sheaf form of
the abelian-sheaf statement `schemeCohomologyPushforwardAddEquiv` of
`CohomologyPushforward.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.cohPushforward` — `ι_* F` as a coherent sheaf.

## Main results

* `AlgebraicGeometry.Scheme.toSheaf_pushforward` — `Scheme.Modules.toSheaf` commutes with
  pushforward, by `rfl`.
* `AlgebraicGeometry.Scheme.modulesCohomologyPushforwardAddEquiv` — cohomology of a module sheaf
  is unchanged by pushforward along a closed immersion.
* `AlgebraicGeometry.Scheme.cohCohomologyPushforwardAddEquiv` — the same comparison for a
  coherent sheaf and its coherent pushforward.

## Implementation notes

### The passage from modules to abelian sheaves is `rfl`

`toSheaf_pushforward` records that `Scheme.Modules.toSheaf` commutes with pushforward **on the
nose**: the module pushforward *is* the abelian pushforward carrying a module structure, so the two
composites are the same abelian sheaf.

This is worth stating because the shape — a functor commuting with a functor — looks like it needs
a comparison isomorphism and does not.

### What makes the target coherent

`Scheme.isCoherent_pushforward`: coherence is preserved by pushforward along a finite morphism
into a locally Noetherian scheme, and a closed immersion is finite. `cohPushforward` packages the
module pushforward of a coherent sheaf with that proof, as an object of `Coh Y`.
**`IsLocallyNoetherian Y` is spent entirely there** — the cohomology comparison needs no chain
condition of its own.

### The `HasExt` universe is pinned

The `HasExt` universe is pinned here, because this instantiation lets instance search find the
witness. `Topology/Sheaves/CohomologyPushforward.lean` keeps it positional
(`cohomologyPushforwardAddEquivAt`) for callers who need another witness; the coherent-cohomology
convention `HasExt.standard` is one such caller, in
`Cohomology/Finiteness/ProjectiveVariety.lean`, where the comparison is also shown natural in `F`
and `k`-linear.

## References

The file cites no literature. It builds on
`DerivedAlgGeo.AlgebraicGeometry.schemeCohomologyPushforwardAddEquiv` and
`AlgebraicGeometry.Scheme.isCoherent_pushforward`.

## Tags

sheaf cohomology, closed immersion, pushforward, coherent sheaf
-/

universe u

open CategoryTheory Limits TopologicalSpace TopCat
open DerivedAlgGeo.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g]

omit [IsClosedImmersion g] in
/-- **`toSheaf` commutes with pushforward, on the nose.**

No hypothesis on `g` at all: this holds for any morphism of schemes. -/
lemma toSheaf_pushforward (F : X.Modules) :
    (Modules.toSheaf Y).obj ((Modules.pushforward g).obj F)
      = ((Opens.map g.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).obj ((Modules.toSheaf X).obj F) := rfl

set_option maxHeartbeats 1000000 in
/-- **Cohomology of a module sheaf is unchanged by pushforward along a closed immersion.** -/
noncomputable def modulesCohomologyPushforwardAddEquiv (F : X.Modules) (n : ℕ) :
    Sheaf.H ((Modules.toSheaf X).obj F) n
      ≃+ Sheaf.H ((Modules.toSheaf Y).obj ((Modules.pushforward g).obj F)) n := by
  rw [toSheaf_pushforward g F]
  exact schemeCohomologyPushforwardAddEquiv g ((Modules.toSheaf X).obj F) n

/-- **`ι_* F` as a coherent sheaf**, by `isCoherent_pushforward`. -/
noncomputable def cohPushforward [IsLocallyNoetherian Y] (F : Coh X) : Coh Y :=
  ⟨(Modules.pushforward g).obj ((Coh.ι X).obj F),
    isCoherent_pushforward g ((Coh.ι X).obj F) F.2⟩

set_option maxHeartbeats 1000000 in
/-- **Cohomology of a coherent sheaf is unchanged by pushforward along a closed immersion.** -/
noncomputable def cohCohomologyPushforwardAddEquiv [IsLocallyNoetherian Y]
    (F : Coh X) (n : ℕ) :
    Sheaf.H ((Modules.toSheaf X).obj ((Coh.ι X).obj F)) n
      ≃+ Sheaf.H ((Modules.toSheaf Y).obj ((Coh.ι Y).obj (cohPushforward g F))) n :=
  modulesCohomologyPushforwardAddEquiv g ((Coh.ι X).obj F) n

end AlgebraicGeometry.Scheme
