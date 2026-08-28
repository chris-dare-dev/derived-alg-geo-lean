/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CohomologyPushforward
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Pushforward.ClosedImmersion

/-!
# Cohomology of a coherent sheaf along a closed immersion

`cohCohomologyPushforwardAddEquiv` : `Hⁿ(X, F) ≃+ Hⁿ(Y, ι_* F)` for `ι` a closed immersion of
schemes and `F` coherent on `X`, with `ι_* F` itself coherent. This closes the last gap between
`CohomologyPushforward.lean`'s abelian-sheaf statement and `#572` step 3's acceptance criterion,
which is phrased for coherent sheaves.

## The passage from modules to abelian sheaves is `rfl`

`toSheaf_pushforward` records that `Scheme.Modules.toSheaf` commutes with pushforward **on the
nose**: the module pushforward *is* the abelian pushforward carrying a module structure, so the two
composites are the same abelian sheaf.

This is worth stating because the shape — a functor commuting with a functor — looks like it needs
a comparison isomorphism and does not. It is the last of several places on this lane where an
unchecked definitional fact was mistaken for unbuilt mathematics; the others were the site bridge
(also `rfl`) and the `EnoughInjectives`/`HasExt` instances (imports).

## What makes the target coherent

`Scheme.isCoherent_pushforward`, `#572` step 2. `cohPushforward` packages the module pushforward of
a coherent sheaf with that proof, as an object of `Coh Y`. **`IsLocallyNoetherian Y` is spent
entirely there** — the cohomology comparison needs no chain condition of its own.

## Two ways this is still weaker than `#572`'s wording

Both inherited from the abelian-sheaf statement:

* **not natural in `F`** — an isomorphism for each `F`, with naturality unproved;
* **the `HasExt` universe is pinned**, because the instantiation lets instance search find it.
  `CategoryTheory/SheafCohomologyPushforward.lean` keeps it parametric for callers who need that.

## Main results

* `toSheaf_pushforward` — the passage, by `rfl`.
* `cohPushforward` — `ι_* F` as a coherent sheaf.
* `modulesCohomologyPushforwardAddEquiv`, `cohCohomologyPushforwardAddEquiv` — the comparison.
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

/-- **`ι_* F` as a coherent sheaf**, by `#572` step 2. -/
noncomputable def cohPushforward [IsLocallyNoetherian Y] (F : Coh X) : Coh Y :=
  ⟨(Modules.pushforward g).obj ((Coh.ι X).obj F),
    isCoherent_pushforward g ((Coh.ι X).obj F) F.2⟩

set_option maxHeartbeats 1000000 in
/-- **`#572` step 3 for coherent sheaves.** -/
noncomputable def cohCohomologyPushforwardAddEquiv [IsLocallyNoetherian Y]
    (F : Coh X) (n : ℕ) :
    Sheaf.H ((Modules.toSheaf X).obj ((Coh.ι X).obj F)) n
      ≃+ Sheaf.H ((Modules.toSheaf Y).obj ((Coh.ι Y).obj (cohPushforward g F))) n :=
  modulesCohomologyPushforwardAddEquiv g ((Coh.ι X).obj F) n

end AlgebraicGeometry.Scheme
