/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.Finiteness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.WallComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Region

/-!
# A bounded region from a Hodge divisor space

`Spherical/Finiteness.lean` proves that finitely many spherical walls meet a
`BoundedRegion` of the `(β, ω)` chart, and defines the chamber they cut out.
Its own module docstring records that nothing inhabits that structure:

> exhibiting a region with these constants is a statement about the ample cone,
> and the ample cone does not appear in this file

and

> `neg_definite` is the *hypothesis* that the geometric theory would discharge
> by Hodge index; here it is supplied.

Until now nothing in the tree discharged either, so every consequence of
`BoundedRegion` was vacuous.  This file supplies the witness.

## The two constants

`BoundedRegion` asks for a positive lower bound on `q(ω,ω)` and a *uniform*
negative-definiteness constant for `q` on `ω^⊥`.  Both come from
`Divisorial/Region.lean`:

* `DivisorSpace.exists_ampleLower` — a continuous positive function on a compact
  set attains a positive minimum.
* `DivisorSpace.exists_uniform_negDefinite` — the definiteness is pointwise by
  `HodgeDefinite.of_pair_pos`, and compactness makes the constant uniform.

The Hodge input enters once, as `DivisorSpace.HodgeDefinite` at a single
reference class.  `HodgeDefinite.of_pair_pos` is what lets one certificate cover
every `ω` of the family, which is why the region does not have to carry a
certificate per point.

## What this does and does not settle

It makes `finite_walls_meeting` and `chamber` non-vacuous on any Hodge divisor
space.  It does not prove a Hodge index theorem for a geometric surface, and it
says nothing about semistable objects: `chamber` is a subset of the parameter
chart, and constancy of anything on it is not asserted.
-/

open Bornology Set

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical

noncomputable section

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {S : Divisorial.DivisorSpace D} {H : D}

namespace BoundedRegion

/-- **The bounded region of a compact family of parameters on a Hodge divisor
space.**

The carrier is the family itself; the two constants are the ones
`Divisorial/Region.lean` produces.  This is the first witness for
`BoundedRegion`, and it is what makes everything downstream of it non-vacuous. -/
def ofDivisorSpace (h : S.HodgeDefinite H) {K : Set (D × D)} (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2) :
    BoundedRegion S.intersection where
  carrier := K
  bounded := hK.isBounded
  ampleLower := (Divisorial.DivisorSpace.exists_ampleLower hK hpos).choose
  ampleLower_pos := (Divisorial.DivisorSpace.exists_ampleLower hK hpos).choose_spec.1
  ample_le := (Divisorial.DivisorSpace.exists_ampleLower hK hpos).choose_spec.2
  coercivity := (Divisorial.DivisorSpace.exists_uniform_negDefinite h hK hpos).choose
  coercivity_pos :=
    (Divisorial.DivisorSpace.exists_uniform_negDefinite h hK hpos).choose_spec.1
  neg_definite := (Divisorial.DivisorSpace.exists_uniform_negDefinite h hK hpos).choose_spec.2

@[simp]
theorem ofDivisorSpace_carrier (h : S.HodgeDefinite H) {K : Set (D × D)} (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2) :
    (ofDivisorSpace h hK hpos).carrier = K := rfl

end BoundedRegion

/-! ### The two charts are one -/

omit [FiniteDimensional ℝ D] in
/-- **The divisorial exponential plane is the spherical chart plane.**

`Divisorial/Region.lean` builds the plane of `exp(B + iω)` for a divisor space,
and `Spherical/WallComparison.lean` builds it in the `(β, ω)` chart.  Since
`Spherical/Basic.lean` now spells its chart with `Mukai.expRe` and
`Mukai.expIm`, the two are the same submodule and this is `rfl`.

With it, `mem_periodDomainWall_iff_mem_wall` reads as a statement about a
divisor space: the walls counted by `Divisorial/Region.lean` are the vanishing
locus inside the half-walls counted here. -/
theorem expPlane_eq_chartPlane (S : Divisorial.DivisorSpace D) (B omega : D) :
    S.expPlane B omega = chartPlane S.intersection B omega := rfl

/-! ### The consequences, now non-vacuous -/

/-- **Finitely many spherical classes of a lattice have a wall meeting a compact
family of parameters on a Hodge divisor space.**

This is `BoundedRegion.finite_wallCandidates` with the region supplied.  Every
hypothesis is discharged except the Hodge certificate itself. -/
theorem finite_wallCandidates_ofDivisorSpace (h : S.HodgeDefinite H) {K : Set (D × D)}
    (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2)
    {ι : Type*} [Finite ι] (basis : Module.Basis ι ℝ D) :
    (wallCandidates S.intersection (BoundedRegion.ofDivisorSpace h hK hpos)
      ↑(Submodule.span ℤ (Set.range basis))).Finite :=
  BoundedRegion.finite_wallCandidates _ (fun x y => S.pair_comm x y) basis

/-- **On a compact family over a Hodge divisor space, the chamber is cut out by
finitely many walls.**

`chamber_inter_carrier` says the chamber of the whole lattice agrees, on the
region, with the chamber of the wall candidates, and
`finite_wallCandidates_ofDivisorSpace` says those are finite.  Together they are
the chamber decomposition the missing witness has been blocking. -/
theorem chamber_inter_ofDivisorSpace (h : S.HodgeDefinite H) {K : Set (D × D)}
    (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2)
    {ι : Type*} (basis : Module.Basis ι ℝ D) :
    chamber S.intersection
        (latticeSpherical S.intersection ↑(Submodule.span ℤ (Set.range basis))) ∩ K
      = chamber S.intersection
        (wallCandidates S.intersection (BoundedRegion.ofDivisorSpace h hK hpos)
          ↑(Submodule.span ℤ (Set.range basis))) ∩ K :=
  chamber_inter_carrier S.intersection (BoundedRegion.ofDivisorSpace h hK hpos)
    ↑(Submodule.span ℤ (Set.range basis))

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical
