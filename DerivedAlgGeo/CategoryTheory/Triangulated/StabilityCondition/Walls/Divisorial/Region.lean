/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.WallRegion

/-!
# Finitely many spherical walls meet a compact family of exponential planes

`Divisorial/Signature.lean` counts the spherical walls through **one** plane of
the period domain.  That is not enough for a wall-and-chamber structure, which
needs finiteness across a neighbourhood.  This file supplies the region-wise
count for the family of planes of `exp(B + iω)` with `(B, ω)` ranging over a
compact set on which `ω²` is positive.

## Why this is now available

`QuadraticForm/WallRegion.lean` records that the coercivity constant of `-Q` on
`Wᗮ` degrades to `0` at the boundary of the positive-plane locus, so a family of
planes inherits no constant from its members; `PlaneRegion` therefore carries
the constant as a field.  Its criterion `ofCompactPairs` supplies that field for
a compact family — but only from `PeriodDomain.HasSignatureTwo`, which nothing
could provide for a divisor space until
`DivisorSpace.hasSignatureTwo_of_hodgeDefinite`.

So the input to this file is the same single certificate as everywhere else in
the divisorial layer: `DivisorSpace.HodgeDefinite`.

## The family

`expPairMap` sends `(B, ω)` to the spanning pair
`(Re exp(B + iω), Im exp(B + iω))`.  It is continuous because the intersection
form is a bilinear map on a finite-dimensional space, so a compact set of
parameters gives a compact set of pairs; and each plane is positive by
`Mukai.isPositivePair_exp` as soon as `ω² > 0`, with `B` unconstrained.  Those
are exactly the two hypotheses of `ofCompactPairs`.

## Main results

* `expPlaneRegion` — the `PlaneRegion` of a compact parameter family.
* `finite_walls_meeting_expFamily` — **finitely many spherical classes of a
  lattice have a wall meeting the family**, stated with the parameters rather
  than with the region, which is the form a chamber argument consumes.

The lattice is the `ℤ`-span of an `ℝ`-basis and is not asserted to be a
geometric lattice; `D` is an arbitrary finite-dimensional real divisor space.

## What is still not proved

Chambers.  Knowing that finitely many walls meet a compact family does not by
itself produce the connected components of its complement, nor that the
semistable objects are constant on one.  That is the next step and is not
attempted here.
-/

open Bornology QuadraticMap

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

namespace DivisorSpace

variable {D : Type w} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable (S : DivisorSpace D)

/-! ### The exponential family of spanning pairs -/

/-- The spanning pair of the plane of `exp(B + iω)`, as a function of the
parameters. -/
def expPairMap (p : D × D) : Mukai.RealExtension D × Mukai.RealExtension D :=
  (Mukai.expRe S.intersection p.1 p.2, Mukai.expIm S.intersection p.1 p.2)

@[simp]
theorem expPairMap_fst (p : D × D) :
    (S.expPairMap p).1 = Mukai.expRe S.intersection p.1 p.2 := rfl

@[simp]
theorem expPairMap_snd (p : D × D) :
    (S.expPairMap p).2 = Mukai.expIm S.intersection p.1 p.2 := rfl

/-- The plane of a parameter pair is the span of its exponential pair. -/
theorem expPlane_eq_span (B omega : D) :
    S.expPlane B omega
      = Submodule.span ℝ ({(S.expPairMap (B, omega)).1, (S.expPairMap (B, omega)).2} : Set _) :=
  rfl

variable [FiniteDimensional ℝ D]

/-- The intersection form is jointly continuous.  Finite dimensionality is what
turns the bilinear map into a continuous one. -/
theorem continuous_pair : Continuous fun p : D × D => S.pair p.1 p.2 :=
  (LinearMap.toContinuousBilinearMap S.intersection).continuous₂

/-- **The exponential parameter map is continuous**, so a compact set of
parameters gives a compact family of spanning pairs. -/
theorem continuous_expPairMap : Continuous S.expPairMap := by
  have hb := S.continuous_pair
  have hbb : Continuous fun p : D × D => S.pair p.1 p.1 :=
    hb.comp (continuous_fst.prodMk continuous_fst)
  have hww : Continuous fun p : D × D => S.pair p.2 p.2 :=
    hb.comp (continuous_snd.prodMk continuous_snd)
  refine Continuous.prodMk ?_ ?_
  · exact continuous_const.prodMk
      (continuous_fst.prodMk ((hbb.sub hww).div_const 2))
  · exact continuous_const.prodMk (continuous_snd.prodMk hb)

/-! ### The region -/

variable {S} {H : D}

/-- **The plane region of a compact family of exponential parameters.**

Both inputs of `PlaneRegion.ofCompactPairs` are discharged: the signature by the
Hodge certificate, and positivity of each plane by `Mukai.isPositivePair_exp`,
which needs only `ω² > 0`. -/
def expPlaneRegion (h : S.HodgeDefinite H) {K : Set (D × D)} (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2) :
    PeriodDomain.PlaneRegion (Mukai.realForm S.intersection) :=
  PeriodDomain.PlaneRegion.ofCompactPairs (hasSignatureTwo_of_hodgeDefinite h)
    (hK.image S.continuous_expPairMap)
    (by
      rintro q ⟨p, hp, rfl⟩
      exact Mukai.isPositivePair_exp S.intersection p.1 p.2
        (fun x y => S.pair_comm x y) (hpos p hp))

@[simp]
theorem expPlaneRegion_carrier (h : S.HodgeDefinite H) {K : Set (D × D)} (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2) :
    (expPlaneRegion h hK hpos).carrier =
      (fun q : Mukai.RealExtension D × Mukai.RealExtension D =>
        Submodule.span ℝ ({q.1, q.2} : Set (Mukai.RealExtension D))) '' (S.expPairMap '' K) :=
  rfl

/-! ### The count -/

/-- **Finitely many spherical classes of a lattice have a wall meeting the
region.**  This is `PlaneRegion.finite_wallClasses_inter` with the region
supplied. -/
theorem finite_wallClasses_expPlaneRegion (h : S.HodgeDefinite H) {K : Set (D × D)}
    (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    ((expPlaneRegion h hK hpos).wallClasses
      ∩ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))).Finite :=
  PeriodDomain.PlaneRegion.finite_wallClasses_inter _ b

/-- **Bridgeland's local finiteness, region-wise, on a divisor space.**

For a compact set `K` of parameters on which `ω²` is positive, only finitely
many spherical classes of the lattice have a wall through the plane of
`exp(B + iω)` for *some* `(B, ω) ∈ K`.

This is the form a chamber argument consumes: the parameters appear, not the
region.  The hypotheses are the Hodge certificate, compactness, and positivity
of `ω²` on the family. -/
theorem finite_walls_meeting_expFamily (h : S.HodgeDefinite H) {K : Set (D × D)}
    (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    {δ : Mukai.RealExtension D |
        PeriodDomain.IsSphericalClass (Mukai.realForm S.intersection) δ ∧
        (∃ p ∈ K, S.expPlane p.1 p.2 ∈
          PeriodDomain.wall (Mukai.realForm S.intersection) δ) ∧
        δ ∈ (Submodule.span ℤ (Set.range b) :
              Set (Mukai.RealExtension D))}.Finite := by
  refine Set.Finite.subset (finite_wallClasses_expPlaneRegion h hK hpos b) ?_
  rintro δ ⟨hsph, ⟨p, hp, hwall⟩, hlat⟩
  refine ⟨⟨hsph, ?_⟩, hlat⟩
  exact ⟨S.expPlane p.1 p.2, ⟨S.expPairMap p, ⟨p, hp, rfl⟩, rfl⟩, hwall⟩

end DivisorSpace

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
