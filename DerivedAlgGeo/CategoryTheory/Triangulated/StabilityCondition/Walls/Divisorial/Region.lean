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

/-! ### A uniform negative-definiteness constant on the family -/

/-- The scaling step: a bound on the normalization of `x` is a bound on `x`. -/
private theorem scale_bound {c : ℝ} {u : D} (hu : u ≠ 0)
    (hle : c ≤ -(S.pair (‖u‖⁻¹ • u) (‖u‖⁻¹ • u))) : S.pair u u ≤ -c * ‖u‖ ^ 2 := by
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hval : S.pair (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) = (‖u‖⁻¹) ^ 2 * S.pair u u := by
    simp only [DivisorSpace.pair, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hval] at hle
  have h2 := mul_le_mul_of_nonneg_right hle (sq_nonneg ‖u‖)
  have hrw : -((‖u‖⁻¹) ^ 2 * S.pair u u) * ‖u‖ ^ 2 = -(S.pair u u) := by
    have hne : (‖u‖ : ℝ) ≠ 0 := ne_of_gt hnu
    field_simp
  rw [hrw] at h2
  linarith

/-- **A compact family of polarizations has a positive lower bound for `ω²`.**

The second constant `Spherical.BoundedRegion` asks for.  A continuous positive
function on a compact set attains a positive minimum; the empty family takes
any positive number. -/
theorem exists_ampleLower {K : Set (D × D)} (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ K, a ≤ S.pair p.2 p.2 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne
      (S.continuous_pair.comp (continuous_snd.prodMk continuous_snd)).continuousOn
    exact ⟨S.pair p₀.2 p₀.2, hpos p₀ hp₀, fun p hp => isMinOn_iff.mp hmin _ hp⟩

/-- **A compact family of polarizations has a uniform negative-definiteness
constant.**

`HodgeDefinite.of_pair_pos` makes the form negative definite on `ω^⊥` at every
point of the family, but with a constant that could in principle degrade across
it.  Compactness rules that out: the pairs of the family and the unit vectors
orthogonal to their `ω` form a compact set, on which `-q` is continuous and
positive, so it attains a positive minimum.  Homogeneity extends the bound off
the sphere.

This is the input `Spherical.BoundedRegion` asks for and has never had. -/
theorem exists_uniform_negDefinite (h : S.HodgeDefinite H) {K : Set (D × D)}
    (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < S.pair p.2 p.2) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x : D, S.pair x p.2 = 0 → S.pair x x ≤ -c * ‖x‖ ^ 2 := by
  have horthC : Continuous fun z : (D × D) × D => S.pair z.2 z.1.2 :=
    S.continuous_pair.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have hclosed : IsClosed {z : (D × D) × D | S.pair z.2 z.1.2 = 0} :=
    isClosed_eq horthC continuous_const
  set T : Set ((D × D) × D) :=
    (K ×ˢ Metric.sphere (0 : D) 1) ∩ {z | S.pair z.2 z.1.2 = 0} with hTdef
  have hTcompact : IsCompact T := (hK.prod (isCompact_sphere (0 : D) 1)).inter_right hclosed
  have hmemT : ∀ p ∈ K, ∀ v : D, ‖v‖ = 1 → S.pair v p.2 = 0 →
      ((p, v) : (D × D) × D) ∈ T := by
    intro p hp v hv hvo
    exact ⟨⟨hp, by simpa [Metric.mem_sphere, dist_eq_norm] using hv⟩, hvo⟩
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, one_pos, fun p hp x hx => ?_⟩
    have hx0 : x = 0 := by
      by_contra hne
      have hnu : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
      have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
      have horth : S.pair (‖x‖⁻¹ • x) p.2 = 0 := by
        simp only [DivisorSpace.pair, map_smul, LinearMap.smul_apply, smul_eq_mul]
        simp only [DivisorSpace.pair] at hx
        rw [hx, mul_zero]
      have hmem := hmemT p hp _ hnorm horth
      rw [hTe] at hmem
      exact hmem
    simp [hx0, DivisorSpace.pair]
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hTcompact.exists_isMinOn hTne
        ((S.continuous_pair.comp (continuous_snd.prodMk continuous_snd)).neg).continuousOn
    have hz₀K : z₀.1 ∈ K := hz₀.1.1
    have hz₀norm : ‖z₀.2‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz₀.1.2
    have hz₀ne : z₀.2 ≠ 0 := by
      intro hc
      rw [hc, norm_zero] at hz₀norm
      exact zero_ne_one hz₀norm
    have hz₀neg : S.pair z₀.2 z₀.2 < 0 :=
      (h.of_pair_pos (hpos z₀.1 hz₀K)).neg_definite z₀.2
        (by rw [S.pair_comm]; exact hz₀.2) hz₀ne
    refine ⟨-(S.pair z₀.2 z₀.2), by linarith, fun p hp x hx => ?_⟩
    rcases eq_or_ne x 0 with rfl | hxne
    · simp [DivisorSpace.pair]
    · refine scale_bound hxne ?_
      have hnu : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hxne
      have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
      have horth : S.pair (‖x‖⁻¹ • x) p.2 = 0 := by
        simp only [DivisorSpace.pair, map_smul, LinearMap.smul_apply, smul_eq_mul]
        simp only [DivisorSpace.pair] at hx
        rw [hx, mul_zero]
      exact isMinOn_iff.mp hmin _ (hmemT p hp _ hnorm horth)


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
