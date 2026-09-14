/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrthogonalityFiniteness

/-!
# Regions of positive planes, and the orthogonality loci that meet them

`OrthogonalityFiniteness.lean` counts the spherical orthogonality loci through
**one** positive plane.
This file does it for a family, which is what a local-finiteness statement about
the period domain needs.

## The constant is a hypothesis, and this file says why

The pointwise count runs on the coercivity constant of `-Q` on `Wᗮ`. That
constant depends on `W` and degrades to `0` as the plane approaches the boundary
of the positive-plane locus, so a family of planes inherits no constant from its
members. This is one of the two gaps in Bridgeland's own §11 argument.

`PlaneRegion` therefore carries `coercivity` as an **explicit field**, exactly as
`Walls/Spherical/Finiteness.lean` does for `BoundedRegion` in the other chart. It
is never derived from boundedness of the region.

## And a criterion that inhabits it

A structure whose hypothesis nobody can satisfy proves nothing.
`exists_uniform_coercivity` supplies the field for a **compact** family of
spanning pairs: orthogonality is a closed condition, so the unit vectors
orthogonal to the planes of the family form a compact set, `-Q` is continuous and
positive there, and its minimum is the constant. `ofCompactPairs` packages that
as a `PlaneRegion`.

The family is parametrized by spanning pairs rather than by the Grassmannian,
which keeps everything inside the linear algebra already in the tree.

## Main results

* `exists_uniform_coercivity` — a compact family of positive planes has a
  uniform coercivity constant. Its closedness input, `mem_orthogonal_span_pair_iff`,
  is pure algebra and lives in `PositivePlane.lean`.
* `PlaneRegion.finite_orthogonalClasses_inter` — **finitely many spherical classes of a
  lattice have an orthogonality locus meeting the region.**
* `PlaneRegion.ofCompactPairs` — the criterion, packaged; and `PlaneRegion.empty`
  for contrast, a witness that proves only non-vacuity of the structure.

As in `PositivePlane.lean`, everything is about an arbitrary real quadratic space
and its lattices, and no geometry is asserted.
-/

open Bornology QuadraticMap

namespace PeriodDomain

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
variable {Q : QuadraticForm ℝ M}

omit [FiniteDimensional ℝ M] in
/-- The scaling step shared by the two coercivity arguments: a bound on the
normalization of `u` is a bound on `u`. -/
private theorem mul_norm_sq_le_of_normalized {c : ℝ} {u : M} (hu : u ≠ 0)
    (h : c ≤ -Q (‖u‖⁻¹ • u)) : c * ‖u‖ ^ 2 ≤ -Q u := by
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  rw [QuadraticMap.map_smul, smul_eq_mul] at h
  have h2 := mul_le_mul_of_nonneg_right h (sq_nonneg ‖u‖)
  rwa [show -((‖u‖⁻¹ * ‖u‖⁻¹) * Q u) * ‖u‖ ^ 2 = -Q u by field_simp] at h2

/-- **A compact family of positive planes has a uniform coercivity constant.**

The pairs of the family and the unit vectors orthogonal to the plane they span
form a compact set — orthogonality is closed by `continuous_polar`, and the
sphere is compact. `-Q` is continuous and, by `neg_of_mem_orthogonal`, positive
there, so it attains a positive minimum. Homogeneity extends the bound off the
sphere. -/
theorem exists_uniform_coercivity (hsig : HasSignatureTwo Q) {S : Set (M × M)}
    (hS : IsCompact S)
    (hpos : ∀ p ∈ S, IsPositivePlane Q (Submodule.span ℝ ({p.1, p.2} : Set M))) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, ∀ u ∈ orthogonal Q (Submodule.span ℝ ({p.1, p.2} : Set M)),
      c * ‖u‖ ^ 2 ≤ -Q u := by
  have hc1 : Continuous fun z : (M × M) × M => polar (⇑Q) z.1.1 z.2 :=
    Q.continuous_polar.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hc2 : Continuous fun z : (M × M) × M => polar (⇑Q) z.1.2 z.2 :=
    Q.continuous_polar.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hclosed : IsClosed {z : (M × M) × M |
      polar (⇑Q) z.1.1 z.2 = 0 ∧ polar (⇑Q) z.1.2 z.2 = 0} :=
    (isClosed_eq hc1 continuous_const).inter (isClosed_eq hc2 continuous_const)
  set T : Set ((M × M) × M) :=
    (S ×ˢ Metric.sphere (0 : M) 1) ∩
      {z | polar (⇑Q) z.1.1 z.2 = 0 ∧ polar (⇑Q) z.1.2 z.2 = 0} with hTdef
  have hTcompact : IsCompact T := (hS.prod (isCompact_sphere (0 : M) 1)).inter_right hclosed
  -- membership in `T`, unfolded once and reused
  have hmemT : ∀ p ∈ S, ∀ v : M, ‖v‖ = 1 →
      v ∈ orthogonal Q (Submodule.span ℝ ({p.1, p.2} : Set M)) → ((p, v) : (M × M) × M) ∈ T := by
    intro p hp v hv hvo
    refine ⟨⟨hp, ?_⟩, mem_orthogonal_span_pair_iff.mp hvo⟩
    simpa [mem_sphere_iff_norm] using hv
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, one_pos, fun p hp u hu => ?_⟩
    have hu0 : u = 0 := by
      by_contra hne
      have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hne
      have hmem : ((p, ‖u‖⁻¹ • u) : (M × M) × M) ∈ T := by
        refine hmemT p hp _ ?_ (Submodule.smul_mem _ _ hu)
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
      rw [hTe] at hmem
      exact hmem
    simp [hu0]
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      hTcompact.exists_isMinOn hTne
        (((continuous_of_finiteDimensional Q).comp continuous_snd).neg).continuousOn
    have hz₀S : z₀.1 ∈ S := hz₀.1.1
    have hz₀norm : ‖z₀.2‖ = 1 := by simpa [mem_sphere_iff_norm] using hz₀.1.2
    have hz₀orth : z₀.2 ∈ orthogonal Q (Submodule.span ℝ ({z₀.1.1, z₀.1.2} : Set M)) :=
      mem_orthogonal_span_pair_iff.mpr hz₀.2
    have hz₀ne : z₀.2 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz₀norm
      exact zero_ne_one hz₀norm
    refine ⟨-Q z₀.2, ?_, fun p hp u hu => ?_⟩
    · have := neg_of_mem_orthogonal hsig (hpos z₀.1 hz₀S) hz₀orth hz₀ne
      linarith
    · rcases eq_or_ne u 0 with rfl | hune
      · simp
      · refine mul_norm_sq_le_of_normalized hune ?_
        have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hune
        have hmem : ((p, ‖u‖⁻¹ • u) : (M × M) × M) ∈ T := by
          refine hmemT p hp _ ?_ (Submodule.smul_mem _ _ hu)
          rw [norm_smul, norm_inv, norm_norm]
          field_simp
        exact isMinOn_iff.mp hmin _ hmem

/-- A **region** of positive planes carrying a uniform coercivity constant.

`coercivity` is a field on purpose: it does not follow from boundedness of the
region, and deriving it is the mistake §11 makes. Use `ofCompactPairs` to build
one. -/
structure PlaneRegion (Q : QuadraticForm ℝ M) where
  /-- The planes of the region. -/
  carrier : Set (Submodule ℝ M)
  /-- Each of them is a positive plane. -/
  isPositivePlane : ∀ W ∈ carrier, IsPositivePlane Q W
  /-- The uniform constant. -/
  coercivity : ℝ
  /-- It is positive. -/
  coercivity_pos : 0 < coercivity
  /-- And it works for every plane of the region at once. -/
  uniform : ∀ W ∈ carrier, ∀ u ∈ orthogonal Q W, coercivity * ‖u‖ ^ 2 ≤ -Q u

namespace PlaneRegion

variable (R : PlaneRegion Q)

/-- The spherical classes with a orthogonalityLocus meeting the region. -/
def orthogonalClasses : Set M :=
  {δ | IsSphericalClass Q δ ∧ ∃ W ∈ R.carrier, W ∈ orthogonalityLocus Q δ}

omit [FiniteDimensional ℝ M] in
/-- **The orthogonalityLocus classes of a region are bounded**, by the one constant the region
carries. -/
theorem isBounded_orthogonalClasses : IsBounded R.orthogonalClasses := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (1 / R.coercivity), ?_⟩
  rintro δ ⟨hsph, W, hW, hwall⟩
  have hmem : δ ∈ orthogonal Q W :=
    (mem_orthogonalityLocus_iff_mem_orthogonal (R.isPositivePlane W hW)).mp hwall
  have h := R.uniform W hW δ hmem
  rw [isSphericalClass_iff_apply.mp hsph] at h
  have hsq : ‖δ‖ ^ 2 ≤ 1 / R.coercivity := by
    rw [le_div_iff₀ R.coercivity_pos]
    linarith
  exact (Real.le_sqrt (norm_nonneg δ) (div_nonneg zero_le_one R.coercivity_pos.le)).mpr hsq

/-- **Only finitely many spherical classes of a lattice have a orthogonalityLocus meeting the
region.** Bridgeland's local finiteness in the period-domain chart, with the
uniform constant explicit. -/
theorem finite_orthogonalClasses_inter {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ M) :
    (R.orthogonalClasses ∩ (Submodule.span ℤ (Set.range b) : Set M)).Finite :=
  ZSpan.setFinite_inter b R.isBounded_orthogonalClasses

end PlaneRegion

/-- **The criterion, packaged.** A compact family of spanning pairs is a region,
with the constant supplied by `exists_uniform_coercivity` rather than assumed. -/
noncomputable def PlaneRegion.ofCompactPairs (hsig : HasSignatureTwo Q) {S : Set (M × M)}
    (hS : IsCompact S)
    (hpos : ∀ p ∈ S, IsPositivePlane Q (Submodule.span ℝ ({p.1, p.2} : Set M))) :
    PlaneRegion Q where
  carrier := (fun p : M × M => Submodule.span ℝ ({p.1, p.2} : Set M)) '' S
  isPositivePlane := by
    rintro W ⟨p, hp, rfl⟩
    exact hpos p hp
  coercivity := (exists_uniform_coercivity hsig hS hpos).choose
  coercivity_pos := (exists_uniform_coercivity hsig hS hpos).choose_spec.1
  uniform := by
    rintro W ⟨p, hp, rfl⟩ u hu
    exact (exists_uniform_coercivity hsig hS hpos).choose_spec.2 p hp u hu

/-- The empty region. It inhabits the structure and proves nothing else — every
statement about it is vacuous. `ofCompactPairs` is the witness that carries
content; this one is here so the difference is on the record. -/
def PlaneRegion.empty (Q : QuadraticForm ℝ M) : PlaneRegion Q where
  carrier := ∅
  isPositivePlane W hW := absurd hW (Set.notMem_empty W)
  coercivity := 1
  coercivity_pos := one_pos
  uniform W hW := absurd hW (Set.notMem_empty W)

end PeriodDomain
