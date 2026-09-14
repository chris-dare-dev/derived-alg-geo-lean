/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrameOpen
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrthogonalityLocus
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Positive planes avoiding countably many orthogonality loci exist

#700 fixed `positivePlanesAway` to take its cutting classes from a set, after the
reading that cut by *every* real class of square `-2` turned out to be empty.
That leaves the obvious question, and this file answers it: for a **countable**
set of nonzero classes — the spherical classes of a lattice, countable because
the lattice is finitely generated and free — the cut domain is nonempty.

## The argument

Genericity, over pairs rather than planes, since `M × M` carries the topology.

* The positive frames are **open** (`isOpen_setOf_isPositiveFrame`) and nonempty
  (`exists_isPositiveFrame`).
* For `δ ≠ 0` the pairs orthogonal to `δ` form a **proper closed subspace** of
  `M × M`: it is the kernel of `p ↦ (⟪δ, p.1⟫, ⟪δ, p.2⟫)`, nonzero because the
  form is nondegenerate. A proper subspace of a normed space has empty interior,
  so its complement is open and dense.
* Baire: a countable intersection of dense open sets is dense, and a dense set
  meets every nonempty open set.

Density of the cut locus in the positive frames is what the argument actually
gives; nonemptiness is the corollary that was asked for.

## The cheap route does not work

Along a ray `ω_t = t • ω₀` in the exponential chart, the orthogonalityLocus condition for a
rank-zero spherical class is `b ω₀ c = 0` together with `b c c = -2`, and neither
depends on `t`: such a class blocks the whole ray. Nonemptiness needs genericity,
not a scaling trick — which is also why Bridgeland works with an ample class
rather than a merely positive one.
-/

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

section Existence

variable [FiniteDimensional ℝ M]

/-- **A positive plane is spanned by a positive frame.** Taking any nonzero `x` of
the plane and any `y` outside its line, the discriminant is positive because
`Q ((-⟪x,y⟫) • x + (2 * Q x) • y) = Q x * (4 * Q x * Q y - ⟪x,y⟫ ^ 2)` and the
left side is positive. -/
theorem exists_isPositiveFrame (hsig : HasSignatureTwo Q) : ∃ x y : M, IsPositiveFrame Q x y := by
  obtain ⟨W, hW⟩ := exists_isPositivePlane hsig
  have hrank : Module.finrank ℝ W = 2 := hW.finrank_eq
  have hnt : Nontrivial W := by
    have hpos : 0 < Module.finrank ℝ W := by omega
    exact (Module.finrank_pos_iff (R := ℝ)).mp hpos
  obtain ⟨x', hx'⟩ := exists_ne (0 : W)
  -- a line inside a plane is proper, so some vector of the plane lies off it
  have hline : (ℝ ∙ x') ≠ (⊤ : Submodule ℝ W) := by
    intro htop
    have h1 : Module.finrank ℝ (ℝ ∙ x' : Submodule ℝ W) = 1 := finrank_span_singleton hx'
    rw [htop] at h1
    simp only [finrank_top] at h1
    omega
  obtain ⟨y', hy'⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hline)
  set x : M := (x' : M) with hx
  set y : M := (y' : M) with hy
  have hxW : x ∈ W := x'.2
  have hyW : y ∈ W := y'.2
  have hQx : 0 < Q x := by
    have := hW.posDef x' (by simpa using hx')
    rwa [QuadraticMap.restrict_apply] at this
  -- a combination with nonzero `y`-coefficient is nonzero, since `y` is off the line
  have hcomb_ne : ∀ a b : ℝ, b ≠ 0 → a • x + b • y ≠ 0 := by
    intro a b hb h0
    apply hy'.2
    have hbx : b • y = (-a) • x := by
      rw [neg_smul]
      linear_combination (norm := module) h0
    have hy_eq : y = (-(a / b)) • x := by
      calc y = b⁻¹ • (b • y) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • ((-a) • x) := by rw [hbx]
        _ = (-(a / b)) • x := by rw [smul_smul]; ring_nf
    have hy'eq : y' = (-(a / b)) • x' := Subtype.ext (by simpa [hx, hy] using hy_eq)
    rw [hy'eq]
    exact Submodule.mem_span_singleton.mpr ⟨-(a / b), rfl⟩
  refine ⟨x, y, (isPositiveFrame_iff x y).mpr ⟨hQx, ?_⟩⟩
  set d : ℝ := 4 * Q x * Q y - (polar (⇑Q) x y) ^ 2 with hd
  set v : M := (-(polar (⇑Q) x y)) • x + (2 * Q x) • y with hv
  have hvW : v ∈ W := Submodule.add_mem _ (Submodule.smul_mem _ _ hxW) (Submodule.smul_mem _ _ hyW)
  have hv0 : v ≠ 0 := hcomb_ne _ _ (by positivity)
  have hQv : 0 < Q v := by
    have := hW.posDef ⟨v, hvW⟩ (by simpa using hv0)
    rwa [QuadraticMap.restrict_apply] at this
  have hval : Q v = Q x * d := by
    rw [hv, apply_smul_add_smul, hd]
    ring
  rw [hval] at hQv
  by_contra hdle
  push Not at hdle
  nlinarith

end Existence

section Baire

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
variable (Q : QuadraticForm ℝ N)

/-- The pairs both of whose entries are orthogonal to `δ`. -/
def orthogonalityPairs (δ : N) : Submodule ℝ (N × N) :=
  LinearMap.ker ((Q.polarBilin δ).prodMap (Q.polarBilin δ))

variable {Q}

omit [FiniteDimensional ℝ N] in
/-- Membership unfolded: a pair is on the orthogonalityLocus of `δ` when `δ` is orthogonal to
both entries, which is the form the Baire argument and `mem_orthogonalityLocus_iff_mem_orthogonal`
both consume. -/
@[simp]
theorem mem_orthogonalityPairs_iff {δ : N} {p : N × N} :
    p ∈ orthogonalityPairs Q δ ↔ polar (⇑Q) δ p.1 = 0 ∧ polar (⇑Q) δ p.2 = 0 := by
  simp [orthogonalityPairs, LinearMap.mem_ker]

omit [FiniteDimensional ℝ N] in
/-- For a nonzero class the orthogonalityLocus is a **proper** subspace of `M × M`.

Nondegeneracy is what supplies a vector the class does not annihilate, and
properness is the whole content: it is what gives the orthogonalityLocus empty interior, and
hence a dense complement for Baire to intersect. Without nondegeneracy a class
could pair to zero with everything and its orthogonalityLocus would be all of `M × M`. -/
theorem orthogonalityPairs_ne_top (hnd : Q.Nondegenerate) {δ : N} (hδ : δ ≠ 0) :
    orthogonalityPairs Q δ ≠ ⊤ := by
  intro htop
  have hpolar : ∀ z : N, polar (⇑Q) δ z = 0 := by
    intro z
    have : ((z, z) : N × N) ∈ orthogonalityPairs Q δ := by rw [htop]; trivial
    exact (mem_orthogonalityPairs_iff.mp this).1
  have hrad : δ ∈ Q.radical := by
    refine ⟨?_, ?_⟩
    · have h := hpolar δ
      rw [polar_self, two_nsmul] at h
      linarith
    · ext z
      simpa using hpolar z
  rw [hnd.radical_eq_bot, Submodule.mem_bot] at hrad
  exact hδ hrad

omit [FiniteDimensional ℝ N] in
/-- Hence its complement is dense.

A proper subspace of a normed space has empty interior — otherwise a ball inside
it would generate the whole space — and a set with empty interior has dense
complement. This is the input Baire consumes, one class at a time. -/
theorem dense_compl_orthogonalityPairs (hnd : Q.Nondegenerate) {δ : N} (hδ : δ ≠ 0) :
    Dense ((orthogonalityPairs Q δ : Set (N × N))ᶜ) := by
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra hint
  exact orthogonalityPairs_ne_top hnd hδ
    (Submodule.eq_top_of_nonempty_interior' (orthogonalityPairs Q δ)
      (Set.nonempty_iff_ne_empty.mpr hint))

/-- **The positive-plane locus avoiding the selected classes is nonempty.**

The positive frames are open and nonempty, each orthogonality locus of a nonzero class is closed
with dense complement, and Baire lets a countable family of them be avoided all
at once. -/
theorem nonempty_positivePlanesAway (hsig : HasSignatureTwo Q) {Δ : Set N}
    (hcount : Δ.Countable) (hzero : ∀ δ ∈ Δ, δ ≠ 0) :
    (positivePlanesAway Q Δ).Nonempty := by
  have hnd : Q.Nondegenerate := nondegenerate hsig
  haveI : Countable Δ := hcount.to_subtype
  have hdense : Dense (⋂ δ : Δ, ((orthogonalityPairs Q (δ : N) : Set (N × N))ᶜ)) := by
    refine dense_iInter_of_isOpen (fun δ => ?_) (fun δ => ?_)
    · exact (Submodule.closed_of_finiteDimensional (orthogonalityPairs Q (δ : N))).isOpen_compl
    · exact dense_compl_orthogonalityPairs hnd (hzero δ δ.2)
  obtain ⟨x, y, hxy⟩ := exists_isPositiveFrame hsig
  obtain ⟨p, hpmem, hppos⟩ :=
    hdense.exists_mem_open (isOpen_setOf_isPositiveFrame Q) ⟨(x, y), hxy⟩
  refine ⟨pairSpan p.1 p.2, hppos, fun δ hδ hwall => ?_⟩
  have hmem : δ ∈ orthogonal Q (pairSpan p.1 p.2) :=
    (mem_orthogonalityLocus_iff_mem_orthogonal hppos).mp hwall
  rw [pairSpan, mem_orthogonal_span_pair_iff] at hmem
  have : p ∈ orthogonalityPairs Q δ := by
    refine mem_orthogonalityPairs_iff.mpr ⟨?_, ?_⟩
    · exact (polar_comm (⇑Q) δ p.1).trans hmem.1
    · exact (polar_comm (⇑Q) δ p.2).trans hmem.2
  exact (Set.mem_iInter.mp hpmem ⟨δ, hδ⟩) this

end Baire

end PeriodDomain
