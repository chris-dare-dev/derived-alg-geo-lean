/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.ComplexPairing
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Positive planes in a real quadratic space of signature `(2, n - 2)`

A quadratic space `(M, Q)` over `ℝ` whose signature is `(2, n - 2)` carries a
distinguished family of two-dimensional subspaces: the **positive planes**, the
planes on which `Q` is positive definite. This file owns that neutral carrier;
`OrthogonalityLocus.lean` separately owns the loci cut out inside it.

In the K3 application, `M = N(X) ⊗ ℝ` and a complex vector determines an
ordered frame `(Re Ω, Im Ω)`, which then forgets to the plane it spans. Those
three presentations are not interchangeable. `PositiveFrame.lean` supplies
the explicit frame-to-plane map; a geometric period-domain identification must
be stated with its geometric realization.

**No geometry is asserted here.** Every statement below is a statement about an
arbitrary real quadratic space of signature `(2, n - 2)` and is true whether or
not any K3 surface exists; the identification of such a space with `N(X) ⊗ ℝ`
needs `Dᵇ(Coh X)`, Chern characters and Hirzebruch–Riemann–Roch, none of which
appear here. This is the discipline `LinearAlgebra/Lattice/Mukai/Basic.lean`
states for the integral lattice, applied to its real span.

## The two conventions, and which one is used

Bridgeland writes the pairing bilinearly: a spherical class has `(δ, δ) = -2`.
Mathlib's signature API is quadratic-form-native (`sigPos`, `sigNeg`), and the
bilinear form belonging to a `QuadraticForm` is its polar form, which satisfies
`polar Q δ δ = 2 * Q δ`. `Q` carries the Sylvester theory and
`Q.polarBilin` **is** the pairing; spherical-class and orthogonality-locus
terminology starts in `OrthogonalityLocus.lean`.

## Main results

* `Nondegenerate` of the form, from the signature hypothesis alone.
* `isCompl_orthogonal` — `M = W ⊕ Wᗮ` for a positive plane `W`.
* `neg_of_mem_orthogonal` and `negDef_orthogonal` — **the engine**: `Q` is
  negative definite on `Wᗮ`. Downstream orthogonality-finiteness statements
  rest on this, since it makes the pairing definite on the orthogonal space.
* `exists_isPositivePlane` and `stdForm_hasSignatureTwo` — the hypothesis is
  inhabited and its positive-plane locus is nonempty, so nothing above is vacuous.
  `sigPos Q = 2` carries its own positive plane; `stdForm` is `x₀² + x₁² - x₂²`
  on `ℝ³`, the smallest space the hypothesis holds for.

## What is deliberately absent

* **Finiteness of orthogonality loci.** That needs a lattice inside `M` and its
  discreteness on top of `negDef_orthogonal`; it is not a statement about the
  real quadratic space alone.
* **The component `P⁺` of `P`.** Choosing the connected component containing
  `exp(iω)` is orientation data on the positive plane. Nothing below needs it.
* **A complex-vector or geometric period domain.** Bridgeland's domain sits in
  `M ⊗ ℝ ℂ`, while `positivePlanes Q` is a set of submodules. Passing through
  `(Re Ω, Im Ω)` forgets an ordered basis and then its orientation; it is a map,
  not a rename or a literal identification of carriers.
-/

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

section Defs

variable (Q : QuadraticForm ℝ M)

/-- A **positive plane**: a two-dimensional subspace on which `Q` is positive
definite. In the K3 case these are the planes spanned by `Re Ω` and `Im Ω` for
`Ω` in Bridgeland's `P(X)`. -/
structure IsPositivePlane (W : Submodule ℝ M) : Prop where
  /-- The subspace is a plane. -/
  finrank_eq : Module.finrank ℝ W = 2
  /-- `Q` is positive definite on it. -/
  posDef : (Q.restrict W).PosDef

/-- The signature hypothesis: `(2, n - 2)`, written without truncated
subtraction. Nondegeneracy is a consequence rather than a field, see
`nondegenerate`. -/
structure HasSignatureTwo : Prop where
  /-- The positive index of inertia is `2`. -/
  sigPos_eq : sigPos Q = 2
  /-- The negative index of inertia takes up everything else. -/
  sigNeg_add_two : sigNeg Q + 2 = Module.finrank ℝ M

/-- The locus of all positive planes. -/
def positivePlanes : Set (Submodule ℝ M) := {W | IsPositivePlane Q W}

end Defs

variable {Q : QuadraticForm ℝ M}

/-- The pairing is symmetric, hence reflexive. -/
theorem polarBilin_isRefl : Q.polarBilin.IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  exact (polar_comm (⇑Q) y x).trans h

/-- The pairing is nondegenerate on a positive plane: a vector of the plane
orthogonal to the whole plane is orthogonal to itself, so its square vanishes
and positive definiteness kills it. -/
theorem restrict_nondegenerate_of_isPositivePlane {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) :
    (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate := by
  have key : ∀ x : W, LinearMap.BilinForm.restrict Q.polarBilin W x x = 0 → x = 0 := by
    intro x hxx
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply, polar_self, two_nsmul] at hxx
    by_contra hx0
    have hpos := hW.posDef x hx0
    rw [restrict_apply] at hpos
    linarith
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

/-- Adjoining a vector of positive square from `Wᗮ` to a positive plane gives a
three-dimensional positive definite subspace. This is the whole content of
`nonpos_of_mem_orthogonal`: `sigPos = 2` forbids such a subspace. -/
private theorem posDef_sup_span {W : Submodule ℝ M} (hW : IsPositivePlane Q W)
    {u : M} (hu : u ∈ orthogonal Q W) (hQu : 0 < Q u) :
    (Q.restrict (W ⊔ (ℝ ∙ u))).PosDef := by
  rintro ⟨x, hx⟩ hx0
  rw [Submodule.mem_sup] at hx
  obtain ⟨w, hw, z, hz, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hpolar : polar (⇑Q) w (a • u) = 0 := by
    rw [polar_smul_right, mem_orthogonal_iff.mp hu w hw, smul_zero]
  have hval : Q (w + a • u) = Q w + (a * a) * Q u := by
    have := polar_add_right (Q := Q) w w (a • u)
    simp only [polar, QuadraticMap.map_smul, smul_eq_mul] at hpolar ⊢
    linarith [hpolar]
  rw [restrict_apply, hval]
  have hne : w ≠ 0 ∨ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (by simp [hcon.1, hcon.2])
  have hw' : 0 ≤ Q w := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · exact le_of_lt (by simpa [restrict_apply] using hW.posDef ⟨w, hw⟩ (by simpa using hw0))
  rcases hne with hne | hne
  · have : 0 < Q w := by
      simpa [restrict_apply] using hW.posDef ⟨w, hw⟩ (by simpa using hne)
    nlinarith [mul_self_nonneg a]
  · nlinarith [mul_self_pos.mpr hne]

/-- On a subspace where `Q` is nonpositive, an isotropic vector is orthogonal to
everything: `t = c / (1 - Q y)` makes `Q (u + t • y) = c² / (1 - Q y)²`, which is
positive as soon as the pairing `c` is nonzero. -/
private theorem polar_eq_zero_of_nonpos {S : Submodule ℝ M}
    (hle : ∀ y ∈ S, Q y ≤ 0) {u : M} (hu : u ∈ S) (hQu : Q u = 0) {y : M} (hy : y ∈ S) :
    polar (⇑Q) u y = 0 := by
  by_contra hc
  set c := polar (⇑Q) u y with hcdef
  set q := Q y with hqdef
  have hq : q ≤ 0 := hle y hy
  have h1 : (0 : ℝ) < 1 - q := by linarith
  set t := c / (1 - q) with htdef
  have hmem : u + t • y ∈ S := S.add_mem hu (S.smul_mem t hy)
  have hval : Q (u + t • y) = Q u + (t * t) * q + t * c := by
    have h₁ : polar (⇑Q) u (t • y) = t * c := by
      rw [polar_smul_right, smul_eq_mul]
    have h₂ : Q (t • y) = (t * t) * Q y := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
    have h₃ : polar (⇑Q) u (t • y) = Q (u + t • y) - Q u - Q (t • y) := rfl
    rw [h₁, h₂] at h₃
    linarith
  have hpos : 0 < Q (u + t • y) := by
    rw [hval, hQu, htdef]
    have hne : c * c > 0 := mul_self_pos.mpr hc
    have : c / (1 - q) * (c / (1 - q)) * q + c / (1 - q) * c
        = c * c / ((1 - q) * (1 - q)) := by
      field_simp
      ring
    rw [zero_add, this]
    positivity
  exact absurd (hle _ hmem) (not_le.mpr hpos)

section FiniteDimensional

variable [FiniteDimensional ℝ M]

/-- The signature hypothesis leaves no radical. -/
theorem nondegenerate (hsig : HasSignatureTwo Q) : Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero]
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hsig.sigPos_eq, ← hsig.sigNeg_add_two] at h
  omega

/-- `M = W ⊕ Wᗮ` for a positive plane `W`. -/
theorem isCompl_orthogonal {W : Submodule ℝ M} (hW : IsPositivePlane Q W) :
    IsCompl W (orthogonal Q W) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate polarBilin_isRefl
    (restrict_nondegenerate_of_isPositivePlane hW)

/-- **`Q` is nonpositive on the orthogonal complement of a positive plane.**
A vector of positive square there would produce a three-dimensional positive
definite subspace, and `sigPos Q = 2`. -/
theorem nonpos_of_mem_orthogonal (hsig : HasSignatureTwo Q) {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) {u : M} (hu : u ∈ orthogonal Q W) : Q u ≤ 0 := by
  by_contra hQu
  push Not at hQu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hQu
    exact lt_irrefl _ hQu
  have hdisj : Disjoint W (ℝ ∙ u) :=
    (isCompl_orthogonal hW).disjoint.mono_right (by simpa using hu)
  have hinf : W ⊓ (ℝ ∙ u) = ⊥ := disjoint_iff.mp hdisj
  have hrank : Module.finrank ℝ (W ⊔ (ℝ ∙ u) : Submodule ℝ M) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (ℝ ∙ u)
    rw [hinf, hW.finrank_eq, finrank_span_singleton hu0] at h
    simpa using h
  have hle := le_sigPos_of_posDef Q (posDef_sup_span hW hu hQu)
  rw [hrank, hsig.sigPos_eq] at hle
  omega

/-- **The engine.** On the orthogonal complement of a positive plane the form is
negative definite.

`nonpos_of_mem_orthogonal` gives nonpositivity; an isotropic vector there would
be orthogonal to `Wᗮ` by `polar_eq_zero_of_nonpos` and to `W` by construction,
hence to `M = W ⊕ Wᗮ`, hence in the radical, which the signature hypothesis
makes trivial. -/
theorem neg_of_mem_orthogonal (hsig : HasSignatureTwo Q) {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) {u : M} (hu : u ∈ orthogonal Q W) (hu0 : u ≠ 0) :
    Q u < 0 := by
  rcases lt_or_eq_of_le (nonpos_of_mem_orthogonal hsig hW hu) with h | h
  · exact h
  · exfalso
    have hQu : Q u = 0 := h
    have hperp : ∀ y ∈ orthogonal Q W, polar (⇑Q) u y = 0 := fun y hy =>
      polar_eq_zero_of_nonpos (fun z hz => nonpos_of_mem_orthogonal hsig hW hz) hu hQu hy
    have hW' : ∀ w ∈ W, polar (⇑Q) u w = 0 := fun w hw =>
      (polar_comm (⇑Q) u w).trans (mem_orthogonal_iff.mp hu w hw)
    have htop : ∀ z : M, polar (⇑Q) u z = 0 := by
      intro z
      have hz : z ∈ W ⊔ orthogonal Q W := by
        rw [(isCompl_orthogonal hW).sup_eq_top]
        trivial
      rw [Submodule.mem_sup] at hz
      obtain ⟨w, hw, v, hv, rfl⟩ := hz
      rw [polar_add_right, hW' w hw, hperp v hv, add_zero]
    have hrad : u ∈ Q.radical := by
      refine ⟨hQu, ?_⟩
      ext z
      simpa using htop z
    rw [(nondegenerate_iff_radical_eq_bot.mp (nondegenerate hsig))] at hrad
    exact hu0 hrad

/-- `negDef_orthogonal` in the shape `sigNeg` consumes: `-Q` is positive
definite on `Wᗮ`. -/
theorem negDef_orthogonal (hsig : HasSignatureTwo Q) {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) : ((-Q).restrict (orthogonal Q W)).PosDef := by
  rintro ⟨u, hu⟩ hu0
  have : u ≠ 0 := by simpa using hu0
  simpa [restrict_apply] using neg_of_mem_orthogonal hsig hW hu this

/-- The complement of a positive plane is a hyperplane pair short of `M`. Only
the splitting is used, so the signature hypothesis is not needed. -/
theorem finrank_orthogonal {W : Submodule ℝ M} (hW : IsPositivePlane Q W) :
    Module.finrank ℝ (orthogonal Q W) + 2 = Module.finrank ℝ M := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_orthogonal hW)
  rw [hW.finrank_eq] at h
  omega


/-- **The positive-plane locus of a signature `(2, n - 2)` space is nonempty.**

`sigPos Q = 2` is exactly the assertion that a two-dimensional positive definite
subspace is available, so the hypothesis carries its own witness and nothing
below is vacuous. -/
theorem exists_isPositivePlane (hsig : HasSignatureTwo Q) :
    ∃ W : Submodule ℝ M, IsPositivePlane Q W := by
  obtain ⟨W, hrank, hposDef⟩ := exists_finrank_eq_sigPos_and_posDef Q
  exact ⟨W, ⟨hrank.trans hsig.sigPos_eq, hposDef⟩⟩

theorem positivePlanes_nonempty (hsig : HasSignatureTwo Q) : (positivePlanes Q).Nonempty :=
  exists_isPositivePlane hsig

end FiniteDimensional

section Witness

/-- The diagonal form `x₀² + x₁² - x₂²` on `ℝ³`. It is the smallest quadratic
space satisfying `HasSignatureTwo`, and it is here so that the hypothesis is
known to be inhabited rather than merely stated. -/
noncomputable def stdForm : QuadraticForm ℝ (Fin 3 → ℝ) :=
  weightedSumSquares ℝ ![(1 : ℝ), 1, -1]

theorem stdForm_hasSignatureTwo : HasSignatureTwo stdForm := by
  have hpos : {i : Fin 3 | 0 < ![(1 : ℝ), 1, -1] i} = ({0, 1} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num
  have hneg : {i : Fin 3 | ![(1 : ℝ), 1, -1] i < 0} = ({2} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [Fin.ext_iff]
  constructor
  · rw [stdForm, QuadraticForm.sigPos_weightedSumSquares, hpos]
    exact Set.ncard_pair (by decide)
  · rw [stdForm, QuadraticForm.sigNeg_weightedSumSquares, hneg, Set.ncard_singleton]
    simp

end Witness

section SignatureOne

variable [FiniteDimensional ℝ M]

omit [FiniteDimensional ℝ M] in
private theorem apply_smul_add_smul (Q : QuadraticForm ℝ M) (u v : M) (a b : ℝ) :
    Q (a • u + b • v) = a ^ 2 * Q u + b ^ 2 * Q v + a * b * polar (⇑Q) u v := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_right]
  ring

/-- **`Q` is nonpositive on the orthogonal complement of a positive vector when
`sigPos Q = 1`.**

The signature-one companion of `nonpos_of_mem_orthogonal`, which is the same
statement one dimension up. A vector of positive square orthogonal to `u` would
span, with `u`, a two-dimensional positive definite subspace, and `sigPos Q = 1`
forbids that.

With `Q` the intersection form of `NS(X) ⊗ ℝ` this **is** the Hodge index
theorem in the form §6 consumes: `c · ω = 0` and `ω² > 0` give `c² ≤ 0`. Stated
here rather than in the Mukai files because it is a fact about a real quadratic
space and mentions no geometry.

Note the orthogonality hypothesis is on `polar`, which for a form built by
`toQuadraticMap` is **twice** the underlying pairing; over `ℝ` that is
immaterial for vanishing, but see `Mukai/RealForm.lean` on why the factor is
not immaterial elsewhere. -/
theorem nonpos_of_sigPos_eq_one (Q : QuadraticForm ℝ M) (hsig : sigPos Q = 1)
    {u v : M} (hu : 0 < Q u) (horth : polar (⇑Q) u v = 0) : Q v ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hv0 : v ≠ 0 := by rintro rfl; simp at hcon
  have hinf : (ℝ ∙ u) ⊓ (ℝ ∙ v) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hx2
    have h1 : polar (⇑Q) u (b • v) = 0 := by
      rw [polar_smul_right, horth, smul_zero]
    have h2 : polar (⇑Q) u (a • u) = 0 := by rw [← hb]; exact h1
    rw [polar_smul_right, polar_self] at h2
    have h3 : a * (2 * Q u) = 0 := by simpa [smul_eq_mul] using h2
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h (by positivity)
    simp [ha]
  have hpos : (Q.restrict ((ℝ ∙ u) ⊔ (ℝ ∙ v))).PosDef := by
    rintro ⟨x, hx⟩ hx0
    rw [Submodule.mem_sup] at hx
    obtain ⟨w, hw, z, hz, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [restrict_apply, apply_smul_add_smul Q u v a b, horth]
    have hne : ¬(a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at hx0
    have h1 : 0 ≤ a ^ 2 * Q u := by positivity
    have h2 : 0 ≤ b ^ 2 * Q v := by positivity
    rcases not_and_or.mp hne with h | h
    · have : 0 < a ^ 2 * Q u := by positivity
      linarith
    · have : 0 < b ^ 2 * Q v := by positivity
      linarith
  have hrank : Module.finrank ℝ ((ℝ ∙ u) ⊔ (ℝ ∙ v) : Submodule ℝ M) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ u) (ℝ ∙ v)
    rw [hinf, finrank_span_singleton hu0, finrank_span_singleton hv0] at h
    simpa using h
  have hle := le_sigPos_of_posDef Q hpos
  rw [hrank, hsig] at hle
  omega

end SignatureOne

end PeriodDomain
