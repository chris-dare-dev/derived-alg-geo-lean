/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositivePlane
import DerivedAlgGeo.LinearAlgebra.Complex.Coordinates
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Normalizing a charge against a quadratic form

Let `Q` be a quadratic form on a finite-dimensional real vector space `V`, and let
`Z : V →ₗ[ℝ] ℂ` be a charge whose kernel `K` is negative definite for `Q`. Then
`V = K ⊕ Kᗮ`, where `Kᗮ` is the orthogonal complement of `K` for the polar form of
`Q`, and `kerProj Q Z` is the projection onto `K` along `Kᗮ`. Write `‖k‖² = -Q k` for
the norm that `-Q` puts on `K`. The pair `(Q, Z)` is **normalized** when

```
Q v = ‖Z v‖ ^ 2 - ‖kerProj Q Z v‖²   for every v ∈ V,
```

which is equation (2) of Bayer, *A short proof of the deformation property of
Bridgeland stability conditions*, arXiv:1606.02169. Equivalently, `Z` restricts to an
isometry from `(Kᗮ, Q)` to `(ℂ, ‖·‖²)`.

Normalization makes the comparison of a deformed charge `W = Z + u ∘ kerProj Q Z`
with `Z` explicit on the cone `0 ≤ Q`. On a class with `0 ≤ Q v`, the identity gives
`‖kerProj Q Z v‖ ≤ ‖Z v‖`, hence `‖W v - Z v‖ ≤ ‖u‖ * ‖Z v‖`. This is the computation
in the proof of Bayer's Lemma 5.7.

## Main definitions

* `QuadraticMap.kerProj` — the `Q`-orthogonal projection onto the kernel of a linear
  map.
* `QuadraticMap.IsNormalized` — `Q` is negative definite on `ker Z`, and `Z` is an
  isometry on the orthogonal complement of `ker Z`.

## Main results

* `QuadraticMap.apply_eq_apply_kerProj_add` — `Q v` splits along `ker Z ⊕ (ker Z)ᗮ`.
* `QuadraticMap.IsNormalized.apply_eq` and `QuadraticMap.IsNormalized.of_apply_eq` —
  normalized pairs are exactly those satisfying Bayer's equation (2).
* `QuadraticMap.isNormalized_actC_comp` — a `GL⁺(2, ℝ)`-translate is normalized once it
  is an isometry on `(ker Z)ᗮ`, because it has the same kernel (`ker_actC_comp`).
* `QuadraticMap.IsNormalized.normalized_charge_bound` — the estimate
  `‖(Z + u ∘ kerProj Q Z) v - Z v‖ ≤ c * ‖Z v‖` for `0 ≤ Q v`, whenever `c` bounds `u`
  against the norm that `-Q` puts on `ker Z`.
* `QuadraticMap.IsNormalized.apply_neg_of_apply_add_eq_zero` — for `c < 1` the kernel
  of `Z + u ∘ kerProj Q Z` is still negative definite for `Q`.
* `QuadraticMap.surjective_of_negDef` and
  `QuadraticMap.posDef_orthogonal_ker_of_hasSignatureTwo` — in signature
  `(2, dim V - 2)` (`PeriodDomain.HasSignatureTwo`), a charge with `Q`-negative definite
  kernel is surjective and `Q` is positive definite on `(ker Z)ᗮ`.
* `QuadraticMap.exists_isNormalized_actC` — Bayer's Lemma 4.2: when `Q` has signature
  `(2, dim V - 2)` and is negative definite on `ker Z`, some `T ∈ GL⁺(2, ℝ)` makes
  `(Q, T ∘ Z)` normalized.

## Implementation notes

`kerProj Q Z` is defined for every pair, with the value `0` when `ker Z` has no
`Q`-orthogonal complement. Every theorem about it carries the hypothesis it needs
(nondegeneracy of the polar form on `ker Z`, or negative definiteness), so no
statement depends on that junk value.

The bound on `u : ker Z →ₗ[ℝ] ℂ` is stated as `‖u k‖ ^ 2 ≤ c ^ 2 * -Q k`, which says
that the operator norm of `u` for the norm `√(-Q)` on `ker Z` is at most `c`. This
avoids putting a second normed-space structure on `ker Z`.

The group `GL⁺(2, ℝ)` acts on charges through `actC`, the action the stability
manifold's `GL⁺(2, ℝ)`-symmetry uses on central charges.

The reduction to signature `(2, dim V - 2)` (Bayer, §7) is not formalized here.
-/

open QuadraticMap LinearMap Module
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

namespace QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Projection

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- A quadratic form that is negative definite on a subspace has nondegenerate polar
form on it. -/
theorem polarBilin_restrict_nondegenerate_of_negDef {Q : QuadraticForm ℝ V}
    {K : Submodule ℝ V} (hK : ((-Q).restrict K).PosDef) :
    (LinearMap.BilinForm.restrict Q.polarBilin K).Nondegenerate := by
  have key : ∀ x : K, LinearMap.BilinForm.restrict Q.polarBilin K x x = 0 → x = 0 := by
    intro x hxx
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply, polar_self, two_nsmul] at hxx
    by_contra hx0
    have hneg : 0 < -Q x := by simpa using hK x hx0
    linarith
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

/-- `Q` is additive on a pair of polar-orthogonal vectors. -/
theorem apply_add_of_mem_orthogonal {Q : QuadraticForm ℝ V} {K : Submodule ℝ V} {k w : V}
    (hk : k ∈ K) (hw : w ∈ BilinForm.orthogonal Q.polarBilin K) :
    Q (k + w) = Q k + Q w := by
  have h0 : polar Q k w = 0 := by
    simpa [polarBilin_apply_apply] using hw k hk
  rw [polar] at h0
  linarith

open Classical in
/-- The projection onto `ker Z` along its orthogonal complement for the polar form
of `Q`. It is the zero map when `ker Z` and that orthogonal complement are not
complementary; the lemmas below assume the polar form is nondegenerate on `ker Z`,
which rules this out. -/
noncomputable def kerProj (Q : QuadraticForm ℝ V) (Z : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] LinearMap.ker Z :=
  if h : IsCompl (LinearMap.ker Z) (BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z)) then
    Submodule.projectionOnto _ _ h
  else 0

variable [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} {Z : V →ₗ[ℝ] W}

/-- The kernel of `Z` and its orthogonal complement are complementary when the polar
form is nondegenerate on the kernel. -/
theorem isCompl_ker_orthogonal
    (hZ : (LinearMap.BilinForm.restrict Q.polarBilin (LinearMap.ker Z)).Nondegenerate) :
    IsCompl (LinearMap.ker Z) (BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z)) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    PeriodDomain.polarBilin_isRefl hZ

/-- Under nondegeneracy, `kerProj` is the projection along the orthogonal
complement. -/
theorem kerProj_eq
    (hZ : (LinearMap.BilinForm.restrict Q.polarBilin (LinearMap.ker Z)).Nondegenerate) :
    kerProj Q Z = Submodule.projectionOnto _ _ (isCompl_ker_orthogonal hZ) := by
  simp [kerProj, isCompl_ker_orthogonal hZ]

/-- The projection fixes the kernel. -/
theorem kerProj_apply_of_mem
    (hZ : (LinearMap.BilinForm.restrict Q.polarBilin (LinearMap.ker Z)).Nondegenerate)
    {v : V} (hv : v ∈ LinearMap.ker Z) : (kerProj Q Z v : V) = v := by
  rw [kerProj_eq hZ, Submodule.projectionOnto_apply_of_mem_left _ hv]

/-- What the projection removes is orthogonal to the kernel. -/
theorem sub_kerProj_mem_orthogonal
    (hZ : (LinearMap.BilinForm.restrict Q.polarBilin (LinearMap.ker Z)).Nondegenerate)
    (v : V) : v - kerProj Q Z v ∈ BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z) := by
  rw [kerProj_eq hZ, Submodule.coe_projectionOnto_apply]
  exact Submodule.sub_projection_mem _ v

/-- **`Q` splits along `ker Z ⊕ (ker Z)ᗮ`.** -/
theorem apply_eq_apply_kerProj_add
    (hZ : (LinearMap.BilinForm.restrict Q.polarBilin (LinearMap.ker Z)).Nondegenerate)
    (v : V) : Q v = Q (kerProj Q Z v) + Q (v - kerProj Q Z v) := by
  conv_lhs => rw [← add_sub_cancel (kerProj Q Z v : V) v]
  exact apply_add_of_mem_orthogonal (kerProj Q Z v).2 (sub_kerProj_mem_orthogonal hZ v)

end Projection

section Normalized

/-- The pair `(Q, Z)` is **normalized**: `Q` is negative definite on `ker Z`, and `Z`
is an isometry from the orthogonal complement of `ker Z` with `Q` to `ℂ` with the
squared norm.

`IsNormalized.apply_eq` is the equivalent form `Q v = ‖Z v‖ ^ 2 + Q (kerProj Q Z v)`,
which is equation (2) of arXiv:1606.02169 since `-Q` is the squared norm on
`ker Z`. -/
structure IsNormalized (Q : QuadraticForm ℝ V) (Z : V →ₗ[ℝ] ℂ) : Prop where
  /-- `Q` is negative definite on the kernel of the charge. -/
  negDef_ker : ((-Q).restrict (LinearMap.ker Z)).PosDef
  /-- `Q` is the squared norm of the charge on the orthogonal complement of the
  kernel. -/
  apply_eq_of_mem_orthogonal :
    ∀ w ∈ BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z), Q w = ‖Z w‖ ^ 2

/-- A `GL⁺(2, ℝ)`-translate of a charge has the same kernel. -/
theorem ker_actC_comp (T : Matrix.GLPos (Fin 2) ℝ) (Z : V →ₗ[ℝ] ℂ) :
    LinearMap.ker (actC T ∘ₗ Z) = LinearMap.ker Z := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have := actC_mul T⁻¹ T (Z v)
  rwa [inv_mul_cancel, actC_one, h, map_zero] at this

/-- A `GL⁺(2, ℝ)`-translate `T ∘ Z` of a charge with `Q`-negative definite kernel is
normalized as soon as it is an isometry on the orthogonal complement of `ker Z`. The
translate has the same kernel (`ker_actC_comp`), so nothing else needs checking. -/
theorem isNormalized_actC_comp {Q : QuadraticForm ℝ V} {Z : V →ₗ[ℝ] ℂ}
    (hZ : ((-Q).restrict (LinearMap.ker Z)).PosDef) {T : Matrix.GLPos (Fin 2) ℝ}
    (hT : ∀ w ∈ BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z),
      Q w = ‖actC T (Z w)‖ ^ 2) :
    IsNormalized Q (actC T ∘ₗ Z) := by
  refine ⟨?_, ?_⟩
  · rw [ker_actC_comp]
    exact hZ
  · rw [ker_actC_comp]
    exact hT

variable [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} {Z : V →ₗ[ℝ] ℂ}

/-- **Bayer's equation (2)**: `Q v = ‖Z v‖ ^ 2 - ‖kerProj Q Z v‖²`, where the norm on
`ker Z` is `√(-Q)`. -/
theorem IsNormalized.apply_eq (h : IsNormalized Q Z) (v : V) :
    Q v = ‖Z v‖ ^ 2 + Q (kerProj Q Z v) := by
  have hZ := polarBilin_restrict_nondegenerate_of_negDef h.negDef_ker
  rw [apply_eq_apply_kerProj_add hZ v,
    h.apply_eq_of_mem_orthogonal _ (sub_kerProj_mem_orthogonal hZ v), map_sub,
    LinearMap.map_coe_ker, sub_zero, add_comm]

/-- Bayer's equation (2), together with negative definiteness on the kernel, makes the
pair normalized. -/
theorem IsNormalized.of_apply_eq (hneg : ((-Q).restrict (LinearMap.ker Z)).PosDef)
    (h : ∀ v, Q v = ‖Z v‖ ^ 2 + Q (kerProj Q Z v)) : IsNormalized Q Z := by
  refine ⟨hneg, fun w hw => ?_⟩
  have hZ := polarBilin_restrict_nondegenerate_of_negDef hneg
  have hp : (kerProj Q Z w : V) = 0 := by
    have hsub := sub_kerProj_mem_orthogonal hZ w
    have hmem : (kerProj Q Z w : V) ∈ BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z) := by
      simpa using Submodule.sub_mem _ hw hsub
    exact (Submodule.disjoint_def.mp (isCompl_ker_orthogonal hZ).disjoint) _
      (kerProj Q Z w).2 hmem
  rw [h w, hp, map_zero, add_zero]

/-- Equation (2), together with negative definiteness on the kernel, characterizes
normalized pairs. -/
theorem isNormalized_iff :
    IsNormalized Q Z ↔ ((-Q).restrict (LinearMap.ker Z)).PosDef ∧
      ∀ v, Q v = ‖Z v‖ ^ 2 + Q (kerProj Q Z v) :=
  ⟨fun h => ⟨h.negDef_ker, h.apply_eq⟩, fun ⟨hneg, h⟩ => .of_apply_eq hneg h⟩

/-- On the classes with `0 ≤ Q v`, the kernel component is bounded by the charge:
`‖kerProj Q Z v‖² ≤ ‖Z v‖ ^ 2`. -/
theorem IsNormalized.neg_apply_kerProj_le (h : IsNormalized Q Z) {v : V} (hv : 0 ≤ Q v) :
    -Q (kerProj Q Z v) ≤ ‖Z v‖ ^ 2 := by
  have := h.apply_eq v
  linarith

/-- The kernel component of a class with `0 ≤ Q v` moves the charge by at most
`c * ‖Z v‖` under any `u` that `c` bounds against the norm `√(-Q)` on `ker Z`. -/
theorem IsNormalized.norm_apply_kerProj_le (h : IsNormalized Q Z)
    {u : LinearMap.ker Z →ₗ[ℝ] ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hu : ∀ k, ‖u k‖ ^ 2 ≤ c ^ 2 * -Q k) {v : V} (hv : 0 ≤ Q v) :
    ‖u (kerProj Q Z v)‖ ≤ c * ‖Z v‖ := by
  have h1 := hu (kerProj Q Z v)
  have h2 := h.neg_apply_kerProj_le hv
  have hsq : ‖u (kerProj Q Z v)‖ ^ 2 ≤ (c * ‖Z v‖) ^ 2 := by
    rw [mul_pow]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg c))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
    two_ne_zero).mp hsq

/-- **The normalized charge bound.** For a normalized pair `(Q, Z)` and the
deformation `W = Z + u ∘ kerProj Q Z`, every class with `0 ≤ Q v` satisfies
`‖W v - Z v‖ ≤ c * ‖Z v‖`, where `c` bounds `u` against the norm `√(-Q)` on `ker Z`.

With `c = ‖u‖` this is the estimate in the proof of Lemma 5.7 of arXiv:1606.02169.
It needs no bound `‖u‖ < 1`; that bound enters only when the estimate is fed to the
deformation theorem. -/
theorem IsNormalized.normalized_charge_bound (h : IsNormalized Q Z)
    {u : LinearMap.ker Z →ₗ[ℝ] ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hu : ∀ k, ‖u k‖ ^ 2 ≤ c ^ 2 * -Q k) {v : V} (hv : 0 ≤ Q v) :
    ‖(Z + u ∘ₗ kerProj Q Z) v - Z v‖ ≤ c * ‖Z v‖ := by
  simpa using h.norm_apply_kerProj_le hc hu hv

/-- **The deformed kernel stays negative definite.** For a normalized pair `(Q, Z)`
and `u` of norm `c < 1` for `√(-Q)` on `ker Z`, every nonzero `v` in the kernel of
`W = Z + u ∘ kerProj Q Z` has `Q v < 0`.

Indeed `Z v = -u (p v)`, so `Q v = ‖u (p v)‖ ^ 2 + Q (p v) ≤ (1 - c ^ 2) Q (p v)`, and
`p v ≠ 0` because otherwise `v ∈ ker Z` and `v = p v = 0`. This is the argument for
`‖u‖ < 1` in the proof of Lemma 4.4(1) of arXiv:1606.02169, run in the other
direction. -/
theorem IsNormalized.apply_neg_of_apply_add_eq_zero (h : IsNormalized Q Z)
    {u : LinearMap.ker Z →ₗ[ℝ] ℂ} {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hu : ∀ k, ‖u k‖ ^ 2 ≤ c ^ 2 * -Q k) {v : V}
    (hv : (Z + u ∘ₗ kerProj Q Z) v = 0) (hv0 : v ≠ 0) : Q v < 0 := by
  have hZ := polarBilin_restrict_nondegenerate_of_negDef h.negDef_ker
  have hZv : Z v = -u (kerProj Q Z v) := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at hv
    exact eq_neg_of_add_eq_zero_left hv
  have hp : kerProj Q Z v ≠ 0 := by
    intro hp0
    have hker : v ∈ LinearMap.ker Z := by
      rw [LinearMap.mem_ker, hZv, hp0, map_zero, neg_zero]
    have := kerProj_apply_of_mem hZ hker
    rw [hp0, Submodule.coe_zero] at this
    exact hv0 this.symm
  have hneg : 0 < -Q (kerProj Q Z v) := by
    simpa using h.negDef_ker _ hp
  have hbound := hu (kerProj Q Z v)
  have heq := h.apply_eq v
  rw [hZv, norm_neg] at heq
  have hc2 : c ^ 2 < 1 := by nlinarith
  nlinarith

end Normalized

section Signature

variable [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} {Z : V →ₗ[ℝ] ℂ}

/-- If `Q` has negative index at most `dim V - 2`, a charge with `Q`-negative definite
kernel has kernel of codimension two. This holds in particular in signature
`(2, dim V - 2)`. -/
theorem finrank_ker_add_two_of_negDef (hneg : sigNeg Q + 2 ≤ finrank ℝ V)
    (hZ : ((-Q).restrict (LinearMap.ker Z)).PosDef) :
    finrank ℝ (LinearMap.ker Z) + 2 = finrank ℝ V := by
  have hle : finrank ℝ (LinearMap.ker Z) ≤ sigNeg Q := le_sigNeg_of_negDef Q hZ
  have hrange : finrank ℝ (LinearMap.range Z) ≤ 2 := by
    simpa [Complex.finrank_real_complex] using Submodule.finrank_le (LinearMap.range Z)
  have hrn := LinearMap.finrank_range_add_finrank_ker Z
  omega

/-- If `Q` has negative index at most `dim V - 2`, a charge with `Q`-negative definite
kernel is surjective. This holds in particular in signature `(2, dim V - 2)`. -/
theorem surjective_of_negDef (hneg : sigNeg Q + 2 ≤ finrank ℝ V)
    (hZ : ((-Q).restrict (LinearMap.ker Z)).PosDef) : Function.Surjective Z := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker Z
  have := finrank_ker_add_two_of_negDef hneg hZ
  rw [Complex.finrank_real_complex]
  omega

/-- With signature `(2, dim V - 2)`, a charge with `Q`-negative definite kernel has
`Q` positive definite on the orthogonal complement of its kernel. -/
theorem posDef_orthogonal_ker_of_hasSignatureTwo (hsig : PeriodDomain.HasSignatureTwo Q)
    (hZ : ((-Q).restrict (LinearMap.ker Z)).PosDef) :
    (Q.restrict (BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z))).PosDef := by
  rintro ⟨w, hw⟩ hw0
  have hw0' : w ≠ 0 := by simpa using hw0
  rw [restrict_apply]
  by_contra hQw
  push Not at hQw
  have hnd := polarBilin_restrict_nondegenerate_of_negDef hZ
  have hdisj := (isCompl_ker_orthogonal hnd).disjoint
  have hwK : w ∉ LinearMap.ker Z := fun hwK =>
    hw0' ((Submodule.disjoint_def.mp hdisj) w hwK hw)
  -- `ker Z ⊔ ℝ ∙ w` is a `Q`-nonpositive subspace of dimension `dim V - 1`.
  have hnonpos : ∀ x ∈ LinearMap.ker Z ⊔ (ℝ ∙ w), Q x ≤ 0 := by
    intro x hx
    obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [apply_add_of_mem_orthogonal hk (Submodule.smul_mem _ t hw), QuadraticMap.map_smul]
    have hk' : Q k ≤ 0 := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · have : 0 < -Q k := by simpa using hZ ⟨k, hk⟩ (by simpa using hk0)
        linarith
    have : t * t * Q w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg t) hQw
    simp only [smul_eq_mul]
    linarith
  have hinf : LinearMap.ker Z ⊓ (ℝ ∙ w) = ⊥ := by
    exact disjoint_iff.mp ((Submodule.disjoint_span_singleton' hw0').mpr hwK)
  have hrank : finrank ℝ (LinearMap.ker Z ⊔ (ℝ ∙ w) : Submodule ℝ V) =
      finrank ℝ (LinearMap.ker Z) + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker Z) (ℝ ∙ w)
    rw [hinf, finrank_span_singleton hw0'] at h
    simpa using h
  have hbound := QuadraticForm.sigPos_add_finrank_le_of_nonpos hnonpos
  rw [hrank, hsig.sigPos_eq] at hbound
  have := finrank_ker_add_two_of_negDef hsig.sigNeg_add_two.le hZ
  omega

/-- **Bayer's Lemma 4.2.** If `Q` has signature `(2, dim V - 2)` and is negative
definite on `ker Z`, then after replacing `Z` by a `GL⁺(2, ℝ)`-translate the pair
`(Q, Z)` is normalized: `Q v = ‖Z v‖ ^ 2 - ‖kerProj Q Z v‖²`.

The translate is the Cholesky factor of `Q` transported to `ℂ` through `Z`, which
is upper triangular with positive diagonal. -/
theorem exists_isNormalized_actC (hsig : PeriodDomain.HasSignatureTwo Q)
    (hZ : ((-Q).restrict (LinearMap.ker Z)).PosDef) :
    ∃ T : Matrix.GLPos (Fin 2) ℝ, IsNormalized Q (actC T ∘ₗ Z) := by
  have hnd := polarBilin_restrict_nondegenerate_of_negDef hZ
  have hdisj := (isCompl_ker_orthogonal hnd).disjoint
  have hpos := posDef_orthogonal_ker_of_hasSignatureTwo hsig hZ
  -- Lifts of `1` and `I` to the orthogonal complement of the kernel.
  obtain ⟨v₁, hv₁⟩ := surjective_of_negDef hsig.sigNeg_add_two.le hZ 1
  obtain ⟨v₂, hv₂⟩ := surjective_of_negDef hsig.sigNeg_add_two.le hZ Complex.I
  set e₁ := v₁ - kerProj Q Z v₁ with he₁_def
  set e₂ := v₂ - kerProj Q Z v₂ with he₂_def
  have he₁ := sub_kerProj_mem_orthogonal hnd v₁
  have he₂ := sub_kerProj_mem_orthogonal hnd v₂
  have hZe₁ : Z e₁ = 1 := by rw [he₁_def, map_sub, LinearMap.map_coe_ker, sub_zero, hv₁]
  have hZe₂ : Z e₂ = Complex.I := by
    rw [he₂_def, map_sub, LinearMap.map_coe_ker, sub_zero, hv₂]
  -- A vector of the complement is determined by its charge.
  have hdecomp : ∀ w ∈ BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z),
      w = (Z w).re • e₁ + (Z w).im • e₂ := by
    intro w hw
    have hmem : w - ((Z w).re • e₁ + (Z w).im • e₂) ∈
        BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z) :=
      Submodule.sub_mem _ hw
        (Submodule.add_mem _ (Submodule.smul_mem _ _ he₁) (Submodule.smul_mem _ _ he₂))
    have hker : w - ((Z w).re • e₁ + (Z w).im • e₂) ∈ LinearMap.ker Z := by
      rw [LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, hZe₁, hZe₂]
      apply Complex.ext <;> simp
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hdisj) _ hker hmem)
  -- The Gram matrix of `Q` in the basis `e₁, e₂`.
  set a := Q e₁ with ha_def
  set c := Q e₂ with hc_def
  set b := polar Q e₁ e₂ / 2 with hb_def
  have hQ : ∀ x y : ℝ, Q (x • e₁ + y • e₂) = a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
    intro x y
    have hpol : polar Q (x • e₁) (y • e₂) = x * y * (2 * b) := by
      rw [polar_smul_left, polar_smul_right, hb_def, smul_eq_mul, smul_eq_mul]
      ring
    have hadd : Q (x • e₁ + y • e₂) =
        Q (x • e₁) + Q (y • e₂) + polar Q (x • e₁) (y • e₂) := by
      rw [polar]
      ring
    rw [hadd, hpol, QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have ha : 0 < a := by
    have hne : e₁ ≠ 0 := fun h => by simp [h] at hZe₁
    simpa using hpos ⟨e₁, he₁⟩ (by simpa using hne)
  have hdisc : 0 < a * c - b ^ 2 := by
    have hx : (-b) • e₁ + a • e₂ ∈ BilinForm.orthogonal Q.polarBilin (LinearMap.ker Z) :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ he₁) (Submodule.smul_mem _ _ he₂)
    have hne : (-b) • e₁ + a • e₂ ≠ 0 := by
      intro h
      have := congrArg (fun v => (Z v).im) h
      simp [hZe₁, hZe₂] at this
      exact ha.ne' this
    have hQx : 0 < Q ((-b) • e₁ + a • e₂) := by
      simpa using hpos ⟨_, hx⟩ (by simpa using hne)
    rw [hQ] at hQx
    have : 0 < a * (a * c - b ^ 2) := by nlinarith
    exact pos_of_mul_pos_right this ha.le
  -- The upper triangular Cholesky factor.
  set d := Real.sqrt a with hd_def
  set f := Real.sqrt ((a * c - b ^ 2) / a) with hf_def
  have hd : 0 < d := Real.sqrt_pos.mpr ha
  have hf : 0 < f := Real.sqrt_pos.mpr (div_pos hdisc ha)
  have hd2 : d ^ 2 = a := Real.sq_sqrt ha.le
  have hf2 : f ^ 2 = (a * c - b ^ 2) / a := Real.sq_sqrt (div_pos hdisc ha).le
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![d, b / d; 0, f] with hM_def
  have hdet : 0 < M.det := by
    rw [hM_def, Matrix.det_fin_two_of]
    nlinarith
  let T : Matrix.GLPos (Fin 2) ℝ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet.ne', by
      rw [Matrix.mem_glpos]
      exact hdet⟩
  have hTre : ∀ z : ℂ, (actC T z).re = d * z.re + b / d * z.im := by
    intro z
    have h := congrFun (congrArg cplxCoord (actC_apply T z)) 0
    rw [LinearEquiv.apply_symm_apply, cplxCoord_apply, cplxCoord_apply] at h
    simpa [toMat, T, hM_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hTim : ∀ z : ℂ, (actC T z).im = f * z.im := by
    intro z
    have h := congrFun (congrArg cplxCoord (actC_apply T z)) 1
    rw [LinearEquiv.apply_symm_apply, cplxCoord_apply, cplxCoord_apply] at h
    simpa [toMat, T, hM_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hT : ∀ z : ℂ, ‖actC T z‖ ^ 2 = a * z.re ^ 2 + 2 * b * z.re * z.im + c * z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply, hTre, hTim]
    have hd0 : d ≠ 0 := hd.ne'
    have hexp : (d * z.re + b / d * z.im) * (d * z.re + b / d * z.im) +
        f * z.im * (f * z.im) =
        d ^ 2 * z.re ^ 2 + 2 * b * z.re * z.im + (b ^ 2 / d ^ 2 + f ^ 2) * z.im ^ 2 := by
      field_simp
      ring
    rw [hexp, hd2, hf2]
    field_simp
    ring
  refine ⟨T, isNormalized_actC_comp hZ fun w hw => ?_⟩
  rw [hT]
  conv_lhs => rw [hdecomp w hw]
  exact hQ _ _

end Signature

end QuadraticMap
