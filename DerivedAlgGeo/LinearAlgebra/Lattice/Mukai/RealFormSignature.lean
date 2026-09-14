/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.SignatureAdditive

/-!
# The signature of the real Mukai extension, from the signature of `V`

`PeriodDomain.HasSignatureTwo` has been a hypothesis everywhere in route (A).
For the Mukai extension it should be a consequence: `ℝ × V × ℝ` is a hyperbolic
plane orthogonal to `V`, the plane contributes `(1, 1)`, and the rest is `V`'s
own signature. With `V = NS(X) ⊗ ℝ` that reduces the hypothesis to the Hodge
index theorem, which is where it should rest.

This is step 2 of the additivity work; step 1 is
`QuadraticForm/SignatureAdditive.lean`.

## Shape of the argument

The two summands are the **ranges** of the obvious inclusions rather than
`Submodule.prod`s. That is not cosmetic: a range comes with
`LinearEquiv.ofInjective`, which is exactly the isometry needed to transport a
signature computation from `ℝ × ℝ` and from `V` into the summand, and it gives
the dimension count for free.

The plane's own signature is pinned by two explicit lines — `(1, -1)` is
positive, `(1, 1)` is negative — plus the counting identity, which forces
`sigPos = sigNeg = 1` and leaves no radical.

## Convention, restated because it is load-bearing

`realForm b` is **half** the self-pairing (`Mukai/RealForm.lean`), so on the
plane it is `(r, s) ↦ -r * s`, and on the middle summand it is `c ↦ b c c / 2`.
Halving does not move definite subspaces, which is `sigPos_smul_of_pos` below,
so `V`'s signature transports unchanged.
-/

open QuadraticMap

namespace QuadraticMap

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The restriction of a form to the range of an injective map is the form
pulled back along that map. This is what makes a range-shaped summand cheap to
compute with. -/
noncomputable def rangeIsometry {N : Type*} [AddCommGroup N] [Module ℝ N]
    (Q : QuadraticForm ℝ M) (f : N →ₗ[ℝ] M) (hf : Function.Injective f) :
    QuadraticMap.IsometryEquiv (Q.comp f) (Q.restrict (LinearMap.range f)) where
  toLinearEquiv := LinearEquiv.ofInjective f hf
  map_app' _ := rfl

variable [FiniteDimensional ℝ M]

/-- A positive scalar does not move the positive definite subspaces. -/
theorem sigPos_smul_of_pos {c : ℝ} (hc : 0 < c) (Q : QuadraticForm ℝ M) :
    sigPos (c • Q) = sigPos Q := by
  have key : ∀ (d : ℝ), 0 < d → ∀ Q' : QuadraticForm ℝ M, sigPos Q' ≤ sigPos (d • Q') := by
    intro d hd Q'
    obtain ⟨U, hU, hpos⟩ := exists_finrank_eq_sigPos_and_posDef Q'
    refine hU ▸ le_sigPos_of_posDef _ ?_
    intro u hu
    have := hpos u hu
    rw [restrict_apply] at this ⊢
    simpa using mul_pos hd this
  refine le_antisymm ?_ (key c hc Q)
  have h := key c⁻¹ (inv_pos.mpr hc) (c • Q)
  rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] at h

/-- The same for `sigNeg`, which is `sigPos` of the negative. -/
theorem sigNeg_smul_of_pos {c : ℝ} (hc : 0 < c) (Q : QuadraticForm ℝ M) :
    sigNeg (c • Q) = sigNeg Q := by
  rw [sigNeg, sigNeg, ← sigPos_smul_of_pos hc (-Q)]
  congr 1
  ext x
  simp

end QuadraticMap

namespace Mukai

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- The inclusion of the hyperbolic plane summand `{(r, 0, s)}`. -/
def hyperbolicIncl : (ℝ × ℝ) →ₗ[ℝ] RealExtension V where
  toFun p := (p.1, 0, p.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The inclusion of the middle summand `{(0, c, 0)}`. -/
def middleIncl : V →ₗ[ℝ] RealExtension V where
  toFun c := (0, c, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem hyperbolicIncl_injective : Function.Injective (hyperbolicIncl V) := by
  intro p q h
  have h1 : p.1 = q.1 := congrArg (fun v : RealExtension V => v.1) h
  have h2 : p.2 = q.2 := congrArg (fun v : RealExtension V => v.2.2) h
  exact Prod.ext h1 h2

theorem middleIncl_injective : Function.Injective (middleIncl V) := by
  intro c d h
  exact congrArg (fun v : RealExtension V => v.2.1) h

/-- The hyperbolic plane summand. -/
def hyperbolic : Submodule ℝ (RealExtension V) := LinearMap.range (hyperbolicIncl V)

/-- The middle summand. -/
def middle : Submodule ℝ (RealExtension V) := LinearMap.range (middleIncl V)

variable {V}

theorem mem_hyperbolic_iff {v : RealExtension V} : v ∈ hyperbolic V ↔ v.2.1 = 0 := by
  constructor
  · rintro ⟨p, rfl⟩; rfl
  · intro h
    exact ⟨(v.1, v.2.2), Prod.ext rfl (Prod.ext h.symm rfl)⟩

theorem mem_middle_iff {v : RealExtension V} : v ∈ middle V ↔ v.1 = 0 ∧ v.2.2 = 0 := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨v.2.1, Prod.ext h1.symm (Prod.ext rfl h2.symm)⟩

theorem isCompl_hyperbolic_middle : IsCompl (hyperbolic V) (middle V) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    rw [mem_hyperbolic_iff] at hv
    rw [mem_middle_iff] at hv'
    exact Prod.ext hv'.1 (Prod.ext hv hv'.2)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨(v.1, 0, v.2.2), mem_hyperbolic_iff.mpr rfl,
      (0, v.2.1, 0), mem_middle_iff.mpr ⟨rfl, rfl⟩, ?_⟩
    simp

variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

theorem orthogonal_hyperbolic_middle (hb : ∀ x y : V, b x y = b y x) :
    ∀ w ∈ hyperbolic V, ∀ w' ∈ middle V, polar (⇑(realForm b)) w w' = 0 := by
  intro w hw w' hw'
  rw [mem_hyperbolic_iff] at hw
  rw [mem_middle_iff] at hw'
  rw [polar_realForm b hb, realPairing, pairing, hw, hw'.1, hw'.2]
  simp

/-- The form the plane carries: `(r, s) ↦ -r * s`. -/
theorem comp_hyperbolicIncl_apply (p : ℝ × ℝ) :
    ((realForm b).comp (hyperbolicIncl V)) p = -(p.1 * p.2) := by
  show realForm b (p.1, 0, p.2) = -(p.1 * p.2)
  rw [realForm_mk]
  simp
  ring

/-- The form the middle summand carries: `c ↦ b c c / 2`. -/
theorem comp_middleIncl_apply (c : V) :
    ((realForm b).comp (middleIncl V)) c = b c c / 2 := by
  show realForm b (0, c, 0) = b c c / 2
  rw [realForm_mk]
  ring



section Signature

/-- The form the hyperbolic plane carries, read on `ℝ × ℝ`. -/
private noncomputable abbrev hypQ : QuadraticForm ℝ (ℝ × ℝ) :=
  (realForm b).comp (hyperbolicIncl V)

private theorem one_le_sigPos_hyp : 1 ≤ sigPos (hypQ b) := by
  have hne : ((1 : ℝ), (-1 : ℝ)) ≠ 0 := by simp
  have hrank : Module.finrank ℝ (Submodule.span ℝ {((1 : ℝ), (-1 : ℝ))}) = 1 :=
    finrank_span_singleton hne
  refine hrank ▸ le_sigPos_of_posDef _ ?_
  rintro ⟨u, hu⟩ hu0
  rw [Submodule.mem_span_singleton] at hu
  obtain ⟨a, rfl⟩ := hu
  have ha : a ≠ 0 := by
    intro h
    exact hu0 (by simp [h])
  rw [restrict_apply, comp_hyperbolicIncl_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, mul_neg]
  nlinarith [mul_self_pos.mpr ha]

private theorem one_le_sigNeg_hyp : 1 ≤ sigNeg (hypQ b) := by
  have hne : ((1 : ℝ), (1 : ℝ)) ≠ 0 := by simp
  have hrank : Module.finrank ℝ (Submodule.span ℝ {((1 : ℝ), (1 : ℝ))}) = 1 :=
    finrank_span_singleton hne
  refine hrank ▸ le_sigNeg_of_negDef _ ?_
  rintro ⟨u, hu⟩ hu0
  rw [Submodule.mem_span_singleton] at hu
  obtain ⟨a, rfl⟩ := hu
  have ha : a ≠ 0 := by
    intro h
    exact hu0 (by simp [h])
  rw [restrict_apply, QuadraticMap.neg_apply, comp_hyperbolicIncl_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one]
  nlinarith [mul_self_pos.mpr ha]

/-- **The hyperbolic plane has signature `(1, 1)`**: two explicit lines and the
counting identity leave no other possibility, and no radical. -/
private theorem sigPos_sigNeg_hyp : sigPos (hypQ b) = 1 ∧ sigNeg (hypQ b) = 1 := by
  have h1 := one_le_sigPos_hyp b
  have h2 := one_le_sigNeg_hyp b
  have htot := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := hypQ b)
  rw [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp] at htot
  omega

private theorem equivalent_hyp :
    QuadraticMap.Equivalent (hypQ b) ((realForm b).restrict (hyperbolic V)) :=
  ⟨QuadraticMap.rangeIsometry _ _ (hyperbolicIncl_injective V)⟩

private theorem comp_middleIncl_eq :
    (realForm b).comp (middleIncl V) = (1 / 2 : ℝ) • (LinearMap.BilinMap.toQuadraticMap b) := by
  ext c
  rw [comp_middleIncl_apply]
  simp [LinearMap.BilinMap.toQuadraticMap_apply]
  ring

private theorem equivalent_middle :
    QuadraticMap.Equivalent ((1 / 2 : ℝ) • (LinearMap.BilinMap.toQuadraticMap b))
      ((realForm b).restrict (middle V)) :=
  ⟨(comp_middleIncl_eq b) ▸ QuadraticMap.rangeIsometry _ _ (middleIncl_injective V)⟩

private theorem finrank_hyperbolic : Module.finrank ℝ (hyperbolic V) = 2 := by
  rw [hyperbolic, ← (LinearEquiv.ofInjective _ (hyperbolicIncl_injective V)).finrank_eq]
  simp

private theorem finrank_middle : Module.finrank ℝ (middle V) = Module.finrank ℝ V := by
  rw [middle, ← (LinearEquiv.ofInjective _ (middleIncl_injective V)).finrank_eq]

/-- **The signature of the real Mukai extension, from the signature of `V`.**

With `V = NS(X) ⊗ ℝ` the hypotheses are the Hodge index theorem, so the
signature condition every period-domain result carries stops being an assumption
about the Mukai lattice. -/
theorem hasSignatureTwo_realForm [FiniteDimensional ℝ V] (hb : ∀ x y : V, b x y = b y x)
    (hpos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hneg : sigNeg (LinearMap.BilinMap.toQuadraticMap b) + 1 = Module.finrank ℝ V) :
    PeriodDomain.HasSignatureTwo (realForm b) := by
  obtain ⟨hhp, hhn⟩ := sigPos_sigNeg_hyp b
  -- the two summands, with their signatures
  have hP₁ : sigPos ((realForm b).restrict (hyperbolic V)) = 1 := by
    rw [← (equivalent_hyp b).sigPos_eq, hhp]
  have hN₁ : sigNeg ((realForm b).restrict (hyperbolic V)) = 1 := by
    rw [← (equivalent_hyp b).sigNeg_eq, hhn]
  have hP₂ : sigPos ((realForm b).restrict (middle V)) = 1 := by
    rw [← (equivalent_middle b).sigPos_eq,
      QuadraticMap.sigPos_smul_of_pos (by norm_num) _, hpos]
  have hN₂ : sigNeg ((realForm b).restrict (middle V)) + 1 = Module.finrank ℝ V := by
    rw [← (equivalent_middle b).sigNeg_eq,
      QuadraticMap.sigNeg_smul_of_pos (by norm_num) _, hneg]
  -- both restrictions are nondegenerate, by counting
  have hnd₁ : ((realForm b).restrict (hyperbolic V)).Nondegenerate := by
    rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero]
    have h := QuadraticForm.sigPos_add_sigNeg_add_radical
      (Q := (realForm b).restrict (hyperbolic V))
    rw [hP₁, hN₁, finrank_hyperbolic] at h
    omega
  have hnd₂ : ((realForm b).restrict (middle V)).Nondegenerate := by
    rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero]
    have h := QuadraticForm.sigPos_add_sigNeg_add_radical
      (Q := (realForm b).restrict (middle V))
    rw [hP₂, finrank_middle] at h
    omega
  obtain ⟨hsumP, hsumN⟩ := QuadraticMap.sigPos_eq_add isCompl_hyperbolic_middle
    (orthogonal_hyperbolic_middle b hb) hnd₁ hnd₂
  have hdim : Module.finrank ℝ (RealExtension V) = Module.finrank ℝ V + 2 := by
    simp [RealExtension, Module.finrank_prod]
    ring
  constructor
  · rw [hsumP, hP₁, hP₂]
  · rw [hsumN, hN₁, hdim]
    omega

end Signature

end Mukai
