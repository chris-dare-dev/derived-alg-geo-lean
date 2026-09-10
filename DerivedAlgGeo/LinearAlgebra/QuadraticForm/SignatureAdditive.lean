/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PeriodDomain

/-!
# The signature is additive over an orthogonal decomposition

Mathlib at the pin has Sylvester's law of inertia — `sigPos`, `sigNeg`, and
`sigPos_add_sigNeg_add_radical` — but not the additivity of the signature over an
orthogonal direct sum. This file supplies it for a nondegenerate orthogonal
decomposition of a finite-dimensional real quadratic space.

It is what turns a signature hypothesis on a summand into one on the whole
space: the Mukai extension is a hyperbolic plane orthogonal to `V`, so the
`(2, n - 2)` signature the period domain assumes should follow from the
`(1, n - 1)` signature of `V` rather than being asserted.

## The proof, which is a squeeze rather than a construction

Only the **easy** direction is proved directly, twice:

* a positive definite subspace of `W` and one of `W'` span a positive definite
  subspace of `M`, because the cross terms vanish — so
  `sigPos (Q|W) + sigPos (Q|W') ≤ sigPos Q`;
* the same for `-Q`, which is `sigNeg`.

Then `sigPos_add_sigNeg_add_radical` on all three spaces, with the radicals
trivial, gives

```
finrank M = sigPos Q + sigNeg Q ≥ (sigPos₁ + sigPos₂) + (sigNeg₁ + sigNeg₂)
          = finrank W + finrank W' = finrank M,
```

so both inequalities are equalities. The hard direction — bounding an arbitrary
positive definite subspace of `M` — is never needed.

## Scope

The restrictions are assumed nondegenerate, which is the case the application
has and which keeps the counting to two terms. The degenerate version follows the
same squeeze with the radical as a third term and a third inequality
`finrank (radical Q|W) + finrank (radical Q|W') ≤ finrank (radical Q)`; it is not
proved here because nothing needs it.
-/

open QuadraticMap

namespace QuadraticMap

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
variable {Q : QuadraticForm ℝ M} {W W' : Submodule ℝ M}

section Sup

variable {V₁ : Submodule ℝ W} {V₂ : Submodule ℝ W'}

omit [FiniteDimensional ℝ M] in
/-- The polar form of a restriction is the restriction of the polar form. -/
private theorem polar_restrict (V : Submodule ℝ M) (u v : V) :
    polar (⇑(Q.restrict V)) u v = polar (⇑Q) (u : M) (v : M) := rfl

omit [FiniteDimensional ℝ M] in
/-- The image in `M` of a subspace of `W` keeps its dimension. -/
private theorem finrank_map_subtype (V : Submodule ℝ W) :
    Module.finrank ℝ (V.map W.subtype) = Module.finrank ℝ V :=
  ((Submodule.equivMapOfInjective W.subtype Subtype.val_injective V).finrank_eq).symm

/-- Two subspaces of complementary summands span the sum of their dimensions. -/
private theorem finrank_sup_map (hcompl : IsCompl W W') (V₁ : Submodule ℝ W)
    (V₂ : Submodule ℝ W') :
    Module.finrank ℝ (V₁.map W.subtype ⊔ V₂.map W'.subtype : Submodule ℝ M)
      = Module.finrank ℝ V₁ + Module.finrank ℝ V₂ := by
  have hinf : (V₁.map W.subtype) ⊓ (V₂.map W'.subtype) = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine le_trans (inf_le_inf (Submodule.map_subtype_le _ _) (Submodule.map_subtype_le _ _)) ?_
    exact le_of_eq hcompl.disjoint.eq_bot
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (V₁.map W.subtype) (V₂.map W'.subtype)
  rw [hinf, finrank_map_subtype, finrank_map_subtype] at h
  simpa using h

omit [FiniteDimensional ℝ M] in
/-- **Positive definiteness adds across an orthogonal decomposition.** The cross
term of the two components vanishes, so the value on a sum is the sum of the
values. -/
private theorem posDef_sup (horth : ∀ w ∈ W, ∀ w' ∈ W', polar (⇑Q) w w' = 0)
    (h₁ : ((Q.restrict W).restrict V₁).PosDef)
    (h₂ : ((Q.restrict W').restrict V₂).PosDef) :
    (Q.restrict (V₁.map W.subtype ⊔ V₂.map W'.subtype)).PosDef := by
  rintro ⟨u, hu⟩ hu0
  rw [Submodule.mem_sup] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  obtain ⟨v₁, hv₁, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨v₂, hv₂, rfl⟩ := Submodule.mem_map.mp hb
  simp only [Submodule.subtype_apply] at *
  have hsplit : Q ((v₁ : M) + (v₂ : M)) = Q (v₁ : M) + Q (v₂ : M) := by
    have hp : polar (⇑Q) (v₁ : M) (v₂ : M) = 0 := horth _ v₁.2 _ v₂.2
    simp only [polar] at hp
    linarith
  have hval₁ : ∀ h : v₁ ∈ V₁, ((Q.restrict W).restrict V₁) ⟨v₁, h⟩ = Q (v₁ : M) := fun _ => rfl
  have hval₂ : ∀ h : v₂ ∈ V₂, ((Q.restrict W').restrict V₂) ⟨v₂, h⟩ = Q (v₂ : M) := fun _ => rfl
  have hnonneg₁ : 0 ≤ Q (v₁ : M) := by
    rcases eq_or_ne v₁ 0 with rfl | hne
    · simp
    · exact (hval₁ hv₁ ▸ h₁ ⟨v₁, hv₁⟩ (by simpa using hne)).le
  have hnonneg₂ : 0 ≤ Q (v₂ : M) := by
    rcases eq_or_ne v₂ 0 with rfl | hne
    · simp
    · exact (hval₂ hv₂ ▸ h₂ ⟨v₂, hv₂⟩ (by simpa using hne)).le
  have hne : v₁ ≠ 0 ∨ v₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu0
    simp [hcon.1, hcon.2]
  rw [restrict_apply, hsplit]
  rcases hne with hne | hne
  · have hpos := hval₁ hv₁ ▸ h₁ ⟨v₁, hv₁⟩ (by simpa using hne)
    linarith
  · have hpos := hval₂ hv₂ ▸ h₂ ⟨v₂, hv₂⟩ (by simpa using hne)
    linarith

end Sup

/-- **The easy half of additivity for `sigPos`.** -/
theorem sigPos_add_le (hcompl : IsCompl W W')
    (horth : ∀ w ∈ W, ∀ w' ∈ W', polar (⇑Q) w w' = 0) :
    sigPos (Q.restrict W) + sigPos (Q.restrict W') ≤ sigPos Q := by
  obtain ⟨V₁, hr₁, hp₁⟩ := exists_finrank_eq_sigPos_and_posDef (Q.restrict W)
  obtain ⟨V₂, hr₂, hp₂⟩ := exists_finrank_eq_sigPos_and_posDef (Q.restrict W')
  have hle := le_sigPos_of_posDef Q (posDef_sup horth hp₁ hp₂)
  rwa [finrank_sup_map hcompl V₁ V₂, hr₁, hr₂] at hle

/-- **The easy half of additivity for `sigNeg`**, which is `sigPos` of `-Q`. -/
theorem sigNeg_add_le (hcompl : IsCompl W W')
    (horth : ∀ w ∈ W, ∀ w' ∈ W', polar (⇑Q) w w' = 0) :
    sigNeg (Q.restrict W) + sigNeg (Q.restrict W') ≤ sigNeg Q := by
  have horth' : ∀ w ∈ W, ∀ w' ∈ W', polar (⇑(-Q)) w w' = 0 := by
    intro w hw w' hw'
    have := horth w hw w' hw'
    simp only [polar] at this ⊢
    simp only [neg_apply]
    linarith
  exact sigPos_add_le (Q := -Q) hcompl horth'

omit [FiniteDimensional ℝ M] in
/-- An orthogonal decomposition into nondegenerate pieces is nondegenerate. -/
theorem nondegenerate_of_isCompl (hcompl : IsCompl W W')
    (horth : ∀ w ∈ W, ∀ w' ∈ W', polar (⇑Q) w w' = 0)
    (h₁ : (Q.restrict W).Nondegenerate) (h₂ : (Q.restrict W').Nondegenerate) :
    Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (by
    rw [hcompl.sup_eq_top]; trivial : x ∈ W ⊔ W')
  have hxpolar : ∀ z : M, polar (⇑Q) (a + b) z = 0 := by
    intro z
    have := congr_arg (fun f => f z) hx.2
    simpa using this
  -- each component is orthogonal to its own summand, hence in that radical
  have hpolar_a : ∀ w ∈ W, polar (⇑Q) a w = 0 := by
    intro w hw
    have h1 := hxpolar w
    rw [polar_add_left] at h1
    have h2 : polar (⇑Q) b w = 0 := by
      rw [polar_comm]
      exact horth w hw b hb
    linarith
  have hpolar_b : ∀ w' ∈ W', polar (⇑Q) b w' = 0 := by
    intro w' hw'
    have h1 := hxpolar w'
    rw [polar_add_left] at h1
    have h2 : polar (⇑Q) a w' = 0 := horth a ha w' hw'
    linarith
  have hQa : Q a = 0 := by
    have h := hpolar_a a ha
    rw [polar_self, two_nsmul] at h
    linarith
  have hQb : Q b = 0 := by
    have h := hpolar_b b hb
    rw [polar_self, two_nsmul] at h
    linarith
  have hazero : a = 0 := by
    have hrad : (⟨a, ha⟩ : W) ∈ (Q.restrict W).radical := by
      refine ⟨hQa, ?_⟩
      ext ⟨z, hz⟩
      simpa [polar_restrict] using hpolar_a z hz
    rw [h₁.radical_eq_bot, Submodule.mem_bot] at hrad
    simpa using congr_arg Subtype.val hrad
  have hbzero : b = 0 := by
    have hrad : (⟨b, hb⟩ : W') ∈ (Q.restrict W').radical := by
      refine ⟨hQb, ?_⟩
      ext ⟨z, hz⟩
      simpa [polar_restrict] using hpolar_b z hz
    rw [h₂.radical_eq_bot, Submodule.mem_bot] at hrad
    simpa using congr_arg Subtype.val hrad
  rw [hazero, hbzero, add_zero]

/-- **The signature is additive over a nondegenerate orthogonal decomposition.** -/
theorem sigPos_eq_add (hcompl : IsCompl W W')
    (horth : ∀ w ∈ W, ∀ w' ∈ W', polar (⇑Q) w w' = 0)
    (h₁ : (Q.restrict W).Nondegenerate) (h₂ : (Q.restrict W').Nondegenerate) :
    sigPos Q = sigPos (Q.restrict W) + sigPos (Q.restrict W') ∧
      sigNeg Q = sigNeg (Q.restrict W) + sigNeg (Q.restrict W') := by
  have hP := sigPos_add_le hcompl horth
  have hN := sigNeg_add_le hcompl horth
  have hQtot := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have h1tot := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q.restrict W)
  have h2tot := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q.restrict W')
  have hQrad : Module.finrank ℝ (Q.radical) = 0 := by
    rw [(nondegenerate_of_isCompl hcompl horth h₁ h₂).radical_eq_bot]
    simp
  have h1rad : Module.finrank ℝ ((Q.restrict W).radical) = 0 := by
    rw [h₁.radical_eq_bot]; simp
  have h2rad : Module.finrank ℝ ((Q.restrict W').radical) = 0 := by
    rw [h₂.radical_eq_bot]; simp
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hQrad] at hQtot
  rw [h1rad] at h1tot
  rw [h2rad] at h2tot
  omega

/-! ### Definite forms and their indices of inertia

Sylvester's law pins the two indices for a definite form.  Mathlib has the
defining maximality property of `sigPos` and the counting identity, but not the
two corollaries every consumer wants, so they are proved here beside the
additivity they are used with. -/

section Definite

variable {N : Type*} [AddCommGroup N] [Module ℝ N]

/-- An anisotropic form is nondegenerate: the radical sits inside the zero
locus. -/
theorem nondegenerate_of_anisotropic {Q : QuadraticForm ℝ N} (h : Q.Anisotropic) :
    Q.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  exact h x hx.1

variable [FiniteDimensional ℝ N]

/-- **A positive definite form has `sigPos = dim` and `sigNeg = 0`.** -/
theorem sigPos_eq_finrank_of_posDef {Q : QuadraticForm ℝ N} (h : Q.PosDef) :
    sigPos Q = Module.finrank ℝ N ∧ sigNeg Q = 0 ∧ Q.Nondegenerate := by
  have hnd : Q.Nondegenerate := nondegenerate_of_anisotropic h.anisotropic
  have htop : (Q.restrict (⊤ : Submodule ℝ N)).PosDef := by
    intro x hx
    have hx' : (x : N) ≠ 0 := fun hc => hx (Subtype.ext hc)
    exact h _ hx'
  have hle : Module.finrank ℝ (⊤ : Submodule ℝ N) ≤ sigPos Q :=
    le_sigPos_of_posDef Q htop
  rw [finrank_top] at hle
  have hpos : sigPos Q = Module.finrank ℝ N :=
    le_antisymm (sigPos_le_finrank Q) hle
  refine ⟨hpos, ?_, hnd⟩
  have htot := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have hrad : Module.finrank ℝ Q.radical = 0 := by rw [hnd.radical_eq_bot]; simp
  omega

/-- **A negative definite form has `sigNeg = dim` and `sigPos = 0`.**

"Negative definite" is spelled the way `sigNeg` is defined, as positive
definiteness of `-Q`. -/
theorem sigNeg_eq_finrank_of_negDef {Q : QuadraticForm ℝ N} (h : (-Q).PosDef) :
    sigNeg Q = Module.finrank ℝ N ∧ sigPos Q = 0 ∧ Q.Nondegenerate := by
  obtain ⟨hpos, hneg, hnd⟩ := sigPos_eq_finrank_of_posDef h
  refine ⟨hpos, ?_, ?_⟩
  · have hswap : sigPos Q = sigNeg (-Q) := by rw [sigNeg, neg_neg]
    rw [hswap, hneg]
  · refine nondegenerate_of_anisotropic ?_
    intro x hx
    refine h.anisotropic x ?_
    simp [hx]

end Definite

end QuadraticMap
