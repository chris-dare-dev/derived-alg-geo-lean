/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Discriminant
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Mukai
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Quadratic

/-!
# The divisorial discriminant is a support form

`Discriminant.lean` defines `Δ`, `\bar Δ^B_ω` and `Δ^C_{ω,B}` as *functions* of a
class `E : N`, because `N` is only an additive group and a `QuadraticForm ℝ N`
is not available there.  The support property of
`Weak/Support/Predicate/Quadratic.lean` needs a bundled `QuadraticForm ℝ V`
against an `ℝ`-linear charge `V →ₗ[ℝ] ℂ`.  This file supplies both on the real
Mukai extension `ℝ × D × ℝ`, which is the smallest real vector space the
divisorial charge factors through, and proves the two halves of
`Support.IsCompatible`.

## The two forms

* `DivisorSpace.realDiscriminant` is `Δ(r, c, s) = c² - 2rs`, the bundled form
  of `ChernCharacter.discriminant`;
* `DivisorSpace.realDiscriminantC` adds `C · (ω · c^B)²`, the bundled
  `ChernCharacter.discriminantC` of Macrì--Schmidt Definition 6.12, with
  `ω · c^B` supplied by the linear functional `DivisorSpace.omegaTwistedDegree`.

`realDiscriminantC_toRealExtension` and its siblings say these agree with the
unbundled functions along the class map, so nothing is a second definition of
the same quantity.

## Why negative definiteness needs `HodgeDefinite`, not `HodgeIndex`

On `ker Z` the computation is exact.  Writing `c^B = c - r B`, vanishing of the
imaginary part says `ω · c^B = 0` and vanishing of the real part pins `s`, and
substituting both gives

```text
Δ^C(v) = (c^B)² - r² ω²   for every C.
```

The `C` term drops because it is `C (ω · c^B)²`, so **no sign condition on `C`
is needed here**; `C ≥ 0` is what `discriminant_le_discriminantC` needs, which
is a different step.

The remaining input is that `(c^B)² < 0` for a nonzero `c^B` orthogonal to `ω`.
`DivisorSpace.HodgeIndex` gives only `≤ 0` — an isotropic class in `ω^⊥` would
make `Δ^C` vanish on a nonzero kernel vector and destroy the support property —
so the hypothesis here is the strictly stronger `DivisorSpace.HodgeDefinite`,
which is exactly the signature `(1, ρ - 1)` statement of the Hodge index
theorem rather than the inequality it implies.

## What is supplied and what is proved

Nonnegativity on the locus is **supplied**: it is Bogomolov--Gieseker, which
this repository does not prove.  `hasQuadraticSupportProperty` takes it as a
hypothesis, and the numerical corollary in
`AlgebraicGeometry/Numerical/Stability/DivisorialSupport.lean` discharges it
from `BogomolovGiesekerData`.  Negative definiteness on the kernel is proved.

The route deliberately avoids `PeriodDomain.HasSignatureTwo (realForm b)`, which
`Mukai/RealForm.lean` records as unavailable at the pinned Mathlib; the argument
below needs only definiteness on `ω^⊥`, which `HodgeDefinite` states directly.
-/

open QuadraticMap

universe v w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

/-! ### The bundled forms and the linear charge -/

section Algebraic

variable {N : Type v} {D : Type w}
variable [AddCommGroup N] [AddCommGroup D] [Module ℝ D]

namespace DivisorSpace

variable (S : DivisorSpace D)

/-- **The discriminant as a genuine quadratic form** on the real extension:
`Δ(r, c, s) = c² - 2rs`.

This is the self-pairing of the Mukai form *without* the halving of
`Mukai.realForm`; the discriminant convention of Macrì--Schmidt is the unhalved
one, and `realDiscriminant_toRealExtension` is what pins the choice. -/
def realDiscriminant : QuadraticForm ℝ (Mukai.RealExtension D) :=
  (Mukai.realBilin S.intersection).toQuadraticMap

@[simp]
theorem realDiscriminant_apply (r : ℝ) (c : D) (s : ℝ) :
    S.realDiscriminant (r, c, s) = S.pair c c - 2 * r * s := by
  rw [realDiscriminant, LinearMap.BilinMap.toQuadraticMap_apply, Mukai.realBilin_apply,
    Mukai.realPairing_apply]
  simp only [DivisorSpace.pair]
  ring

/-- **The twisted `ω`-degree** `v ↦ ω · (c - r B)`, as a linear functional on the
real extension.  It is the linear form whose square `Δ^C` adds to `Δ`. -/
def omegaTwistedDegree (P : StabilityParameters D) :
    Mukai.RealExtension D →ₗ[ℝ] ℝ where
  toFun v := S.intersection P.omega (v.2.1 - v.1 • P.B)
  map_add' v w := by
    have h : (v + w).2.1 - (v + w).1 • P.B
        = (v.2.1 - v.1 • P.B) + (w.2.1 - w.1 • P.B) := by
      simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    rw [h, map_add]
  map_smul' a v := by
    have h : (a • v).2.1 - (a • v).1 • P.B = a • (v.2.1 - v.1 • P.B) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_sub, smul_smul, smul_eq_mul]
    rw [h, map_smul]
    rfl

@[simp]
theorem omegaTwistedDegree_apply (P : StabilityParameters D) (v : Mukai.RealExtension D) :
    S.omegaTwistedDegree P v = S.pair P.omega (v.2.1 - v.1 • P.B) := rfl

/-- **The `C`-discriminant as a genuine quadratic form**:
`Δ^C_{ω,B} = Δ + C (ω · c^B)²`. -/
def realDiscriminantC (P : StabilityParameters D) (C : ℝ) :
    QuadraticForm ℝ (Mukai.RealExtension D) :=
  S.realDiscriminant + C • (QuadraticMap.sq.comp (S.omegaTwistedDegree P))

theorem realDiscriminantC_apply (P : StabilityParameters D) (C : ℝ)
    (v : Mukai.RealExtension D) :
    S.realDiscriminantC P C v =
      S.realDiscriminant v + C * S.omegaTwistedDegree P v ^ 2 := by
  simp only [realDiscriminantC, QuadraticMap.add_apply, QuadraticMap.smul_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, smul_eq_mul]
  ring

/-- **The divisorial central charge as an `ℝ`-linear map** on the real
extension.  It is `Mukai.expCharge`, which `Charge.lean` already proved the
divisorial charge to be. -/
def realCentralCharge (P : StabilityParameters D) :
    Mukai.RealExtension D →ₗ[ℝ] ℂ :=
  Mukai.expChargeLinearMap S.intersection P.B P.omega

theorem realCentralCharge_apply (P : StabilityParameters D) (r : ℝ) (c : D) (s : ℝ) :
    S.realCentralCharge P (r, c, s) =
      Complex.ofReal (S.pair P.B c - s - r * (S.pair P.B P.B - S.pair P.omega P.omega) / 2)
        + Complex.ofReal (S.pair P.omega c - r * S.pair P.B P.omega) * Complex.I := by
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  rw [realCentralCharge, Mukai.expChargeLinearMap_apply, Mukai.expCharge_apply _ _ _ hb]
  rfl

end DivisorSpace

/-! ### Agreement with the unbundled discriminants -/

namespace ChernCharacter

variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- Not a `simp` lemma: `toRealExtension_apply` is already `simp`, so it rewrites
the left-hand side first and the normal-form linter rejects the attribute.  The
statement is the identification that keeps the bundled and unbundled forms from
being two definitions of one quantity. -/
theorem realDiscriminant_toRealExtension (E : N) :
    S.realDiscriminant (ch.toRealExtension E) = ch.discriminant S E := by
  rw [toRealExtension_apply, DivisorSpace.realDiscriminant_apply, discriminant]

@[simp]
theorem omegaTwistedDegree_toRealExtension (P : StabilityParameters D) (E : N) :
    S.omegaTwistedDegree P (ch.toRealExtension E)
      = S.pair P.omega ((ch.twist S P.B).chOne E) := by
  rw [DivisorSpace.omegaTwistedDegree_apply, toRealExtension_apply, twist_chOne]

/-- Not a `simp` lemma: `toRealExtension_apply` is already `simp`, so it rewrites
the left-hand side first and the normal-form linter rejects the attribute.  The
statement is the identification that keeps the bundled and unbundled forms from
being two definitions of one quantity. -/
theorem realDiscriminantC_toRealExtension (P : StabilityParameters D) (C : ℝ) (E : N) :
    S.realDiscriminantC P C (ch.toRealExtension E) = ch.discriminantC S P C E := by
  rw [DivisorSpace.realDiscriminantC_apply, ch.realDiscriminant_toRealExtension S E,
    ch.omegaTwistedDegree_toRealExtension S P E, discriminantC]

/-- Not a `simp` lemma: `toRealExtension_apply` is already `simp`, so it rewrites
the left-hand side first and the normal-form linter rejects the attribute.  The
statement is the identification that keeps the bundled and unbundled forms from
being two definitions of one quantity. -/
theorem realCentralCharge_toRealExtension (P : StabilityParameters D) (E : N) :
    S.realCentralCharge P (ch.toRealExtension E) = ch.centralCharge S P E := by
  rw [DivisorSpace.realCentralCharge, Mukai.expChargeLinearMap_apply,
    ← Mukai.expChargeHom_apply, ← ch.centralCharge_eq_expChargeHom S P E]

end ChernCharacter

/-! ### Negative definiteness on the kernel of the charge -/

namespace DivisorSpace

variable (S : DivisorSpace D)

/-- The imaginary part of a vanishing charge says the twisted `ω`-degree
vanishes. -/
theorem omegaTwistedDegree_eq_zero_of_charge_eq_zero (P : StabilityParameters D)
    {v : Mukai.RealExtension D} (hZ : S.realCentralCharge P v = 0) :
    S.omegaTwistedDegree P v = 0 := by
  obtain ⟨r, c, s⟩ := v
  rw [S.realCentralCharge_apply P r c s] at hZ
  have him : S.pair P.omega c - r * S.pair P.B P.omega = 0 := by
    have := congrArg Complex.im hZ
    simpa using this
  rw [omegaTwistedDegree_apply]
  simp only [DivisorSpace.pair, map_sub, map_smul, smul_eq_mul] at him ⊢
  linear_combination him + r * S.intersection_symm.eq P.B P.omega

/-- **The kernel computation.**  On a class of vanishing charge the
`C`-discriminant is `(c^B)² - r² ω²`, independently of `C`.

Both halves of `Z v = 0` are used: the imaginary part kills the `C` term and the
real part eliminates `s`. -/
theorem realDiscriminantC_of_charge_eq_zero (P : StabilityParameters D) (C : ℝ)
    {v : Mukai.RealExtension D} (hZ : S.realCentralCharge P v = 0) :
    S.realDiscriminantC P C v =
      S.pair (v.2.1 - v.1 • P.B) (v.2.1 - v.1 • P.B) - v.1 ^ 2 * S.pair P.omega P.omega := by
  have hL := S.omegaTwistedDegree_eq_zero_of_charge_eq_zero P hZ
  obtain ⟨r, c, s⟩ := v
  rw [S.realCentralCharge_apply P r c s] at hZ
  have hre : S.pair P.B c - s - r * (S.pair P.B P.B - S.pair P.omega P.omega) / 2 = 0 := by
    have := congrArg Complex.re hZ
    simpa using this
  rw [realDiscriminantC_apply, hL]
  simp only [realDiscriminant_apply]
  have hBc : S.pair c P.B = S.pair P.B c := S.pair_comm c P.B
  simp only [DivisorSpace.pair, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at hre hBc ⊢
  linear_combination (2 * r) * hre + r * hBc

/-- **`Δ^C` is negative on every nonzero class of vanishing charge**, given the
Hodge index theorem in its definite form at `ω`.

No sign condition is imposed on `C`; the `C` term vanishes on the kernel. -/
theorem realDiscriminantC_neg_of_charge_eq_zero (P : StabilityParameters D)
    (hω : S.HodgeDefinite P.omega) (C : ℝ) {v : Mukai.RealExtension D}
    (hZ : S.realCentralCharge P v = 0) (hv : v ≠ 0) :
    S.realDiscriminantC P C v < 0 := by
  have hval := S.realDiscriminantC_of_charge_eq_zero P C hZ
  have hL := S.omegaTwistedDegree_eq_zero_of_charge_eq_zero P hZ
  rw [omegaTwistedDegree_apply] at hL
  by_cases hc0 : v.2.1 - v.1 • P.B = 0
  · have hr : v.1 ≠ 0 := by
      intro hr0
      apply hv
      have hc : v.2.1 = 0 := by
        rw [hr0, zero_smul, sub_zero] at hc0
        exact hc0
      obtain ⟨r, c, s⟩ := v
      simp only at hr0 hc
      subst hr0
      subst hc
      rw [S.realCentralCharge_apply P 0 0 s] at hZ
      have hre : S.pair P.B 0 - s - 0 * (S.pair P.B P.B - S.pair P.omega P.omega) / 2 = 0 := by
        have := congrArg Complex.re hZ
        simpa using this
      have hs : s = 0 := by
        simp only [DivisorSpace.pair, map_zero, zero_mul, zero_div, sub_zero, zero_sub,
          neg_eq_zero] at hre
        exact hre
      rw [hs]
      rfl
    rw [hval, hc0, S.pair_zero_left]
    have hrpos : 0 < v.1 ^ 2 := by positivity
    nlinarith [hω.H_square_pos, hrpos]
  · have hneg : S.pair (v.2.1 - v.1 • P.B) (v.2.1 - v.1 • P.B) < 0 :=
      hω.neg_definite _ hL hc0
    rw [hval]
    nlinarith [hω.H_square_pos, sq_nonneg v.1, hneg]

end DivisorSpace

end Algebraic

/-! ### The support property -/

section Normed

variable {D : Type w}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

namespace DivisorSpace

variable (S : DivisorSpace D)

/-- **The divisorial charge has the quadratic support property** on any locus
where the `C`-discriminant is nonnegative, given the Hodge index theorem in its
definite form at `ω`.

Nonnegativity on the locus is the supplied Bogomolov--Gieseker input; negative
definiteness on the kernel is proved. -/
theorem hasQuadraticSupportProperty (P : StabilityParameters D)
    (hω : S.HodgeDefinite P.omega) (C : ℝ) (locus : Set (Mukai.RealExtension D))
    (hloc : ∀ v ∈ locus, 0 ≤ S.realDiscriminantC P C v) :
    Support.HasQuadraticSupportProperty (S.realCentralCharge P) locus :=
  ⟨S.realDiscriminantC P C,
    ⟨hloc, fun _ hZ hv => S.realDiscriminantC_neg_of_charge_eq_zero P hω C hZ hv⟩⟩

section FiniteDimensional

variable [FiniteDimensional ℝ D]

/-- The norm-bound formulation, for consumers stated against
`Support.HasSupportProperty`. -/
theorem hasSupportProperty (P : StabilityParameters D)
    (hω : S.HodgeDefinite P.omega) (C : ℝ) (locus : Set (Mukai.RealExtension D))
    (hloc : ∀ v ∈ locus, 0 ≤ S.realDiscriminantC P C v) :
    Support.HasSupportProperty (S.realCentralCharge P) locus :=
  (S.hasQuadraticSupportProperty P hω C locus hloc).hasSupportProperty

end FiniteDimensional

end DivisorSpace

namespace ChernCharacter

variable {N : Type v} [AddCommGroup N]
variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- **The support property on the image of a locus of classes.**

This is the shape a numerical consumer wants: the hypothesis is
`0 ≤ Δ^C_{ω,B}(E)` for classes `E` in the locus, which
`discriminant_le_discriminantC` supplies from `Δ(E) ≥ 0` once `C ≥ 0`. -/
theorem hasQuadraticSupportProperty_image (P : StabilityParameters D)
    (hω : S.HodgeDefinite P.omega) (C : ℝ) (locus : Set N)
    (hloc : ∀ E ∈ locus, 0 ≤ ch.discriminantC S P C E) :
    Support.HasQuadraticSupportProperty (S.realCentralCharge P)
      (ch.toRealExtension '' locus) := by
  refine S.hasQuadraticSupportProperty P hω C _ ?_
  rintro _ ⟨E, hE, rfl⟩
  rw [ch.realDiscriminantC_toRealExtension S P C E]
  exact hloc E hE

end ChernCharacter

end Normed

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
