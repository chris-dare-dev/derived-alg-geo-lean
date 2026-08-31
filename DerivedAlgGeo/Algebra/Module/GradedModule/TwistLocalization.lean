/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Shift

/-!
# Trivializing a graded-module twist after degree-one localization

If `f` is homogeneous of degree one, multiplication by `f ^ d` trivializes the natural shift
`A(d)` after localizing away from `f`.  This file constructs that statement at the exact
degree-zero-localization level used by the associated-sheaf construction.

The sign convention is DerivedAlgGeo's convention `A(d)ₙ = Aₙ₊d`: a fraction in the shifted
degree-zero localization has ordinary graded degree `d`.  Multiplying it by `f⁻ᵈ` produces a
degree-zero fraction, and multiplication by `fᵈ` is the inverse operation.
-/

noncomputable section

open DirectSum SetLike
open scoped Pointwise

namespace GradedModule

universe u

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace DegreeZeroLocalization

variable {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)

private def twistPower : Submonoid.powers f := ⟨f ^ d, ⟨d, rfl⟩⟩

private def twistInverse : Localization (.powers f) :=
  Localization.mk 1 (twistPower d)

private def twistForward : Localization (.powers f) :=
  Localization.mk (f ^ d) 1

/-- Divide an `A(d)` fraction by `f ^ d`, obtaining an ordinary degree-zero fraction. -/
noncomputable def natShiftToSelfLinearMap :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) →ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        DegreeZeroLocalization 𝒜 𝒜 (.powers f) where
  toFun z := by
    refine ⟨twistInverse (f := f) d • (z : LocalizedModule (.powers f) A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d
        num := c.num
        den := ⟨(c.den : A) * f ^ d, ?_⟩
        den_mem := (Submonoid.powers f).mul_mem c.den_mem ⟨d, rfl⟩ }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk (c.num : A)
        (⟨(c.den : A) * f ^ d, ?_⟩ : Submonoid.powers f) =
          Localization.mk 1 (twistPower (f := f) d) •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_smul]
      congr 1
      ext
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverse (f := f) d) (x : LocalizedModule (.powers f) A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverse (f := f) d) a (z : LocalizedModule (.powers f) A)

/-- Multiply an ordinary degree-zero fraction by `f ^ d`, obtaining a fraction in `A(d)`. -/
noncomputable def selfToNatShiftLinearMap :
    DegreeZeroLocalization 𝒜 𝒜 (.powers f) →ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) where
  toFun z := by
    refine ⟨twistForward (f := f) d • (z : LocalizedModule (.powers f) A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨(c.num : A) * f ^ d, ?_⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * f ^ d)
        (⟨c.den, c.den_mem⟩ : Submonoid.powers f) =
          Localization.mk (f ^ d) 1 •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_mul]
      congr 1
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistForward (f := f) d) (x : LocalizedModule (.powers f) A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistForward (f := f) d) a (z : LocalizedModule (.powers f) A)

private theorem twistInverse_mul_forward :
    twistInverse (f := f) d * twistForward (f := f) d = 1 := by
  unfold twistInverse twistForward
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_mul_mk'_eq_one
    (S := Localization (Submonoid.powers f)) (1 : Submonoid.powers f)
      (twistPower (f := f) d)

private theorem twistForward_mul_inverse :
    twistForward (f := f) d * twistInverse (f := f) d = 1 := by
  rw [mul_comm]
  exact twistInverse_mul_forward (f := f) d

/-- On a degree-one chart, the degree-zero localization of `A(d)` is canonically the chart ring
as a module over itself. -/
noncomputable def natShiftSelfLinearEquiv :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) ≃ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        DegreeZeroLocalization 𝒜 𝒜 (.powers f) where
  toLinearMap := natShiftToSelfLinearMap 𝒜 hf d
  invFun := selfToNatShiftLinearMap 𝒜 hf d
  left_inv z := by
    apply ext
    change twistForward (f := f) d • (twistInverse (f := f) d •
      (z : LocalizedModule (.powers f) A)) = z
    rw [← mul_smul, twistForward_mul_inverse (f := f) d, one_smul]
  right_inv z := by
    apply ext
    change twistInverse (f := f) d • (twistForward (f := f) d •
      (z : LocalizedModule (.powers f) A)) = z
    rw [← mul_smul, twistInverse_mul_forward (f := f) d, one_smul]

@[simp]
theorem natShiftSelfLinearEquiv_apply_mk
    (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) (.powers f)) :
    natShiftSelfLinearEquiv 𝒜 hf d (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d
          num := c.num
          den := ⟨(c.den : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)⟩
          den_mem := (Submonoid.powers f).mul_mem c.den_mem ⟨d, rfl⟩ } := by
  apply ext
  change Localization.mk 1 (twistPower (f := f) d) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (c.num : A)
      ⟨(c.den : A) * f ^ d, (Submonoid.powers f).mul_mem c.den_mem ⟨d, rfl⟩⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_smul]
  congr 1
  ext
  exact mul_comm _ _

@[simp]
theorem natShiftSelfLinearEquiv_symm_apply_mk
    (c : NumDenSameDeg 𝒜 𝒜 (.powers f)) :
    (natShiftSelfLinearEquiv 𝒜 hf d).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨(c.num : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply ext
  change Localization.mk (f ^ d) 1 •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * f ^ d) ⟨(c.den : A), c.den_mem⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_mul]
  congr 1
  exact mul_comm _ _

/-- The chart trivialization with Mathlib's homogeneous-localization ring as target. -/
noncomputable def natShiftAwayLinearEquiv :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) ≃ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        HomogeneousLocalization 𝒜 (.powers f) :=
  (natShiftSelfLinearEquiv 𝒜 hf d).trans
    (selfLinearEquiv 𝒜 (.powers f)).symm

/-! ## Trivialization in any localization containing the degree-one element -/

variable {S : Submonoid A}

private def twistPowerOfMem (hfS : f ∈ S) : S :=
  ⟨f ^ d, S.pow_mem hfS d⟩

private def twistInverseOfMem (hfS : f ∈ S) : Localization S :=
  Localization.mk 1 (twistPowerOfMem (f := f) d hfS)

private def twistForwardOfMem : Localization S :=
  Localization.mk (f ^ d) 1

/-- **The transition cocycle**: `(g'/g)ⁿ · (f/g')ⁿ = (f/g)ⁿ`.

Composing the transition from the `g'`-chart to the `g`-chart with the scalar
that the `g'`-chart clears gives exactly the scalar the `g`-chart clears.

This is why the per-chart extensions of `#585` agree where two charts meet: over
`D₊(g)`, `s` is cleared by `(f/g)ⁿ`, and over `D₊(g')` by `(f/g')ⁿ`; this
identity says that carrying the second across by the transition lands on the
first, with no correction factor.

Cancellation of `g'ⁿ`, and nothing else — note `f` never has to be a unit, it
appears only in numerators. -/
theorem transitionScalar_mul (n : ℕ) {g g' : A} (hgS : g ∈ S) (hg'S : g' ∈ S) :
    Localization.mk (g' ^ n) (twistPowerOfMem (f := g) n hgS) *
        Localization.mk (f ^ n) (twistPowerOfMem (f := g') n hg'S) =
      Localization.mk (f ^ n) (twistPowerOfMem (f := g) n hgS) := by
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [twistPowerOfMem]; ring⟩


/-- Divide an `A(d)` fraction by `f ^ d`, given that `f` itself lies in `S`.

Membership is genuinely the hypothesis consumed, not merely invertibility of `f` in
`Localization S`: the graded representative below keeps every denominator inside `S` by
multiplying `c.den` by `f ^ d`, which needs `f ^ d ∈ S`.  When `f` is only invertible — the
Čech-intersection case, where the denominator submonoid contains no degree-one element at
all — use `natShiftLinearEquivOfMulMem`, which asks instead for a homogeneous cofactor `h`
with `f * h ∈ S`; taking `h = 1` recovers the membership hypothesis. -/
noncomputable def natShiftToSelfLinearMapOfMem (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toFun z := by
    refine ⟨twistInverseOfMem (f := f) d hfS • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d
        num := c.num
        den := ⟨(c.den : A) * f ^ d, ?_⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d) }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk (c.num : A)
        (⟨(c.den : A) * f ^ d, _⟩ : S) =
          Localization.mk 1 (twistPowerOfMem (f := f) d hfS) •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_smul]
      congr 1
      ext
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverseOfMem (f := f) d hfS)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverseOfMem (f := f) d hfS) a
      (z : LocalizedModule S A)

/-- Multiply an ordinary degree-zero fraction by `f ^ d` in any localization containing `f`. -/
noncomputable def selfToNatShiftLinearMapOfMem :
    DegreeZeroLocalization 𝒜 𝒜 S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S where
  toFun z := by
    refine ⟨twistForwardOfMem (S := S) (f := f) d • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨(c.num : A) * f ^ d, ?_⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * f ^ d)
        (⟨c.den, c.den_mem⟩ : S) =
          Localization.mk (f ^ d) 1 •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_mul]
      congr 1
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistForwardOfMem (S := S) (f := f) d)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistForwardOfMem (S := S) (f := f) d) a
      (z : LocalizedModule S A)

private theorem twistInverseOfMem_mul_forward (hfS : f ∈ S) :
    twistInverseOfMem (f := f) d hfS * twistForwardOfMem (S := S) (f := f) d = 1 := by
  unfold twistInverseOfMem twistForwardOfMem
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_mul_mk'_eq_one
    (S := Localization S) (1 : S) (twistPowerOfMem (f := f) d hfS)

/-! ## Trivializing when `f` is only invertible, not a member

`natShiftToSelfLinearMapOfMem` asks for `f ∈ S`, but its own statement only needs `f` to be
invertible in `Localization S`.  The gap is not academic: on a Čech intersection the denominator
submonoid is `.powers (∏ₐ gₐ)`, which for more than one factor contains no degree-one element at
all, while every `gₐ` is invertible there.

The hypothesis below records invertibility in the form the graded bookkeeping can use: a
homogeneous cofactor `h` with `f * h ∈ S`.  Division by `f ^ d` is then performed as
multiplication by `h ^ d / (f * h) ^ d`, which is the same element of the localization but keeps
every denominator literally inside `S`.  Taking `h = 1` recovers the membership hypothesis.
-/

private def twistPowerOfMulMem {h : A} (hfh : f * h ∈ S) : S :=
  ⟨(f * h) ^ d, S.pow_mem hfh d⟩

private def twistInverseOfMulMem {h : A} (hfh : f * h ∈ S) : Localization S :=
  Localization.mk (h ^ d) (twistPowerOfMulMem (f := f) d hfh)

/-- Divide an `A(d)` fraction by `f ^ d` whenever a homogeneous cofactor carries `f` into the
denominator submonoid. -/
noncomputable def natShiftToSelfLinearMapOfMulMem {h : A} {e : ℕ} (h_deg : h ∈ 𝒜 e)
    (hfh : f * h ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toFun z := by
    refine ⟨twistInverseOfMulMem (f := f) d hfh • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d * (1 + e)
        num := ⟨(c.num : A) * h ^ d, ?_⟩
        den := ⟨(c.den : A) * (f * h) ^ d, ?_⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfh d) }, ?_⟩
    · have hnum : (c.num : A) ∈ 𝒜 (c.deg + d) := c.num.2
      simpa [Nat.mul_add, Nat.mul_comm, ← add_assoc] using
        SetLike.mul_mem_graded hnum (SetLike.pow_mem_graded d h_deg)
    · simpa using SetLike.mul_mem_graded c.den.2
        (SetLike.pow_mem_graded d (SetLike.mul_mem_graded hf h_deg))
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * h ^ d)
        (⟨(c.den : A) * (f * h) ^ d, _⟩ : S) =
          Localization.mk (h ^ d) (twistPowerOfMulMem (f := f) d hfh) •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      congr 1
      · exact mul_comm _ _
      · ext
        exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverseOfMulMem (f := f) d hfh)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverseOfMulMem (f := f) d hfh) a
      (z : LocalizedModule S A)

private theorem twistInverseOfMulMem_mul_forward {h : A} (hfh : f * h ∈ S) :
    twistInverseOfMulMem (f := f) d hfh * twistForwardOfMem (S := S) (f := f) d = 1 := by
  unfold twistInverseOfMulMem twistForwardOfMem twistPowerOfMulMem
  rw [Localization.mk_mul]
  have hnum : h ^ d * f ^ d = ((f * h) ^ d : A) := by
    rw [mul_pow]; exact mul_comm _ _
  rw [hnum]
  simp

/-- Multiplication and division by `f ^ d` are inverse whenever a homogeneous cofactor carries
`f` into the denominator submonoid.  This is the form the Čech intersections need: there `f` is
one variable and the cofactor is the product of the others. -/
noncomputable def natShiftLinearEquivOfMulMem {h : A} {e : ℕ} (h_deg : h ∈ 𝒜 e)
    (hfh : f * h ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toLinearMap := natShiftToSelfLinearMapOfMulMem 𝒜 hf d h_deg hfh
  invFun := selfToNatShiftLinearMapOfMem (S := S) 𝒜 hf d
  left_inv z := by
    apply ext
    change twistForwardOfMem (S := S) (f := f) d •
      (twistInverseOfMulMem (f := f) d hfh • (z : LocalizedModule S A)) = z
    rw [← mul_smul, mul_comm, twistInverseOfMulMem_mul_forward (f := f) d hfh, one_smul]
  right_inv z := by
    apply ext
    change twistInverseOfMulMem (f := f) d hfh •
      (twistForwardOfMem (S := S) (f := f) d • (z : LocalizedModule S A)) = z
    rw [← mul_smul, twistInverseOfMulMem_mul_forward (f := f) d hfh, one_smul]

/-- Multiplication and division by `f ^ d` give inverse degree-zero localization maps whenever
`f` belongs to the denominator submonoid. -/
noncomputable def natShiftLinearEquivOfMem (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toLinearMap := natShiftToSelfLinearMapOfMem 𝒜 hf d hfS
  invFun := selfToNatShiftLinearMapOfMem (S := S) 𝒜 hf d
  left_inv z := by
    apply ext
    change twistForwardOfMem (S := S) (f := f) d •
      (twistInverseOfMem (f := f) d hfS • (z : LocalizedModule S A)) = z
    rw [← mul_smul, mul_comm, twistInverseOfMem_mul_forward (f := f) d hfS, one_smul]
  right_inv z := by
    apply ext
    change twistInverseOfMem (f := f) d hfS •
      (twistForwardOfMem (S := S) (f := f) d • (z : LocalizedModule S A)) = z
    rw [← mul_smul, twistInverseOfMem_mul_forward (f := f) d hfS, one_smul]

@[simp]
theorem natShiftLinearEquivOfMem_apply_mk (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) S) :
    natShiftLinearEquivOfMem 𝒜 hf d hfS (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d
          num := c.num
          den := ⟨(c.den : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d) } := by
  apply ext
  change Localization.mk 1 (twistPowerOfMem (f := f) d hfS) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (c.num : A)
      ⟨(c.den : A) * f ^ d, S.mul_mem c.den_mem (S.pow_mem hfS d)⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_smul]
  congr 1
  ext
  exact mul_comm _ _

@[simp]
theorem natShiftLinearEquivOfMem_symm_apply_mk (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 𝒜 S) :
    (natShiftLinearEquivOfMem 𝒜 hf d hfS).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨(c.num : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply ext
  change Localization.mk (f ^ d) 1 •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * f ^ d) ⟨(c.den : A), c.den_mem⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_mul]
  congr 1
  exact mul_comm _ _

/-- Value of the cofactor trivialization on a homogeneous fraction.

The `OfMem` sibling above divides by `f ^ d`; here `f` need only be invertible, so the fraction
is multiplied by the cofactor power `h ^ d` and the denominator picks up `(f * h) ^ d` instead.
This is the computation rule the Čech comparison needs, where `f` is one variable and `h` is the
product of the others. -/
@[simp]
theorem natShiftLinearEquivOfMulMem_apply_mk {h : A} {e : ℕ} (h_deg : h ∈ 𝒜 e)
    (hfh : f * h ∈ S) (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) S) :
    natShiftLinearEquivOfMulMem 𝒜 hf d h_deg hfh (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d * (1 + e)
          num := ⟨(c.num : A) * h ^ d, by
            have hnum : (c.num : A) ∈ 𝒜 (c.deg + d) := c.num.2
            simpa [Nat.mul_add, Nat.mul_comm, ← add_assoc] using
              SetLike.mul_mem_graded hnum (SetLike.pow_mem_graded d h_deg)⟩
          den := ⟨(c.den : A) * (f * h) ^ d, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded d (SetLike.mul_mem_graded hf h_deg))⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfh d) } := by
  apply ext
  change Localization.mk (h ^ d) (twistPowerOfMulMem (f := f) d hfh) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * h ^ d)
      ⟨(c.den : A) * (f * h) ^ d, S.mul_mem c.den_mem (S.pow_mem hfh d)⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 1
  · exact mul_comm _ _
  · ext
    exact mul_comm _ _

/-! ## Integer twists

`intShift 𝒜 d` is the zero-extended integer shift: its degree-`n` piece asks for an element of
`𝒜 k` with `(k : ℤ) = n + d`, and retains `0` when that integer is negative.

Lowering the twist by `e` while raising the fraction's degree by `e` leaves that integer
condition *identical* — `((n + e : ℕ) : ℤ) + (d - e) = (n : ℤ) + d`. So multiplying the
denominator by `f ^ e` transports the whole disjunctive membership verbatim, and in particular
the zero branch needs no separate treatment. That is what makes the integer case no harder than
the natural one here, and it is the step a negative twist is built from: taking `d = 0` sends
`A` to `A(-e)`.
-/

section IntShift

variable {f : A} {S : Submonoid A}

omit [GradedRing 𝒜] in
/-- The integer-shift membership condition depends only on the integer `n + d`, so raising the
degree by `e` and lowering the twist by `e` is the same condition. -/
theorem mem_intShift_sub_natCast_add (d : ℤ) (e n : ℕ) (a : A) :
    a ∈ intShift 𝒜 (d - e) (n + e) ↔ a ∈ intShift 𝒜 d n := by
  simp only [intShift_apply, mem_intShiftPiece]
  constructor
  · rintro (rfl | ⟨k, hk, ha⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨k, by push_cast at hk ⊢; omega, ha⟩
  · rintro (rfl | ⟨k, hk, ha⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨k, by push_cast at hk ⊢; omega, ha⟩

/-- Divide an `A(d)` fraction by `f ^ e`, lowering the integer twist to `d - e`.

Only membership of `f` in the denominator submonoid is used, exactly as in the nonnegative
case; the twist `d` is unconstrained in sign. -/
noncomputable def intShiftLowerLinearMap (hf : f ∈ 𝒜 1) (d : ℤ) (e : ℕ) (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝒜 (d - e)) S where
  toFun z := by
    refine ⟨twistInverseOfMem (f := f) e hfS • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + e
        num := ⟨(c.num : A),
          (mem_intShift_sub_natCast_add 𝒜 d e c.deg (c.num : A)).mpr c.num.2⟩
        den := ⟨(c.den : A) * f ^ e, by
          simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded e hf)⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS e) }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk (c.num : A)
        (⟨(c.den : A) * f ^ e, _⟩ : S) =
      Localization.mk 1 (twistPowerOfMem (f := f) e hfS) •
        LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
    rw [LocalizedModule.mk_smul_mk]
    simp only [one_smul]
    congr 1
    ext
    exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverseOfMem (f := f) e hfS)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverseOfMem (f := f) e hfS) a
      (z : LocalizedModule S A)

/-- Multiplying the numerator by `f ^ e` raises an integer twist back by `e`. -/
theorem mul_pow_mem_intShift (hf : f ∈ 𝒜 1) (d : ℤ) (e n : ℕ) (a : A)
    (ha : a ∈ intShift 𝒜 (d - e) n) : a * f ^ e ∈ intShift 𝒜 d n := by
  simp only [intShift_apply, mem_intShiftPiece] at ha ⊢
  rcases ha with rfl | ⟨k, hk, ha⟩
  · exact Or.inl (zero_mul _)
  · refine Or.inr ⟨k + e, ?_, ?_⟩
    · push_cast at hk ⊢; omega
    · simpa using SetLike.mul_mem_graded ha (SetLike.pow_mem_graded e hf)

/-- Multiply an `A(d - e)` fraction by `f ^ e`, raising the integer twist back to `d`. -/
noncomputable def intShiftRaiseLinearMap (hf : f ∈ 𝒜 1) (d : ℤ) (e : ℕ) :
    DegreeZeroLocalization 𝒜 (intShift 𝒜 (d - e)) S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S where
  toFun z := by
    refine ⟨twistForwardOfMem (S := S) (f := f) e • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨(c.num : A) * f ^ e,
          mul_pow_mem_intShift 𝒜 hf d e c.deg (c.num : A) c.num.2⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk ((c.num : A) * f ^ e) (⟨(c.den : A), c.den_mem⟩ : S) =
      Localization.mk (f ^ e) 1 •
        LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
    rw [LocalizedModule.mk_smul_mk]
    congr 1
    · exact mul_comm _ _
    · ext
      exact (one_mul _).symm
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistForwardOfMem (S := S) (f := f) e)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistForwardOfMem (S := S) (f := f) e) a
      (z : LocalizedModule S A)

/-- Multiplication and division by `f ^ e` identify an integer twist with its lowering by `e`.

Taking `d = 0` gives `A ≃ A(-e)` over any localization containing `f`, which is the negative
twist the Serre-finiteness dévissage needs. The sign of `d` plays no role. -/
noncomputable def intShiftLowerLinearEquiv (hf : f ∈ 𝒜 1) (d : ℤ) (e : ℕ) (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝒜 (d - e)) S where
  toLinearMap := intShiftLowerLinearMap 𝒜 hf d e hfS
  invFun := intShiftRaiseLinearMap 𝒜 hf d e
  left_inv z := by
    apply ext
    change twistForwardOfMem (S := S) (f := f) e •
      (twistInverseOfMem (f := f) e hfS • (z : LocalizedModule S A)) = z
    rw [← mul_smul, mul_comm, twistInverseOfMem_mul_forward (f := f) e hfS, one_smul]
  right_inv z := by
    apply ext
    change twistInverseOfMem (f := f) e hfS •
      (twistForwardOfMem (S := S) (f := f) e • (z : LocalizedModule S A)) = z
    rw [← mul_smul, twistInverseOfMem_mul_forward (f := f) e hfS, one_smul]

@[simp]
theorem intShiftLowerLinearEquiv_apply_mk (hf : f ∈ 𝒜 1) (d : ℤ) (e : ℕ) (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (intShift 𝒜 d) S) :
    intShiftLowerLinearEquiv 𝒜 hf d e hfS (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + e
          num := ⟨(c.num : A),
            (mem_intShift_sub_natCast_add 𝒜 d e c.deg (c.num : A)).mpr c.num.2⟩
          den := ⟨(c.den : A) * f ^ e, by
            simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded e hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS e) } := by
  apply ext
  change Localization.mk 1 (twistPowerOfMem (f := f) e hfS) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (c.num : A)
      ⟨(c.den : A) * f ^ e, S.mul_mem c.den_mem (S.pow_mem hfS e)⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_smul]
  congr 1
  ext
  exact mul_comm _ _

/-! ### Reaching twist zero

`intShiftLowerLinearEquiv` computes its target as `d - e`, which is awkward to aim at a
prescribed twist: hitting `A(0)` from `A(d)` would need `d - e` to be *definitionally* zero. The
hypothesis-carrying form below takes the target twist as a parameter instead, so a caller
supplies the arithmetic as a proof rather than fighting a transport. -/

/-- `intShiftLowerLinearEquiv` with the target twist named rather than computed. -/
noncomputable def intShiftShiftLinearEquiv (hf : f ∈ 𝒜 1) (d d' : ℤ) (e : ℕ)
    (hdd' : d' = d - e) (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝒜 d') S := by
  subst hdd'
  exact intShiftLowerLinearEquiv 𝒜 hf d e hfS

/-! ### Trivializing an integer twist, without a sign split in the term

Writing the trivialization as `if 0 ≤ d then … else …` type-checks, but it makes every
downstream computation branch: a locally fractional section carries an explicit
degree/numerator/denominator certificate, so a caller needs a formula for the image of `mk c`,
and a definition by cases yields one formula per branch forever after.

There is a single formula covering both signs. Multiplying by

`f ^ (-d).toNat / f ^ d.toNat`

divides by `f ^ d` when `d ≥ 0` and multiplies by `f ^ (-d)` when `d < 0`, because exactly one
of `d.toNat` and `(-d).toNat` is nonzero. The sign of `d` then appears only inside the
degree bookkeeping, discharged by `omega`, and never in the term. -/

/-- The scalar trivializing an integer twist: `f ^ (-d)` over `f ^ d`, with both exponents
truncated at zero so that exactly one of them is active. -/
private def intTwistScalar (d : ℤ) (hfS : f ∈ S) : Localization S :=
  Localization.mk (f ^ (-d).toNat) (twistPowerOfMem (f := f) d.toNat hfS)

/-- The numerator of the trivialized fraction lies in the degree the denominator does. -/
theorem mul_pow_toNat_mem_intShift_zero (hf : f ∈ 𝒜 1) (d : ℤ) (n : ℕ) (a : A)
    (ha : a ∈ intShift 𝒜 d n) :
    a * f ^ (-d).toNat ∈ intShift 𝒜 0 (n + d.toNat) := by
  simp only [intShift_apply, mem_intShiftPiece] at ha ⊢
  rcases ha with rfl | ⟨k, hk, ha⟩
  · exact Or.inl (zero_mul _)
  · refine Or.inr ⟨n + d.toNat, by push_cast; omega, ?_⟩
    have hidx : k + (-d).toNat = n + d.toNat := by omega
    have := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded (-d).toNat hf)
    simpa [hidx] using this

/-- Every integer twist is trivial on a localization containing a degree-one element.

One formula covers both signs; see the section comment. -/
noncomputable def intShiftZeroLinearEquiv (hf : f ∈ 𝒜 1) (d : ℤ) (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝒜 0) S where
  toFun z := by
    refine ⟨intTwistScalar (f := f) d hfS • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d.toNat
        num := ⟨(c.num : A) * f ^ (-d).toNat,
          mul_pow_toNat_mem_intShift_zero 𝒜 hf d c.deg (c.num : A) c.num.2⟩
        den := ⟨(c.den : A) * f ^ d.toNat, by
          simpa using SetLike.mul_mem_graded c.den.2
            (SetLike.pow_mem_graded d.toNat hf)⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d.toNat) }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk ((c.num : A) * f ^ (-d).toNat)
        (⟨(c.den : A) * f ^ d.toNat, _⟩ : S) =
      Localization.mk (f ^ (-d).toNat) (twistPowerOfMem (f := f) d.toNat hfS) •
        LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
    rw [LocalizedModule.mk_smul_mk]
    congr 1
    · exact mul_comm _ _
    · ext
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (intTwistScalar (f := f) d hfS) (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (intTwistScalar (f := f) d hfS) a (z : LocalizedModule S A)
  invFun z := by
    refine ⟨Localization.mk (f ^ d.toNat)
      (twistPowerOfMem (f := f) (-d).toNat hfS) • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + (-d).toNat
        num := ⟨(c.num : A) * f ^ d.toNat, ?_⟩
        den := ⟨(c.den : A) * f ^ (-d).toNat, by
          simpa using SetLike.mul_mem_graded c.den.2
            (SetLike.pow_mem_graded (-d).toNat hf)⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS (-d).toNat) }, ?_⟩
    · simp only [intShift_apply, mem_intShiftPiece] at c ⊢
      rcases c.num.2 with h0 | ⟨k, hk, ha⟩
      · exact Or.inl (by rw [show (c.num : A) = 0 from h0]; exact zero_mul _)
      · refine Or.inr ⟨k + d.toNat, by push_cast at hk ⊢; omega, ?_⟩
        simpa using SetLike.mul_mem_graded ha (SetLike.pow_mem_graded d.toNat hf)
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * f ^ d.toNat)
          (⟨(c.den : A) * f ^ (-d).toNat, _⟩ : S) =
        Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
          LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      congr 1
      · exact mul_comm _ _
      · ext
        exact mul_comm _ _
  left_inv z := by
    apply ext
    change Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
      (intTwistScalar (f := f) d hfS • (z : LocalizedModule S A)) = z
    rw [← mul_smul, intTwistScalar, Localization.mk_mul]
    rw [show Localization.mk (f ^ d.toNat * f ^ (-d).toNat)
        (twistPowerOfMem (f := f) (-d).toNat hfS *
          twistPowerOfMem (f := f) d.toNat hfS) = 1 from ?_, one_smul]
    rw [mul_comm (f ^ d.toNat : A) (f ^ (-d).toNat)]
    exact Localization.mk_self (twistPowerOfMem (f := f) (-d).toNat hfS *
      twistPowerOfMem (f := f) d.toNat hfS)
  right_inv z := by
    apply ext
    change intTwistScalar (f := f) d hfS •
      (Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
        (z : LocalizedModule S A)) = z
    rw [← mul_smul, intTwistScalar, Localization.mk_mul]
    rw [show Localization.mk (f ^ (-d).toNat * f ^ d.toNat)
        (twistPowerOfMem (f := f) d.toNat hfS *
          twistPowerOfMem (f := f) (-d).toNat hfS) = 1 from ?_, one_smul]
    rw [mul_comm (f ^ (-d).toNat : A) (f ^ d.toNat)]
    exact Localization.mk_self (twistPowerOfMem (f := f) d.toNat hfS *
      twistPowerOfMem (f := f) (-d).toNat hfS)

/-- The trivialization in explicit fractions, in one formula for both signs.

This is what makes the uniform definition worth having: a locally fractional section carries a
degree/numerator/denominator certificate, and rebuilding it downstream needs exactly this
rule — once, not once per sign. -/
@[simp]
theorem intShiftZeroLinearEquiv_apply_mk (hf : f ∈ 𝒜 1) (d : ℤ) (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (intShift 𝒜 d) S) :
    intShiftZeroLinearEquiv 𝒜 hf d hfS (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d.toNat
          num := ⟨(c.num : A) * f ^ (-d).toNat,
            mul_pow_toNat_mem_intShift_zero 𝒜 hf d c.deg (c.num : A) c.num.2⟩
          den := ⟨(c.den : A) * f ^ d.toNat, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded d.toNat hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d.toNat) } := by
  apply ext
  change Localization.mk (f ^ (-d).toNat) (twistPowerOfMem (f := f) d.toNat hfS) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * f ^ (-d).toNat)
      ⟨(c.den : A) * f ^ d.toNat, S.mul_mem c.den_mem (S.pow_mem hfS d.toNat)⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 1
  · exact mul_comm _ _
  · ext
    exact mul_comm _ _

/-- **The two degree-one trivializations of an integer twist differ by `gⁿ / fⁿ`.**

`intShiftZeroLinearEquiv` is multiplication by `intTwistScalar`, which at a
nonnegative twist `n` is `1 / fⁿ`. So trivializing at `f` and trivializing at `g`
differ by the unit `gⁿ / fⁿ`, and the identity reduces to a cancellation in
`Localization S`.

This is the transition function of `O(n)` between two degree-one charts, and it
is what an overlap comparison consumes: on `D₊(f) ⊓ D₊(g)` a section trivialized
one way is `gⁿ/fⁿ` times the same section trivialized the other way.

Stated on the underlying `LocalizedModule`, which drops the degree bookkeeping
entirely — both sides are scalar multiples of the same `z`, so no `NumDenSameDeg`
appears and no degree has to be matched. -/
theorem intShiftZeroLinearEquiv_transition (hf : f ∈ 𝒜 1) {g : A} (hg : g ∈ 𝒜 1)
    (hfS : f ∈ S) (hgS : g ∈ S) (n : ℕ)
    (z : DegreeZeroLocalization 𝒜 (intShift 𝒜 (n : ℤ)) S) :
    ((intShiftZeroLinearEquiv 𝒜 hf (n : ℤ) hfS z : LocalizedModule S A)) =
      Localization.mk (g ^ n) (twistPowerOfMem (f := f) n hfS) •
        ((intShiftZeroLinearEquiv 𝒜 hg (n : ℤ) hgS z : LocalizedModule S A)) := by
  show intTwistScalar (f := f) (n : ℤ) hfS • (z : LocalizedModule S A) =
    Localization.mk (g ^ n) (twistPowerOfMem (f := f) n hfS) •
      (intTwistScalar (f := g) (n : ℤ) hgS • (z : LocalizedModule S A))
  rw [smul_smul]
  congr 1
  simp only [intTwistScalar, twistPowerOfMem, Localization.mk_mul, Int.toNat_natCast,
    Int.toNat_neg_natCast, pow_zero]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- The numerator of the inverse trivialization lies in the twist it should. -/
theorem mul_pow_toNat_mem_intShift (hf : f ∈ 𝒜 1) (d : ℤ) (n : ℕ) (a : A)
    (ha : a ∈ intShift 𝒜 0 n) : a * f ^ d.toNat ∈ intShift 𝒜 d (n + (-d).toNat) := by
  simp only [intShift_apply, mem_intShiftPiece] at ha ⊢
  rcases ha with rfl | ⟨k, hk, ha⟩
  · exact Or.inl (zero_mul _)
  · refine Or.inr ⟨k + d.toNat, by push_cast at hk ⊢; omega, ?_⟩
    simpa using SetLike.mul_mem_graded ha (SetLike.pow_mem_graded d.toNat hf)

/-- The inverse trivialization in explicit fractions, again in one formula for both signs. -/
@[simp]
theorem intShiftZeroLinearEquiv_symm_apply_mk (hf : f ∈ 𝒜 1) (d : ℤ) (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (intShift 𝒜 0) S) :
    (intShiftZeroLinearEquiv 𝒜 hf d hfS).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + (-d).toNat
          num := ⟨(c.num : A) * f ^ d.toNat,
            mul_pow_toNat_mem_intShift 𝒜 hf d c.deg (c.num : A) c.num.2⟩
          den := ⟨(c.den : A) * f ^ (-d).toNat, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded (-d).toNat hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS (-d).toNat) } := by
  apply ext
  change Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * f ^ d.toNat)
      ⟨(c.den : A) * f ^ (-d).toNat, S.mul_mem c.den_mem (S.pow_mem hfS (-d).toNat)⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 1
  · exact mul_comm _ _
  · ext
    exact mul_comm _ _

/-! ### The cofactor form, for Čech intersections

`intShiftZeroLinearEquiv` asks for `f ∈ S`. A Čech intersection cannot supply that: the
denominator there is `∏ₐ X_{x a}`, homogeneous of degree `n + 1`, so for `n ≥ 1` its powers
submonoid contains no degree-one element at all. What is available is a homogeneous cofactor `h`
with `f * h ∈ S` — the product of the remaining variables.

The scalar is parameterized by its two exponents rather than by `d` directly. That is not
cosmetic: writing the inverse as the `-d` instance of the same definition puts `(- -d).toNat`
in the term, which is only propositionally `d.toNat`, and every subsequent `change` fails on it.
Naming the exponents makes the forward and inverse scalars the *same* definition with the pair
swapped, and their product telescopes to `(f * h) ^ (a + b)` over itself. -/

/-- The cofactor scalar `h ^ a * f ^ b / (f * h) ^ a`, which equals `f ^ (b - a)` in the
localization while keeping every denominator inside `S`. -/
private def cofactorScalar {h : A} (a b : ℕ) (hfh : f * h ∈ S) : Localization S :=
  Localization.mk (h ^ a * f ^ b) (twistPowerOfMulMem (f := f) a hfh)

omit [GradedRing 𝒜] in
/-- Swapping the two exponents inverts the cofactor scalar. -/
private theorem cofactorScalar_mul {h : A} (a b : ℕ) (hfh : f * h ∈ S) :
    cofactorScalar (f := f) (h := h) a b hfh *
      cofactorScalar (f := f) (h := h) b a hfh = 1 := by
  unfold cofactorScalar twistPowerOfMulMem
  rw [Localization.mk_mul]
  have hnum : (h ^ a * f ^ b) * (h ^ b * f ^ a) = ((f * h) ^ (a + b) : A) := by
    rw [mul_pow, pow_add, pow_add]
    ring
  have hden : ((⟨(f * h) ^ a, S.pow_mem hfh a⟩ : S) * ⟨(f * h) ^ b, S.pow_mem hfh b⟩) =
      ⟨(f * h) ^ (a + b), S.pow_mem hfh (a + b)⟩ := by
    ext
    exact (pow_add _ _ _).symm
  rw [hnum, hden]
  exact Localization.mk_self (⟨(f * h) ^ (a + b), S.pow_mem hfh (a + b)⟩ : S)

/-- Degrees for the cofactor trivialization: multiplying by `h ^ a * f ^ b` carries the twist
`(a : ℤ) - b` to the twist zero. -/
theorem mul_pow_mul_pow_mem_intShift_zero {h : A} {e : ℕ} (hf : f ∈ 𝒜 1) (h_deg : h ∈ 𝒜 e)
    (a b : ℕ) (d : ℤ) (hd : d = (a : ℤ) - b) (n : ℕ) (x : A)
    (hx : x ∈ intShift 𝒜 d n) :
    x * h ^ a * f ^ b ∈ intShift 𝒜 0 (n + a * (1 + e)) := by
  simp only [intShift_apply, mem_intShiftPiece] at hx ⊢
  rcases hx with rfl | ⟨k, hk, hx⟩
  · exact Or.inl (by simp)
  · refine Or.inr ⟨n + a * (1 + e), by push_cast; omega, ?_⟩
    have hkey : k + b = n + a := by subst hd; omega
    have hidx : k + a * e + b = n + a * (1 + e) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hmul := SetLike.mul_mem_graded
      (SetLike.mul_mem_graded hx (SetLike.pow_mem_graded a h_deg))
      (SetLike.pow_mem_graded b hf)
    simpa [hidx] using hmul

/-- The same, in the direction that produces the twist rather than removing it. -/
theorem mul_pow_mul_pow_mem_intShift {h : A} {e : ℕ} (hf : f ∈ 𝒜 1) (h_deg : h ∈ 𝒜 e)
    (a b : ℕ) (d : ℤ) (hd : d = (a : ℤ) - b) (n : ℕ) (x : A)
    (hx : x ∈ intShift 𝒜 0 n) :
    x * h ^ b * f ^ a ∈ intShift 𝒜 d (n + b * (1 + e)) := by
  simp only [intShift_apply, mem_intShiftPiece] at hx ⊢
  rcases hx with rfl | ⟨k, hk, hx⟩
  · exact Or.inl (by simp)
  · refine Or.inr ⟨k + b * e + a, ?_, ?_⟩
    · have hkn : k = n := by omega
      have hexp : n + b * (1 + e) = n + b + b * e := by ring
      rw [hexp, hkn]
      push_cast
      omega
    · have hmul := SetLike.mul_mem_graded
        (SetLike.mul_mem_graded hx (SetLike.pow_mem_graded b h_deg))
        (SetLike.pow_mem_graded a hf)
      simpa using hmul

/-- Trivializing an integer twist when `f` is only invertible in `S`, via a homogeneous cofactor.

This is the form the Čech intersections need: there `f` is one variable of the index and `h` is
the product of the others. The twist is given as `(a : ℤ) - b` so that the caller chooses the
exponents; `a = d.toNat`, `b = (-d).toNat` recovers an arbitrary `d`. -/
noncomputable def intShiftZeroLinearEquivOfMulMem {h : A} {e : ℕ} (hf : f ∈ 𝒜 1)
    (h_deg : h ∈ 𝒜 e) (a b : ℕ) (d : ℤ) (hd : d = (a : ℤ) - b) (hfh : f * h ∈ S) :
    DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝒜 0) S where
  toFun z := by
    refine ⟨cofactorScalar (f := f) (h := h) a b hfh • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + a * (1 + e)
        num := ⟨(c.num : A) * h ^ a * f ^ b,
          mul_pow_mul_pow_mem_intShift_zero 𝒜 hf h_deg a b d hd c.deg (c.num : A) c.num.2⟩
        den := ⟨(c.den : A) * (f * h) ^ a, by
          simpa using SetLike.mul_mem_graded c.den.2
            (SetLike.pow_mem_graded a (SetLike.mul_mem_graded hf h_deg))⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfh a) }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk ((c.num : A) * h ^ a * f ^ b)
        (⟨(c.den : A) * (f * h) ^ a, S.mul_mem c.den_mem (S.pow_mem hfh a)⟩ : S) =
      Localization.mk (h ^ a * f ^ b) (twistPowerOfMulMem (f := f) a hfh) •
        LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
    rw [LocalizedModule.mk_smul_mk]
    congr 1
    · rw [mul_assoc]
      exact mul_comm _ _
    · ext
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (cofactorScalar (f := f) (h := h) a b hfh)
      (x : LocalizedModule S A) y
  map_smul' r z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (cofactorScalar (f := f) (h := h) a b hfh) r
      (z : LocalizedModule S A)
  invFun z := by
    refine ⟨cofactorScalar (f := f) (h := h) b a hfh • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + b * (1 + e)
        num := ⟨(c.num : A) * h ^ b * f ^ a,
          mul_pow_mul_pow_mem_intShift 𝒜 hf h_deg a b d hd c.deg (c.num : A) c.num.2⟩
        den := ⟨(c.den : A) * (f * h) ^ b, by
          simpa using SetLike.mul_mem_graded c.den.2
            (SetLike.pow_mem_graded b (SetLike.mul_mem_graded hf h_deg))⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfh b) }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk ((c.num : A) * h ^ b * f ^ a)
        (⟨(c.den : A) * (f * h) ^ b, S.mul_mem c.den_mem (S.pow_mem hfh b)⟩ : S) =
      Localization.mk (h ^ b * f ^ a) (twistPowerOfMulMem (f := f) b hfh) •
        LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
    rw [LocalizedModule.mk_smul_mk]
    congr 1
    · rw [mul_assoc]
      exact mul_comm _ _
    · ext
      exact mul_comm _ _
  left_inv z := by
    apply ext
    change cofactorScalar (f := f) (h := h) b a hfh •
      (cofactorScalar (f := f) (h := h) a b hfh • (z : LocalizedModule S A)) = z
    rw [← mul_smul, mul_comm, cofactorScalar_mul (f := f) (h := h) a b hfh, one_smul]
  right_inv z := by
    apply ext
    change cofactorScalar (f := f) (h := h) a b hfh •
      (cofactorScalar (f := f) (h := h) b a hfh • (z : LocalizedModule S A)) = z
    rw [← mul_smul, cofactorScalar_mul (f := f) (h := h) a b hfh, one_smul]

/-- The cofactor trivialization in explicit fractions. -/
@[simp]
theorem intShiftZeroLinearEquivOfMulMem_apply_mk {h : A} {e : ℕ} (hf : f ∈ 𝒜 1)
    (h_deg : h ∈ 𝒜 e) (a b : ℕ) (d : ℤ) (hd : d = (a : ℤ) - b) (hfh : f * h ∈ S)
    (c : NumDenSameDeg 𝒜 (intShift 𝒜 d) S) :
    intShiftZeroLinearEquivOfMulMem 𝒜 hf h_deg a b d hd hfh
        (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + a * (1 + e)
          num := ⟨(c.num : A) * h ^ a * f ^ b,
            mul_pow_mul_pow_mem_intShift_zero 𝒜 hf h_deg a b d hd c.deg (c.num : A) c.num.2⟩
          den := ⟨(c.den : A) * (f * h) ^ a, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded a (SetLike.mul_mem_graded hf h_deg))⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfh a) } := by
  apply ext
  change Localization.mk (h ^ a * f ^ b) (twistPowerOfMulMem (f := f) a hfh) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * h ^ a * f ^ b)
      ⟨(c.den : A) * (f * h) ^ a, S.mul_mem c.den_mem (S.pow_mem hfh a)⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 1
  · rw [mul_assoc]
    exact mul_comm _ _
  · ext
    exact mul_comm _ _

/-! ### The same trivialization for a graded module

Everything above is stated for `𝒜` as a module over itself, which is all the twisting sheaf needs
and all that `TwistChart.lean` and `Finiteness.lean` ever ask for. The tensor comparison
`F ⊗ O(d) ≅ F(d)` of `#584` needs it for an **arbitrary** graded module, and nothing in the
construction resists: `intTwistScalar` lives in `Localization S` and acts on `LocalizedModule S M`
exactly as it acts on `LocalizedModule S A`.

Only two things are genuinely new. The degree bookkeeping is `SetLike.GradedSMul.smul_mem` where
the ring case used `SetLike.mul_mem_graded`; and `map_smul'` has to name the `algebraMap` into
`Localization S`, because the `HomogeneousLocalization 𝒜 S`-action is `Module.compHom` along it and
the two actions commute only after that is made visible.

The numerator here is `f ^ (-d).toNat • m` rather than `m * f ^ (-d).toNat`, which is the order
`LocalizedModule.mk_smul_mk` produces, so the numerator needs no `mul_comm` fix-up — only the
denominator does. -/

section GradedModule

variable {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
variable (𝓜 : ℕ → σM) [SetLike.GradedSMul 𝒜 𝓜]

/-- The numerator of the trivialized fraction lies in the degree the denominator does. -/
theorem pow_smul_mem_intShift_zero (hf : f ∈ 𝒜 1) (d : ℤ) (n : ℕ) (m : M)
    (hm : m ∈ intShift 𝓜 d n) :
    f ^ (-d).toNat • m ∈ intShift 𝓜 0 (n + d.toNat) := by
  simp only [intShift_apply, mem_intShiftPiece] at hm ⊢
  rcases hm with rfl | ⟨k, hk, hm⟩
  · exact Or.inl (smul_zero _)
  · refine Or.inr ⟨n + d.toNat, by push_cast; omega, ?_⟩
    have hidx : (-d).toNat + k = n + d.toNat := by omega
    have := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded (-d).toNat hf) hm
    simpa [hidx] using this

/-- The numerator of the inverse trivialization lies in the twist it should. -/
theorem pow_smul_mem_intShift (hf : f ∈ 𝒜 1) (d : ℤ) (n : ℕ) (m : M)
    (hm : m ∈ intShift 𝓜 0 n) : f ^ d.toNat • m ∈ intShift 𝓜 d (n + (-d).toNat) := by
  simp only [intShift_apply, mem_intShiftPiece] at hm ⊢
  rcases hm with rfl | ⟨k, hk, hm⟩
  · exact Or.inl (smul_zero _)
  · refine Or.inr ⟨d.toNat + k, by push_cast at hk ⊢; omega, ?_⟩
    simpa using SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded d.toNat hf) hm

/-- **Every integer twist of a graded module is trivial on a localization containing a
degree-one element.** -/
noncomputable def intShiftZeroModuleLinearEquiv (hf : f ∈ 𝒜 1) (d : ℤ) (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (intShift 𝓜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (intShift 𝓜 0) S where
  toFun z := by
    refine ⟨intTwistScalar (f := f) d hfS • (z : LocalizedModule S M), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d.toNat
        num := ⟨f ^ (-d).toNat • (c.num : M),
          pow_smul_mem_intShift_zero 𝒜 𝓜 hf d c.deg (c.num : M) c.num.2⟩
        den := ⟨(c.den : A) * f ^ d.toNat, by
          simpa using SetLike.mul_mem_graded c.den.2
            (SetLike.pow_mem_graded d.toNat hf)⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d.toNat) }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk (f ^ (-d).toNat • (c.num : M))
        (⟨(c.den : A) * f ^ d.toNat, _⟩ : S) =
      Localization.mk (f ^ (-d).toNat) (twistPowerOfMem (f := f) d.toNat hfS) •
        LocalizedModule.mk (c.num : M) ⟨(c.den : A), c.den_mem⟩
    rw [LocalizedModule.mk_smul_mk]
    congr 1
    ext
    exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (intTwistScalar (f := f) d hfS) (x : LocalizedModule S M) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (intTwistScalar (f := f) d hfS)
      (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S) a)
      (z : LocalizedModule S M)
  invFun z := by
    refine ⟨Localization.mk (f ^ d.toNat)
      (twistPowerOfMem (f := f) (-d).toNat hfS) • (z : LocalizedModule S M), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + (-d).toNat
        num := ⟨f ^ d.toNat • (c.num : M), ?_⟩
        den := ⟨(c.den : A) * f ^ (-d).toNat, by
          simpa using SetLike.mul_mem_graded c.den.2
            (SetLike.pow_mem_graded (-d).toNat hf)⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS (-d).toNat) }, ?_⟩
    · exact pow_smul_mem_intShift 𝒜 𝓜 hf d c.deg (c.num : M) c.num.2
    · rw [← hc]
      change LocalizedModule.mk (f ^ d.toNat • (c.num : M))
          (⟨(c.den : A) * f ^ (-d).toNat, _⟩ : S) =
        Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
          LocalizedModule.mk (c.num : M) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      congr 1
      ext
      exact mul_comm _ _
  left_inv z := by
    apply ext
    change Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
      (intTwistScalar (f := f) d hfS • (z : LocalizedModule S M)) = z
    rw [← mul_smul, intTwistScalar, Localization.mk_mul]
    rw [show Localization.mk (f ^ d.toNat * f ^ (-d).toNat)
        (twistPowerOfMem (f := f) (-d).toNat hfS *
          twistPowerOfMem (f := f) d.toNat hfS) = 1 from ?_, one_smul]
    rw [mul_comm (f ^ d.toNat : A) (f ^ (-d).toNat)]
    exact Localization.mk_self (twistPowerOfMem (f := f) (-d).toNat hfS *
      twistPowerOfMem (f := f) d.toNat hfS)
  right_inv z := by
    apply ext
    change intTwistScalar (f := f) d hfS •
      (Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
        (z : LocalizedModule S M)) = z
    rw [← mul_smul, intTwistScalar, Localization.mk_mul]
    rw [show Localization.mk (f ^ (-d).toNat * f ^ d.toNat)
        (twistPowerOfMem (f := f) d.toNat hfS *
          twistPowerOfMem (f := f) (-d).toNat hfS) = 1 from ?_, one_smul]
    rw [mul_comm (f ^ (-d).toNat : A) (f ^ d.toNat)]
    exact Localization.mk_self (twistPowerOfMem (f := f) d.toNat hfS *
      twistPowerOfMem (f := f) (-d).toNat hfS)


/-- The trivialization in explicit fractions, in one formula for both signs.

The module analogue of `intShiftZeroLinearEquiv_apply_mk`, and needed for the same reason: a
locally fractional section carries a degree/numerator/denominator certificate, and rebuilding it
downstream needs exactly this rule. -/
@[simp]
theorem intShiftZeroModuleLinearEquiv_apply_mk (hf : f ∈ 𝒜 1) (d : ℤ) (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (intShift 𝓜 d) S) :
    intShiftZeroModuleLinearEquiv 𝒜 𝓜 hf d hfS (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d.toNat
          num := ⟨f ^ (-d).toNat • (c.num : M),
            pow_smul_mem_intShift_zero 𝒜 𝓜 hf d c.deg (c.num : M) c.num.2⟩
          den := ⟨(c.den : A) * f ^ d.toNat, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded d.toNat hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d.toNat) } := by
  apply ext
  change Localization.mk (f ^ (-d).toNat) (twistPowerOfMem (f := f) d.toNat hfS) •
      LocalizedModule.mk (c.num : M) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (f ^ (-d).toNat • (c.num : M))
      ⟨(c.den : A) * f ^ d.toNat, S.mul_mem c.den_mem (S.pow_mem hfS d.toNat)⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 1
  ext
  exact mul_comm _ _

/-- The inverse trivialization in explicit fractions, again in one formula for both signs. -/
@[simp]
theorem intShiftZeroModuleLinearEquiv_symm_apply_mk (hf : f ∈ 𝒜 1) (d : ℤ) (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (intShift 𝓜 0) S) :
    (intShiftZeroModuleLinearEquiv 𝒜 𝓜 hf d hfS).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + (-d).toNat
          num := ⟨f ^ d.toNat • (c.num : M),
            pow_smul_mem_intShift 𝒜 𝓜 hf d c.deg (c.num : M) c.num.2⟩
          den := ⟨(c.den : A) * f ^ (-d).toNat, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded (-d).toNat hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS (-d).toNat) } := by
  apply ext
  change Localization.mk (f ^ d.toNat) (twistPowerOfMem (f := f) (-d).toNat hfS) •
      LocalizedModule.mk (c.num : M) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (f ^ d.toNat • (c.num : M))
      ⟨(c.den : A) * f ^ (-d).toNat, S.mul_mem c.den_mem (S.pow_mem hfS (-d).toNat)⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 1
  ext
  exact mul_comm _ _

end GradedModule

end IntShift

end DegreeZeroLocalization

end GradedModule
