/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Localization

/-!
# Shifts of naturally graded modules

An `ℕ`-graded ring can support module twists conventionally indexed by `ℤ`. This file keeps that
boundary visible without assuming a geometric realization.

* `natShift 𝓜 d` has degree-`n` piece `𝓜 (n + d)` and composes strictly.
* `intShift 𝓜 d` uses the same formula with `n + d : ℤ`, extending `𝓜` by the zero subgroup
  in negative degrees.  It is a one-step shift of the original natural grading.  Iterated mixed
  integer shifts are deliberately not identified at the graded-module level: truncation at degree
  zero makes that false before passing to associated sheaves.

Our sign convention is therefore `M(d)ₙ = Mₙ₊d`.
-/

noncomputable section

open scoped Pointwise

namespace GradedModule

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

/-! ## Natural shifts -/

/-- The natural shift with convention `M(d)ₙ = Mₙ₊d`. -/
def natShift (d : ℕ) : ℕ → σM := fun n => 𝓜 (n + d)

instance natShiftGradedSMul (d : ℕ) : SetLike.GradedSMul 𝒜 (natShift 𝓜 d) where
  smul_mem {i j} {a m} ha hm := by
    change m ∈ 𝓜 (j + d) at hm
    have h := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝓜) ha hm
    change a • m ∈ 𝓜 (i + (j + d)) at h
    change a • m ∈ 𝓜 ((i + j) + d)
    simpa only [Nat.add_assoc] using h

@[simp]
theorem natShift_apply (d n : ℕ) : natShift 𝓜 d n = 𝓜 (n + d) := rfl

@[simp]
theorem natShift_zero : natShift 𝓜 0 = 𝓜 := by
  funext n
  simp [natShift]

@[simp]
theorem natShift_add (d e : ℕ) :
    natShift (natShift 𝓜 d) e = natShift 𝓜 (d + e) := by
  funext n
  simp [natShift, Nat.add_assoc, Nat.add_comm d e]

/-! ## Integer shifts by zero extension -/

/-- The degree-`n` subgroup of the integer shift.  A nonzero element belongs precisely when it
lies in a natural graded piece whose integer degree equals `n + d`; zero is retained when that
integer is negative. -/
def intShiftPiece (d : ℤ) (n : ℕ) : AddSubgroup M where
  carrier := {m | m = 0 ∨ ∃ k : ℕ, (k : ℤ) = (n : ℤ) + d ∧ m ∈ 𝓜 k}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | ⟨k, hk, hx⟩) (rfl | ⟨l, hl, hy⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨l, hl, by simpa using hy⟩
    · exact Or.inr ⟨k, hk, by simpa using hx⟩
    · have hkl : k = l := Int.ofNat_inj.mp (hk.trans hl.symm)
      subst l
      exact Or.inr ⟨k, hk, add_mem hx hy⟩
  neg_mem' := by
    rintro x (rfl | ⟨k, hk, hx⟩)
    · exact Or.inl (neg_zero)
    · exact Or.inr ⟨k, hk, neg_mem hx⟩

/-- The integer shift of a naturally graded module, using zero in negative degrees. -/
def intShift (d : ℤ) : ℕ → AddSubgroup M := fun n => intShiftPiece 𝓜 d n

@[simp]
theorem mem_intShiftPiece {d : ℤ} {n : ℕ} {m : M} :
    m ∈ intShiftPiece 𝓜 d n ↔
      m = 0 ∨ ∃ k : ℕ, (k : ℤ) = (n : ℤ) + d ∧ m ∈ 𝓜 k :=
  Iff.rfl

/-- A shifted graded piece below degree zero is trivial.

`intShift` is `ℕ`-indexed and `intShiftPiece 𝓜 d n` asks for an element of
degree `n + d`. When that integer is negative, no natural degree witnesses
membership, so only zero remains. -/
theorem intShiftPiece_eq_bot_of_neg {M σM : Type u} [AddCommGroup M]
    [SetLike σM M] [AddSubgroupClass σM M] (𝓜 : ℕ → σM) (d : ℤ) (n : ℕ)
    (hn : (n : ℤ) + d < 0) :
    intShiftPiece 𝓜 d n = ⊥ := by
  ext m
  simp only [AddSubgroup.mem_bot]
  constructor
  · rintro (h0 | ⟨j, hj, -⟩)
    · exact h0
    · exact absurd hj (by omega)
  · rintro rfl
    exact Or.inl rfl

instance intShiftGradedSMul (d : ℤ) : SetLike.GradedSMul 𝒜 (intShift 𝓜 d) where
  smul_mem {i j} {a m} ha hm := by
    rcases hm with rfl | ⟨k, hk, hm⟩
    · exact Or.inl (smul_zero a)
    · refine Or.inr ⟨i + k, ?_,
        SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝓜) ha hm⟩
      change ((i + k : ℕ) : ℤ) = ((i + j : ℕ) : ℤ) + d
      push_cast
      omega

@[simp]
theorem intShift_apply (d : ℤ) (n : ℕ) : intShift 𝓜 d n = intShiftPiece 𝓜 d n := rfl

/-- At shift zero the integer-shifted pieces are the original pieces, expressed as an equality
of their carriers. -/
theorem mem_intShift_zero_iff (n : ℕ) (m : M) :
    m ∈ intShift 𝓜 0 n ↔ m ∈ 𝓜 n := by
  constructor
  · rintro (rfl | ⟨k, hk, hm⟩)
    · exact zero_mem _
    · have hkn : k = n := Int.ofNat_inj.mp (by simpa using hk)
      simpa [hkn] using hm
  · intro hm
    exact Or.inr ⟨n, by simp, hm⟩

/-- A nonnegative integer shift agrees with the corresponding natural shift, at the level of
membership in each graded piece. -/
theorem mem_intShift_ofNat_iff (d n : ℕ) (m : M) :
    m ∈ intShift 𝓜 (d : ℤ) n ↔ m ∈ natShift 𝓜 d n := by
  constructor
  · rintro (rfl | ⟨k, hk, hm⟩)
    · exact zero_mem _
    · have hkn : k = n + d := Int.ofNat_inj.mp (by simpa using hk)
      simpa [natShift, hkn] using hm
  · intro hm
    exact Or.inr ⟨n + d, by simp, hm⟩

omit [AddCommGroup M] [AddSubgroupClass σM M] in
/-- Strict composition for nonnegative shifts, phrased as membership so it applies uniformly
even when the subobject types differ. -/
theorem mem_natShift_add_iff (d e n : ℕ) (m : M) :
    m ∈ natShift (natShift 𝓜 d) e n ↔ m ∈ natShift 𝓜 (d + e) n := by
  simp only [natShift_apply]
  rw [Nat.add_assoc, Nat.add_comm e d]

/-- **Integer shifts compose only where the intermediate degree exists**, and `hne` is exactly
that condition.

The unrestricted statement — `intShift (intShift 𝓜 d) e = intShift 𝓜 (d + e)` — is **false**, and
the hypothesis here is where it fails rather than a convenience. Shifting by a negative `e` first
asks for a graded piece in degree `n + e`; when that integer is negative the zero extension supplies
`0` and the information is gone, while the single shift by `d + e` may still land in a genuine
piece. Concretely, with `d = 10`, `e = -5` and `n = 0`, the left side is `{0}` because no natural
number has integer value `-5`, and the right side is `𝓜 5`.

This is a fact about the *algebraic* model, not about the sheaf. `associatedSheaf` only ever reads
these pieces through homogeneous localizations, where the missing degrees are inverted back in, so
the sheaf-level composition `O(d)(e) ≅ O(d + e)` is not obstructed by this — but it cannot be
obtained by transporting an algebraic identity, and has to be proved on the sheaf side. Recorded
here because that is the trap this lemma exists to mark. -/
theorem mem_intShift_add_iff_of_nonneg (d e : ℤ) (n : ℕ) (hne : 0 ≤ (n : ℤ) + e) (m : M) :
    m ∈ intShift (intShift 𝓜 d) e n ↔ m ∈ intShift 𝓜 (d + e) n := by
  constructor
  · rintro (rfl | ⟨k, hk, hm⟩)
    · exact Or.inl rfl
    · rcases hm with rfl | ⟨l, hl, hm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨l, by omega, hm⟩
  · rintro (rfl | ⟨l, hl, hm⟩)
    · exact Or.inl rfl
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (n : ℤ) + e :=
        ⟨((n : ℤ) + e).toNat, Int.toNat_of_nonneg hne⟩
      exact Or.inr ⟨k, hk, Or.inr ⟨l, by omega, hm⟩⟩

/-- **Below the intermediate degree the double shift is zero.** This is the failure
`mem_intShift_add_iff_of_nonneg`'s hypothesis avoids, as a theorem rather than a remark: an inner
shift by `e` asks for degree `n + e`, and no natural number has a negative integer value, so
nothing but zero survives.

Together with membership in the single shift — for instance any nonzero element of `𝓜 (n + d + e)`
when that degree is a natural number — this exhibits the two sides as different subgroups, which is
why no unrestricted composition lemma appears above. -/
theorem eq_zero_of_mem_intShift_intShift_of_neg (d e : ℤ) (n : ℕ) (hne : (n : ℤ) + e < 0)
    {m : M} (hm : m ∈ intShift (intShift 𝓜 d) e n) : m = 0 := by
  rcases hm with rfl | ⟨k, hk, _⟩
  · rfl
  · exact absurd hk (by omega)

omit [GradedRing 𝒜] in
/-- **Degree bookkeeping for the twisted multiplication.**

A ring element of the degree-`d` shift scales a module element of degree `j` into the degree-`d`
shift of the module. This is what makes `A(d) ⊗ M → M(d)` land where it should, and it is the
`SetLike.GradedSMul` analogue of the fact that `𝒜 i · 𝓜 j ⊆ 𝓜 (i + j)`. -/
theorem smul_mem_intShift (d : ℤ) (i j : ℕ) {a : A} {m : M}
    (ha : a ∈ intShift 𝒜 d i) (hm : m ∈ 𝓜 j) :
    a • m ∈ intShift 𝓜 d (i + j) := by
  simp only [intShift_apply, mem_intShiftPiece] at ha ⊢
  rcases ha with rfl | ⟨k, hk, ha⟩
  · exact Or.inl (zero_smul _ _)
  · refine Or.inr ⟨k + j, by push_cast at hk ⊢; omega, ?_⟩
    exact SetLike.GradedSMul.smul_mem ha hm

/-! ## The composition, at the localization

`mem_intShift_add_iff_of_nonneg` and `eq_zero_of_mem_intShift_intShift_of_neg` together say the
double shift and the single shift are genuinely different graded submodule families, and record
that the sheaf-level composition `O(d)(e) ≅ O(d + e)` therefore cannot be transported from an
algebraic identity. This section supplies the algebraic half of the replacement: at a localization
whose denominators contain a homogeneous element of positive degree, the two families have the
*same* degree-zero part, because the degrees the double shift truncates are inverted back in.

That is exactly the reading `Shift`'s note above predicted. What remains for the sheaf statement is
to carry this from one localization to the sections of the associated sheaf, and it is not here. -/

/-- The double shift always lands in the single shift.

Only the converse needs the degree bound of `mem_intShift_add_iff_of_nonneg`; this direction is
unconditional, so it is the one that gives a graded map without hypotheses. -/
theorem mem_intShift_add_of_mem_intShift_intShift (d e : ℤ) (n : ℕ) {m : M}
    (hm : m ∈ intShift (intShift 𝓜 d) e n) : m ∈ intShift 𝓜 (d + e) n := by
  rcases hm with rfl | ⟨k, hk, hm⟩
  · exact Or.inl rfl
  · rcases hm with rfl | ⟨l, hl, hm⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨l, by omega, hm⟩

/-- **The double shift and the single shift have the same degree-zero localization**, once the
denominators contain a homogeneous element `t` of positive degree.

One direction is `mem_intShift_add_of_mem_intShift_intShift` applied to the numerator; the other is
where the content is. A fraction certified only for `intShift 𝓜 (d + e)` is rewritten by
multiplying numerator and denominator by a power of `t`, which raises its degree without changing
the element, until the degree clears the bound `mem_intShift_add_iff_of_nonneg` asks for. This is
the precise sense in which the truncated degrees are "inverted back in": they are never needed at
a degree the localization cannot reach. -/
theorem isDegreeZero_intShift_intShift_iff (S : Submonoid A)
    {m : ℕ} (hm : 0 < m) {t : A} (ht : t ∈ 𝒜 m) (htS : t ∈ S) (d e : ℤ)
    (z : LocalizedModule S M) :
    IsDegreeZero 𝒜 (intShift (intShift 𝓜 d) e) S z ↔
      IsDegreeZero 𝒜 (intShift 𝓜 (d + e)) S z := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.deg, ⟨(c.num : M),
      mem_intShift_add_of_mem_intShift_intShift 𝓜 d e c.deg c.num.2⟩,
      c.den, c.den_mem⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    set k : ℕ := (-e).toNat with hk_def
    have hkm : (0 : ℤ) ≤ ((c.deg + k * m : ℕ) : ℤ) + e := by
      have h1 : -e ≤ (k : ℤ) := by rw [hk_def]; exact Int.self_le_toNat _
      have h2 : k * 1 ≤ k * m := Nat.mul_le_mul_left k hm
      push_cast
      omega
    refine ⟨⟨c.deg + k * m,
      ⟨t ^ k • (c.num : M), ?_⟩,
      ⟨t ^ k * (c.den : A), ?_⟩, ?_⟩, ?_⟩
    · refine (mem_intShift_add_iff_of_nonneg 𝓜 d e (c.deg + k * m) hkm _).mpr ?_
      have hnum : t ^ k • (c.num : M) ∈ intShift 𝓜 (d + e) (k * m + c.deg) :=
        SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded k ht) c.num.2
      rwa [add_comm (k * m) c.deg] at hnum
    · have hden : t ^ k * (c.den : A) ∈ 𝒜 (k * m + c.deg) :=
        SetLike.mul_mem_graded (SetLike.pow_mem_graded k ht) c.den.2
      rwa [add_comm (k * m) c.deg] at hden
    · exact Submonoid.mul_mem _ (Submonoid.pow_mem _ htS k) c.den_mem
    · show LocalizedModule.mk _ _ = LocalizedModule.mk _ _
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.mk_smul, smul_smul]
      rw [mul_comm]

end GradedModule
