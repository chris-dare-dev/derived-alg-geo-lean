/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.Coefficients

/-!
# Purity, the Gieseker order, and Gieseker (semi)stability

A coherent sheaf is Gieseker-semistable when no nonzero subsheaf has a larger reduced Hilbert
function for large `n`. This file defines purity, that order, the two stability predicates, and
proves the structural facts: the order is reflexive and transitive, it is decided by the
normalized coefficient vector read lexicographically from the top, and it is total on sheaves of
positive multiplicity.

## Which classical definition this is

With `IsPure` as a conjunct, `IsGiesekerSemistable` is Huybrechts–Lehn's Gieseker semistability
for a pure sheaf of dimension `P.dim`, with purity expressed through Hilbert multiplicity rather
than through dimension of support. The geometric equivalence of the two forms of purity is *not*
claimed: no dimension-of-support theory exists at this pin. The subsheaf quantifier is over
monomorphisms `G ⟶ F` throughout; the translation to `Subobject F` is made where it is needed,
in `MuStability.lean`, and is not mixed into the definitions here.

## Why purity is a conjunct and not an afterthought

`reducedHilbert P G` divides by `multiplicity P G` and takes Lean's junk value `0` when that is
zero. Without purity, every nonzero subsheaf of multiplicity zero would satisfy the order
relation vacuously, the predicate would fail to exclude exactly the subsheaves it exists to
exclude, and the comparison theorem of `MuStability.lean` would be false. Purity is definable
from `multiplicity` alone and needs no new geometry, so it belongs here.

## Why this is not a `StabilityFunctionOn`

Gieseker stability is ordered by a *polynomial*, compared at infinity; the repository's
`StabilityFunctionOn` is ordered by the argument of a complex charge in the upper half-plane.
There is no charge whose argument reproduces this order, and encoding a polynomial in a complex
number to force the two together would be a false unification of the kind
`docs/architecture/abstraction-tree.md` forbids. The comparison between the two theories happens
one level down, between *slopes*, and is proved in `MuStability.lean`.

## The numerical core

`eventually_nonneg_binomial_iff` is subject-neutral: an integer binomial sum is eventually
nonnegative exactly when its coefficient vector is lexicographically nonnegative from the top. It
is stated here, for its only consumer, rather than added to `Algebra/NumericalPolynomial/`; if a
second consumer appears it should move there. Its proof turns on *integrality*: a strictly
increasing integer sequence increases without bound, which is what upgrades "the difference is
eventually positive" to "the sum is eventually positive".
-/

universe u

open CategoryTheory Limits Finset Filter

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

/-! ### The numerical core: eventual sign of an integer binomial sum -/

/-- The binomial sum truncates at any index above which the coefficients vanish. -/
theorem sum_binomial_eq_of_vanishing {a : ℕ → ℤ} {J d : ℕ} (hJd : J ≤ d)
    (h : ∀ i, J < i → i ≤ d → a i = 0) (n : ℕ) :
    ∑ j ∈ range (d + 1), (n.choose j : ℤ) * a j =
      ∑ j ∈ range (J + 1), (n.choose j : ℤ) * a j := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro j hj hjJ
    simp only [Finset.mem_range] at hj hjJ
    rw [h j (by omega) (by omega), mul_zero]

/-- **One forward difference of a binomial sum shifts its coefficients down.** -/
theorem sum_binomial_succ_sub (a : ℕ → ℤ) (J n : ℕ) :
    (∑ j ∈ range (J + 1 + 1), ((n + 1).choose j : ℤ) * a j) -
        ∑ j ∈ range (J + 1 + 1), (n.choose j : ℤ) * a j =
      ∑ j ∈ range (J + 1), (n.choose j : ℤ) * a (j + 1) := by
  rw [Finset.sum_range_succ' (fun j ↦ ((n + 1).choose j : ℤ) * a j),
    Finset.sum_range_succ' (fun j ↦ (n.choose j : ℤ) * a j)]
  have hstep : ∀ j ∈ range (J + 1),
      ((n + 1).choose (j + 1) : ℤ) * a (j + 1) =
        (n.choose j : ℤ) * a (j + 1) + (n.choose (j + 1) : ℤ) * a (j + 1) := by
    intro j _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

/-- An integer sequence that eventually gains at least one per step is eventually positive.
This is where integrality enters, and it is what makes the binomial induction below close. -/
theorem eventually_pos_of_succ_le {c : ℕ → ℤ} {N : ℕ}
    (h : ∀ n, N ≤ n → c n + 1 ≤ c (n + 1)) : ∀ᶠ n : ℕ in atTop, 0 < c n := by
  have hgrow : ∀ m : ℕ, c N + m ≤ c (N + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hs := h (N + m) (Nat.le_add_right N m)
        have hNm : N + (m + 1) = N + m + 1 := by omega
        rw [hNm]
        push_cast
        linarith
  refine eventually_atTop.mpr ⟨N + (1 - c N).toNat, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
  have hmnat : (1 - c N).toNat ≤ m := by omega
  have hm : ((1 - c N).toNat : ℤ) ≤ (m : ℤ) := by exact_mod_cast hmnat
  have htoNat : (1 - c N) ≤ ((1 - c N).toNat : ℤ) := Int.self_le_toNat _
  have hg := hgrow m
  linarith

/-- **Integer binomial sums with a positive top coefficient are eventually positive.**

The induction is on the top index. One forward difference lowers it by one, so the inductive
hypothesis makes the sum eventually strictly increasing; `eventually_pos_of_succ_le` then turns
that into eventual positivity, using that the values are integers. -/
theorem eventually_pos_binomial_of_top_pos (J : ℕ) (a : ℕ → ℤ) (hJ : 0 < a J) :
    ∀ᶠ n : ℕ in atTop, 0 < ∑ j ∈ range (J + 1), (n.choose j : ℤ) * a j := by
  induction J generalizing a with
  | zero =>
      refine Eventually.of_forall fun n ↦ ?_
      simpa using hJ
  | succ J ih =>
      obtain ⟨N, hN⟩ := eventually_atTop.mp (ih (fun j ↦ a (j + 1)) hJ)
      refine eventually_pos_of_succ_le (c := fun n ↦
        ∑ j ∈ range (J + 1 + 1), (n.choose j : ℤ) * a j) (N := N) ?_
      intro n hn
      have hd : 0 < ∑ j ∈ range (J + 1), (n.choose j : ℤ) * a (j + 1) := hN n hn
      have hsub := sum_binomial_succ_sub a J n
      show (∑ j ∈ range (J + 1 + 1), (n.choose j : ℤ) * a j) + 1 ≤
        ∑ j ∈ range (J + 1 + 1), ((n + 1).choose j : ℤ) * a j
      omega

/-- The top index at which a coefficient vector supported in `range (d + 1)` is nonzero. -/
theorem exists_top_ne_zero {a : ℕ → ℤ} {d : ℕ} (h : ¬∀ j ≤ d, a j = 0) :
    ∃ J ≤ d, a J ≠ 0 ∧ ∀ i, J < i → i ≤ d → a i = 0 := by
  classical
  have hex : ∃ j, j ≤ d ∧ a j ≠ 0 := by
    by_contra hcon
    exact h fun j hj ↦ by
      by_contra haj
      exact hcon ⟨j, hj, haj⟩
  obtain ⟨j₀, hj₀d, hj₀⟩ := hex
  have hSne : ((range (d + 1)).filter (fun j ↦ a j ≠ 0)).Nonempty := by
    refine ⟨j₀, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hj₀⟩
  refine ⟨((range (d + 1)).filter (fun j ↦ a j ≠ 0)).max' hSne, ?_, ?_, ?_⟩
  · have hmem := Finset.max'_mem _ hSne
    rw [Finset.mem_filter, Finset.mem_range] at hmem
    omega
  · have hmem := Finset.max'_mem _ hSne
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  · intro i hi hid
    by_contra hai
    have hiS : i ∈ (range (d + 1)).filter (fun j ↦ a j ≠ 0) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hai⟩
    have hle := Finset.le_max' _ i hiS
    omega

/-- **The eventual sign of an integer binomial sum is decided lexicographically from the top.**

The sum is eventually nonnegative exactly when either every coefficient vanishes, or the highest
nonvanishing one is positive. -/
theorem eventually_nonneg_binomial_iff (a : ℕ → ℤ) (d : ℕ) :
    (∀ᶠ n : ℕ in atTop, 0 ≤ ∑ j ∈ range (d + 1), (n.choose j : ℤ) * a j) ↔
      ((∀ j ≤ d, a j = 0) ∨ ∃ J ≤ d, 0 < a J ∧ ∀ i, J < i → i ≤ d → a i = 0) := by
  constructor
  · intro hev
    by_cases hzero : ∀ j ≤ d, a j = 0
    · exact Or.inl hzero
    · obtain ⟨J, hJd, hJne, hJabove⟩ := exists_top_ne_zero hzero
      rcases lt_or_gt_of_ne hJne with hneg | hpos
      · exfalso
        have hnegpos : 0 < (fun j ↦ -a j) J := by simpa using hneg
        have hneg' := eventually_pos_binomial_of_top_pos J (fun j ↦ -a j) hnegpos
        have hsum : ∀ n : ℕ, ∑ j ∈ range (J + 1), (n.choose j : ℤ) * (-a j) =
            -∑ j ∈ range (d + 1), (n.choose j : ℤ) * a j := by
          intro n
          rw [sum_binomial_eq_of_vanishing hJd hJabove n, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
        obtain ⟨n, hn₁, hn₂⟩ := (hev.and hneg').exists
        have hn₂' : 0 < ∑ j ∈ range (J + 1), (n.choose j : ℤ) * (-a j) := hn₂
        rw [hsum n] at hn₂'
        omega
      · exact Or.inr ⟨J, hJd, hpos, hJabove⟩
  · rintro (hzero | ⟨J, hJd, hJpos, hJabove⟩)
    · refine Eventually.of_forall fun n ↦ ?_
      have hterm : ∀ j ∈ range (d + 1), (n.choose j : ℤ) * a j = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hzero j (by omega), mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero]
    · refine (eventually_pos_binomial_of_top_pos J a hJpos).mono fun n hn ↦ ?_
      rw [sum_binomial_eq_of_vanishing hJd hJabove n]
      exact hn.le

/-- The lexicographic criterion is total: one of the two coefficient vectors dominates. -/
theorem eventually_nonneg_binomial_total (a : ℕ → ℤ) (d : ℕ) :
    (∀ᶠ n : ℕ in atTop, 0 ≤ ∑ j ∈ range (d + 1), (n.choose j : ℤ) * a j) ∨
      (∀ᶠ n : ℕ in atTop, 0 ≤ ∑ j ∈ range (d + 1), (n.choose j : ℤ) * (-a j)) := by
  by_cases hzero : ∀ j ≤ d, a j = 0
  · exact Or.inl ((eventually_nonneg_binomial_iff a d).mpr (Or.inl hzero))
  · obtain ⟨J, hJd, hJne, hJabove⟩ := exists_top_ne_zero hzero
    rcases lt_or_gt_of_ne hJne with hneg | hpos
    · refine Or.inr ((eventually_nonneg_binomial_iff (fun j ↦ -a j) d).mpr
        (Or.inr ⟨J, hJd, ?_, ?_⟩))
      · show 0 < -a J
        omega
      · intro i hi hid
        show -a i = 0
        rw [hJabove i hi hid, neg_zero]
    · exact Or.inl ((eventually_nonneg_binomial_iff a d).mpr (Or.inr ⟨J, hJd, hpos, hJabove⟩))

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable (P : PolarizedVarietyData k X)

/-! ### Purity -/

/-- **Hilbert purity.** Every nonzero subsheaf has positive multiplicity, that is, full
`P.dim`-dimensional support in the Hilbert sense.

This is a definition, not a supplied `…Data` field. The geometric characterisation — no subsheaf
whose support has dimension below `P.dim` — is not proved here, because no dimension-of-support
theory exists at this pin. -/
def IsPure (F : Coh X) : Prop :=
  ¬IsZero F ∧ ∀ (G : Coh X) (i : G ⟶ F), Mono i → ¬IsZero G → 0 < P.multiplicity G

variable {P}

/-- A pure sheaf has positive multiplicity, by testing purity against its own identity. -/
theorem IsPure.multiplicity_pos {F : Coh X} (h : P.IsPure F) : 0 < P.multiplicity F :=
  h.2 F (𝟙 F) inferInstance h.1

theorem IsPure.not_isZero {F : Coh X} (h : P.IsPure F) : ¬IsZero F := h.1

/-- Purity is invariant under isomorphism. -/
theorem IsPure.of_iso {F G : Coh X} (h : P.IsPure F) (e : F ≅ G) : P.IsPure G := by
  refine ⟨fun hG ↦ h.1 (hG.of_iso e), fun H i hi hH ↦ ?_⟩
  haveI := hi
  exact h.2 H (i ≫ e.inv) (mono_comp i e.inv) hH

variable (P)

/-! ### The Gieseker order -/

/-- **The Gieseker order**: the reduced Hilbert function of `F` is eventually at most that of
`G`. No `Preorder` instance is registered on `Coh X`; this is a relation, used as one. -/
def GiesekerLE (F G : Coh X) : Prop :=
  ∀ᶠ n : ℕ in atTop, P.reducedHilbert F n ≤ P.reducedHilbert G n

theorem giesekerLE_refl (F : Coh X) : P.GiesekerLE F F :=
  Eventually.of_forall fun _ ↦ le_rfl

theorem giesekerLE_trans {F G H : Coh X} (h₁ : P.GiesekerLE F G) (h₂ : P.GiesekerLE G H) :
    P.GiesekerLE F H :=
  (h₁.and h₂).mono fun _ h ↦ h.1.trans h.2

/-- The reduced Hilbert function is an isomorphism invariant. -/
theorem reducedHilbert_eq_of_iso {F G : Coh X} (e : F ≅ G) :
    P.reducedHilbert F = P.reducedHilbert G := by
  funext n
  rw [reducedHilbert_apply, reducedHilbert_apply, P.hilbertFunction_eq_of_iso e,
    P.multiplicity_eq_of_iso e]

/-- Isomorphic sheaves are Gieseker-comparable. -/
theorem giesekerLE_of_iso {F G : Coh X} (e : F ≅ G) : P.GiesekerLE F G := by
  have hEq : P.reducedHilbert F = P.reducedHilbert G := P.reducedHilbert_eq_of_iso e
  exact Eventually.of_forall fun n ↦ by rw [hEq]

/-- **Strict Gieseker order.** -/
def GiesekerLT (F G : Coh X) : Prop := P.GiesekerLE F G ∧ ¬P.GiesekerLE G F

theorem giesekerLT_irrefl (F : Coh X) : ¬P.GiesekerLT F F := fun h ↦ h.2 h.1

theorem giesekerLT_trans {F G H : Coh X} (h₁ : P.GiesekerLT F G) (h₂ : P.GiesekerLT G H) :
    P.GiesekerLT F H :=
  ⟨P.giesekerLE_trans h₁.1 h₂.1, fun hHF ↦ h₁.2 (P.giesekerLE_trans h₂.1 hHF)⟩

/-! ### The lexicographic coefficient criterion -/

/-- The Hilbert coefficient vector normalized by the multiplicity. Its top entry is `1` for every
sheaf of positive multiplicity, which is why the Gieseker comparison always drops to the entry
below the top. -/
noncomputable def normalizedCoefficient (F : Coh X) (j : ℕ) : ℚ :=
  (P.hilbertCoefficient F j : ℚ) / (P.multiplicity F : ℚ)

/-- **The lexicographic order on normalized coefficient vectors**, read from `j = P.dim` down. -/
def CoeffLexLE (F G : Coh X) : Prop :=
  (∀ j ≤ P.dim, P.normalizedCoefficient F j = P.normalizedCoefficient G j) ∨
    ∃ J ≤ P.dim, P.normalizedCoefficient F J < P.normalizedCoefficient G J ∧
      ∀ i, J < i → i ≤ P.dim → P.normalizedCoefficient F i = P.normalizedCoefficient G i

/-- The integer coefficient whose sign decides the Gieseker comparison at index `j`. -/
noncomputable def lexDiff (F G : Coh X) (j : ℕ) : ℤ :=
  P.multiplicity F * P.hilbertCoefficient G j - P.multiplicity G * P.hilbertCoefficient F j

theorem lexDiff_swap (F G : Coh X) (j : ℕ) : P.lexDiff G F j = -P.lexDiff F G j := by
  rw [lexDiff, lexDiff]; ring

variable {P}

theorem normalizedCoefficient_le_iff {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) (j : ℕ) :
    P.normalizedCoefficient F j ≤ P.normalizedCoefficient G j ↔ 0 ≤ P.lexDiff F G j := by
  have hFq : (0 : ℚ) < (P.multiplicity F : ℚ) := by exact_mod_cast hF
  have hGq : (0 : ℚ) < (P.multiplicity G : ℚ) := by exact_mod_cast hG
  rw [normalizedCoefficient, normalizedCoefficient, div_le_div_iff₀ hFq hGq, lexDiff, sub_nonneg]
  constructor
  · intro hle
    have hq : ((P.multiplicity G * P.hilbertCoefficient F j : ℤ) : ℚ) ≤
        ((P.multiplicity F * P.hilbertCoefficient G j : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast hq
  · intro hle
    have hq : ((P.multiplicity G * P.hilbertCoefficient F j : ℤ) : ℚ) ≤
        ((P.multiplicity F * P.hilbertCoefficient G j : ℤ) : ℚ) := by exact_mod_cast hle
    push_cast at hq
    linarith

theorem normalizedCoefficient_eq_iff {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) (j : ℕ) :
    P.normalizedCoefficient F j = P.normalizedCoefficient G j ↔ P.lexDiff F G j = 0 := by
  rw [le_antisymm_iff, normalizedCoefficient_le_iff hF hG j,
    normalizedCoefficient_le_iff hG hF j, P.lexDiff_swap F G j]
  omega

theorem normalizedCoefficient_lt_iff {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) (j : ℕ) :
    P.normalizedCoefficient F j < P.normalizedCoefficient G j ↔ 0 < P.lexDiff F G j := by
  rw [← not_le, ← not_le, normalizedCoefficient_le_iff hG hF j, P.lexDiff_swap F G j]
  omega

/-- The Gieseker comparison at a single `n`, cross-multiplied into an integer binomial sum. -/
theorem reducedHilbert_le_iff_sum {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) (n : ℕ) :
    P.reducedHilbert F n ≤ P.reducedHilbert G n ↔
      0 ≤ ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * P.lexDiff F G j := by
  have hFq : (0 : ℚ) < (P.multiplicity F : ℚ) := by exact_mod_cast hF
  have hGq : (0 : ℚ) < (P.multiplicity G : ℚ) := by exact_mod_cast hG
  have hsum : ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * P.lexDiff F G j =
      P.multiplicity F * P.hilbertFunction G n - P.multiplicity G * P.hilbertFunction F n := by
    rw [P.hilbertFunction_eq_sum_choose F n, P.hilbertFunction_eq_sum_choose G n,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [lexDiff]; ring
  rw [reducedHilbert_apply, reducedHilbert_apply, div_le_div_iff₀ hFq hGq, hsum, sub_nonneg]
  constructor
  · intro hle
    have hq : ((P.multiplicity G * P.hilbertFunction F n : ℤ) : ℚ) ≤
        ((P.multiplicity F * P.hilbertFunction G n : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast hq
  · intro hle
    have hq : ((P.multiplicity G * P.hilbertFunction F n : ℤ) : ℚ) ≤
        ((P.multiplicity F * P.hilbertFunction G n : ℤ) : ℚ) := by exact_mod_cast hle
    push_cast at hq
    linarith

/-- **The lexicographic coefficient criterion.** For sheaves of positive multiplicity, the
Gieseker order is exactly the lexicographic order on normalized coefficient vectors read from the
top. The proof compares the two Gregory–Newton sums delivered by `Coefficients.lean`. -/
theorem giesekerLE_iff_coeffLexLE {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) :
    P.GiesekerLE F G ↔ P.CoeffLexLE F G := by
  have hiff : P.GiesekerLE F G ↔
      ∀ᶠ n : ℕ in atTop, 0 ≤ ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * P.lexDiff F G j :=
    eventually_congr (Eventually.of_forall fun n ↦ reducedHilbert_le_iff_sum hF hG n)
  rw [hiff, eventually_nonneg_binomial_iff]
  constructor
  · rintro (hzero | ⟨J, hJd, hJpos, hJabove⟩)
    · exact Or.inl fun j hj ↦ (normalizedCoefficient_eq_iff hF hG j).mpr (hzero j hj)
    · exact Or.inr ⟨J, hJd, (normalizedCoefficient_lt_iff hF hG J).mpr hJpos,
        fun i hi hid ↦ (normalizedCoefficient_eq_iff hF hG i).mpr (hJabove i hi hid)⟩
  · rintro (hzero | ⟨J, hJd, hJlt, hJabove⟩)
    · exact Or.inl fun j hj ↦ (normalizedCoefficient_eq_iff hF hG j).mp (hzero j hj)
    · exact Or.inr ⟨J, hJd, (normalizedCoefficient_lt_iff hF hG J).mp hJlt,
        fun i hi hid ↦ (normalizedCoefficient_eq_iff hF hG i).mp (hJabove i hi hid)⟩

/-- **Totality on sheaves of positive multiplicity**, a corollary of the criterion. -/
theorem giesekerLE_total {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) : P.GiesekerLE F G ∨ P.GiesekerLE G F := by
  have hiffF : P.GiesekerLE F G ↔
      ∀ᶠ n : ℕ in atTop, 0 ≤ ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * P.lexDiff F G j :=
    eventually_congr (Eventually.of_forall fun n ↦ reducedHilbert_le_iff_sum hF hG n)
  have hiffG : P.GiesekerLE G F ↔
      ∀ᶠ n : ℕ in atTop,
        0 ≤ ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * (-P.lexDiff F G j) := by
    refine eventually_congr (Eventually.of_forall fun n ↦ ?_)
    have hcongr : ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * P.lexDiff G F j =
        ∑ j ∈ range (P.dim + 1), (n.choose j : ℤ) * (-P.lexDiff F G j) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [P.lexDiff_swap F G j]
    rw [reducedHilbert_le_iff_sum hG hF n, hcongr]
  rcases eventually_nonneg_binomial_total (P.lexDiff F G) P.dim with hpos | hneg
  · exact Or.inl (hiffF.mpr hpos)
  · exact Or.inr (hiffG.mpr hneg)

/-- The normalized coefficient at the top index is `1` for every sheaf of positive
multiplicity. This is why the Gieseker comparison always drops to the index below the top. -/
theorem normalizedCoefficient_dim {F : Coh X} (hF : 0 < P.multiplicity F) :
    P.normalizedCoefficient F P.dim = 1 := by
  have hne : (P.multiplicity F : ℚ) ≠ 0 := by exact_mod_cast hF.ne'
  have htop : P.hilbertCoefficient F P.dim = P.multiplicity F := rfl
  rw [normalizedCoefficient, htop]
  exact div_self hne

/-- **The Gieseker comparison always drops to the index below the top.**

At `j = P.dim` both normalized coefficients are `1`, so the lexicographic comparison can never be
decided there; whatever it decides, the entry at `P.dim - 1` is comparable in the same direction.
That entry is the slope, which is why this is the bridge to the weak slope theory. -/
theorem normalizedCoefficient_pred_le_of_giesekerLE {F G : Coh X} (hF : 0 < P.multiplicity F)
    (hG : 0 < P.multiplicity G) (hle : P.GiesekerLE F G) :
    P.normalizedCoefficient F (P.dim - 1) ≤ P.normalizedCoefficient G (P.dim - 1) := by
  rcases (giesekerLE_iff_coeffLexLE hF hG).mp hle with hzero | ⟨J, hJd, hJlt, hJabove⟩
  · exact le_of_eq (hzero (P.dim - 1) (by omega))
  · rcases lt_trichotomy J (P.dim - 1) with hJ | hJ | hJ
    · exact le_of_eq (hJabove (P.dim - 1) hJ (by omega))
    · exact hJ ▸ hJlt.le
    · exfalso
      have hJdim : J = P.dim := by omega
      rw [hJdim, normalizedCoefficient_dim hF, normalizedCoefficient_dim hG] at hJlt
      exact lt_irrefl 1 hJlt

variable (P)

/-! ### Gieseker semistability and stability -/

/-- **Gieseker semistability**: a pure sheaf no nonzero subsheaf of which has eventually larger
reduced Hilbert function. Purity is a conjunct, so every `G` reaching the quantifier has positive
multiplicity and its reduced Hilbert function is never the junk value. -/
def IsGiesekerSemistable (F : Coh X) : Prop :=
  P.IsPure F ∧ ∀ (G : Coh X) (i : G ⟶ F), Mono i → ¬IsZero G → P.GiesekerLE G F

/-- **Gieseker stability**: the strict form, on subsheaves that are not isomorphisms onto `F`. -/
def IsGiesekerStable (F : Coh X) : Prop :=
  P.IsPure F ∧ ∀ (G : Coh X) (i : G ⟶ F), Mono i → ¬IsZero G → ¬IsIso i → P.GiesekerLT G F

variable {P}

theorem IsGiesekerSemistable.isPure {F : Coh X} (h : P.IsGiesekerSemistable F) : P.IsPure F :=
  h.1

theorem IsGiesekerSemistable.multiplicity_pos {F : Coh X} (h : P.IsGiesekerSemistable F) :
    0 < P.multiplicity F :=
  h.1.multiplicity_pos

theorem IsGiesekerSemistable.not_isZero {F : Coh X} (h : P.IsGiesekerSemistable F) : ¬IsZero F :=
  h.1.1

/-- A stable sheaf is semistable: a subsheaf that is an isomorphism onto `F` is comparable by
transport along that isomorphism, and every other one by the strict order. -/
theorem IsGiesekerStable.isGiesekerSemistable {F : Coh X} (h : P.IsGiesekerStable F) :
    P.IsGiesekerSemistable F := by
  refine ⟨h.1, fun G i hi hG ↦ ?_⟩
  by_cases hiso : IsIso i
  · haveI := hiso
    exact P.giesekerLE_of_iso (asIso i)
  · exact (h.2 G i hi hG hiso).1

/-- The zero sheaf is not Gieseker-semistable, because it is not pure. -/
theorem not_isGiesekerSemistable_of_isZero {F : Coh X} (hF : IsZero F) :
    ¬P.IsGiesekerSemistable F :=
  fun h ↦ h.1.1 hF

theorem not_isGiesekerStable_of_isZero {F : Coh X} (hF : IsZero F) : ¬P.IsGiesekerStable F :=
  fun h ↦ h.1.1 hF

/-- Gieseker semistability is invariant under isomorphism. -/
theorem IsGiesekerSemistable.of_iso {F G : Coh X} (h : P.IsGiesekerSemistable F) (e : F ≅ G) :
    P.IsGiesekerSemistable G := by
  refine ⟨h.1.of_iso e, fun H i hi hH ↦ ?_⟩
  haveI := hi
  exact P.giesekerLE_trans (h.2 H (i ≫ e.inv) (mono_comp i e.inv) hH) (P.giesekerLE_of_iso e)

/-- Gieseker stability is invariant under isomorphism. -/
theorem IsGiesekerStable.of_iso {F G : Coh X} (h : P.IsGiesekerStable F) (e : F ≅ G) :
    P.IsGiesekerStable G := by
  refine ⟨h.1.of_iso e, fun H i hi hH hiso ↦ ?_⟩
  haveI := hi
  have hnotiso : ¬IsIso (i ≫ e.inv) := by
    intro hcon
    haveI := hcon
    have hcomp : IsIso ((i ≫ e.inv) ≫ e.hom) := inferInstance
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hcomp
    exact hiso hcomp
  have hlt := h.2 H (i ≫ e.inv) (mono_comp i e.inv) hH hnotiso
  refine ⟨P.giesekerLE_trans hlt.1 (P.giesekerLE_of_iso e), fun hcon ↦ ?_⟩
  exact hlt.2 (P.giesekerLE_trans (P.giesekerLE_of_iso e) hcon)

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
