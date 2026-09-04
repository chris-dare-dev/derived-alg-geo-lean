/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.HNPolygon
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin.Rotate

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Convex-polygon perimeter comparison

This file isolates the Euclidean (`t = 0`) polygon comparison used in
Ikeda's Lemma 3.7.  The proof is finite-dimensional: supporting functionals
select a monotone subsequence of the outer boundary, and discrete integration
by parts reduces the perimeter comparison to the triangle inequality.
-/

open CategoryTheory.Triangulated
open Complex
open scoped BigOperators ComplexConjugate

namespace CategoryTheory.Triangulated.ComplexPolygonalPath

noncomputable section

/-- The Euclidean scalar product with `r`, bundled as a continuous
real-linear functional. -/
def dotFunctional (r : ℂ) : ℂ →L[ℝ] ℝ :=
  r.re • Complex.reCLM + r.im • Complex.imCLM

@[simp]
theorem dotFunctional_apply (r z : ℂ) :
    dotFunctional r z = r.re * z.re + r.im * z.im := by
  simp [dotFunctional]

/-- The direction of a vector, with the zero vector assigned direction zero. -/
def unitDirection (z : ℂ) : ℂ :=
  (↑(‖z‖⁻¹ : ℝ) : ℂ) * z

theorem norm_unitDirection_le_one (z : ℂ) : ‖unitDirection z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [unitDirection, hz]
  · rw [unitDirection, norm_mul, norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem dotFunctional_unitDirection_self (z : ℂ) :
    dotFunctional (unitDirection z) z = ‖z‖ := by
  by_cases hz : z = 0
  · simp [unitDirection, hz]
  · rw [dotFunctional_apply, unitDirection]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im, add_zero]
    rw [show ‖z‖⁻¹ * z.re * z.re + ‖z‖⁻¹ * z.im * z.im =
      ‖z‖⁻¹ * (z.re * z.re + z.im * z.im) by ring]
    rw [show z.re * z.re + z.im * z.im = ‖z‖ ^ 2 by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]]
    field_simp

/-- A nonzero vector's normalized direction is the unit ray at its principal
argument. -/
theorem unitDirection_eq_unitRay_arg {z : ℂ} (hz : z ≠ 0) :
    unitDirection z = unitRay (Complex.arg z) := by
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  apply Complex.ext
  · simp only [unitDirection, mul_re, ofReal_re, ofReal_im, zero_mul,
      sub_zero, unitRay_re]
    rw [← Complex.norm_mul_cos_arg]
    field_simp
  · simp only [unitDirection, mul_im, ofReal_re, ofReal_im, zero_mul,
      add_zero, unitRay_im]
    rw [← Complex.norm_mul_sin_arg]
    field_simp

/-- Cauchy--Schwarz in the concrete scalar-product notation used below. -/
theorem dotFunctional_le_norm_mul (r z : ℂ) :
    dotFunctional r z ≤ ‖r‖ * ‖z‖ := by
  rw [dotFunctional_apply]
  have hre := Complex.re_le_norm (starRingEnd ℂ r * z)
  rw [Complex.mul_re] at hre
  change (conj r).re * z.re - (conj r).im * z.im ≤ ‖conj r * z‖ at hre
  rw [conj_re, conj_im, norm_mul, norm_conj] at hre
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hre

theorem dotFunctional_sub_left (r s z : ℂ) :
    dotFunctional (r - s) z = dotFunctional r z - dotFunctional s z := by
  simp [dotFunctional_apply]
  ring

theorem dotFunctional_sub_right (r z w : ℂ) :
    dotFunctional r (z - w) = dotFunctional r z - dotFunctional r w := by
  exact map_sub (dotFunctional r) z w

/-- The turn between two unit rays is a positive multiple of the cross
functional at their angular bisector. -/
theorem dotFunctional_unitRay_sub (a b : ℝ) (z : ℂ) :
    dotFunctional (unitRay a - unitRay b) z =
      (2 * Real.sin ((a - b) / 2)) *
        crossFunctional (unitRay ((a + b) / 2)) z := by
  simp only [dotFunctional_apply, sub_re, sub_im, unitRay_re, unitRay_im,
    crossFunctional_apply]
  rw [Real.cos_sub_cos, Real.sin_sub_sin]
  ring

/-- Length from a fixed initial point through a list of subsequent vertices. -/
private def chainLengthFrom (x : ℂ) : List ℂ → ℝ
  | [] => 0
  | y :: ys => ‖y - x‖ + chainLengthFrom y ys

/-- Length of a list viewed as a polygonal chain. -/
def chainLength : List ℂ → ℝ
  | [] => 0
  | x :: xs => chainLengthFrom x xs

@[simp] theorem chainLength_nil : chainLength [] = 0 := rfl
@[simp] theorem chainLength_singleton (x : ℂ) : chainLength [x] = 0 := rfl
@[simp] theorem chainLength_cons_cons (x y : ℂ) (xs : List ℂ) :
    chainLength (x :: y :: xs) = ‖y - x‖ + chainLength (y :: xs) := rfl

/-- Inserting an extra initial vertex cannot shorten the route from a fixed
anchor point through a chain. -/
private theorem chainLength_insert_front (a b : ℂ) (xs : List ℂ) :
    chainLengthFrom a xs ≤ ‖b - a‖ + chainLengthFrom b xs := by
  cases xs with
  | nil => simp [chainLengthFrom]
  | cons x xs =>
      simp only [chainLengthFrom]
      have h := norm_add_le (b - a) (x - b)
      rw [show b - a + (x - b) = x - a by ring] at h
      linarith

private theorem chainLengthFrom_mono_sublist (a : ℂ) {xs ys : List ℂ}
    (h : List.Sublist xs ys) : chainLengthFrom a xs ≤ chainLengthFrom a ys := by
  induction h generalizing a with
  | slnil => simp [chainLengthFrom]
  | cons b h ih =>
      exact (ih a).trans (chainLength_insert_front a b _)
  | cons_cons b h ih =>
      simpa only [chainLengthFrom, add_le_add_iff_left] using ih b

private theorem chainLength_le_cons (a : ℂ) (xs : List ℂ) :
    chainLength xs ≤ chainLength (a :: xs) := by
  cases xs with
  | nil => simp [chainLength, chainLengthFrom]
  | cons x xs =>
      simp only [chainLength_cons_cons]
      exact le_add_of_nonneg_left (norm_nonneg _)

/-- Polygonal-chain length is monotone under taking a sublist.  This is the
finite triangle inequality in the exact form needed for monotone support
selectors. -/
theorem chainLength_mono_sublist {xs ys : List ℂ} (h : List.Sublist xs ys) :
    chainLength xs ≤ chainLength ys := by
  induction h with
  | slnil => simp [chainLength]
  | cons a h ih =>
      exact ih.trans (chainLength_le_cons a _)
  | cons_cons a h ih =>
      exact chainLengthFrom_mono_sublist a h

/-- Removing consecutive repetitions before applying a vertex map does not
change polygonal-chain length. -/
private theorem destutter'_ne_eq_cons {I : Type*} [DecidableEq I]
    (a : I) : ∀ xs : List I, ∃ ys, xs.destutter' (· ≠ ·) a = a :: ys := by
  intro xs
  induction xs generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b xs ih =>
      rw [List.destutter']
      by_cases hab : a ≠ b
      · rw [if_pos hab]
        exact ⟨xs.destutter' (· ≠ ·) b, rfl⟩
      · rw [if_neg hab]
        exact ih a

private theorem chainLength_map_destutter_ne {I : Type*} [DecidableEq I]
    (f : I → ℂ) : ∀ xs : List I,
    chainLength ((xs.destutter (· ≠ ·)).map f) = chainLength (xs.map f) := by
  intro xs
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih ih₂ =>
      rw [List.destutter_cons_cons]
      by_cases hab : a ≠ b
      · rw [if_pos hab]
        change chainLength (f a :: ((b :: xs).destutter (· ≠ ·)).map f) =
          chainLength (f a :: f b :: xs.map f)
        obtain ⟨ys, hys⟩ := destutter'_ne_eq_cons b xs
        have hhead : ((b :: xs).destutter (· ≠ ·)).map f = f b :: ys.map f := by
          rw [List.destutter_cons']
          rw [hys]
          rfl
        rw [hhead]
        simp only [chainLength_cons_cons]
        have hi := ih₂ b
        rw [hhead] at hi
        exact congrArg (fun t ↦ ‖f b - f a‖ + t) hi
      · rw [if_neg hab]
        have hab' : a = b := Classical.not_not.mp hab
        subst b
        change chainLength (((a :: xs).destutter (· ≠ ·)).map f) =
          chainLength (f a :: f a :: xs.map f)
        rw [ih₂ a]
        simp [chainLength, chainLengthFrom]

/-- A monotone choice of vertices gives a chain no longer than the original
finite chain.  Repeated choices are harmless and are removed by `destutter`.
-/
theorem chainLength_comp_monotone_le {n m : ℕ} (w : Fin (m + 1) → ℂ)
    (q : Fin (n + 1) → Fin (m + 1)) (hq : Monotone q) :
    chainLength (List.ofFn fun i ↦ w (q i)) ≤ chainLength (List.ofFn w) := by
  let qs : List (Fin (m + 1)) := List.ofFn q
  have hsorted : qs.SortedLE := by
    exact hq.sortedLE_ofFn
  have hdedup : qs.destutter (· ≠ ·) = qs.dedup :=
    hsorted.pairwise.destutter_eq_dedup
  have hsub : List.Sublist qs.dedup (List.ofFn (id : Fin (m + 1) → Fin (m + 1))) := by
    apply List.sublist_of_subperm_of_sortedLE
    · exact (List.nodup_dedup qs).subperm (by
        intro i hi
        simp only [List.mem_ofFn]
        exact ⟨i, rfl⟩)
    · exact (List.Pairwise.sublist (List.dedup_sublist qs) hsorted.pairwise).sortedLE
    · exact monotone_id.sortedLE_ofFn
  have hmap := chainLength_mono_sublist (hsub.map w)
  calc
    chainLength (List.ofFn fun i ↦ w (q i)) = chainLength (qs.map w) := by
      simp [qs, List.ofFn_comp']
    _ = chainLength ((qs.destutter (· ≠ ·)).map w) :=
      (chainLength_map_destutter_ne w qs).symm
    _ = chainLength (qs.dedup.map w) := by rw [hdedup]
    _ ≤ chainLength ((List.ofFn (id : Fin (m + 1) → Fin (m + 1))).map w) := hmap
    _ = chainLength (List.ofFn w) := by simp [List.ofFn_comp']

/-- The list and `Fin` presentations of an open polygonal path have the same
length. -/
theorem chainLength_ofFn_eq_length {n : ℕ} (z : Fin (n + 1) → ℂ) :
    chainLength (List.ofFn z) = length z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [chainLength]
      rw [List.ofFn_succ]
      simp only [chainLengthFrom]
      unfold length
      rw [Fin.sum_univ_succ]
      congr 1
      have htail := ih (fun i : Fin (n + 1) ↦ z i.succ)
      unfold length at htail
      simpa only [List.ofFn_succ, chainLength, chainLengthFrom,
        Fin.castSucc_succ] using htail

/-- The cyclic edge leaving a vertex; the last vertex is joined back to the
first by `finRotate`. -/
def closedEdge {n : ℕ} (z : Fin (n + 1) → ℂ) (i : Fin (n + 1)) : ℂ :=
  z (finRotate (n + 1) i) - z i

/-- The perimeter of the closed polygonal chain obtained by adjoining the
last-to-first chord. -/
def closedLength {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i : Fin (n + 1), ‖closedEdge z i‖

/-- The unit direction of a cyclic edge. -/
def closedTangent {n : ℕ} (z : Fin (n + 1) → ℂ) (i : Fin (n + 1)) : ℂ :=
  unitDirection (closedEdge z i)

/-- The outward turning functional at a cyclic vertex. -/
def turningFunctional {n : ℕ} (z : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    ℂ →L[ℝ] ℝ :=
  dotFunctional (closedTangent z ((finRotate (n + 1)).symm i) - closedTangent z i)

private theorem sum_dot_turning_eq {n : ℕ} (t x : Fin (n + 1) → ℂ) :
    (∑ i : Fin (n + 1),
        dotFunctional (t ((finRotate (n + 1)).symm i) - t i) (x i)) =
      ∑ i : Fin (n + 1), dotFunctional (t i) (x (finRotate (n + 1) i) - x i) := by
  have hreindex :
      (∑ i : Fin (n + 1), dotFunctional (t ((finRotate (n + 1)).symm i)) (x i)) =
        ∑ i : Fin (n + 1), dotFunctional (t i) (x (finRotate (n + 1) i)) := by
    simpa using (Equiv.sum_comp (finRotate (n + 1))
      (fun i ↦ dotFunctional (t ((finRotate (n + 1)).symm i)) (x i))).symm
  simp_rw [dotFunctional_sub_left, dotFunctional_sub_right]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hreindex]

/-- A closed perimeter is its discrete support sum.  This is the finite
integration-by-parts identity behind the comparison theorem. -/
theorem closedLength_eq_sum_turning {n : ℕ} (z : Fin (n + 1) → ℂ) :
    closedLength z = ∑ i : Fin (n + 1), turningFunctional z i (z i) := by
  calc
    closedLength z = ∑ i : Fin (n + 1),
        dotFunctional (closedTangent z i) (closedEdge z i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (dotFunctional_unitDirection_self (closedEdge z i)).symm
    _ = ∑ i : Fin (n + 1),
        (dotFunctional (closedTangent z i) (z (finRotate (n + 1) i)) -
          dotFunctional (closedTangent z i) (z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact dotFunctional_sub_right _ _ _
    _ = ∑ i : Fin (n + 1), turningFunctional z i (z i) := by
      simp_rw [← dotFunctional_sub_right]
      rw [← sum_dot_turning_eq]
      rfl

/-- Closing an open path adds exactly its endpoint chord. -/
theorem closedLength_eq_length_add_chord {n : ℕ} (z : Fin (n + 1) → ℂ) :
    closedLength z = length z + ‖z 0 - z (Fin.last n)‖ := by
  unfold closedLength length closedEdge
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hne : i.castSucc ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    have hrot : finRotate (n + 1) i.castSucc = i.succ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hne]
      rfl
    rw [hrot]
  · rw [finRotate_last]

/-- Appending one terminal vertex appends exactly one edge to an open
polygonal path. -/
theorem length_snoc {n : ℕ} (z : Fin (n + 1) → ℂ) (a : ℂ) :
    length (Fin.snoc z a) = length z + ‖a - z (Fin.last n)‖ := by
  unfold length
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl]
    simp only [Fin.snoc_castSucc]
  · rw [show (Fin.last n).succ = Fin.last (n + 1) by apply Fin.ext; simp]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]

/-- A monotone vertex selector preserving the two endpoints cannot increase
closed perimeter. -/
theorem closedLength_comp_monotone_le {n m : ℕ} (w : Fin (m + 1) → ℂ)
    (q : Fin (n + 1) → Fin (m + 1)) (hq : Monotone q)
    (hq₀ : q 0 = 0) (hq_last : q (Fin.last n) = Fin.last m) :
    closedLength (fun i ↦ w (q i)) ≤ closedLength w := by
  rw [closedLength_eq_length_add_chord, closedLength_eq_length_add_chord]
  have hopen := chainLength_comp_monotone_le w q hq
  rw [chainLength_ofFn_eq_length, chainLength_ofFn_eq_length] at hopen
  rw [hq₀, hq_last]
  exact add_le_add hopen le_rfl

/-- **Finite support-fan perimeter comparison.** If each turning functional
of a closed inner chain is no larger at its inner vertex than at a monotone
choice of outer vertices, then the inner perimeter is no larger than the
outer perimeter. -/
theorem closedLength_le_of_monotone_support {n m : ℕ}
    (z : Fin (n + 1) → ℂ) (w : Fin (m + 1) → ℂ)
    (q : Fin (n + 1) → Fin (m + 1)) (hq : Monotone q)
    (hq₀ : q 0 = 0) (hq_last : q (Fin.last n) = Fin.last m)
    (hsupport : ∀ i, turningFunctional z i (z i) ≤
      turningFunctional z i (w (q i))) :
    closedLength z ≤ closedLength w := by
  rw [closedLength_eq_sum_turning]
  calc
    ∑ i : Fin (n + 1), turningFunctional z i (z i) ≤
        ∑ i : Fin (n + 1), turningFunctional z i (w (q i)) := by
      exact Finset.sum_le_sum fun i _ ↦ hsupport i
    _ = ∑ i : Fin (n + 1), dotFunctional (closedTangent z i)
          (w (q (finRotate (n + 1) i)) - w (q i)) := by
      exact sum_dot_turning_eq (closedTangent z) (fun i ↦ w (q i))
    _ ≤ ∑ i : Fin (n + 1), ‖w (q (finRotate (n + 1) i)) - w (q i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (dotFunctional_le_norm_mul _ _).trans
      have ht : ‖closedTangent z i‖ ≤ 1 :=
        norm_unitDirection_le_one (closedEdge z i)
      exact mul_le_of_le_one_left (norm_nonneg _) ht
    _ = closedLength (fun i ↦ w (q i)) := by rfl
    _ ≤ closedLength w := closedLength_comp_monotone_le w q hq hq₀ hq_last

/-- A nonempty path all of whose edges lie in the semi-closed upper
half-plane has endpoint displacement in that half-plane. -/
theorem last_sub_zero_mem_semiClosedUpperHalfPlane {n : ℕ} (hn : 0 < n)
    (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane) :
    z (Fin.last n) - z 0 ∈ semiClosedUpperHalfPlane := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn₀ : n = 0
      · subst n
        simpa using hedge (0 : Fin 1)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn₀
        let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
        have hp : z (Fin.last n).castSucc - z 0 ∈ semiClosedUpperHalfPlane := by
          simpa [z'] using ih hnpos z' (fun i ↦ hedge i.castSucc)
        have hl : z (Fin.last (n + 1)) - z (Fin.last n).castSucc ∈
            semiClosedUpperHalfPlane := by
          have := hedge (Fin.last n)
          simpa using this
        have hadd := add_mem_semiClosedUpperHalfPlane hp hl
        convert hadd using 1
        ring

/-- Every forward chord of such a path remains in the semi-closed upper
half-plane. -/
theorem sub_mem_semiClosedUpperHalfPlane_of_lt {n : ℕ}
    (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    {a b : Fin (n + 1)} (hba : b < a) :
    z a - z b ∈ semiClosedUpperHalfPlane := by
  let d : ℕ := a.1 - b.1
  have hd : 0 < d := Nat.sub_pos_of_lt hba
  let p : Fin (d + 1) → ℂ := fun j ↦ z ⟨b.1 + j.1, by
    dsimp [d] at j ⊢
    omega⟩
  have hp := last_sub_zero_mem_semiClosedUpperHalfPlane hd p (fun j ↦ by
    let i : Fin n := ⟨b.1 + j.1, by
      dsimp [d] at j ⊢
      omega⟩
    have hi := hedge i
    simpa [p, i, Nat.add_assoc] using hi)
  have hlast : p (Fin.last d) = z a := by
    apply congrArg z
    apply Fin.ext
    simp [d]
    omega
  have hzero : p 0 = z b := by simp [p]
  simpa [hlast, hzero] using hp

/-- The incoming open edge at an interior vertex. -/
def interiorPrevEdge {n : ℕ} (z : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) (hk₀ : 0 < k) : ℂ :=
  z (⟨k.1 - 1, by omega⟩ : Fin n).succ -
    z (⟨k.1 - 1, by omega⟩ : Fin n).castSucc

/-- The outgoing open edge at a nonterminal vertex. -/
def interiorNextEdge {n : ℕ} (z : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) (hkn : k < Fin.last n) : ℂ :=
  z (⟨k.1, by omega⟩ : Fin n).succ -
    z (⟨k.1, by omega⟩ : Fin n).castSucc

/-- The angular bisector of the two open edges at an interior vertex. -/
def interiorBisector {n : ℕ} (z : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) : ℝ :=
  (Complex.arg (interiorPrevEdge z k hk₀) +
    Complex.arg (interiorNextEdge z k hkn)) / 2

/-- The positive scale relating a turn to its bisector support. -/
def interiorTurnScale {n : ℕ} (z : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) : ℝ :=
  2 * Real.sin ((Complex.arg (interiorPrevEdge z k hk₀) -
    Complex.arg (interiorNextEdge z k hkn)) / 2)

/-- At an interior vertex, the cyclic turning functional is the positive
bisector support functional used by the decreasing-argument proof. -/
theorem turningFunctional_interior_eq_cross {n : ℕ}
    (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) (x : ℂ) :
    turningFunctional z k x = interiorTurnScale z k hk₀ hkn *
      crossFunctional (unitRay (interiorBisector z k hk₀ hkn)) x := by
  let iPrev : Fin n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin n := ⟨k.1, by omega⟩
  let ePrev : ℂ := z iPrev.succ - z iPrev.castSucc
  let eNext : ℂ := z iNext.succ - z iNext.castSucc
  have hkNext : k = iNext.castSucc := by apply Fin.ext; rfl
  have hkPrev : k = iPrev.succ := by apply Fin.ext; simp [iPrev]; omega
  have hpred : (finRotate (n + 1)).symm k = iPrev.castSucc := by
    apply Fin.ext
    rw [coe_finRotate_symm_of_ne_zero (by exact ne_of_gt hk₀)]
    rfl
  have hrotNext : finRotate (n + 1) k = iNext.succ := by
    rw [hkNext]
    have hne : iNext.castSucc ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    apply Fin.ext
    rw [coe_finRotate_of_ne_last hne]
    rfl
  have hprevTangent : closedTangent z ((finRotate (n + 1)).symm k) =
      unitRay (Complex.arg ePrev) := by
    unfold closedTangent closedEdge
    rw [hpred]
    rw [show finRotate (n + 1) iPrev.castSucc = k by
      rw [← hpred]
      exact (finRotate (n + 1)).apply_symm_apply k]
    rw [hkPrev]
    exact unitDirection_eq_unitRay_arg
      (semiClosedUpperHalfPlane_ne_zero (hedge iPrev))
  have hnextTangent : closedTangent z k = unitRay (Complex.arg eNext) := by
    unfold closedTangent closedEdge
    rw [hrotNext, hkNext]
    exact unitDirection_eq_unitRay_arg
      (semiClosedUpperHalfPlane_ne_zero (hedge iNext))
  rw [turningFunctional, hprevTangent, hnextTangent]
  rw [dotFunctional_unitRay_sub]
  rfl

theorem interiorTurnScale_pos {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) :
    0 < interiorTurnScale z k hk₀ hkn := by
  let iPrev : Fin n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin n := ⟨k.1, by omega⟩
  have hipn : iPrev < iNext := by
    simp only [iPrev, iNext, Fin.mk_lt_mk]
    omega
  have hdiff : 0 < Complex.arg (z iPrev.succ - z iPrev.castSucc) -
      Complex.arg (z iNext.succ - z iNext.castSucc) := sub_pos.mpr (harg hipn)
  have hdiffpi :
      (Complex.arg (z iPrev.succ - z iPrev.castSucc) -
        Complex.arg (z iNext.succ - z iNext.castSucc)) / 2 < Real.pi := by
    have hp := arg_pos_of_mem_semiClosedUpperHalfPlane (hedge iNext)
    have hle := Complex.arg_le_pi (z iPrev.succ - z iPrev.castSucc)
    linarith [Real.pi_pos]
  unfold interiorTurnScale interiorPrevEdge interiorNextEdge
  change 0 < 2 * Real.sin ((Complex.arg
      (z iPrev.succ - z iPrev.castSucc) -
        Complex.arg (z iNext.succ - z iNext.castSucc)) / 2)
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by linarith) hdiffpi)

theorem interiorBisector_mem_Ioo {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) :
    interiorBisector z k hk₀ hkn ∈ Set.Ioo 0 Real.pi := by
  let iPrev : Fin n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin n := ⟨k.1, by omega⟩
  have hp := arg_pos_of_mem_semiClosedUpperHalfPlane (hedge iPrev)
  have hn := arg_pos_of_mem_semiClosedUpperHalfPlane (hedge iNext)
  have hpp := Complex.arg_le_pi (z iPrev.succ - z iPrev.castSucc)
  have hipn : iPrev < iNext := by simp only [iPrev, iNext, Fin.mk_lt_mk]; omega
  have hnp := harg hipn
  unfold interiorBisector interiorPrevEdge interiorNextEdge
  change 0 < (Complex.arg (z iPrev.succ - z iPrev.castSucc) +
      Complex.arg (z iNext.succ - z iNext.castSucc)) / 2 ∧
    (Complex.arg (z iPrev.succ - z iPrev.castSucc) +
      Complex.arg (z iNext.succ - z iNext.castSucc)) / 2 < Real.pi
  constructor <;> linarith

theorem interiorBisector_strictAnti {n : ℕ} (z : Fin (n + 1) → ℂ)
    (harg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    {k l : Fin (n + 1)} (hk₀ : 0 < k) (hkn : k < Fin.last n)
    (hl₀ : 0 < l) (hln : l < Fin.last n) (hkl : k < l) :
    interiorBisector z l hl₀ hln < interiorBisector z k hk₀ hkn := by
  let kp : Fin n := ⟨k.1 - 1, by omega⟩
  let kn : Fin n := ⟨k.1, by omega⟩
  let lp : Fin n := ⟨l.1 - 1, by omega⟩
  let ln : Fin n := ⟨l.1, by omega⟩
  have hp : kp < lp := by simp only [kp, lp, Fin.mk_lt_mk]; omega
  have hn : kn < ln := by simp only [kn, ln, Fin.mk_lt_mk]; omega
  have hpa := harg hp
  have hna := harg hn
  unfold interiorBisector interiorPrevEdge interiorNextEdge
  change (Complex.arg (z lp.succ - z lp.castSucc) +
      Complex.arg (z ln.succ - z ln.castSucc)) / 2 <
    (Complex.arg (z kp.succ - z kp.castSucc) +
      Complex.arg (z kn.succ - z kn.castSucc)) / 2
  linarith

/-- A vertex where the cross support at angle `θ` is maximal. -/
noncomputable def crossMaxIndex {n : ℕ} (z : Fin (n + 1) → ℂ) (θ : ℝ) :
    Fin (n + 1) :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun i ↦ crossFunctional (unitRay θ) (z i)) Finset.univ_nonempty)

theorem crossMaxIndex_max {n : ℕ} (z : Fin (n + 1) → ℂ) (θ : ℝ)
    (j : Fin (n + 1)) :
    crossFunctional (unitRay θ) (z j) ≤
      crossFunctional (unitRay θ) (z (crossMaxIndex z θ)) := by
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun i ↦ crossFunctional (unitRay θ) (z i)) Finset.univ_nonempty)).2 j
    (Finset.mem_univ j)

/-- As the support angle turns clockwise, a maximizing vertex of a
decreasing-argument upper-half-plane path can only move forward. -/
theorem crossMaxIndex_mono_of_angle_gt {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 Real.pi)
    (hθ₂ : θ₂ ∈ Set.Ioo 0 Real.pi) (hθ : θ₂ < θ₁) :
    crossMaxIndex z θ₁ ≤ crossMaxIndex z θ₂ := by
  by_contra hle
  have hlt : crossMaxIndex z θ₂ < crossMaxIndex z θ₁ := lt_of_not_ge hle
  let c : ℂ := z (crossMaxIndex z θ₁) - z (crossMaxIndex z θ₂)
  have hc : c ∈ semiClosedUpperHalfPlane :=
    sub_mem_semiClosedUpperHalfPlane_of_lt z hedge hlt
  have h₁nonneg : 0 ≤ crossFunctional (unitRay θ₁) c := by
    have hm := crossMaxIndex_max z θ₁ (crossMaxIndex z θ₂)
    rw [show crossFunctional (unitRay θ₁) c =
      crossFunctional (unitRay θ₁) (z (crossMaxIndex z θ₁)) -
        crossFunctional (unitRay θ₁) (z (crossMaxIndex z θ₂)) by
      exact map_sub (crossFunctional (unitRay θ₁)) _ _]
    linarith
  have h₂nonpos : crossFunctional (unitRay θ₂) c ≤ 0 := by
    have hm := crossMaxIndex_max z θ₂ (crossMaxIndex z θ₁)
    rw [show crossFunctional (unitRay θ₂) c =
      crossFunctional (unitRay θ₂) (z (crossMaxIndex z θ₁)) -
        crossFunctional (unitRay θ₂) (z (crossMaxIndex z θ₂)) by
      exact map_sub (crossFunctional (unitRay θ₂)) _ _]
    linarith
  have hr₁ : unitRay θ₁ ∈ semiClosedUpperHalfPlane :=
    unitRay_mem_semiClosedUpperHalfPlane hθ₁.1 hθ₁.2
  have hr₂ : unitRay θ₂ ∈ semiClosedUpperHalfPlane :=
    unitRay_mem_semiClosedUpperHalfPlane hθ₂.1 hθ₂.2
  have harg₁ : θ₁ ≤ Complex.arg c := by
    by_contra h
    have hneg := crossFunctional_neg_of_arg_lt hr₁ hc (by
      rw [arg_unitRay hθ₁.1 hθ₁.2]
      exact lt_of_not_ge h)
    linarith
  have harg₂ : Complex.arg c ≤ θ₂ := by
    by_contra h
    have hpos := crossFunctional_pos_of_arg_lt hr₂ hc (by
      rw [arg_unitRay hθ₂.1 hθ₂.2]
      exact lt_of_not_ge h)
    linarith
  linarith

/-- **Ikeda's polygon-perimeter comparison at `t = 0`.** Two nonempty
upper-half-plane paths have common endpoints.  If the inner path turns with
strictly decreasing edge arguments and its closed vertex hull is contained in
the outer vertex hull, then its Euclidean length is no larger than the outer
path length.

This slightly strengthens the literal `t = 0` specialization of Ikeda's
Lemma 3.7: no decreasing-turn hypothesis is needed for the outer path.  The
proof only selects a monotone subsequence of its support-maximizing vertices;
any remaining turns can only increase the outer polygonal length.

The proof closes both paths by their common endpoint chord, chooses a maximal
outer vertex for every inner bisector support, proves those choices are
monotone, and applies `closedLength_le_of_monotone_support`. -/
theorem length_le_of_convexHull_subset {n m : ℕ} (hn : 0 < n)
    (z : Fin (n + 1) → ℂ) (w : Fin (m + 1) → ℂ)
    (hzero : z 0 = w 0) (hlast : z (Fin.last n) = w (Fin.last m))
    (hzedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (hwedge : ∀ i : Fin m, w i.succ - w i.castSucc ∈ semiClosedUpperHalfPlane)
    (hzarg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    (hcontain : convexHull ℝ (Set.range z) ⊆ convexHull ℝ (Set.range w)) :
    length z ≤ length w := by
  let q : Fin (n + 1) → Fin (m + 1) := fun k ↦
    if hk₀ : k = 0 then 0
    else if hkl : k = Fin.last n then Fin.last m
    else crossMaxIndex w (interiorBisector z k
      (Fin.pos_iff_ne_zero.mpr hk₀)
      (lt_of_le_of_ne (Fin.le_last k) hkl))
  have hq₀ : q 0 = 0 := by simp [q]
  have hq_last : q (Fin.last n) = Fin.last m := by
    have hne : (Fin.last n : Fin (n + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
    unfold q
    rw [dif_neg hne, dif_pos rfl]
  have hq : Monotone q := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · by_cases ha₀ : a = 0
      · simp [q, ha₀]
      · by_cases hbl : b = Fin.last n
        · rw [hbl, hq_last]
          exact Fin.le_last _
        · have hal : a ≠ Fin.last n := by
            intro h
            subst a
            exact (not_lt_of_ge (Fin.le_last b)) hab
          have hb₀ : b ≠ 0 := by
            intro h
            subst b
            exact Fin.not_lt_zero a hab
          have ha_pos : 0 < a := Fin.pos_iff_ne_zero.mpr ha₀
          have hb_pos : 0 < b := Fin.pos_iff_ne_zero.mpr hb₀
          have ha_last : a < Fin.last n :=
            lt_of_le_of_ne (Fin.le_last a) hal
          have hb_last : b < Fin.last n :=
            lt_of_le_of_ne (Fin.le_last b) hbl
          simp only [q, dif_neg ha₀, dif_neg hal, dif_neg hb₀, dif_neg hbl]
          exact crossMaxIndex_mono_of_angle_gt w hwedge
            (interiorBisector_mem_Ioo z hzedge hzarg a ha_pos ha_last)
            (interiorBisector_mem_Ioo z hzedge hzarg b hb_pos hb_last)
            (interiorBisector_strictAnti z hzarg ha_pos ha_last hb_pos hb_last hab)
  have hsupport : ∀ k, turningFunctional z k (z k) ≤
      turningFunctional z k (w (q k)) := by
    intro k
    by_cases hk₀ : k = 0
    · subst k
      rw [hq₀, hzero]
    by_cases hkl : k = Fin.last n
    · subst k
      rw [hq_last, hlast]
    have hk_pos : 0 < k := Fin.pos_iff_ne_zero.mpr hk₀
    have hk_last : k < Fin.last n :=
      lt_of_le_of_ne (Fin.le_last k) hkl
    let θ := interiorBisector z k hk_pos hk_last
    let l : ℂ →L[ℝ] ℝ := crossFunctional (unitRay θ)
    have hzmem : z k ∈ convexHull ℝ (Set.range w) := by
      apply hcontain
      exact subset_convexHull ℝ (Set.range z) (Set.mem_range_self k)
    obtain ⟨y, ⟨j, rfl⟩, hy⟩ :=
      (l.toLinearMap.convexOn (convex_univ : Convex ℝ (Set.univ : Set ℂ))).exists_ge_of_mem_convexHull
        (Set.subset_univ _) hzmem
    have hcross : l (z k) ≤ l (w (crossMaxIndex w θ)) :=
      hy.trans (crossMaxIndex_max w θ j)
    have hqk : q k = crossMaxIndex w θ := by
      simp [q, hk₀, hkl, θ]
    rw [turningFunctional_interior_eq_cross z hzedge k hk_pos hk_last,
      turningFunctional_interior_eq_cross z hzedge k hk_pos hk_last, hqk]
    exact mul_le_mul_of_nonneg_left hcross
      (le_of_lt (interiorTurnScale_pos z hzedge hzarg k hk_pos hk_last))
  have hclosed := closedLength_le_of_monotone_support z w q hq hq₀ hq_last hsupport
  rw [closedLength_eq_length_add_chord, closedLength_eq_length_add_chord,
    hzero, hlast] at hclosed
  linarith

end

end CategoryTheory.Triangulated.ComplexPolygonalPath

namespace CategoryTheory.Triangulated

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E E' : A}

/-- HN-path specialization of the finite perimeter comparison for
applications which already have containment of the two closed finite vertex
polygons.  The monomorphism comparison below uses the more precise ambient
support theorem instead of trying to derive this hypothesis from full ambient
HN-polygon containment. -/
theorem polygonLength_le_of_vertexHull_subset
    (F : AbelianHNFiltration Z E) (G : AbelianHNFiltration Z E')
    (hcharge : Z.charge E = Z.charge E')
    (hcontain : convexHull ℝ (Set.range F.polygonVertex) ⊆
      convexHull ℝ (Set.range G.polygonVertex)) :
    F.polygonLength ≤ G.polygonLength := by
  apply ComplexPolygonalPath.length_le_of_convexHull_subset F.nonempty
  · rw [F.polygonVertex_zero, G.polygonVertex_zero]
  · calc
      F.polygonVertex (Fin.last F.n) = Z.charge E := F.polygonVertex_last
      _ = Z.charge E' := hcharge
      _ = G.polygonVertex (Fin.last G.n) := G.polygonVertex_last.symm
  · exact fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i
  · exact fun i ↦ G.polygonEdge_mem_semiClosedUpperHalfPlane i
  · exact F.polygonEdge_arg_strictAnti
  · exact hcontain

/-- **Boundary-cut HN polygon comparison.** If `E ⟶ E'` is monic, the HN
path of `E` is no longer than the HN path of `E'` followed by the single edge
from `Z(E')` back to `Z(E)`.

This is the `t = 0` comparison used in Ikeda's Lemma 3.8, strengthened at that
parameter by not requiring the cokernel to have phase one.  (That phase
hypothesis controls the exponential weight for general `t`; it disappears
when `t = 0`.)  The final edge is allowed to lie on the positive real boundary
when the cokernel does have phase one.  No false claim that the full ambient HN
polygon is the closed HN vertex hull is used.  Instead, positive-angle support
maxima of the ambient polygon are supplied by `HNPolygon` and the finite
support-fan perimeter theorem closes the argument. -/
theorem polygonLength_le_add_norm_charge_sub_of_mono
    (F : AbelianHNFiltration Z E) (G : AbelianHNFiltration Z E')
    (hHN : Z.HasHNProperty) (f : E ⟶ E') [Mono f] :
    F.polygonLength ≤ G.polygonLength + ‖Z.charge E - Z.charge E'‖ := by
  let w : Fin (G.n + 2) → ℂ := Fin.snoc G.polygonVertex (Z.charge E)
  let q : Fin (F.n + 1) → Fin (G.n + 2) := fun k ↦
    if hk₀ : k = 0 then 0
    else if hkl : k = Fin.last F.n then Fin.last (G.n + 1)
    else (ComplexPolygonalPath.crossMaxIndex G.polygonVertex
      (ComplexPolygonalPath.interiorBisector F.polygonVertex k
        (Fin.pos_iff_ne_zero.mpr hk₀)
        (lt_of_le_of_ne (Fin.le_last k) hkl))).castSucc
  have hq₀ : q 0 = 0 := by simp [q]
  have hq_last : q (Fin.last F.n) = Fin.last (G.n + 1) := by
    have hne : (Fin.last F.n : Fin (F.n + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      have := F.nonempty
      omega
    unfold q
    rw [dif_neg hne, dif_pos rfl]
  have hq : Monotone q := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · by_cases ha₀ : a = 0
      · simp [q, ha₀]
      · by_cases hbl : b = Fin.last F.n
        · rw [hbl, hq_last]
          exact Fin.le_last _
        · have hal : a ≠ Fin.last F.n := by
            intro h
            subst a
            exact (not_lt_of_ge (Fin.le_last b)) hab
          have hb₀ : b ≠ 0 := by
            intro h
            subst b
            exact Fin.not_lt_zero a hab
          have ha_pos : 0 < a := Fin.pos_iff_ne_zero.mpr ha₀
          have hb_pos : 0 < b := Fin.pos_iff_ne_zero.mpr hb₀
          have ha_last : a < Fin.last F.n :=
            lt_of_le_of_ne (Fin.le_last a) hal
          have hb_last : b < Fin.last F.n :=
            lt_of_le_of_ne (Fin.le_last b) hbl
          simp only [q, dif_neg ha₀, dif_neg hal, dif_neg hb₀, dif_neg hbl,
            Fin.castSucc_le_castSucc_iff]
          exact ComplexPolygonalPath.crossMaxIndex_mono_of_angle_gt
            G.polygonVertex (fun i ↦ G.polygonEdge_mem_semiClosedUpperHalfPlane i)
            (ComplexPolygonalPath.interiorBisector_mem_Ioo F.polygonVertex
              (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
              F.polygonEdge_arg_strictAnti a ha_pos ha_last)
            (ComplexPolygonalPath.interiorBisector_mem_Ioo F.polygonVertex
              (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
              F.polygonEdge_arg_strictAnti b hb_pos hb_last)
            (ComplexPolygonalPath.interiorBisector_strictAnti F.polygonVertex
              F.polygonEdge_arg_strictAnti ha_pos ha_last hb_pos hb_last hab)
  have hsupport : ∀ k, ComplexPolygonalPath.turningFunctional
      F.polygonVertex k (F.polygonVertex k) ≤
        ComplexPolygonalPath.turningFunctional
          F.polygonVertex k (w (q k)) := by
    intro k
    by_cases hk₀ : k = 0
    · subst k
      rw [hq₀]
      simp [w, F.polygonVertex_zero, G.polygonVertex_zero]
    by_cases hkl : k = Fin.last F.n
    · subst k
      rw [hq_last]
      have hw : w (Fin.last (G.n + 1)) =
          F.polygonVertex (Fin.last F.n) := by
        rw [show w (Fin.last (G.n + 1)) = Z.charge E by simp [w]]
        exact F.polygonVertex_last.symm
      rw [hw]
    have hk_pos : 0 < k := Fin.pos_iff_ne_zero.mpr hk₀
    have hk_last : k < Fin.last F.n :=
      lt_of_le_of_ne (Fin.le_last k) hkl
    let θ := ComplexPolygonalPath.interiorBisector
      F.polygonVertex k hk_pos hk_last
    let j := ComplexPolygonalPath.crossMaxIndex G.polygonVertex θ
    have hθ : θ ∈ Set.Ioo 0 Real.pi :=
      ComplexPolygonalPath.interiorBisector_mem_Ioo F.polygonVertex
        (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        F.polygonEdge_arg_strictAnti k hk_pos hk_last
    have hzB : F.polygonVertex k ∈ Z.hnPolygon E' :=
      Z.hnPolygon_mono f (F.polygonVertex_mem_hnPolygon k)
    have hcross : ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (F.polygonVertex k) ≤
      ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (G.polygonVertex j) :=
      G.hnPolygon_le_of_polygonVertex_isMax hHN hθ j
        (fun i ↦ ComplexPolygonalPath.crossMaxIndex_max
          G.polygonVertex θ i) hzB
    have hqk : q k = j.castSucc := by
      simp [q, hk₀, hkl, θ, j]
    rw [ComplexPolygonalPath.turningFunctional_interior_eq_cross
        F.polygonVertex (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        k hk_pos hk_last,
      ComplexPolygonalPath.turningFunctional_interior_eq_cross
        F.polygonVertex (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        k hk_pos hk_last, hqk]
    simp only [w, Fin.snoc_castSucc]
    exact mul_le_mul_of_nonneg_left hcross
      (le_of_lt (ComplexPolygonalPath.interiorTurnScale_pos F.polygonVertex
        (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        F.polygonEdge_arg_strictAnti k hk_pos hk_last))
  have hclosed := ComplexPolygonalPath.closedLength_le_of_monotone_support
    F.polygonVertex w q hq hq₀ hq_last hsupport
  rw [ComplexPolygonalPath.closedLength_eq_length_add_chord,
    ComplexPolygonalPath.closedLength_eq_length_add_chord] at hclosed
  have hw₀ : w 0 = F.polygonVertex 0 := by
    simp [w, F.polygonVertex_zero, G.polygonVertex_zero]
  have hwlast : w (Fin.last (G.n + 1)) = F.polygonVertex (Fin.last F.n) := by
    rw [show w (Fin.last (G.n + 1)) = Z.charge E by simp [w]]
    exact F.polygonVertex_last.symm
  rw [hw₀, hwlast] at hclosed
  have hopen : F.polygonLength ≤ ComplexPolygonalPath.length w := by
    exact le_of_add_le_add_right hclosed
  rw [ComplexPolygonalPath.length_snoc] at hopen
  have hGlast : G.polygonVertex (Fin.last G.n) = Z.charge E' :=
    G.polygonVertex_last
  rw [hGlast] at hopen
  simpa [w, polygonLength] using hopen

/-- Mass form of the boundary-cut comparison.  The closing-edge charge is
the negative of the cokernel charge, by additivity of the stability
function. -/
theorem mass_le_add_norm_cokernel_of_mono
    (F : AbelianHNFiltration Z E) (G : AbelianHNFiltration Z E')
    (hHN : Z.HasHNProperty) (f : E ⟶ E') [Mono f] :
    F.mass ≤ G.mass + ‖Z.charge (Limits.cokernel f)‖ := by
  have hse : (ShortComplex.mk f (Limits.cokernel.π f)
      (Limits.cokernel.condition f)).ShortExact :=
    StabilityFunction.shortExact_of_mono f
  have hadd := Z.additive _ hse
  have hsub : Z.charge E - Z.charge E' = -Z.charge (Limits.cokernel f) := by
    linear_combination -hadd
  rw [← F.polygonLength_eq_mass, ← G.polygonLength_eq_mass, ← norm_neg,
    ← hsub]
  exact F.polygonLength_le_add_norm_charge_sub_of_mono G hHN f

/-- Short-exact-sequence form of the boundary-cut comparison. -/
theorem mass_le_add_norm_of_shortExact (S : ShortComplex A)
    (hS : S.ShortExact) (F : AbelianHNFiltration Z S.X₁)
    (G : AbelianHNFiltration Z S.X₂) (hHN : Z.HasHNProperty) :
    F.mass ≤ G.mass + ‖Z.charge S.X₃‖ := by
  letI := hS.mono_f
  have hmass := F.mass_le_add_norm_cokernel_of_mono G hHN S.f
  let e : Limits.cokernel S.f ≅ S.X₃ :=
    Limits.IsColimit.coconePointUniqueUpToIso (Limits.cokernelIsCokernel S.f)
      hS.gIsCokernel
  have hcharge : Z.charge (Limits.cokernel S.f) = Z.charge S.X₃ :=
    Z.charge_eq_of_iso e
  rwa [hcharge] at hmass

/-- The mass of an abelian HN filtration is independent of the chosen
filtration.  This is the identity-monomorphism specialization of the
boundary-cut comparison. -/
theorem mass_eq_mass (F G : AbelianHNFiltration Z E)
    (hHN : Z.HasHNProperty) :
    F.mass = G.mass := by
  apply le_antisymm
  · rw [← F.polygonLength_eq_mass, ← G.polygonLength_eq_mass]
    simpa using F.polygonLength_le_add_norm_charge_sub_of_mono G hHN (𝟙 E)
  · rw [← F.polygonLength_eq_mass, ← G.polygonLength_eq_mass]
    simpa using G.polygonLength_le_add_norm_charge_sub_of_mono F hHN (𝟙 E)

end AbelianHNFiltration

end

end CategoryTheory.Triangulated
