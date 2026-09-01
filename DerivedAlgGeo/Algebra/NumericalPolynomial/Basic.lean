/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Numerical polynomials and mixed finite differences

This file supplies an algebraic finite-difference API for integer-valued functions on integer
lattices. A point of the lattice is a function `ι → ℤ`, and a numerical function is simply a
function `(ι → ℤ) → ℤ`. No scheme, sheaf, or line-bundle vocabulary enters this root; geometric
polynomiality theorems such as Snapper's theorem consume it from algebraic geometry.

## Upstream audit

Mathlib's `Mathlib.Algebra.Group.ForwardDiff` already provides the one-direction operator
`fwdDiff`, its iterates, the Gregory--Newton formula, additivity, and the expected vanishing
theorems for ordinary polynomials.  We reuse that operator rather than defining a competing
univariate theory.

`jjaassoonn/DimensionTheory` contains substantial theory of univariate integer-valued and Hilbert
polynomials, including binomial-polynomial coefficient extraction.  At the time of this audit it
does not provide arbitrary-direction mixed differences, is pinned to a different Mathlib commit,
and would add a large dependency for an API which is otherwise elementary. Consequently
DerivedAlgGeo
uses it as design precedent but does not depend on it.  The definitions below form the small
multivariable layer missing from Mathlib and specialize back to Mathlib's `fwdDiff` in one variable.

## Main definitions

* `Lattice ι` is the exponent lattice `ι → ℤ`.
* `mixedDifference directions f` successively applies forward differences in every direction.
* `DegreeLE n f` means that every `(n + 1)`-fold mixed difference vanishes.
* `coefficient directions f` evaluates a mixed difference at the origin; in top degree this is a
  symmetric multilinear function of the directions.
* `surfacePairing` bundles the degree-two specialization as a symmetric bilinear form.
-/

namespace NumericalPolynomial

open Function
open scoped fwdDiff
open scoped BigOperators

/-- The exponent lattice for a family indexed by `ι`.  For `ι = Fin r`, this is `ℤ^r`. -/
abbrev Lattice (ι : Type*) := ι → ℤ

/-- An integer-valued function on an exponent lattice. -/
abbrev NumericalFunction (ι : Type*) := Lattice ι → ℤ

/-- The forward difference of `f` in the lattice direction `v`. -/
def difference {ι : Type*} (v : Lattice ι) (f : NumericalFunction ι) :
    NumericalFunction ι :=
  fwdDiff v f

@[simp]
theorem difference_apply {ι : Type*} (v : Lattice ι) (f : NumericalFunction ι)
    (x : Lattice ι) :
    difference v f x = f (x + v) - f x :=
  rfl

@[simp]
theorem difference_zero_direction {ι : Type*} (f : NumericalFunction ι) :
    difference 0 f = 0 := by
  ext x
  simp [difference, fwdDiff]

@[simp]
theorem difference_zero_function {ι : Type*} (v : Lattice ι) :
    difference v (0 : NumericalFunction ι) = 0 := by
  ext x
  simp [difference, fwdDiff]

@[simp]
theorem difference_add_function {ι : Type*} (v : Lattice ι)
    (f g : NumericalFunction ι) :
    difference v (f + g) = difference v f + difference v g :=
  fwdDiff_add v f g

/-- Forward differences in two lattice directions commute. -/
theorem difference_comm {ι : Type*} (v w : Lattice ι) (f : NumericalFunction ι) :
    difference v (difference w f) = difference w (difference v f) := by
  funext x
  simp only [difference_apply]
  have harg : x + v + w = x + w + v := by abel
  rw [harg]
  abel

/-- Splitting a direction introduces one second-order correction term. -/
theorem difference_add_direction {ι : Type*} (v w : Lattice ι)
    (f : NumericalFunction ι) :
    difference (v + w) f =
      difference v f + difference w f + difference v (difference w f) := by
  funext x
  simp only [difference_apply, Pi.add_apply]
  have harg : x + (v + w) = x + v + w := by abel
  rw [harg]
  abel

/-- The positive unit vector in coordinate `i`. -/
def coordinateDirection {ι : Type*} [DecidableEq ι] (i : ι) : Lattice ι :=
  Pi.single i 1

/-- The forward difference in coordinate `i`. -/
def coordinateDifference {ι : Type*} [DecidableEq ι] (i : ι)
    (f : NumericalFunction ι) : NumericalFunction ι :=
  difference (coordinateDirection i) f

@[simp]
theorem coordinateDifference_apply {ι : Type*} [DecidableEq ι] (i : ι)
    (f : NumericalFunction ι) (x : Lattice ι) :
    coordinateDifference i f x = f (x + coordinateDirection i) - f x :=
  rfl

/-- Successive forward differences in the listed directions. -/
def mixedDifference {ι : Type*} :
    List (Lattice ι) → NumericalFunction ι → NumericalFunction ι
  | [], f => f
  | v :: directions, f => difference v (mixedDifference directions f)

@[simp]
theorem mixedDifference_nil {ι : Type*} (f : NumericalFunction ι) :
    mixedDifference [] f = f :=
  rfl

@[simp]
theorem mixedDifference_cons {ι : Type*} (v : Lattice ι)
    (directions : List (Lattice ι)) (f : NumericalFunction ι) :
    mixedDifference (v :: directions) f = difference v (mixedDifference directions f) :=
  rfl

@[simp]
theorem mixedDifference_zero {ι : Type*} (directions : List (Lattice ι)) :
    mixedDifference directions (0 : NumericalFunction ι) = 0 := by
  induction directions with
  | nil => rfl
  | cons v directions ih => simp [ih]

@[simp]
theorem mixedDifference_add {ι : Type*} (directions : List (Lattice ι))
    (f g : NumericalFunction ι) :
    mixedDifference directions (f + g) =
      mixedDifference directions f + mixedDifference directions g := by
  induction directions with
  | nil => rfl
  | cons v directions ih => simp [ih]

/-- Applying one more difference can be moved past any list of mixed differences. -/
theorem mixedDifference_difference {ι : Type*} (directions : List (Lattice ι))
    (v : Lattice ι) (f : NumericalFunction ι) :
    mixedDifference directions (difference v f) =
      difference v (mixedDifference directions f) := by
  induction directions with
  | nil => rfl
  | cons w directions ih =>
      simp only [mixedDifference_cons, ih]
      exact difference_comm w v (mixedDifference directions f)

/-- A mixed difference depends only on the multiset of its directions. -/
theorem mixedDifference_eq_of_perm {ι : Type*} {directions directions' : List (Lattice ι)}
    (h : directions.Perm directions') (f : NumericalFunction ι) :
    mixedDifference directions f = mixedDifference directions' f := by
  induction h with
  | nil => rfl
  | cons v _ ih => simpa only [mixedDifference_cons] using congrArg (difference v) ih
  | swap v w directions =>
      simp only [mixedDifference_cons]
      exact (difference_comm v w (mixedDifference directions f)).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A numerical function has degree at most `n` when all `(n + 1)`-fold mixed differences vanish.

This is the Eilenberg--Mac Lane finite-difference characterization in exactly the form used by
Snapper's theorem: the directions are arbitrary lattice vectors, not merely coordinate vectors.
-/
def DegreeLE {ι : Type*} (n : ℕ) (f : NumericalFunction ι) : Prop :=
  ∀ directions : List (Lattice ι), directions.length = n + 1 →
    mixedDifference directions f = 0

theorem degreeLE_iff_vanishing {ι : Type*} (n : ℕ) (f : NumericalFunction ι) :
    DegreeLE n f ↔
      ∀ directions : List (Lattice ι), directions.length = n + 1 →
        mixedDifference directions f = 0 :=
  Iff.rfl

/-- Equivalent fixed-arity form of the degree criterion.  This is convenient when a later
construction already presents its directions as an `(n + 1)`-tuple. -/
theorem degreeLE_iff_fin {ι : Type*} (n : ℕ) (f : NumericalFunction ι) :
    DegreeLE n f ↔
      ∀ directions : Fin (n + 1) → Lattice ι,
        mixedDifference (List.ofFn directions) f = 0 := by
  constructor
  · intro hf directions
    exact hf (List.ofFn directions) (by simp)
  · intro hf directions hlength
    have hzero := hf fun i => directions.get (Fin.cast hlength.symm i)
    rw [← List.ofFn_get directions]
    rw [List.ofFn_congr hlength]
    exact hzero

@[simp]
theorem degreeLE_zero {ι : Type*} (n : ℕ) :
    DegreeLE n (0 : NumericalFunction ι) := by
  intro directions _
  exact mixedDifference_zero directions

theorem DegreeLE.add {ι : Type*} {n : ℕ} {f g : NumericalFunction ι}
    (hf : DegreeLE n f) (hg : DegreeLE n g) :
    DegreeLE n (f + g) := by
  intro directions hlength
  rw [mixedDifference_add, hf directions hlength, hg directions hlength, add_zero]

/-- A function of degree at most `n` also has degree at most `n + 1`. -/
theorem DegreeLE.succ {ι : Type*} {n : ℕ} {f : NumericalFunction ι}
    (hf : DegreeLE n f) :
    DegreeLE (n + 1) f := by
  intro directions hlength
  cases directions with
  | nil => simp at hlength
  | cons v directions =>
      rw [mixedDifference_cons, hf directions (by simpa using hlength)]
      exact difference_zero_function v

/-- Monotonicity of the degree bound. -/
theorem DegreeLE.mono {ι : Type*} {n m : ℕ} {f : NumericalFunction ι}
    (hf : DegreeLE n f) (hnm : n ≤ m) :
    DegreeLE m f := by
  induction m, hnm using Nat.le_induction with
  | base => exact hf
  | succ m _ ih => simpa [Nat.add_comm] using ih.succ

/-- Taking a finite difference lowers a positive degree bound by one. -/
theorem DegreeLE.difference {ι : Type*} {n : ℕ} {f : NumericalFunction ι}
    (hf : DegreeLE (n + 1) f) (v : Lattice ι) :
    DegreeLE n (difference v f) := by
  intro directions hlength
  rw [mixedDifference_difference]
  exact hf (v :: directions) (by simpa using hlength)

/-- The mixed finite-difference coefficient attached to a list of directions. -/
def coefficient {ι : Type*} (directions : List (Lattice ι))
    (f : NumericalFunction ι) : ℤ :=
  mixedDifference directions f 0

@[simp]
theorem coefficient_nil {ι : Type*} (f : NumericalFunction ι) :
    coefficient [] f = f 0 :=
  rfl

@[simp]
theorem coefficient_zero {ι : Type*} (directions : List (Lattice ι)) :
    coefficient directions (0 : NumericalFunction ι) = 0 := by
  simp [coefficient]

theorem coefficient_add {ι : Type*} (directions : List (Lattice ι))
    (f g : NumericalFunction ι) :
    coefficient directions (f + g) = coefficient directions f + coefficient directions g := by
  simp [coefficient]

/-- Coefficient extraction is symmetric in the chosen directions. -/
theorem coefficient_eq_of_perm {ι : Type*} {directions directions' : List (Lattice ι)}
    (h : directions.Perm directions') (f : NumericalFunction ι) :
    coefficient directions f = coefficient directions' f := by
  rw [coefficient, coefficient, mixedDifference_eq_of_perm h]

/-- Coefficient extraction with `n` explicitly indexed directions. -/
def topCoefficient {ι : Type*} {n : ℕ} (directions : Fin n → Lattice ι)
    (f : NumericalFunction ι) : ℤ :=
  coefficient (List.ofFn directions) f

/-- `topCoefficient` is invariant under every permutation of its `n` inputs. -/
theorem topCoefficient_comp_perm {ι : Type*} {n : ℕ}
    (directions : Fin n → Lattice ι) (σ : Equiv.Perm (Fin n))
    (f : NumericalFunction ι) :
    topCoefficient (directions ∘ σ) f = topCoefficient directions f :=
  coefficient_eq_of_perm (σ.ofFn_comp_perm directions) f

/-- The coordinate directions prescribed by a multi-index.  The internal order chosen by
`Finset.toList` is immaterial by `coefficient_eq_of_perm`. -/
noncomputable def coordinateDirections {ι : Type*} [Fintype ι] [DecidableEq ι]
    (powers : ι → ℕ) : List (Lattice ι) :=
  Finset.univ.toList.flatMap fun i => List.replicate (powers i) (coordinateDirection i)

@[simp]
theorem coordinateDirections_length {ι : Type*} [Fintype ι] [DecidableEq ι]
    (powers : ι → ℕ) :
    (coordinateDirections powers).length = ∑ i, powers i := by
  simp [coordinateDirections]

/-- The multivariable Newton coefficient indexed by coordinate multiplicities. -/
noncomputable def newtonCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (powers : ι → ℕ) (f : NumericalFunction ι) : ℤ :=
  coefficient (coordinateDirections powers) f

@[simp]
theorem newtonCoefficient_zero_index {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : NumericalFunction ι) :
    newtonCoefficient (fun _ => 0) f = f 0 := by
  have hnil : ∀ l : List ι,
      l.flatMap (fun _ => ([] : List (Lattice ι))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp [ih]
  rw [newtonCoefficient, coordinateDirections]
  simp only [List.replicate_zero]
  rw [hnil]
  rfl

/-- An `n`-fold mixed difference of a degree-`≤ n` function is constant, so evaluating it at the
origin loses no information. -/
theorem mixedDifference_eq_coefficient_of_degreeLE {ι : Type*} {n : ℕ}
    {f : NumericalFunction ι} (hf : DegreeLE n f) (directions : List (Lattice ι))
    (hlength : directions.length = n) (x : Lattice ι) :
    mixedDifference directions f x = coefficient directions f := by
  have hzero := congrFun (hf (x :: directions) (by simp [hlength])) 0
  have heq : mixedDifference directions f x = mixedDifference directions f 0 := by
    apply sub_eq_zero.mp
    simpa [mixedDifference, difference, fwdDiff] using hzero
  exact heq

/-- Additivity of a top mixed coefficient in its first direction.  The correction term in
`difference_add_direction` vanishes because it has one direction too many. -/
theorem coefficient_cons_add {ι : Type*} {f : NumericalFunction ι}
    (directions : List (Lattice ι)) (v w : Lattice ι)
    (hf : DegreeLE (directions.length + 1) f) :
    coefficient ((v + w) :: directions) f =
      coefficient (v :: directions) f + coefficient (w :: directions) f := by
  have hcorrection :
      difference v (difference w (mixedDifference directions f)) = 0 := by
    exact hf (v :: w :: directions) (by simp [Nat.add_assoc])
  simp only [coefficient, mixedDifference_cons, difference_add_direction, hcorrection,
    Pi.add_apply, Pi.zero_apply, add_zero]

/-- Additivity of a top mixed coefficient in an arbitrary direction slot. -/
theorem coefficient_middle_add {ι : Type*} {f : NumericalFunction ι}
    (before after : List (Lattice ι)) (v w : Lattice ι)
    (hf : DegreeLE (before.length + after.length + 1) f) :
    coefficient (before ++ (v + w) :: after) f =
      coefficient (before ++ v :: after) f + coefficient (before ++ w :: after) f := by
  calc
    coefficient (before ++ (v + w) :: after) f =
        coefficient ((v + w) :: (before ++ after)) f :=
      coefficient_eq_of_perm List.perm_middle f
    _ = coefficient (v :: (before ++ after)) f +
        coefficient (w :: (before ++ after)) f := by
      apply coefficient_cons_add
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    _ = coefficient (before ++ v :: after) f + coefficient (before ++ w :: after) f := by
      rw [coefficient_eq_of_perm List.perm_middle.symm f,
        coefficient_eq_of_perm List.perm_middle.symm f]

/-- A top mixed coefficient, with all but one direction fixed, as an additive homomorphism. -/
def coefficientAddHom {ι : Type*} {f : NumericalFunction ι}
    (before after : List (Lattice ι))
    (hf : DegreeLE (before.length + after.length + 1) f) :
    Lattice ι →+ ℤ where
  toFun v := coefficient (before ++ v :: after) f
  map_zero' := by
    rw [coefficient_eq_of_perm List.perm_middle f]
    simp [coefficient]
  map_add' v w := coefficient_middle_add before after v w hf

@[simp]
theorem coefficientAddHom_apply {ι : Type*} {f : NumericalFunction ι}
    (before after : List (Lattice ι))
    (hf : DegreeLE (before.length + after.length + 1) f) (v : Lattice ι) :
    coefficientAddHom before after hf v = coefficient (before ++ v :: after) f :=
  rfl

/-- Integer homogeneity in every slot; together with `coefficient_middle_add`, this is
multilinearity of the top mixed difference. -/
theorem coefficient_middle_zsmul {ι : Type*} {f : NumericalFunction ι}
    (before after : List (Lattice ι)) (c : ℤ) (v : Lattice ι)
    (hf : DegreeLE (before.length + after.length + 1) f) :
    coefficient (before ++ (c • v) :: after) f =
      c • coefficient (before ++ v :: after) f := by
  exact (coefficientAddHom before after hf).map_zsmul c v

/-! ## One-variable specialization -/

/-- Embed an integer as a point of the rank-one lattice. -/
def oneVariablePoint (x : ℤ) : Lattice (Fin 1) :=
  fun _ => x

/-- Regard an ordinary integer-valued function as a function on the rank-one lattice. -/
def oneVariable (f : ℤ → ℤ) : NumericalFunction (Fin 1) :=
  fun x => f (x 0)

/-- The positive unit direction in the rank-one lattice. -/
def oneVariableDirection : Lattice (Fin 1) :=
  oneVariablePoint 1

/-- Repeated mixed differences in the unit direction agree with Mathlib's iterated `fwdDiff`. -/
theorem mixedDifference_oneVariable (f : ℤ → ℤ) (n : ℕ) (x : ℤ) :
    mixedDifference (List.replicate n oneVariableDirection) (oneVariable f)
        (oneVariablePoint x) =
      (fwdDiff (1 : ℤ))^[n] f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, mixedDifference_cons, difference_apply,
        Function.iterate_succ_apply']
      have hpoint : oneVariablePoint x + oneVariableDirection = oneVariablePoint (x + 1) := by
        ext i
        rfl
      rw [hpoint, ih, ih]
      rfl

/-- The general degree predicate implies the familiar one-variable `(n + 1)`-st difference
criterion. -/
theorem oneVariable_fwdDiff_vanishes {f : ℤ → ℤ} {n : ℕ}
    (hf : DegreeLE n (oneVariable f)) :
    (fwdDiff (1 : ℤ))^[n + 1] f = 0 := by
  funext x
  rw [← mixedDifference_oneVariable]
  have hzero := hf (List.replicate (n + 1) oneVariableDirection) (by simp)
  exact congrFun hzero (oneVariablePoint x)

/-- In one variable, generic coefficient extraction is the usual Newton coefficient. -/
theorem coefficient_oneVariable (f : ℤ → ℤ) (n : ℕ) :
    coefficient (List.replicate n oneVariableDirection) (oneVariable f) =
      (fwdDiff (1 : ℤ))^[n] f 0 := by
  exact mixedDifference_oneVariable f n 0

/-! ## Surface specialization -/

/-- The degree-two top mixed difference, bundled as a bilinear form over `ℤ`. -/
noncomputable def surfacePairing {ι : Type*} (f : NumericalFunction ι)
    (hf : DegreeLE 2 f) :
    Lattice ι →ₗ[ℤ] Lattice ι →ₗ[ℤ] ℤ where
  toFun v := (coefficientAddHom [v] [] (by simpa using hf)).toIntLinearMap
  map_add' v w := by
    ext u
    exact coefficient_middle_add [] [u] v w (by simpa using hf)
  map_smul' c v := by
    ext u
    exact coefficient_middle_zsmul [] [u] c v (by simpa using hf)

@[simp]
theorem surfacePairing_apply {ι : Type*} (f : NumericalFunction ι)
    (hf : DegreeLE 2 f) (v w : Lattice ι) :
    surfacePairing f hf v w = coefficient [v, w] f :=
  rfl

/-- The surface pairing is symmetric. -/
theorem surfacePairing_symm {ι : Type*} (f : NumericalFunction ι)
    (hf : DegreeLE 2 f) (v w : Lattice ι) :
    surfacePairing f hf v w = surfacePairing f hf w v := by
  simp only [surfacePairing_apply]
  exact coefficient_eq_of_perm (List.Perm.swap v w []).symm f

end NumericalPolynomial
