/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.AssociatedSheaf
import DerivedAlgGeo.Algebra.NumericalPolynomial.Basic
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.Snapper

/-!
# Intersection numbers from Snapper coefficients

Intersection numbers are the top mixed finite differences of the Euler characteristic of
line-bundle twists.  No cycle group or Chow ring occurs in the construction.

The geometric input remains explicit.  `TwistContext` records coherent representatives and the
`Snapper.GeometricInduction` certificates for every finite family of Picard classes, together
with one Picard-level Euler function which they realize.  `IntersectionContext` specializes the
base coherent sheaf to the structure sheaf.  Thus the missing geometric construction is data in
a theorem statement, never a global axiom.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.IntersectionTheory.Number

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open NumericalPolynomial
open AlgebraicGeometry.IntersectionTheory.Snapper
open scoped BigOperators

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

noncomputable section

/-! ## Finite differences on the Picard group -/

/-- One finite difference of an integer-valued function on the Picard group. -/
def picardDifference (L : Pic X) (f : Pic X → ℤ) :
    Pic X → ℤ :=
  fun M ↦ f (M * L) - f M

/-- Successive finite differences in a list of Picard classes. -/
def picardMixedDifference :
    List (Pic X) → (Pic X → ℤ) → Pic X → ℤ
  | [], f => f
  | L :: classes, f => picardDifference L (picardMixedDifference classes f)

/-- A mixed Picard coefficient is evaluated at the trivial line bundle. -/
def picardCoefficient (classes : List (Pic X))
    (f : Pic X → ℤ) : ℤ :=
  picardMixedDifference classes f 1

@[simp]
theorem picardMixedDifference_nil (f : Pic X → ℤ) :
    picardMixedDifference [] f = f :=
  rfl

@[simp]
theorem picardMixedDifference_cons (L : Pic X)
    (classes : List (Pic X)) (f : Pic X → ℤ) :
    picardMixedDifference (L :: classes) f =
      picardDifference L (picardMixedDifference classes f) :=
  rfl

theorem picardDifference_comm (L M : Pic X) (f : Pic X → ℤ) :
    picardDifference L (picardDifference M f) =
      picardDifference M (picardDifference L f) := by
  funext N
  simp only [picardDifference]
  have harg : N * L * M = N * M * L := by ac_rfl
  rw [harg]
  omega

/-- Picard mixed differences are symmetric in their directions. -/
theorem picardMixedDifference_eq_of_perm
    {classes classes' : List (Pic X)} (h : classes.Perm classes')
    (f : Pic X → ℤ) :
    picardMixedDifference classes f = picardMixedDifference classes' f := by
  induction h with
  | nil => rfl
  | cons L _ ih => simpa only [picardMixedDifference_cons] using congrArg (picardDifference L) ih
  | swap L M classes =>
      simp only [picardMixedDifference_cons]
      exact (picardDifference_comm L M (picardMixedDifference classes f)).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem picardCoefficient_eq_of_perm
    {classes classes' : List (Pic X)} (h : classes.Perm classes')
    (f : Pic X → ℤ) :
    picardCoefficient classes f = picardCoefficient classes' f := by
  rw [picardCoefficient, picardCoefficient, picardMixedDifference_eq_of_perm h f]

@[simp]
theorem picardDifference_one (f : Pic X → ℤ) : picardDifference 1 f = 0 := by
  funext L
  simp [picardDifference]

/-- Splitting a tensor-product direction introduces one second-difference correction. -/
theorem picardDifference_mul_direction (L M : Pic X)
    (f : Pic X → ℤ) :
    picardDifference (L * M) f =
      picardDifference L f + picardDifference M f +
        picardDifference L (picardDifference M f) := by
  funext N
  simp only [picardDifference, Pi.add_apply, mul_assoc]
  omega

/-- Picard-group degree at most `d`, in the coefficient form needed for intersections. -/
def PicardDegreeLE (d : ℕ) (f : Pic X → ℤ) : Prop :=
  ∀ classes : List (Pic X), classes.length = d + 1 →
    picardCoefficient classes f = 0

/-- Additivity of a top Picard coefficient in its first class. -/
theorem picardCoefficient_cons_mul (classes : List (Pic X))
    (L M : Pic X) (f : Pic X → ℤ)
    (hf : PicardDegreeLE (classes.length + 1) f) :
    picardCoefficient ((L * M) :: classes) f =
      picardCoefficient (L :: classes) f + picardCoefficient (M :: classes) f := by
  have hcorrection :
      picardCoefficient (L :: M :: classes) f = 0 := by
    apply hf
    simp [Nat.add_assoc]
  change picardDifference (L * M) (picardMixedDifference classes f) 1 = _
  rw [picardDifference_mul_direction]
  change picardCoefficient (L :: classes) f + picardCoefficient (M :: classes) f +
      picardCoefficient (L :: M :: classes) f = _
  rw [hcorrection, add_zero]

/-- Additivity of a top Picard coefficient in any class slot. -/
theorem picardCoefficient_middle_mul (before after : List (Pic X))
    (L M : Pic X) (f : Pic X → ℤ)
    (hf : PicardDegreeLE (before.length + after.length + 1) f) :
    picardCoefficient (before ++ (L * M) :: after) f =
      picardCoefficient (before ++ L :: after) f +
        picardCoefficient (before ++ M :: after) f := by
  calc
    picardCoefficient (before ++ (L * M) :: after) f =
        picardCoefficient ((L * M) :: (before ++ after)) f :=
      picardCoefficient_eq_of_perm List.perm_middle f
    _ = picardCoefficient (L :: (before ++ after)) f +
        picardCoefficient (M :: (before ++ after)) f := by
      apply picardCoefficient_cons_mul
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    _ = picardCoefficient (before ++ L :: after) f +
        picardCoefficient (before ++ M :: after) f := by
      rw [picardCoefficient_eq_of_perm List.perm_middle.symm f,
        picardCoefficient_eq_of_perm List.perm_middle.symm f]

/-- With every other class fixed, a top Picard coefficient is an additive homomorphism from
the Picard group written additively. -/
def picardCoefficientAddHom (before after : List (Pic X))
    (f : Pic X → ℤ)
    (hf : PicardDegreeLE (before.length + after.length + 1) f) :
    Additive (Pic X) →+ ℤ where
  toFun L := picardCoefficient (before ++ L.toMul :: after) f
  map_zero' := by
    rw [picardCoefficient_eq_of_perm List.perm_middle f]
    simp [picardCoefficient]
  map_add' L M := picardCoefficient_middle_mul before after L.toMul M.toMul f hf

@[simp]
theorem picardCoefficientAddHom_apply (before after : List (Pic X))
    (f : Pic X → ℤ)
    (hf : PicardDegreeLE (before.length + after.length + 1) f)
    (L : Additive (Pic X)) :
    picardCoefficientAddHom before after f hf L =
      picardCoefficient (before ++ L.toMul :: after) f :=
  rfl

/-- Integer homogeneity of a top Picard coefficient in every slot. -/
theorem picardCoefficient_middle_zpow (before after : List (Pic X))
    (L : Pic X) (m : ℤ) (f : Pic X → ℤ)
    (hf : PicardDegreeLE (before.length + after.length + 1) f) :
    picardCoefficient (before ++ (L ^ m) :: after) f =
      m * picardCoefficient (before ++ L :: after) f := by
  have h := (picardCoefficientAddHom before after f hf).map_zsmul m (Additive.ofMul L)
  exact h

/-- The Picard class represented by an integer vector in a finite family. -/
def picardMonomial {ι : Type*} [Fintype ι]
    (L : ι → Pic X) (n : NumericalPolynomial.Lattice ι) : Pic X :=
  ∏ i, L i ^ n i

/-- Restrict a Picard-level function to the exponent lattice generated by `L`. -/
def picardPolynomial {ι : Type*} [Fintype ι]
    (f : Pic X → ℤ) (L : ι → Pic X) : NumericalFunction ι :=
  fun n ↦ f (picardMonomial L n)

@[simp]
theorem picardMonomial_zero {ι : Type*} [Fintype ι]
    (L : ι → Pic X) : picardMonomial L 0 = 1 := by
  simp [picardMonomial]

theorem picardMonomial_add {ι : Type*} [Fintype ι]
    (L : ι → Pic X) (m n : NumericalPolynomial.Lattice ι) :
    picardMonomial L (m + n) = picardMonomial L m * picardMonomial L n := by
  simp only [picardMonomial, Pi.add_apply, zpow_add]
  exact Finset.prod_mul_distrib

/-- Lattice mixed differences are Picard mixed differences in the represented classes. -/
theorem mixedDifference_picardPolynomial {ι : Type*} [Fintype ι]
    (f : Pic X → ℤ) (L : ι → Pic X)
    (directions : List (NumericalPolynomial.Lattice ι))
    (n : NumericalPolynomial.Lattice ι) :
    mixedDifference directions (picardPolynomial f L) n =
      picardMixedDifference (directions.map (picardMonomial L)) f
        (picardMonomial L n) := by
  induction directions generalizing n with
  | nil => rfl
  | cons v directions ih =>
      simp only [mixedDifference_cons, difference_apply, List.map_cons,
        picardMixedDifference_cons, picardDifference]
      rw [ih (n + v), ih n, picardMonomial_add]

@[simp]
theorem picardMonomial_coordinateDirection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Pic X) (i : ι) :
    picardMonomial L (coordinateDirection i) = L i := by
  classical
  unfold picardMonomial coordinateDirection
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The standard-coordinate top coefficient is the intrinsic Picard mixed coefficient. -/
theorem topCoefficient_picardPolynomial {d : ℕ}
    (f : Pic X → ℤ) (L : Fin d → Pic X) :
    topCoefficient (fun i : Fin d ↦ coordinateDirection i) (picardPolynomial f L) =
      picardCoefficient (List.ofFn L) f := by
  rw [topCoefficient, coefficient, mixedDifference_picardPolynomial, picardCoefficient]
  rw [picardMonomial_zero]
  rw [List.map_ofFn]
  have hdirections :
      (picardMonomial L ∘ fun i : Fin d ↦ coordinateDirection i) = L := by
    funext i
    exact picardMonomial_coordinateDirection L i
  rw [hdirections]

/-! ## Explicit geometric contexts -/

/-- Uniform Snapper data for twists of one coherent sheaf by every finite family of line
bundles.  The single `eulerPic` field makes coefficients independent of the chosen finite
presentation; `realization` identifies it with the actual geometric Euler characteristic. -/
structure TwistContext (D : FiniteCohomology k X) (F : Coh X) (d : ℕ) where
  eulerPic : Pic X → ℤ
  twistFamily : ∀ (r : ℕ) (L : Fin r → Pic X), CoherentTwistFamily F L
  geometricInduction : ∀ (r : ℕ) (L : Fin r → Pic X),
    GeometricInduction D (twistFamily r L) d
  realization : ∀ (r : ℕ) (L : Fin r → Pic X)
    (n : NumericalPolynomial.Lattice (Fin r)),
    eulerPic (picardMonomial L n) = eulerFunction D (twistFamily r L) n

/-- The structure sheaf as a coherent object, from the explicitly supplied coherence proof. -/
def structureSheafObject
    (h : Scheme.Modules.IsCoherent X
      (SheafOfModules.unit X.ringCatSheaf)) : Coh X :=
  ⟨SheafOfModules.unit X.ringCatSheaf, h⟩

/-- Snapper input specialized to twists of the structure sheaf. -/
structure IntersectionContext (D : FiniteCohomology k X)
    (C : D.LinearConnectingSystem) (d : ℕ) where
  structureSheafCoherent : Scheme.Modules.IsCoherent X
    (SheafOfModules.unit X.ringCatSheaf)
  twists : TwistContext D (structureSheafObject structureSheafCoherent) d

namespace TwistContext

variable {D : FiniteCohomology k X} {F : Coh X} {d : ℕ}

/-- The geometric Euler function of any chosen finite presentation is the restriction of the
intrinsic Picard-level Euler function. -/
theorem eulerFunction_eq_picardPolynomial (P : TwistContext D F d)
    (r : ℕ) (L : Fin r → Pic X) :
    eulerFunction D (P.twistFamily r L) = picardPolynomial P.eulerPic L := by
  funext n
  exact (P.realization r L n).symm

/-- Snapper polynomiality for every finite presentation implies intrinsic Picard coefficient
vanishing in degree `d + 1`. -/
theorem picardDegreeLE (P : TwistContext D F d) (C : D.LinearConnectingSystem) :
    PicardDegreeLE d P.eulerPic := by
  intro classes hlength
  let L : Fin (d + 1) → Pic X :=
    fun i ↦ classes.get (Fin.cast hlength.symm i)
  have hs : DegreeLE d (picardPolynomial P.eulerPic L) := by
    rw [← P.eulerFunction_eq_picardPolynomial (d + 1) L]
    exact snapper D C (P.twistFamily (d + 1) L) d
      (P.geometricInduction (d + 1) L)
  have hzero := congrFun
    (hs (List.ofFn (fun i : Fin (d + 1) ↦ coordinateDirection i)) (by simp)) 0
  have hcoefficient : picardCoefficient (List.ofFn L) P.eulerPic = 0 := by
    rw [← topCoefficient_picardPolynomial]
    exact hzero
  rw [← List.ofFn_get classes]
  rw [List.ofFn_congr hlength]
  exact hcoefficient

end TwistContext

namespace IntersectionContext

variable {D : FiniteCohomology k X} {C : D.LinearConnectingSystem} {d : ℕ}

/-- The intrinsic Euler characteristic of a Picard class. -/
def eulerPic (P : IntersectionContext D C d) : Pic X → ℤ :=
  P.twists.eulerPic

/-- The Picard Euler function has finite-difference degree at most the geometric dimension. -/
theorem picardDegreeLE (P : IntersectionContext D C d) :
    PicardDegreeLE d P.eulerPic :=
  P.twists.picardDegreeLE C

/-- The dimension-`d` intersection number of `d` Picard classes, defined as the top mixed
Snapper coefficient of the corresponding structure-sheaf twists. -/
def picardIntersectionNumber (P : IntersectionContext D C d)
    (L : Fin d → Pic X) : ℤ :=
  topCoefficient (fun i : Fin d ↦ coordinateDirection i)
    (eulerFunction D (P.twists.twistFamily d L))

/-- Intrinsic formulation: the intersection number is the iterated Picard difference of
`eulerPic`, evaluated at the trivial bundle. -/
theorem picardIntersectionNumber_eq_coefficient (P : IntersectionContext D C d)
    (L : Fin d → Pic X) :
    P.picardIntersectionNumber L = picardCoefficient (List.ofFn L) P.eulerPic := by
  rw [picardIntersectionNumber, P.twists.eulerFunction_eq_picardPolynomial]
  exact topCoefficient_picardPolynomial P.eulerPic L

/-- List form of the intersection coefficient.  The separate list API is convenient for
multilinearity proofs and for downstream Chern-character formulas. -/
def picardIntersectionList (P : IntersectionContext D C d)
    (classes : List (Pic X)) : ℤ :=
  picardCoefficient classes P.eulerPic

@[simp]
theorem picardIntersectionList_ofFn (P : IntersectionContext D C d)
    (L : Fin d → Pic X) :
    P.picardIntersectionList (List.ofFn L) = P.picardIntersectionNumber L := by
  rw [picardIntersectionNumber_eq_coefficient]
  rfl

/-- Intersection numbers are invariant under line-bundle isomorphism.  Equality in `Pic X` is
exactly equality of isomorphism classes. -/
theorem picardIntersectionNumber_congr (P : IntersectionContext D C d)
    {L M : Fin d → Pic X} (h : ∀ i, L i = M i) :
    P.picardIntersectionNumber L = P.picardIntersectionNumber M := by
  have hLM : L = M := funext h
  subst M
  rfl

/-- Symmetry in all divisor arguments. -/
theorem picardIntersectionNumber_comp_perm (P : IntersectionContext D C d)
    (L : Fin d → Pic X) (σ : Equiv.Perm (Fin d)) :
    P.picardIntersectionNumber (L ∘ σ) = P.picardIntersectionNumber L := by
  rw [picardIntersectionNumber_eq_coefficient, picardIntersectionNumber_eq_coefficient]
  exact picardCoefficient_eq_of_perm (σ.ofFn_comp_perm L) P.eulerPic

theorem picardIntersectionList_eq_of_perm (P : IntersectionContext D C d)
    {classes classes' : List (Pic X)} (h : classes.Perm classes') :
    P.picardIntersectionList classes = P.picardIntersectionList classes' :=
  picardCoefficient_eq_of_perm h P.eulerPic

/-- Multilinearity, in list form: tensor product in any one slot becomes addition of
intersection numbers. -/
theorem picardIntersectionList_middle_mul (P : IntersectionContext D C d)
    (before after : List (Pic X)) (L M : Pic X)
    (hlength : before.length + after.length + 1 = d) :
    P.picardIntersectionList (before ++ (L * M) :: after) =
      P.picardIntersectionList (before ++ L :: after) +
        P.picardIntersectionList (before ++ M :: after) := by
  apply picardCoefficient_middle_mul
  simpa [hlength] using P.picardDegreeLE

/-- Integer homogeneity, in list form. -/
theorem picardIntersectionList_middle_zpow (P : IntersectionContext D C d)
    (before after : List (Pic X)) (L : Pic X) (m : ℤ)
    (hlength : before.length + after.length + 1 = d) :
    P.picardIntersectionList (before ++ (L ^ m) :: after) =
      m * P.picardIntersectionList (before ++ L :: after) := by
  apply picardCoefficient_middle_zpow
  simpa [hlength] using P.picardDegreeLE

/-- A trivial line-bundle argument makes every positive-arity intersection vanish. -/
theorem picardIntersectionList_middle_one (P : IntersectionContext D C d)
    (before after : List (Pic X)) :
    P.picardIntersectionList (before ++ (1 : Pic X) :: after) = 0 := by
  unfold picardIntersectionList
  rw [picardCoefficient_eq_of_perm List.perm_middle P.eulerPic]
  simp [picardCoefficient]

/-! ## Cartier divisors and divisor classes -/

/-- Intersection numbers of Cartier divisor classes, through the additive class-to-Picard map. -/
def cartierClassIntersectionNumber (P : IntersectionContext D C d)
    (classes : Fin d → CartierDivisor.ClassGroup X) : ℤ :=
  P.picardIntersectionNumber fun i ↦
    (CartierDivisor.classToPicAdd (classes i)).toMul

/-- Intersection numbers of actual Cartier divisors depend only on their divisor classes. -/
def cartierDivisorIntersectionNumber (P : IntersectionContext D C d)
    (divisors : Fin d → CartierDivisor X) : ℤ :=
  P.cartierClassIntersectionNumber fun i ↦
    CartierDivisor.toClass X (divisors i)

/-- The divisor and Picard formulations agree under `D ↦ O_X(D)`. -/
theorem cartierDivisorIntersectionNumber_eq_picard (P : IntersectionContext D C d)
    (divisors : Fin d → CartierDivisor X) :
    P.cartierDivisorIntersectionNumber divisors =
      P.picardIntersectionNumber fun i ↦ CartierDivisor.toPic (divisors i) := by
  apply P.picardIntersectionNumber_congr
  intro i
  rfl

/-- Principal equivalence does not change intersection numbers. -/
theorem cartierDivisorIntersectionNumber_eq_of_principalEquivalent
    (P : IntersectionContext D C d) {divisors divisors' : Fin d → CartierDivisor X}
    (h : ∀ i, CartierDivisor.toClass X (divisors i) =
      CartierDivisor.toClass X (divisors' i)) :
    P.cartierDivisorIntersectionNumber divisors =
      P.cartierDivisorIntersectionNumber divisors' := by
  unfold cartierDivisorIntersectionNumber cartierClassIntersectionNumber
  apply P.picardIntersectionNumber_congr
  intro i
  dsimp
  rw [h i]

/-- Adding a principal divisor in every slot leaves the intersection number unchanged. -/
theorem cartierDivisorIntersectionNumber_add_principal
    (P : IntersectionContext D C d) (divisors : Fin d → CartierDivisor X)
    (f : Fin d → Additive X.functionFieldˣ) :
    P.cartierDivisorIntersectionNumber
        (fun i ↦ divisors i + CartierDivisor.principal X (f i)) =
      P.cartierDivisorIntersectionNumber divisors := by
  apply P.cartierDivisorIntersectionNumber_eq_of_principalEquivalent
  intro i
  simp

/-- Symmetry also holds in the Cartier-divisor formulation. -/
theorem cartierDivisorIntersectionNumber_comp_perm
    (P : IntersectionContext D C d) (divisors : Fin d → CartierDivisor X)
    (σ : Equiv.Perm (Fin d)) :
    P.cartierDivisorIntersectionNumber (divisors ∘ σ) =
      P.cartierDivisorIntersectionNumber divisors := by
  rw [cartierDivisorIntersectionNumber_eq_picard,
    cartierDivisorIntersectionNumber_eq_picard]
  exact P.picardIntersectionNumber_comp_perm
    (fun i ↦ CartierDivisor.toPic (divisors i)) σ

/-! ## Dimension-zero, curve, and surface specializations -/

/-- In dimension zero the empty intersection is honestly the empty coefficient: `χ(O_X)`. -/
theorem point_normalization (P : IntersectionContext D C 0)
    (L : Fin 0 → Pic X) :
    P.picardIntersectionNumber L = P.eulerPic 1 := by
  rw [picardIntersectionNumber_eq_coefficient]
  simp [picardCoefficient]

/-- On a curve the divisor number is the first difference `χ(L) - χ(O_X)`. -/
theorem curve_intersection_eq (P : IntersectionContext D C 1)
    (L : Pic X) :
    P.picardIntersectionNumber (fun _ : Fin 1 ↦ L) = P.eulerPic L - P.eulerPic 1 := by
  rw [picardIntersectionNumber_eq_coefficient]
  simp [picardCoefficient, picardMixedDifference, picardDifference]

/-- The binary surface intersection coefficient. -/
def surfaceIntersectionNumber (P : IntersectionContext D C 2)
    (L M : Pic X) : ℤ :=
  picardCoefficient [L, M] P.eulerPic

/-- The binary name is exactly the `Fin 2` top Snapper coefficient. -/
theorem picardIntersectionNumber_fin2 (P : IntersectionContext D C 2)
    (L M : Pic X) :
    P.picardIntersectionNumber ![L, M] = P.surfaceIntersectionNumber L M := by
  rw [picardIntersectionNumber_eq_coefficient]
  rfl

/-- The surface coefficient is the expected inclusion-exclusion expression. -/
theorem surfaceIntersectionNumber_eq (P : IntersectionContext D C 2)
    (L M : Pic X) :
    P.surfaceIntersectionNumber L M =
      P.eulerPic (L * M) - P.eulerPic L - P.eulerPic M + P.eulerPic 1 := by
  simp [surfaceIntersectionNumber, picardCoefficient, picardMixedDifference,
    picardDifference, mul_comm]
  omega

/-- The surface specialization as a symmetric bilinear form on the additive Picard group. -/
noncomputable def surfaceIntersectionPairing (P : IntersectionContext D C 2) :
    Additive (Pic X) →ₗ[ℤ] Additive (Pic X) →ₗ[ℤ] ℤ where
  toFun L := (picardCoefficientAddHom [L.toMul] [] P.eulerPic
    (by simpa using P.picardDegreeLE)).toIntLinearMap
  map_add' L M := by
    ext N
    exact picardCoefficient_middle_mul [] [N.toMul] L.toMul M.toMul P.eulerPic
      (by simpa using P.picardDegreeLE)
  map_smul' m L := by
    ext M
    exact picardCoefficient_middle_zpow [] [M.toMul] L.toMul m P.eulerPic
      (by simpa using P.picardDegreeLE)

@[simp]
theorem surfaceIntersectionPairing_apply (P : IntersectionContext D C 2)
    (L M : Pic X) :
    P.surfaceIntersectionPairing (Additive.ofMul L) (Additive.ofMul M) =
      P.surfaceIntersectionNumber L M :=
  rfl

theorem surfaceIntersectionPairing_symm (P : IntersectionContext D C 2)
    (L M : Pic X) :
    P.surfaceIntersectionPairing (Additive.ofMul L) (Additive.ofMul M) =
      P.surfaceIntersectionPairing (Additive.ofMul M) (Additive.ofMul L) := by
  simp only [surfaceIntersectionPairing_apply, surfaceIntersectionNumber]
  exact picardCoefficient_eq_of_perm (List.Perm.swap L M []).symm P.eulerPic

end IntersectionContext

end

end AlgebraicGeometry.IntersectionTheory.Number
