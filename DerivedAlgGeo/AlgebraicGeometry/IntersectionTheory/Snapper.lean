/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Additivity
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Effective
import DerivedAlgGeo.AlgebraicGeometry.Divisors.PicardGroup
import DerivedAlgGeo.Algebra.NumericalPolynomial.Basic

/-!
# Snapper polynomiality for line-bundle twists

This file is the geometric bridge from Picard-group tensor powers and Euler characteristics to
the dimension-general finite-difference API in `NumericalPolynomial`.

Mathlib and the present geometric layer do not yet supply the hyperplane-section induction used
in the usual proof of Snapper's theorem, nor a general dimension API for schemes.  We therefore
package exactly that missing input as `GeometricInduction`: its steps are genuine short exact
sequences, with the scalar-linear connecting maps required by Euler additivity, and its terminal
families are zero after `d + 1` cuts.  `snapper` proves polynomiality from this certificate.  A
future geometric construction of the certificate will not change the theorem or its downstream
coefficient API.

The exponent of a line bundle is an integer.  Positive and negative powers are formed in
`Pic X`, so negative twists use the tensor inverse already contained in the Picard group rather
than a separate ad hoc construction.
-/

universe u v

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.IntersectionTheory.Snapper

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Scheme.Modules
open NumericalPolynomial

variable {k : Type u} [Field k]
variable {X : Variety k}

noncomputable section

/-! ## Integer powers in the Picard group -/

/-- The `n`th tensor power of a line-bundle class, including negative powers. -/
def picardPower (L : Pic X.toScheme) (n : ℤ) : Pic X.toScheme :=
  L ^ n

@[simp]
theorem picardPower_zero (L : Pic X.toScheme) : picardPower L 0 = 1 := by
  simp [picardPower]

@[simp]
theorem picardPower_add (L : Pic X.toScheme) (m n : ℤ) :
    picardPower L (m + n) = picardPower L m * picardPower L n := by
  exact zpow_add L m n

@[simp]
theorem picardPower_neg (L : Pic X.toScheme) (n : ℤ) :
    picardPower L (-n) = (picardPower L n)⁻¹ := by
  simp [picardPower]

/-- A chosen invertible-sheaf representative of the integer Picard power `L ^ n`. -/
noncomputable def linePower (L : Pic X.toScheme) (n : ℤ) : X.toScheme.Modules :=
  ((CategoryTheory.fromSkeleton (InvertibleSheaf X.toScheme)).obj
    (((picardPower L n : Pic X.toScheme) : PicardClass X.toScheme))).1

noncomputable instance linePower_isInvertible (L : Pic X.toScheme) (n : ℤ) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.toScheme.ringCatSheaf from linePower L n) :=
  ((CategoryTheory.fromSkeleton (InvertibleSheaf X.toScheme)).obj
    (((picardPower L n : Pic X.toScheme) : PicardClass X.toScheme))).2

/-- The chosen representative has exactly the requested Picard class. -/
@[simp]
theorem linePower_picardClass (L : Pic X.toScheme) (n : ℤ) :
    PicardClass.mk (linePower L n) =
      ((picardPower L n : Pic X.toScheme) : PicardClass X.toScheme) := by
  exact CategoryTheory.toSkeleton_fromSkeleton_obj _

/-! ## Multivariable twists -/

/-- Tensor a module sheaf successively by the integer powers indexed by a list. -/
noncomputable def twistModulesAlong {ι : Type v} :
    List ι → (ι → Pic X.toScheme) → NumericalPolynomial.Lattice ι → X.toScheme.Modules →
      X.toScheme.Modules
  | [], _, _, F => F
  | i :: indices, L, n, F =>
      tensorObj (linePower (L i) (n i)) (twistModulesAlong indices L n F)

/-- The simultaneous line-bundle twist.  The list order is fixed by `Finset.univ.toList`; the
Picard group records that different tensor orders are canonically isomorphic. -/
noncomputable def twistModules {ι : Type v} [Fintype ι] [DecidableEq ι]
    (L : ι → Pic X.toScheme) (n : NumericalPolynomial.Lattice ι) (F : X.toScheme.Modules) :
    X.toScheme.Modules :=
  twistModulesAlong Finset.univ.toList L n F

/-- Twisting carries an isomorphism of the underlying module sheaves through every tensor
factor. -/
noncomputable def twistModulesAlongMapIso {ι : Type v} (indices : List ι)
    (L : ι → Pic X.toScheme) (n : NumericalPolynomial.Lattice ι) {F G : X.toScheme.Modules}
    (e : F ≅ G) :
    twistModulesAlong indices L n F ≅ twistModulesAlong indices L n G := by
  induction indices with
  | nil => exact e
  | cons i indices ih =>
      exact (tensorLeftFunctor (linePower (L i) (n i))).mapIso ih

/-- Simultaneous twisting is functorial on isomorphisms. -/
noncomputable def twistModulesMapIso {ι : Type v} [Fintype ι] [DecidableEq ι]
    (L : ι → Pic X.toScheme) (n : NumericalPolynomial.Lattice ι) {F G : X.toScheme.Modules}
    (e : F ≅ G) : twistModules L n F ≅ twistModules L n G :=
  twistModulesAlongMapIso Finset.univ.toList L n e

/-- Coherence of every integer twist.  This field isolates the current missing closure theorem
for tensoring a finitely presented module sheaf by an invertible sheaf. -/
structure CoherentTwistFamily {ι : Type v} [Fintype ι] [DecidableEq ι]
    (F : Coh X.toScheme) (L : ι → Pic X.toScheme) where
  coherent : ∀ n : NumericalPolynomial.Lattice ι,
    Scheme.Modules.IsCoherent X.toScheme (twistModules L n F.1)

namespace CoherentTwistFamily

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {F : Coh X.toScheme} {L : ι → Pic X.toScheme}

/-- The coherent sheaf represented by the twist at exponent `n`. -/
noncomputable def obj (T : CoherentTwistFamily F L)
    (n : NumericalPolynomial.Lattice ι) : Coh X.toScheme :=
  ⟨twistModules L n F.1, T.coherent n⟩

end CoherentTwistFamily

/-- Euler characteristic as a function on the full integer exponent lattice. -/
noncomputable def eulerFunction {ι : Type v} [Fintype ι] [DecidableEq ι]
    (D : FiniteCohomology X) {F : Coh X.toScheme} {L : ι → Pic X.toScheme}
    (T : CoherentTwistFamily F L) : NumericalFunction ι :=
  fun n ↦ D.eulerCharacteristic (T.obj n)

/-! ## Geometric induction certificate -/

/-- The exact-sequence induction input in the classical proof of Snapper's theorem.

`descended directions n` is the sheaf obtained after the cuts in `directions`.  A new cut `v`
is exhibited by a short exact sequence

`0 ⟶ descended directions n ⟶ descended directions (n + v)
   ⟶ descended (v :: directions) n ⟶ 0`.

After `d + 1` cuts the descended sheaf is zero. -/
structure GeometricInduction {ι : Type v} [Fintype ι] [DecidableEq ι]
    (D : FiniteCohomology X) {F : Coh X.toScheme} {L : ι → Pic X.toScheme}
    (T : CoherentTwistFamily F L) (d : ℕ) where
  descended : List (NumericalPolynomial.Lattice ι) →
    NumericalPolynomial.Lattice ι → Coh X.toScheme
  baseIso : ∀ n, descended [] n ≅ T.obj n
  step : ∀ (_directions : List (NumericalPolynomial.Lattice ι))
    (_v : NumericalPolynomial.Lattice ι) (_n : NumericalPolynomial.Lattice ι),
    ShortComplex (Coh X.toScheme)
  stepShortExact : ∀ directions v n, (step directions v n).ShortExact
  stepX₁ : ∀ directions v n, (step directions v n).X₁ ≅ descended directions n
  stepX₂ : ∀ directions v n, (step directions v n).X₂ ≅ descended directions (n + v)
  stepX₃ : ∀ directions v n, (step directions v n).X₃ ≅ descended (v :: directions) n
  stepConnecting : ∀ directions v n,
    D.LinearConnectingMaps (step directions v n) (stepShortExact directions v n)
  terminalIsZero : ∀ directions, directions.length = d + 1 → ∀ n,
    IsZero (descended directions n)

namespace GeometricInduction

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {D : FiniteCohomology X} {F : Coh X.toScheme} {L : ι → Pic X.toScheme}
variable {T : CoherentTwistFamily F L} {d : ℕ}

/-- Euler characteristic of the family after a list of geometric cuts. -/
noncomputable def descendedEuler (I : GeometricInduction D T d)
    (directions : List (NumericalPolynomial.Lattice ι)) : NumericalFunction ι :=
  fun n ↦ D.eulerCharacteristic (I.descended directions n)

/-- Euler additivity identifies one geometric cut with one forward difference. -/
theorem difference_descendedEuler (I : GeometricInduction D T d)
    (directions : List (NumericalPolynomial.Lattice ι))
    (v : NumericalPolynomial.Lattice ι) :
    difference v (I.descendedEuler directions) = I.descendedEuler (v :: directions) := by
  funext n
  have hadd := D.eulerCharacteristic_additive (I.stepConnecting directions v n)
  rw [D.eulerCharacteristic_iso (I.stepX₂ directions v n),
    D.eulerCharacteristic_iso (I.stepX₁ directions v n),
    D.eulerCharacteristic_iso (I.stepX₃ directions v n)] at hadd
  simp only [difference_apply, descendedEuler]
  omega

/-- Every mixed difference is the Euler characteristic of the corresponding descended family. -/
theorem mixedDifference_eulerFunction (I : GeometricInduction D T d)
    (directions : List (NumericalPolynomial.Lattice ι)) :
    mixedDifference directions (eulerFunction D T) = I.descendedEuler directions := by
  induction directions with
  | nil =>
      funext n
      exact (D.eulerCharacteristic_iso (I.baseIso n)).symm
  | cons v directions ih =>
      rw [mixedDifference_cons, ih, I.difference_descendedEuler]

end GeometricInduction

/-! ## Snapper's theorem and its exposed difference coefficients -/

/-- The zero coherent sheaf has Euler characteristic zero, using the same global choice of
linear connecting maps required for all Euler-additivity arguments. -/
theorem eulerCharacteristic_isZero (D : FiniteCohomology X)
    (C : D.LinearConnectingSystem) {F : Coh X.toScheme} (hF : IsZero F) :
    D.eulerCharacteristic F = 0 := by
  let S : ShortComplex (Coh X.toScheme) :=
    ShortComplex.mk (0 : (0 : Coh X.toScheme) ⟶ 0) (0 : (0 : Coh X.toScheme) ⟶ 0)
      zero_comp
  have hS : S.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_of_isZero_X₂ S (isZero_zero _)
    · exact (isZero_zero _).mono _
    · exact (isZero_zero _).epi _
  have hadd := D.eulerCharacteristic_additive (C S hS)
  have hzero : D.eulerCharacteristic (0 : Coh X.toScheme) = 0 := by
    change D.eulerCharacteristic (0 : Coh X.toScheme) =
      D.eulerCharacteristic (0 : Coh X.toScheme) +
        D.eulerCharacteristic (0 : Coh X.toScheme) at hadd
    omega
  exact (D.eulerCharacteristic_iso (hF.isoZero)).trans hzero

/-- **Snapper polynomiality.**  Euler characteristics of simultaneous integer line-bundle twists
have total finite-difference degree at most `d`. -/
theorem snapper {ι : Type v} [Fintype ι] [DecidableEq ι]
    (D : FiniteCohomology X) (C : D.LinearConnectingSystem)
    {F : Coh X.toScheme} {L : ι → Pic X.toScheme} (T : CoherentTwistFamily F L) (d : ℕ)
    (I : GeometricInduction D T d) : DegreeLE d (eulerFunction D T) := by
  intro directions hlength
  rw [I.mixedDifference_eulerFunction]
  funext n
  exact eulerCharacteristic_isZero D C (I.terminalIsZero directions hlength n)

/-- The mixed-difference form needed by later intersection-theoretic constructions. -/
theorem mixedDifference_eq_euler_descended {ι : Type v} [Fintype ι] [DecidableEq ι]
    {D : FiniteCohomology X} {F : Coh X.toScheme} {L : ι → Pic X.toScheme}
    {T : CoherentTwistFamily F L} {d : ℕ} (I : GeometricInduction D T d)
    (directions : List (NumericalPolynomial.Lattice ι))
    (n : NumericalPolynomial.Lattice ι) :
    mixedDifference directions (eulerFunction D T) n =
      D.eulerCharacteristic (I.descended directions n) := by
  exact congrFun (I.mixedDifference_eulerFunction directions) n

/-- A Newton coefficient is the Euler characteristic of the descended sheaf at the origin. -/
theorem coefficient_eq_euler_descended {ι : Type v} [Fintype ι] [DecidableEq ι]
    {D : FiniteCohomology X} {F : Coh X.toScheme} {L : ι → Pic X.toScheme}
    {T : CoherentTwistFamily F L} {d : ℕ} (I : GeometricInduction D T d)
    (directions : List (NumericalPolynomial.Lattice ι)) :
    coefficient directions (eulerFunction D T) =
      D.eulerCharacteristic (I.descended directions 0) := by
  exact mixedDifference_eq_euler_descended I directions 0

/-! ## Invariance and one-variable specialization -/

/-- Euler-twist functions are invariant under isomorphism of the coherent base sheaf. -/
theorem eulerFunction_eq_of_coherentSheafIso {ι : Type v} [Fintype ι] [DecidableEq ι]
    (D : FiniteCohomology X) {F G : Coh X.toScheme} (e : F ≅ G)
    {L : ι → Pic X.toScheme} (TF : CoherentTwistFamily F L)
    (TG : CoherentTwistFamily G L) : eulerFunction D TF = eulerFunction D TG := by
  funext n
  apply D.eulerCharacteristic_iso
  exact ObjectProperty.isoMk (Scheme.coherent X.toScheme)
    (twistModulesMapIso L n ((Coh.ι X.toScheme).mapIso e))

/-- Equality in `Pic X` is precisely line-bundle isomorphism class equality, so pointwise equal
Picard classes give the same Euler-twist function. -/
theorem eulerFunction_eq_of_lineBundleIso {ι : Type v} [Fintype ι] [DecidableEq ι]
    (D : FiniteCohomology X) {F : Coh X.toScheme}
    {L M : ι → Pic X.toScheme} (h : ∀ i, L i = M i)
    (TL : CoherentTwistFamily F L) (TM : CoherentTwistFamily F M) :
    eulerFunction D TL = eulerFunction D TM := by
  have hLM : L = M := funext h
  subst M
  funext n
  apply D.eulerCharacteristic_iso
  exact ObjectProperty.isoMk (Scheme.coherent X.toScheme) (Iso.refl _)

/-- The ordinary one-variable Euler function attached to powers of one Picard class. -/
noncomputable def oneVariableEulerFunction (D : FiniteCohomology X)
    {F : Coh X.toScheme} (L : Pic X.toScheme)
    (T : CoherentTwistFamily F (fun _ : Fin 1 ↦ L)) : ℤ → ℤ :=
  fun n ↦ eulerFunction D T (oneVariablePoint n)

theorem oneVariable_eulerFunction (D : FiniteCohomology X)
    {F : Coh X.toScheme} (L : Pic X.toScheme)
    (T : CoherentTwistFamily F (fun _ : Fin 1 ↦ L)) :
    oneVariable (oneVariableEulerFunction D L T) = eulerFunction D T := by
  funext n
  apply congrArg (eulerFunction D T)
  funext i
  rw [Fin.eq_zero i]
  rfl

/-- One-variable specialization: the `(d + 1)`st ordinary forward difference vanishes. -/
theorem oneVariable_fwdDiff_euler_vanishes (D : FiniteCohomology X)
    (C : D.LinearConnectingSystem) {F : Coh X.toScheme} (L : Pic X.toScheme)
    (T : CoherentTwistFamily F (fun _ : Fin 1 ↦ L)) (d : ℕ)
    (I : GeometricInduction D T d) :
    (fwdDiff (1 : ℤ))^[d + 1] (oneVariableEulerFunction D L T) = 0 := by
  apply oneVariable_fwdDiff_vanishes
  rw [oneVariable_eulerFunction]
  exact snapper D C T d I

end

end AlgebraicGeometry.IntersectionTheory.Snapper
