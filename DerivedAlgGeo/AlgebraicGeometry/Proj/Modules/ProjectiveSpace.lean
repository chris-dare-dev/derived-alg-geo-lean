/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.Cech.Basic
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.Finiteness
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Twists on polynomial projective space

This file constructs the comparison between degree-`d` homogeneous polynomials and global
sections of `O(d)` on polynomial `Proj`.  The proof uses the variable basic-open cover, the
constructed chart comparison from `TwistChart`, and the generic point of the polynomial ring.

The global-section comparison is stated over a field and for a nonempty finite variable type,
which is the projective-space range consumed by the Serre-finiteness argument.  These hypotheses
make the generic-point and denominator-cancellation steps explicit.

The global-section comparison is for a *nonnegative* twist. The imported algebraic Čech terms
come in both flavours: `polynomialVariableCechTerm` for `d : ℕ` and
`polynomialVariableIntCechTerm` for `d : ℤ`. This file begins where geometry enters: it compares
those terms with projective basic opens and sections. The two algebraic terms are not yet
identified for a nonnegative `d`; the landed Čech differential still uses the `ℕ` version.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace
open scoped DirectSum Pointwise

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Global sections of the natural shift associated to `A(d)` on polynomial `Proj`. -/
abbrev polynomialNatGlobalSections (ι k : Type u) [Field k] (d : ℕ) :=
  (associatedSheafInType (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)).1.obj
      (op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))

/-- A homogeneous polynomial of degree `d` defines the global section represented everywhere
by the fraction `p / 1` in the shifted module. -/
noncomputable def polynomialToNatGlobalSections (ι k : Type u) [Field k] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d →+
      polynomialNatGlobalSections ι k d where
  toFun p := by
    let num : ↥(GradedModule.natShift
        (polynomialGrading ι k) d 0) :=
      ⟨p.1, by change p.1 ∈ polynomialGrading ι k (0 + d); simpa using p.2⟩
    let den : polynomialGrading ι k 0 :=
      ⟨1, one_mem_graded (polynomialGrading ι k)⟩
    refine ⟨fun x => DegreeZeroLocalization.mk
      { deg := 0
        num := num
        den := den
        den_mem := Ideal.IsPrime.one_notMem inferInstance }, ?_⟩
    intro x
    exact ⟨⊤, x.2, 𝟙 _, 0, num, den,
      fun _ => Ideal.IsPrime.one_notMem inferInstance, fun _ => rfl⟩
  map_zero' := by
    apply section_ext
    funext x
    apply DegreeZeroLocalization.ext
    change LocalizedModule.mk (0 : MvPolynomial ι k) _ = 0
    simp
  map_add' p q := by
    apply section_ext
    funext x
    apply DegreeZeroLocalization.ext
    change LocalizedModule.mk ((p + q :
      MvPolynomial.homogeneousSubmodule ι k d) : MvPolynomial ι k) _ =
        LocalizedModule.mk (p : MvPolynomial ι k) _ +
          LocalizedModule.mk (q : MvPolynomial ι k) _
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp⟩

/-- The zero homogeneous ideal is the generic point of polynomial projective space. -/
def polynomialGenericPoint (ι k : Type u) [Field k] [Nonempty ι] :
    ProjectiveSpectrum (polynomialGrading ι k) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial ι k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le h := by
    let i : ι := Classical.choice inferInstance
    have hX : MvPolynomial.X i ∈
        HomogeneousIdeal.irrelevant (polynomialGrading ι k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X k i)
    have h0 : (MvPolynomial.X i : MvPolynomial ι k) ∈ (⊥ : Ideal _) := h hX
    rw [Ideal.mem_bot] at h0
    exact (MvPolynomial.X_ne_zero i) h0

/-- Restriction of a global natural-twist section to the variable chart `D₊(Xᵢ)`. -/
noncomputable def restrictNatGlobalSectionsToVariable
    (ι k : Type u) [Field k] (d : ℕ) (i : ι) :
    polynomialNatGlobalSections ι k d →+
      (associatedSheafInType (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d)).1.obj
          (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
            (MvPolynomial.X i))) where
  toFun s := ((associatedSheafInType (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)).presheaf.map
      (homOfLE le_top).op).hom s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The homogeneous fraction representing a global section on the variable chart `D₊(Xᵢ)`. -/
noncomputable def variableFractionOfGlobalSection
    (ι k : Type u) [Field k] (d : ℕ) (i : ι) :
    polynomialNatGlobalSections ι k d →+
      DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) :=
  (natShiftBasicOpenSectionAddEquiv (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) d).symm.toAddMonoidHom.comp
      (restrictNatGlobalSectionsToVariable ι k d i)

theorem moduleAwayToSection_variableFractionOfGlobalSection
    (ι k : Type u) [Field k] (d : ℕ) (i : ι)
    (s : polynomialNatGlobalSections ι k d) :
    moduleAwayToSection (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (MvPolynomial.X i)
        (variableFractionOfGlobalSection ι k d i s) =
      restrictNatGlobalSectionsToVariable ι k d i s := by
  rw [← natShiftBasicOpenSectionAddEquiv_toAddMonoidHom
    (polynomialGrading ι k) (MvPolynomial.isHomogeneous_X k i) d]
  exact (natShiftBasicOpenSectionAddEquiv (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) d).apply_symm_apply _

/-- The denominator submonoid at the polynomial generic point. -/
abbrev polynomialGenericDenominators (ι k : Type u) [Field k] [Nonempty ι] :
    Submonoid (MvPolynomial ι k) :=
  (polynomialGenericPoint ι k).asHomogeneousIdeal.toIdeal.primeCompl

/-- Every variable is invertible at the polynomial generic point. -/
theorem powers_X_le_polynomialGenericDenominators
    (ι k : Type u) [Field k] [Nonempty ι] (i : ι) :
    Submonoid.powers (MvPolynomial.X i) ≤ polynomialGenericDenominators ι k := by
  apply Submonoid.powers_le.mpr
  change (MvPolynomial.X i : MvPolynomial ι k) ∉ (⊥ : Ideal _)
  simpa only [Ideal.mem_bot] using MvPolynomial.X_ne_zero (R := k) i

/-- A variable-chart fraction viewed in the common generic localization. -/
noncomputable def variableFractionToGeneric
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) (i : ι) :
    DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) →+
      DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d)
          (polynomialGenericDenominators ι k) :=
  DegreeZeroLocalization.mapOfLE
    (powers_X_le_polynomialGenericDenominators ι k i)

/-- All variable-chart representatives of a global section have the same generic value. -/
theorem variableFractionToGeneric_apply_globalSection
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) (i : ι)
    (s : polynomialNatGlobalSections ι k d) :
    variableFractionToGeneric ι k d i
        (variableFractionOfGlobalSection ι k d i s) =
      s.1 ⟨polynomialGenericPoint ι k, Set.mem_univ _⟩ := by
  let x : ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X i) :=
    ⟨polynomialGenericPoint ι k,
      powers_X_le_polynomialGenericDenominators ι k i
        ⟨1, by simp⟩⟩
  have h := congr_arg (fun t => t.1 x)
    (moduleAwayToSection_variableFractionOfGlobalSection ι k d i s)
  rw [moduleAwayToSection_apply] at h
  exact h

/-- Passing from a variable localization to the generic localization loses no information. -/
theorem variableFractionToGeneric_injective
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) (i : ι) :
    Function.Injective (variableFractionToGeneric ι k d i) := by
  intro z w hzw
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  obtain ⟨e, rfl⟩ := DegreeZeroLocalization.mk_surjective w
  simp only [variableFractionToGeneric, DegreeZeroLocalization.mapOfLE_mk] at hzw
  rw [DegreeZeroLocalization.mk_eq_mk_iff] at hzw
  obtain ⟨u, hu⟩ := hzw
  have hu0 : (u : MvPolynomial ι k) ≠ 0 := by
    have hu' := u.2
    change (u : MvPolynomial ι k) ∉ (⊥ : Ideal _) at hu'
    intro h0
    exact hu' (by simpa only [Ideal.mem_bot] using h0)
  have hcancel : (e.den : MvPolynomial ι k) * (c.num : MvPolynomial ι k) =
      (c.den : MvPolynomial ι k) * (e.num : MvPolynomial ι k) :=
    mul_left_cancel₀ hu0 (by simpa only [smul_eq_mul, mul_assoc] using hu)
  rw [DegreeZeroLocalization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  simpa [smul_eq_mul] using hcancel

/-- Dividing a homogeneous polynomial of degree `n + d` by `Xᵢⁿ`, when the division is exact,
produces a homogeneous polynomial of degree `d`. -/
theorem divMonomial_single_mem_homogeneousSubmodule
    (ι k : Type u) [Field k] (i : ι) (n d : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k (n + d)) :
    p.divMonomial (Finsupp.single i n) ∈
      MvPolynomial.homogeneousSubmodule ι k d := by
  intro s hs
  have hcoeff : MvPolynomial.coeff (Finsupp.single i n + s) p ≠ 0 := by
    simpa only [MvPolynomial.coeff_divMonomial] using hs
  have hdeg := hp hcoeff
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, nsmul_eq_mul, mul_one] at hdeg
  exact Nat.add_left_cancel hdeg

/-- Exact division by `Xᵢⁿ` reconstructs the original polynomial. -/
theorem X_pow_mul_divMonomial_single
    (ι k : Type u) [Field k] (i : ι) (n : ℕ) (p : MvPolynomial ι k)
    (hdiv : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣ p) :
    MvPolynomial.X i ^ n * p.divMonomial (Finsupp.single i n) = p := by
  rw [MvPolynomial.X_pow_eq_monomial]
  have hmod : p.modMonomial (Finsupp.single i n) = 0 :=
    MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero.mp
      (by simpa only [MvPolynomial.X_pow_eq_monomial] using hdiv)
  simpa only [hmod, add_zero] using
    MvPolynomial.divMonomial_add_modMonomial p (Finsupp.single i n)

/-- A fraction with denominator a power of `Xᵢ` that also admits a denominator involving only a
different variable has numerator divisible by the entire power of `Xᵢ`. -/
theorem X_pow_dvd_of_cross_mul
    (ι k : Type u) [Field k] {i j : ι} (hij : i ≠ j) (n m : ℕ)
    (p q : MvPolynomial ι k)
    (hcross : MvPolynomial.X j ^ m * p = MvPolynomial.X i ^ n * q) :
    (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣ p := by
  have hnot : ¬(MvPolynomial.X i : MvPolynomial ι k) ∣ MvPolynomial.X j ^ m := by
    intro h
    have hX : (MvPolynomial.X i : MvPolynomial ι k) ∣ MvPolynomial.X j :=
      (MvPolynomial.X_prime (R := k) (i := i)).dvd_of_dvd_pow h
    exact hij (MvPolynomial.X_dvd_X.mp hX)
  apply (MvPolynomial.X_prime (R := k) (i := i)).pow_dvd_of_dvd_mul_left n hnot
  exact ⟨q, hcross⟩

/-- The chart fraction `p / 1` associated to a degree-`d` homogeneous polynomial. -/
def polynomialVariableFraction
    (ι k : Type u) [Field k] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d) (i : ι) :
    DegreeZeroLocalization (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) :=
  DegreeZeroLocalization.mk
    { deg := 0
      num := ⟨p.1, by
        change p.1 ∈ polynomialGrading ι k (0 + d)
        simpa using p.2⟩
      den := ⟨1, one_mem_graded (polynomialGrading ι k)⟩
      den_mem := Submonoid.one_mem _ }

/-- Restricting the polynomial section to a variable chart recovers the literal fraction
`p / 1`. -/
theorem variableFractionOfGlobalSection_polynomial
    (ι k : Type u) [Field k] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d) (i : ι) :
    variableFractionOfGlobalSection ι k d i
        (polynomialToNatGlobalSections ι k d p) =
      polynomialVariableFraction ι k d p i := by
  apply (projectiveSpace_variableSection_bijective ι k i d).1
  rw [moduleAwayToSection_variableFractionOfGlobalSection]
  rw [polynomialVariableFraction, moduleAwayToSection_mk]
  apply section_ext
  funext x
  apply DegreeZeroLocalization.ext
  rfl

/-- The fractions `p / 1` on any two variable charts agree in the generic localization. -/
theorem polynomialVariableFractionToGeneric_independent
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d) (i j : ι) :
    variableFractionToGeneric ι k d i (polynomialVariableFraction ι k d p i) =
      variableFractionToGeneric ι k d j (polynomialVariableFraction ι k d p j) := by
  simp only [variableFractionToGeneric, polynomialVariableFraction,
    DegreeZeroLocalization.mapOfLE_mk]

/-- The variables generate the polynomial ring over its degree-zero part.

This is the hypothesis `degreeOneCharts_coversTop` takes, extracted from the cover proof below
so that the twist results can consume it directly. -/
theorem polynomialVariable_adjoin_eq_top (ι k : Type u) [Field k] :
    Algebra.adjoin (polynomialGrading ι k 0)
      (Set.range fun i => ((MvPolynomial.X i : MvPolynomial ι k))) = ⊤ := by
  set S := Algebra.adjoin (polynomialGrading ι k 0)
    (Set.range fun i => ((MvPolynomial.X i : MvPolynomial ι k))) with hS
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact S.algebraMap_mem
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (σ := ι) r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- The standard variable basic opens cover polynomial projective space. -/
theorem polynomialVariableBasicOpen_cover (ι k : Type u) [Field k] :
    (⨆ i : ι, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X i)) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · let S := Algebra.adjoin (polynomialGrading ι k 0)
      (Set.range (MvPolynomial.X : ι → MvPolynomial ι k))
    change S = ⊤
    apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C r =>
        exact S.algebraMap_mem
          ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (σ := ι) r⟩
    | add p q hp hq => exact S.add_mem hp hq
    | mul_X p i hp =>
        exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- A global section of a nonnegative twist on polynomial projective space is represented by a
single homogeneous polynomial. -/
theorem polynomialToNatGlobalSections_surjective
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    Function.Surjective (polynomialToNatGlobalSections ι k d) := by
  intro s
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let zi := variableFractionOfGlobalSection ι k d i s
  let zj := variableFractionOfGlobalSection ι k d j s
  obtain ⟨ci, hci⟩ := DegreeZeroLocalization.mk_surjective zi
  obtain ⟨cj, hcj⟩ := DegreeZeroLocalization.mk_surjective zj
  obtain ⟨n, hn⟩ := ci.den_mem
  obtain ⟨m, hm⟩ := cj.den_mem
  have hpowi : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∈
      polynomialGrading ι k n := by
    simpa using SetLike.pow_mem_graded (A := polynomialGrading ι k) n
      (MvPolynomial.isHomogeneous_X k i)
  have hpowj : (MvPolynomial.X j : MvPolynomial ι k) ^ m ∈
      polynomialGrading ι k m := by
    simpa using SetLike.pow_mem_graded (A := polynomialGrading ι k) m
      (MvPolynomial.isHomogeneous_X k j)
  have hdegi : ci.deg = n := by
    apply DirectSum.degree_eq_of_mem_mem (polynomialGrading ι k) ci.den.2
      (hn ▸ hpowi)
    simpa only [← hn] using pow_ne_zero n (MvPolynomial.X_ne_zero (R := k) i)
  have hdegj : cj.deg = m := by
    apply DirectSum.degree_eq_of_mem_mem (polynomialGrading ι k) cj.den.2
      (hm ▸ hpowj)
    simpa only [← hm] using pow_ne_zero m (MvPolynomial.X_ne_zero (R := k) j)
  have hgeneric :
      variableFractionToGeneric ι k d i (DegreeZeroLocalization.mk ci) =
        variableFractionToGeneric ι k d j (DegreeZeroLocalization.mk cj) := by
    rw [hci, hcj, variableFractionToGeneric_apply_globalSection,
      variableFractionToGeneric_apply_globalSection]
  simp only [variableFractionToGeneric, DegreeZeroLocalization.mapOfLE_mk] at hgeneric
  rw [DegreeZeroLocalization.mk_eq_mk_iff] at hgeneric
  obtain ⟨u, hu⟩ := hgeneric
  have hu0 : (u : MvPolynomial ι k) ≠ 0 := by
    have hu' := u.2
    change (u : MvPolynomial ι k) ∉ (⊥ : Ideal _) at hu'
    intro h0
    exact hu' (by simpa only [Ideal.mem_bot] using h0)
  have hcross0 : (cj.den : MvPolynomial ι k) * (ci.num : MvPolynomial ι k) =
      (ci.den : MvPolynomial ι k) * (cj.num : MvPolynomial ι k) :=
    mul_left_cancel₀ hu0 (by simpa only [smul_eq_mul, mul_assoc] using hu)
  have hcross : MvPolynomial.X j ^ m * (ci.num : MvPolynomial ι k) =
      MvPolynomial.X i ^ n * (cj.num : MvPolynomial ι k) := by
    simpa only [hn, hm] using hcross0
  have hdiv : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣
      (ci.num : MvPolynomial ι k) :=
    X_pow_dvd_of_cross_mul ι k hij n m _ _ hcross
  have hpnum : (ci.num : MvPolynomial ι k) ∈
      MvPolynomial.homogeneousSubmodule ι k (n + d) := by
    have hpnum0 := ci.num.2
    change (ci.num : MvPolynomial ι k) ∈
      polynomialGrading ι k (ci.deg + d) at hpnum0
    simpa only [hdegi] using hpnum0
  let p : MvPolynomial.homogeneousSubmodule ι k d :=
    ⟨MvPolynomial.divMonomial (ci.num : MvPolynomial ι k) (Finsupp.single i n), by
      apply divMonomial_single_mem_homogeneousSubmodule ι k i n d _ hpnum⟩
  refine ⟨p, ?_⟩
  apply section_ext
  funext x
  have hx : x.1 ∈ (⨆ a : ι, ProjectiveSpectrum.basicOpen
      (polynomialGrading ι k) (MvPolynomial.X a)) := by
    rw [polynomialVariableBasicOpen_cover]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let xa : ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X a) := ⟨x.1, ha⟩
  have hp_generic : variableFractionToGeneric ι k d i
      (polynomialVariableFraction ι k d p i) =
        variableFractionToGeneric ι k d i
          (variableFractionOfGlobalSection ι k d i s) := by
    change variableFractionToGeneric ι k d i
      (polynomialVariableFraction ι k d p i) =
        variableFractionToGeneric ι k d i zi
    rw [← hci]
    simp only [polynomialVariableFraction, variableFractionToGeneric,
      DegreeZeroLocalization.mapOfLE_mk]
    rw [DegreeZeroLocalization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    have hdenmul : (ci.den : MvPolynomial ι k) * (p : MvPolynomial ι k) =
        (ci.num : MvPolynomial ι k) := by
      rw [← hn]
      simpa [p] using
        X_pow_mul_divMonomial_single ι k i n (ci.num : MvPolynomial ι k) hdiv
    simpa [smul_eq_mul] using hdenmul
  have ha_fraction : variableFractionOfGlobalSection ι k d a s =
      polynomialVariableFraction ι k d p a := by
    apply variableFractionToGeneric_injective ι k d a
    calc
      variableFractionToGeneric ι k d a
          (variableFractionOfGlobalSection ι k d a s) =
          s.1 ⟨polynomialGenericPoint ι k, Set.mem_univ _⟩ :=
        variableFractionToGeneric_apply_globalSection ι k d a s
      _ = variableFractionToGeneric ι k d i
          (variableFractionOfGlobalSection ι k d i s) :=
        (variableFractionToGeneric_apply_globalSection ι k d i s).symm
      _ = variableFractionToGeneric ι k d i
          (polynomialVariableFraction ι k d p i) := hp_generic.symm
      _ = variableFractionToGeneric ι k d a
          (polynomialVariableFraction ι k d p a) :=
        polynomialVariableFractionToGeneric_independent ι k d p i a
  have hsections := congr_arg (fun t => t.1 xa)
    (congr_arg (moduleAwayToSection (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (MvPolynomial.X a)) ha_fraction)
  rw [moduleAwayToSection_variableFractionOfGlobalSection,
    ← variableFractionOfGlobalSection_polynomial,
    moduleAwayToSection_variableFractionOfGlobalSection] at hsections
  exact hsections.symm

/-- Distinct homogeneous polynomials define distinct global sections. -/
theorem polynomialToNatGlobalSections_injective
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) :
    Function.Injective (polynomialToNatGlobalSections ι k d) := by
  intro p q hpq
  let i : ι := Classical.choice inferInstance
  have hchart := congr_arg (variableFractionOfGlobalSection ι k d i) hpq
  rw [variableFractionOfGlobalSection_polynomial,
    variableFractionOfGlobalSection_polynomial] at hchart
  have hgeneric := congr_arg (variableFractionToGeneric ι k d i) hchart
  simp only [variableFractionToGeneric, polynomialVariableFraction,
    DegreeZeroLocalization.mapOfLE_mk] at hgeneric
  rw [DegreeZeroLocalization.mk_eq_mk_iff] at hgeneric
  obtain ⟨u, hu⟩ := hgeneric
  have hu0 : (u : MvPolynomial ι k) ≠ 0 := by
    have hu' := u.2
    change (u : MvPolynomial ι k) ∉ (⊥ : Ideal _) at hu'
    intro h0
    exact hu' (by simpa only [Ideal.mem_bot] using h0)
  apply Subtype.ext
  apply mul_left_cancel₀ hu0
  simpa [smul_eq_mul] using hu

/-- Concrete additive comparison between degree-`d` homogeneous polynomials and global sections
of the natural-shift model of `O(d)`. -/
noncomputable def polynomialNatGlobalSectionsAddEquiv
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d ≃+
      polynomialNatGlobalSections ι k d :=
  AddEquiv.ofBijective (polynomialToNatGlobalSections ι k d)
    ⟨polynomialToNatGlobalSections_injective ι k d,
      polynomialToNatGlobalSections_surjective ι k d⟩

/-- Global sections of the integer-indexed twisting sheaf `O(d)`. -/
abbrev polynomialTwistingGlobalSections (ι k : Type u) [Field k] (d : ℕ) :=
  (twistingSheaf (polynomialGrading ι k) (d : ℤ)).val.obj
    (op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))

/-- For a nonnegative twist, transport global sections from the natural-shift model to the
integer-indexed twisting sheaf. -/
noncomputable def polynomialNatToTwistingGlobalSectionsAddEquiv
    (ι k : Type u) [Field k] (d : ℕ) :
    polynomialNatGlobalSections ι k d ≃+
      polynomialTwistingGlobalSections ι k d :=
  (asIso ((twistingSheafOfNatIso (polynomialGrading ι k) d).hom.app
    (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))).addCommGroupIsoToAddEquiv.symm

/-- The concrete global-section comparison requested for polynomial projective space:
degree-`d` homogeneous polynomials are exactly `Γ(Proj k[Xᵢ], O(d))`. -/
noncomputable def polynomialTwistingGlobalSectionsAddEquiv
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d ≃+
      polynomialTwistingGlobalSections ι k d :=
  (polynomialNatGlobalSectionsAddEquiv ι k d).trans
    (polynomialNatToTwistingGlobalSectionsAddEquiv ι k d)

/-- Global sections equipped with the canonical field-module structure transported through the
explicit polynomial comparison.  This avoids pretending that a separate base-ring action is
definitionally present in Mathlib's sheaf-of-modules section type. -/
noncomputable def polynomialTwistingGlobalSectionsModule
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) : ModuleCat.{u} k := by
  let e := polynomialTwistingGlobalSectionsAddEquiv ι k d
  letI : Module k (polynomialTwistingGlobalSections ι k d) := e.symm.module k
  exact ModuleCat.of k (polynomialTwistingGlobalSections ι k d)

/-- The concrete comparison as an isomorphism of `k`-modules, using the transported action made
explicit by `polynomialTwistingGlobalSectionsModule`. -/
noncomputable def polynomialTwistingGlobalSectionsModuleIso
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    ModuleCat.of k (MvPolynomial.homogeneousSubmodule ι k d) ≅
      polynomialTwistingGlobalSectionsModule ι k d := by
  let e := polynomialTwistingGlobalSectionsAddEquiv ι k d
  letI : Module k (polynomialTwistingGlobalSections ι k d) := e.symm.module k
  exact LinearEquiv.toModuleIso (e.symm.linearEquiv (A := k)).symm

/-- Nonnegative twists on polynomial projective space are quasi-coherent.

The variable charts have degree one and cover, which is exactly the hypothesis of
`natShift_isQuasicoherent`.  No comparison on higher-degree charts is needed or available. -/
theorem polynomialNatShift_isQuasicoherent (ι k : Type u) [Field k] (d : ℕ) :
    (associatedSheaf (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d)).IsQuasicoherent :=
  natShift_isQuasicoherent (polynomialGrading ι k)
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
    (polynomialVariable_adjoin_eq_top ι k)

/-- Every integer twist of polynomial projective space is quasi-coherent.

The variable charts have degree one and generate, which is exactly the hypothesis
`intShift_isQuasicoherent` takes. The sign of `d` never enters. This is the negative-twist
input the Serre-finiteness dévissage needs. -/
theorem polynomialIntShift_isQuasicoherent (ι k : Type u) [Field k] (d : ℤ) :
    (associatedSheaf (polynomialGrading ι k)
      (intShift (polynomialGrading ι k) d)).IsQuasicoherent :=
  intShift_isQuasicoherent (polynomialGrading ι k)
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
    (polynomialVariable_adjoin_eq_top ι k)

/-! ## Comparing the algebraic variable Čech diagram with projective basic opens -/

/-- The basic open of the product denominator is exactly the finite intersection of the
corresponding variable charts. -/
theorem basicOpen_polynomialVariableCechDenominator
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x) =
      ⨅ a, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X (x a)) := by
  classical
  have hInf : (⨅ a, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X (x a))) =
      Finset.univ.inf fun a => ProjectiveSpectrum.basicOpen
        (polynomialGrading ι k) (MvPolynomial.X (x a)) := by
    rw [Finset.inf_eq_iInf]
    simp
  rw [hInf]
  unfold polynomialVariableCechDenominator
  change ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (∏ a ∈ Finset.univ, MvPolynomial.X (x a)) =
    Finset.univ.inf fun a => ProjectiveSpectrum.basicOpen
      (polynomialGrading ι k) (MvPolynomial.X (x a))
  generalize (Finset.univ : Finset (Fin (n + 1))) = F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
      rw [Finset.prod_insert ha, Finset.inf_insert, ProjectiveSpectrum.basicOpen_mul, ih]

/-- A Čech intersection lies inside the chart of its first variable, which is the degree-one
chart the sheaf-level trivialization needs. -/
theorem basicOpen_denominator_le (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x) ≤
      ProjectiveSpectrum.basicOpen (polynomialGrading ι k) (MvPolynomial.X (x 0)) := by
  rw [← X_mul_cechCofactor ι k x, ProjectiveSpectrum.basicOpen_mul]
  exact inf_le_left

/-- The algebraic Čech term for `O(d)` is the sections of `O(d)` over the corresponding
intersection.

Three comparisons compose, and each is used at exactly the generality it has.  The denominator
has degree `n + 1`, so no degree-one hypothesis can be applied to it directly:

* `natShiftLinearEquivOfMulMem` trivializes `A(d)` at the *algebraic* level.  It needs `X (x 0)`
  invertible in the localization rather than a member of it, which `X_mul_cechCofactor` supplies —
  `.powers (∏ₐ X_{x a})` contains no degree-one element for `n ≥ 1`.
* `selfBasicOpenSectionAddEquiv` compares the structure module with its sections, and is already
  general in the degree of the denominator.
* `natShiftSectionAddEquivOn` trivializes at the *sheaf* level, over any open below a degree-one
  chart; `basicOpen_denominator_le` places the intersection below the first variable's chart. -/
noncomputable def cechTermSectionAddEquiv (ι k : Type u) [Field k] (d : ℕ) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    polynomialVariableCechTerm ι k d n x ≃+
      (associatedSheafInType (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d)).1.obj
        (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
          (polynomialVariableCechDenominator ι k x))) :=
  (DegreeZeroLocalization.natShiftLinearEquivOfMulMem (polynomialGrading ι k)
      (MvPolynomial.isHomogeneous_X k (x 0)) d (cechCofactor_mem ι k x)
      (by rw [X_mul_cechCofactor]; exact Submonoid.mem_powers _)).toAddEquiv.trans
    ((selfBasicOpenSectionAddEquiv (polynomialGrading ι k)
        (polynomialVariableCechDenominator_mem ι k x) (Nat.succ_pos n)).trans
      (natShiftSectionAddEquivOn (polynomialGrading ι k)
        (MvPolynomial.isHomogeneous_X k (x 0)) d (basicOpen_denominator_le ι k x)).symm)

/-- The Čech comparison is the canonical homogeneous-fraction section map.

This is what makes the comparison usable rather than merely existent. As defined,
`cechTermSectionAddEquiv` is a composite of three equivalences, two of which are built from a
choice of trivializing element — the first variable `X (x 0)` of the index. Nothing about the
statement should depend on that choice, and this says so: the composite is
`moduleAwayToSection`, which is canonical and refers to no trivialization at all. The two
trivializations cancel, one algebraic and one pointwise on stalks.

The consequence worth having is that `moduleAwayToSection` is defined *pointwise*, by enlarging
the denominator submonoid at each point. Any statement about how the comparison interacts with
restriction to a smaller open therefore reduces to a pointwise computation, instead of having to
be pushed through three constructed equivalences. That is the route to the Čech differential. -/
theorem cechTermSectionAddEquiv_apply_mk (ι k : Type u) [Field k] (d : ℕ) {n : ℕ}
    (x : Fin (n + 1) → ι)
    (c : NumDenSameDeg (polynomialGrading ι k) (natShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k x))) :
    cechTermSectionAddEquiv ι k d x (DegreeZeroLocalization.mk c) =
      moduleAwayToSection (polynomialGrading ι k) (natShift (polynomialGrading ι k) d)
        (polynomialVariableCechDenominator ι k x) (DegreeZeroLocalization.mk c) := by
  change natShiftSectionFromSelfOn (polynomialGrading ι k)
      (MvPolynomial.isHomogeneous_X k (x 0)) d (basicOpen_denominator_le ι k x)
      (selfBasicOpenSectionAddEquiv (polynomialGrading ι k)
        (polynomialVariableCechDenominator_mem ι k x) (Nat.succ_pos n)
        (DegreeZeroLocalization.natShiftLinearEquivOfMulMem (polynomialGrading ι k)
          (MvPolynomial.isHomogeneous_X k (x 0)) d (cechCofactor_mem ι k x) _
          (DegreeZeroLocalization.mk c))) = _
  rw [DegreeZeroLocalization.natShiftLinearEquivOfMulMem_apply_mk,
    natShiftSectionFromSelfOn_selfBasicOpenSectionAddEquiv_mk]
  congr 1
  apply DegreeZeroLocalization.ext
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul, mul_pow]
  ring

/-- As an additive map, the Čech comparison is exactly the canonical fraction-to-section map. -/
theorem cechTermSectionAddEquiv_toAddMonoidHom (ι k : Type u) [Field k] (d : ℕ) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    (cechTermSectionAddEquiv ι k d x).toAddMonoidHom =
      moduleAwayToSection (polynomialGrading ι k) (natShift (polynomialGrading ι k) d)
        (polynomialVariableCechDenominator ι k x) :=
  moduleAwayToSection_unique _ _ _ _ (cechTermSectionAddEquiv_apply_mk ι k d x)

/-- The Čech comparison intertwines the algebraic face with restriction of sections.

This is the compatibility the Čech differential is transported by: on the algebraic side the
`j`-th face is `polynomialVariableCechFace`, on the sheaf side it is restriction from the
`(n + 1)`-fold intersection to the `(n + 2)`-fold one, and the comparison carries one to the
other. It reduces to `moduleAwayToSection_res_faceMap` because
`cechTermSectionAddEquiv_toAddMonoidHom` already identifies the comparison with the canonical
pointwise map, where restriction only reindexes the point. -/
theorem cechTermSectionAddEquiv_res_face (ι k : Type u) [Field k] (d : ℕ) {n : ℕ}
    (x : Fin (n + 2) → ι) (j : Fin (n + 2))
    (i : (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k (x ∘ j.succAbove))) :
          (Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))ᵒᵖ) ⟶
      op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x)))
    (z : polynomialVariableCechTerm ι k d n (x ∘ j.succAbove)) :
    (associatedSheafInType (polynomialGrading ι k)
          (natShift (polynomialGrading ι k) d)).1.map i
        (cechTermSectionAddEquiv ι k d (x ∘ j.succAbove) z) =
      cechTermSectionAddEquiv ι k d x (polynomialVariableCechFace ι k d x j z) := by
  change (associatedSheafInType (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d)).1.map i
      ((cechTermSectionAddEquiv ι k d (x ∘ j.succAbove)).toAddMonoidHom z) =
    (cechTermSectionAddEquiv ι k d x).toAddMonoidHom
      (polynomialVariableCechFace ι k d x j z)
  rw [cechTermSectionAddEquiv_toAddMonoidHom, cechTermSectionAddEquiv_toAddMonoidHom]
  exact moduleAwayToSection_res_faceMap (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)
    (MvPolynomial.isHomogeneous_X k (x j))
    (polynomialVariableCechDenominator_succAbove_mem ι k x j)
    (polynomialVariableCechDenominator_succAbove ι k x j) i z

/-- The integer-twist Čech comparison: the algebraic term at one variable intersection is the
sections of `O(d)` there, for a twist of either sign.

Five steps rather than the nonnegative case's three, and the two extra ones are both grading
transports rather than geometry:

1. `intShiftZeroLinearEquivOfMulMem` — the cofactor trivialization. The Čech denominator has
   degree `n + 1`, so `f = X (x 0)` is only *invertible* in it, never a member; the cofactor is
   the product of the remaining variables.
2. `linearEquivOfMemIff` — `A(0)` is `A`, at the localization level.
3. `selfBasicOpenSectionAddEquiv` — the structure module against its sections.
4. `sectionAddEquivOfMemIff` — `A` is `A(0)`, at the section level.
5. `intShiftSectionAddEquivOn` — the chart trivialization, undone.

Steps 2 and 4 exist because the integer trivializations land at `A(0)` while the section
comparison is stated against `A`; they move no data at all. -/
noncomputable def intCechTermSectionAddEquiv (ι k : Type u) [Field k] (d : ℤ) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    polynomialVariableIntCechTerm ι k d n x ≃+
      (associatedSheafInType (polynomialGrading ι k)
        (intShift (polynomialGrading ι k) d)).1.obj
        (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
          (polynomialVariableCechDenominator ι k x))) :=
  ((DegreeZeroLocalization.intShiftZeroLinearEquivOfMulMem (polynomialGrading ι k)
      (MvPolynomial.isHomogeneous_X k (x 0)) (cechCofactor_mem ι k x)
      d.toNat (-d).toNat d (by omega)
      (by rw [X_mul_cechCofactor]; exact Submonoid.mem_powers _)).toAddEquiv.trans
    ((DegreeZeroLocalization.linearEquivOfMemIff (𝒜 := polynomialGrading ι k)
        (𝓜 := intShift (polynomialGrading ι k) 0) (polynomialGrading ι k)
        (fun i a => mem_intShift_zero_iff (polynomialGrading ι k) i a)).toAddEquiv.trans
      ((selfBasicOpenSectionAddEquiv (polynomialGrading ι k)
          (polynomialVariableCechDenominator_mem ι k x) (Nat.succ_pos n)).trans
        ((sectionAddEquivOfMemIff (polynomialGrading ι k) (polynomialGrading ι k)
            (intShift (polynomialGrading ι k) 0)
            (fun i a => (mem_intShift_zero_iff (polynomialGrading ι k) i a).symm) _).trans
          (intShiftSectionAddEquivOn (polynomialGrading ι k)
            (MvPolynomial.isHomogeneous_X k (x 0)) d
            (basicOpen_denominator_le ι k x)).symm))))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The integer Čech comparison is the canonical homogeneous-fraction section map.

The five-step composite has to be named by `change` before anything will rewrite: `simp` will
not unfold it far enough to expose the `mk` argument, because two of the steps are `AddEquiv`
transports whose `apply` lemmas only fire once the argument is already in `mk` form. Naming the
chain, then rewriting inside-out, reduces the whole statement to a pointwise identity in the
localization at each prime, closed by `ring`. -/
theorem intCechTermSectionAddEquiv_apply_mk (ι k : Type u) [Field k] (d : ℤ) {n : ℕ}
    (x : Fin (n + 1) → ι)
    (c : NumDenSameDeg (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k x))) :
    intCechTermSectionAddEquiv ι k d x (DegreeZeroLocalization.mk c) =
      moduleAwayToSection (polynomialGrading ι k)
        (intShift (polynomialGrading ι k) d)
        (polynomialVariableCechDenominator ι k x) (DegreeZeroLocalization.mk c) := by
  change intShiftSectionFromZeroOn (polynomialGrading ι k)
      (MvPolynomial.isHomogeneous_X k (x 0)) d (basicOpen_denominator_le ι k x)
      (sectionAddEquivOfMemIff (polynomialGrading ι k) (polynomialGrading ι k)
        (intShift (polynomialGrading ι k) 0)
        (fun i a => (mem_intShift_zero_iff (polynomialGrading ι k) i a).symm) _
        (selfBasicOpenSectionAddEquiv (polynomialGrading ι k)
          (polynomialVariableCechDenominator_mem ι k x) (Nat.succ_pos n)
          (DegreeZeroLocalization.linearEquivOfMemIff (polynomialGrading ι k)
            (fun i a => mem_intShift_zero_iff (polynomialGrading ι k) i a)
            (DegreeZeroLocalization.intShiftZeroLinearEquivOfMulMem (polynomialGrading ι k)
              (MvPolynomial.isHomogeneous_X k (x 0)) (cechCofactor_mem ι k x)
              d.toNat (-d).toNat d (by omega)
              (by rw [X_mul_cechCofactor]; exact Submonoid.mem_powers _)
              (DegreeZeroLocalization.mk c))))) = _
  rw [DegreeZeroLocalization.intShiftZeroLinearEquivOfMulMem_apply_mk,
    DegreeZeroLocalization.linearEquivOfMemIff_mk,
    selfBasicOpenSectionAddEquiv_apply_mk]
  apply section_ext
  funext y
  rw [intShiftSectionFromZeroOn_apply, sectionAddEquivOfMemIff_apply,
    moduleAwayToSection_apply, moduleAwayToSection_apply,
    DegreeZeroLocalization.mapOfLE_mk,
    DegreeZeroLocalization.linearEquivOfMemIff_mk,
    DegreeZeroLocalization.mapOfLE_mk,
    intShiftFiberLinearEquivOfMem_symm_apply_mk]
  apply DegreeZeroLocalization.ext
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul, mul_pow]
  ring

/-- As an additive map, the integer Čech comparison is the canonical fraction-to-section map. -/
theorem intCechTermSectionAddEquiv_toAddMonoidHom (ι k : Type u) [Field k] (d : ℤ) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    (intCechTermSectionAddEquiv ι k d x).toAddMonoidHom =
      moduleAwayToSection (polynomialGrading ι k)
        (intShift (polynomialGrading ι k) d)
        (polynomialVariableCechDenominator ι k x) :=
  moduleAwayToSection_unique _ _ _ _ (intCechTermSectionAddEquiv_apply_mk ι k d x)

/-- The integer Čech comparison intertwines the algebraic face with restriction of sections.

This is `cechTermSectionAddEquiv_res_face` for a twist of either sign, and it is the same proof:
once `intCechTermSectionAddEquiv_toAddMonoidHom` has identified the five-step composite with the
canonical fraction-to-section map, the statement is `moduleAwayToSection_res_faceMap`, which is
generic in the graded module and never mentions the twist. The sign lives entirely in the
`intShift` bookkeeping that `intCechTermSectionAddEquiv` already absorbed. -/
theorem intCechTermSectionAddEquiv_res_face (ι k : Type u) [Field k] (d : ℤ) {n : ℕ}
    (x : Fin (n + 2) → ι) (j : Fin (n + 2))
    (i : (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k (x ∘ j.succAbove))) :
          (Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))ᵒᵖ) ⟶
      op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x)))
    (z : polynomialVariableIntCechTerm ι k d n (x ∘ j.succAbove)) :
    (associatedSheafInType (polynomialGrading ι k)
          (intShift (polynomialGrading ι k) d)).1.map i
        (intCechTermSectionAddEquiv ι k d (x ∘ j.succAbove) z) =
      intCechTermSectionAddEquiv ι k d x (polynomialVariableIntCechFace ι k d x j z) := by
  change (associatedSheafInType (polynomialGrading ι k)
        (intShift (polynomialGrading ι k) d)).1.map i
      ((intCechTermSectionAddEquiv ι k d (x ∘ j.succAbove)).toAddMonoidHom z) =
    (intCechTermSectionAddEquiv ι k d x).toAddMonoidHom
      (polynomialVariableIntCechFace ι k d x j z)
  rw [intCechTermSectionAddEquiv_toAddMonoidHom, intCechTermSectionAddEquiv_toAddMonoidHom]
  exact moduleAwayToSection_res_faceMap (polynomialGrading ι k)
    (intShift (polynomialGrading ι k) d)
    (MvPolynomial.isHomogeneous_X k (x j))
    (polynomialVariableCechDenominator_succAbove_mem ι k x j)
    (polynomialVariableCechDenominator_succAbove ι k x j) i z

/-- The canonical fraction-to-section map is bijective on every Čech intersection, for a twist
of either sign. -/
theorem moduleAwayToSection_intCechDenominator_bijective (ι k : Type u) [Field k] (d : ℤ)
    {n : ℕ} (x : Fin (n + 1) → ι) :
    Function.Bijective (moduleAwayToSection (polynomialGrading ι k)
      (intShift (polynomialGrading ι k) d)
      (polynomialVariableCechDenominator ι k x)) := by
  rw [← intCechTermSectionAddEquiv_toAddMonoidHom ι k d x]
  exact (intCechTermSectionAddEquiv ι k d x).bijective

/-- The canonical fraction-to-section map is bijective on every Čech intersection.

The degree-one statement `moduleAwayToSection_natShift_degreeOne_bijective` does not cover this:
a Čech denominator is a product of `n + 1` variables, so it has degree `n + 1`, and the chart it
cuts out is not a degree-one chart once `n ≥ 1`. -/
theorem moduleAwayToSection_cechDenominator_bijective (ι k : Type u) [Field k] (d : ℕ) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    Function.Bijective (moduleAwayToSection (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (polynomialVariableCechDenominator ι k x)) := by
  rw [← cechTermSectionAddEquiv_toAddMonoidHom ι k d x]
  exact (cechTermSectionAddEquiv ι k d x).bijective

end AlgebraicGeometry.Proj
