/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.Cech.Basic
import DerivedAlgGeo.Algebra.MvPolynomial.DivMonomial
import DerivedAlgGeo.Algebra.MvPolynomial.Grading
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Finiteness
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Twists on polynomial projective space

This file constructs the comparison between degree-`d` homogeneous polynomials and global
sections of `O(d)` on polynomial `Proj`, over any commutative ring. The proof uses the variable
basic-open cover, the constructed chart comparison from `TwistChart`, and the Čech intersections
of pairs of charts.

## Main definitions

* `AlgebraicGeometry.Proj.polynomialNatGlobalSectionsAddEquiv`,
  `AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsAddEquiv` and
  `AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsModuleIso` — degree-`d` homogeneous
  polynomials are exactly `Γ(Proj k[Xᵢ], O(d))`, additively and as `k`-modules.
* `AlgebraicGeometry.Proj.cechTermSectionAddEquiv` and
  `AlgebraicGeometry.Proj.intCechTermSectionAddEquiv` — the algebraic Čech term for `O(d)` is
  the sections of `O(d)` over the corresponding intersection, for `d : ℕ` and `d : ℤ`.

## Main results

* `AlgebraicGeometry.Proj.polynomialToNatGlobalSections_surjective` and
  `AlgebraicGeometry.Proj.polynomialToNatGlobalSections_injective`.
* `AlgebraicGeometry.Proj.polynomialNatShift_isQuasicoherent` and
  `AlgebraicGeometry.Proj.polynomialIntShift_isQuasicoherent` — every twist of polynomial
  projective space is quasi-coherent.
* `AlgebraicGeometry.Proj.cechTermSectionAddEquiv_res_face` and
  `AlgebraicGeometry.Proj.intCechTermSectionAddEquiv_res_face` — the comparisons carry the
  algebraic Čech faces to restriction.
* `AlgebraicGeometry.Proj.moduleAwayToSection_cechDenominator_bijective` and
  `AlgebraicGeometry.Proj.moduleAwayToSection_intCechDenominator_bijective`.

## Implementation notes

The global-section comparison holds over any commutative ring. Two charts of a global section are
compared on the Čech intersection of the pair, where restriction is the Čech face and sections are
fractions; variables are non-zero-divisors, so the faces are injective and the overlap condition
clears to a cross equation of numerators (`X_pow_dvd_of_cross_mul`). With a single variable the
divisibility needs no second chart.

The global-section comparison is for a *nonnegative* twist. The imported algebraic layer owns
variable generation, exact monomial division, the canonical localization fraction, and both Čech
terms: `polynomialVariableCechTerm` for `d : ℕ` and `polynomialVariableIntCechTerm` for `d : ℤ`.
This file begins where geometry enters by comparing those terms with projective basic opens and
sections. The two algebraic terms are not identified here for a nonnegative `d`; the Čech
differential uses the `ℕ` version.

## References

The algebraic Čech terms are `polynomialVariableCechTerm` and `polynomialVariableIntCechTerm`;
the twist quasi-coherence criteria are `natShift_isQuasicoherent` and
`intShift_isQuasicoherent`.

## Tags

projective space, twisting sheaf, global sections, homogeneous polynomial, Čech complex
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace
open scoped DirectSum Pointwise

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Global sections of the natural shift associated to `A(d)` on polynomial `Proj`. -/
abbrev polynomialNatGlobalSections (ι k : Type u) [CommRing k] (d : ℕ) :=
  (associatedSheafInType (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)).1.obj
      (op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A homogeneous polynomial of degree `d` defines the global section represented everywhere
by the fraction `p / 1` in the shifted module. -/
noncomputable def polynomialToNatGlobalSections (ι k : Type u) [CommRing k] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d →+
      polynomialNatGlobalSections ι k d where
  toFun p := by
    let num : ↥(GradedModule.natShift
        (polynomialGrading ι k) d 0) :=
      ⟨p.1, by change p.1 ∈ polynomialGrading ι k (0 + d); simp⟩
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The section of a polynomial is the fraction `p / 1` at every point. -/
theorem polynomialToNatGlobalSections_apply (ι k : Type u) [CommRing k] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d)
    (x : ProjectiveSpectrum.top (polynomialGrading ι k)) (hx : x ∈ (⊤ : Opens _)) :
    (polynomialToNatGlobalSections ι k d p).1 ⟨x, hx⟩ =
      DegreeZeroLocalization.mk
        { deg := 0
          num := ⟨p.1, by change p.1 ∈ polynomialGrading ι k (0 + d); simp⟩
          den := ⟨1, SetLike.one_mem_graded (polynomialGrading ι k)⟩
          den_mem := Ideal.IsPrime.one_notMem inferInstance } :=
  rfl

/-- Nonnegative twists on polynomial projective space are quasi-coherent.

The variable charts have degree one and cover, which is exactly the hypothesis of
`natShift_isQuasicoherent`.  No comparison on higher-degree charts is needed or available. -/
theorem polynomialNatShift_isQuasicoherent (ι k : Type u) [CommRing k] (d : ℕ) :
    (associatedSheaf (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d)).IsQuasicoherent :=
  natShift_isQuasicoherent (polynomialGrading ι k)
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
    (polynomialVariable_adjoin_eq_top ι k)

/-- Every integer twist of polynomial projective space is quasi-coherent.

The variable charts have degree one and generate, which is exactly the hypothesis
`intShift_isQuasicoherent` takes. The sign of `d` never enters. This is the negative-twist
input the Serre-finiteness dévissage needs. -/
theorem polynomialIntShift_isQuasicoherent (ι k : Type u) [CommRing k] (d : ℤ) :
    (associatedSheaf (polynomialGrading ι k)
      (intShift (polynomialGrading ι k) d)).IsQuasicoherent :=
  intShift_isQuasicoherent (polynomialGrading ι k)
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
    (polynomialVariable_adjoin_eq_top ι k)

/-! ## Comparing the algebraic variable Čech diagram with projective basic opens -/

/-- The basic open of the product denominator is exactly the finite intersection of the
corresponding variable charts. -/
theorem basicOpen_polynomialVariableCechDenominator
    (ι k : Type u) [CommRing k] {n : ℕ} (x : Fin (n + 1) → ι) :
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
theorem basicOpen_denominator_le (ι k : Type u) [CommRing k] {n : ℕ} (x : Fin (n + 1) → ι) :
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
noncomputable def cechTermSectionAddEquiv (ι k : Type u) [CommRing k] (d : ℕ) {n : ℕ}
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
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
theorem cechTermSectionAddEquiv_apply_mk (ι k : Type u) [CommRing k] (d : ℕ) {n : ℕ}
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
theorem cechTermSectionAddEquiv_toAddMonoidHom (ι k : Type u) [CommRing k] (d : ℕ) {n : ℕ}
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
theorem cechTermSectionAddEquiv_res_face (ι k : Type u) [CommRing k] (d : ℕ) {n : ℕ}
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
noncomputable def intCechTermSectionAddEquiv (ι k : Type u) [CommRing k] (d : ℤ) {n : ℕ}
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The integer Čech comparison is the canonical homogeneous-fraction section map.

The five-step composite has to be named by `change` before anything will rewrite: `simp` will
not unfold it far enough to expose the `mk` argument, because two of the steps are `AddEquiv`
transports whose `apply` lemmas only fire once the argument is already in `mk` form. Naming the
chain, then rewriting inside-out, reduces the whole statement to a pointwise identity in the
localization at each prime, closed by `ring`. -/
theorem intCechTermSectionAddEquiv_apply_mk (ι k : Type u) [CommRing k] (d : ℤ) {n : ℕ}
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
theorem intCechTermSectionAddEquiv_toAddMonoidHom (ι k : Type u) [CommRing k] (d : ℤ) {n : ℕ}
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
theorem intCechTermSectionAddEquiv_res_face (ι k : Type u) [CommRing k] (d : ℤ) {n : ℕ}
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
theorem moduleAwayToSection_intCechDenominator_bijective (ι k : Type u) [CommRing k] (d : ℤ)
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
theorem moduleAwayToSection_cechDenominator_bijective (ι k : Type u) [CommRing k] (d : ℕ) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    Function.Bijective (moduleAwayToSection (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (polynomialVariableCechDenominator ι k x)) := by
  rw [← cechTermSectionAddEquiv_toAddMonoidHom ι k d x]
  exact (cechTermSectionAddEquiv ι k d x).bijective

/-! ## Global sections of a nonnegative twist

A global section is compared with a homogeneous polynomial chart by chart. Two charts `D₊(Xᵢ)` and
`D₊(Xₐ)` are compared on their overlap `D₊(Xᵢ Xₐ)`, which is the Čech intersection of the pair
`![i, a]`: restriction there is the Čech face (`moduleAwayToSection_res_faceMap`), and sections
there are fractions (`moduleAwayToSection_cechDenominator_bijective`). Variables are
non-zero-divisors over any commutative ring, so the faces lose nothing and the overlap condition
clears to a cross equation of numerators without a domain hypothesis. -/

/-- Restriction of a global natural-twist section to the variable chart `D₊(Xᵢ)`. -/
noncomputable def restrictNatGlobalSectionsToVariable
    (ι k : Type u) [CommRing k] (d : ℕ) (i : ι) :
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
    (ι k : Type u) [CommRing k] (d : ℕ) (i : ι) :
    polynomialNatGlobalSections ι k d →+
      DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) :=
  (natShiftBasicOpenSectionAddEquiv (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) d).symm.toAddMonoidHom.comp
      (restrictNatGlobalSectionsToVariable ι k d i)

theorem moduleAwayToSection_variableFractionOfGlobalSection
    (ι k : Type u) [CommRing k] (d : ℕ) (i : ι)
    (s : polynomialNatGlobalSections ι k d) :
    moduleAwayToSection (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (MvPolynomial.X i)
        (variableFractionOfGlobalSection ι k d i s) =
      restrictNatGlobalSectionsToVariable ι k d i s := by
  rw [← natShiftBasicOpenSectionAddEquiv_toAddMonoidHom
    (polynomialGrading ι k) (MvPolynomial.isHomogeneous_X k i) d]
  exact (natShiftBasicOpenSectionAddEquiv (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) d).apply_symm_apply _

/-- Restricting the polynomial section to a variable chart recovers the literal fraction
`p / 1`. -/
theorem variableFractionOfGlobalSection_polynomial
    (ι k : Type u) [CommRing k] (d : ℕ)
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

/-- The standard variable basic opens cover polynomial projective space. -/
theorem polynomialVariableBasicOpen_cover (ι k : Type u) [CommRing k] :
    (⨆ i : ι, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X i)) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · exact polynomialVariable_adjoin_eq_top ι k

/-- The overlap of the charts of `Xᵢ` and `Xₐ` is the Čech intersection of the pair `![i, a]`. -/
private theorem X_mul_X_eq_pairDenominator (ι k : Type u) [CommRing k] (i a : ι) :
    (MvPolynomial.X i : MvPolynomial ι k) * MvPolynomial.X a =
      polynomialVariableCechDenominator ι k ![i, a] := by
  simp [polynomialVariableCechDenominator, Fin.prod_univ_two]

private theorem X_mul_X_mem_powers_pairDenominator (ι k : Type u) [CommRing k] (i a : ι) :
    (MvPolynomial.X i : MvPolynomial ι k) * MvPolynomial.X a ∈
      Submonoid.powers (polynomialVariableCechDenominator ι k ![i, a]) :=
  ⟨1, (pow_one _).trans (X_mul_X_eq_pairDenominator ι k i a).symm⟩

/-- The overlap denominator `Xᵢ Xₐ` is a non-zero-divisor over any commutative ring. -/
private theorem isSMulRegular_pairDenominator (ι k : Type u) [CommRing k] (i a : ι) :
    IsSMulRegular (MvPolynomial ι k) (polynomialVariableCechDenominator ι k ![i, a]) := by
  rw [← X_mul_X_eq_pairDenominator]
  exact (MvPolynomial.isRegular_X.mul MvPolynomial.isRegular_X).left.isSMulRegular

/-- From the chart of `Xᵢ` to its overlap with the chart of `Xₐ`: the face multiplying by `Xₐ`. -/
private noncomputable abbrev leftPairFace (ι k : Type u) [CommRing k] (d : ℕ) (i a : ι) :
    DegreeZeroLocalization (polynomialGrading ι k) (natShift (polynomialGrading ι k) d)
        (.powers (MvPolynomial.X i)) →+
      polynomialVariableCechTerm ι k d 1 ![i, a] :=
  DegreeZeroLocalization.faceMap (MvPolynomial.isHomogeneous_X k a)
    (X_mul_X_mem_powers_pairDenominator ι k i a) (X_mul_X_eq_pairDenominator ι k i a)

/-- From the chart of `Xₐ` to its overlap with the chart of `Xᵢ`: the face multiplying by `Xᵢ`. -/
private noncomputable abbrev rightPairFace (ι k : Type u) [CommRing k] (d : ℕ) (i a : ι) :
    DegreeZeroLocalization (polynomialGrading ι k) (natShift (polynomialGrading ι k) d)
        (.powers (MvPolynomial.X a)) →+
      polynomialVariableCechTerm ι k d 1 ![i, a] :=
  DegreeZeroLocalization.faceMap (MvPolynomial.isHomogeneous_X k i)
    (by rw [mul_comm]; exact X_mul_X_mem_powers_pairDenominator ι k i a)
    (by rw [mul_comm]; exact X_mul_X_eq_pairDenominator ι k i a)

/-- A numerator over `Xⁿ` stays a numerator over `(Xᵢ Xₐ)ⁿ` after multiplying by the other
variable's `n`-th power. -/
private theorem X_pow_smul_mem_natShift (ι k : Type u) [CommRing k] (d : ℕ) (b : ι) (n : ℕ)
    {r : MvPolynomial ι k} (hr : r ∈ natShift (polynomialGrading ι k) d (n • 1)) :
    (MvPolynomial.X b : MvPolynomial ι k) ^ n • r ∈
      natShift (polynomialGrading ι k) d (n • (1 + 1)) := by
  have h := SetLike.GradedSMul.smul_mem
    (SetLike.pow_mem_graded (A := polynomialGrading ι k) n (MvPolynomial.isHomogeneous_X k b)) hr
  rwa [vadd_eq_add, ← nsmul_add] at h

/-- **The two charts of a global section agree on their overlap.** Both faces are restrictions of
the same section, and sections on the overlap are fractions. -/
private theorem leftPairFace_eq_rightPairFace (ι k : Type u) [CommRing k] (d : ℕ) (i a : ι)
    (s : polynomialNatGlobalSections ι k d) :
    leftPairFace ι k d i a (variableFractionOfGlobalSection ι k d i s) =
      rightPairFace ι k d i a (variableFractionOfGlobalSection ι k d a s) := by
  have hi : ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k ![i, a]) ≤
      ProjectiveSpectrum.basicOpen (polynomialGrading ι k) (MvPolynomial.X i) := by
    rw [← X_mul_X_eq_pairDenominator, ProjectiveSpectrum.basicOpen_mul]
    exact inf_le_left
  have ha : ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k ![i, a]) ≤
      ProjectiveSpectrum.basicOpen (polynomialGrading ι k) (MvPolynomial.X a) := by
    rw [← X_mul_X_eq_pairDenominator, ProjectiveSpectrum.basicOpen_mul]
    exact inf_le_right
  apply (moduleAwayToSection_cechDenominator_bijective ι k d ![i, a]).1
  have e₁ := moduleAwayToSection_res_faceMap (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d) (MvPolynomial.isHomogeneous_X k a)
    (X_mul_X_mem_powers_pairDenominator ι k i a) (X_mul_X_eq_pairDenominator ι k i a)
    (homOfLE hi).op (variableFractionOfGlobalSection ι k d i s)
  have e₂ := moduleAwayToSection_res_faceMap (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d) (MvPolynomial.isHomogeneous_X k i)
    (by rw [mul_comm]; exact X_mul_X_mem_powers_pairDenominator ι k i a)
    (by rw [mul_comm]; exact X_mul_X_eq_pairDenominator ι k i a)
    (homOfLE ha).op (variableFractionOfGlobalSection ι k d a s)
  rw [moduleAwayToSection_variableFractionOfGlobalSection] at e₁ e₂
  refine e₁.symm.trans (Eq.trans ?_ e₂)
  apply section_ext
  funext x
  rfl

/-- Multiplying by a variable loses nothing: the face from the chart of `Xₐ` to its overlap with
the chart of `Xᵢ` is injective, because both variables are non-zero-divisors. -/
private theorem rightPairFace_injective (ι k : Type u) [CommRing k] (d : ℕ) (i a : ι) :
    Function.Injective (rightPairFace ι k d i a) := by
  intro z w h
  obtain ⟨n, p, q, hp, hq, rfl, rfl⟩ := DegreeZeroLocalization.exists_awayMk_pair
    (MvPolynomial.isHomogeneous_X k a) z w
  have hg₂ := polynomialVariableCechDenominator_mem ι k ![i, a]
  have h' := ((DegreeZeroLocalization.faceMap_awayMk (MvPolynomial.isHomogeneous_X k i)
      (MvPolynomial.isHomogeneous_X k a) _ _ hg₂ n p hp
      (X_pow_smul_mem_natShift ι k d i n hp)).symm.trans h).trans
    (DegreeZeroLocalization.faceMap_awayMk (MvPolynomial.isHomogeneous_X k i)
      (MvPolynomial.isHomogeneous_X k a) _ _ hg₂ n q hq
      (X_pow_smul_mem_natShift ι k d i n hq))
  rw [DegreeZeroLocalization.awayMk_eq_awayMk_iff _ (isSMulRegular_pairDenominator ι k i a)] at h'
  obtain rfl : p = q :=
    (MvPolynomial.isRegular_X_pow n).left.isSMulRegular
      ((isSMulRegular_pairDenominator ι k i a).pow n h')
  rfl

/-- With a single variable, a homogeneous polynomial of degree `n + d` is divisible by `Xᵢⁿ`: its
only possible monomial is `Xᵢ ^ (n + d)`. -/
private theorem X_pow_dvd_of_subsingleton (ι k : Type u) [CommRing k] [Subsingleton ι] (i : ι)
    (n d : ℕ) {P : MvPolynomial ι k} (hP : P ∈ MvPolynomial.homogeneousSubmodule ι k (n + d)) :
    (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣ P := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  ext s
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hle : Finsupp.single i n ≤ s
  · exact coeff_modMonomial_of_le P hle
  · rw [coeff_modMonomial_of_not_le P hle]
    by_contra hs
    have hdeg := hP hs
    have hsi : s = Finsupp.single i (s i) := by
      ext j
      rw [Subsingleton.elim j i]
      simp
    rw [Finsupp.single_le_iff] at hle
    rw [hsi] at hdeg
    simp only [Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at hdeg
    omega

/-- A global section of a nonnegative twist on polynomial projective space is represented by a
single homogeneous polynomial.

Pick a variable `Xᵢ` and write the section on its chart as `P / Xᵢⁿ`. The candidate is
`p = P / Xᵢⁿ`, once `Xᵢⁿ ∣ P` is known. With a second variable `Xⱼ`, the two numerators
cross-multiply on the overlap of the charts and `X_pow_dvd_of_cross_mul` gives the divisibility;
with a single variable every monomial of `P` is a power of `Xᵢ` of degree at least `n`. Every
other chart agrees with `p` after the injective face to its overlap with the chart of `Xᵢ`. -/
theorem polynomialToNatGlobalSections_surjective
    (ι k : Type u) [CommRing k] [Nonempty ι] (d : ℕ) :
    Function.Surjective (polynomialToNatGlobalSections ι k d) := by
  intro s
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨n, P, hP, hPi⟩ := DegreeZeroLocalization.exists_awayMk
    (MvPolynomial.isHomogeneous_X k i) (variableFractionOfGlobalSection ι k d i s)
  have hPhom : P ∈ MvPolynomial.homogeneousSubmodule ι k (n + d) := by
    have h : P ∈ polynomialGrading ι k (n • 1 + d) := hP
    simpa only [smul_eq_mul, mul_one] using h
  -- The numerator over `Xᵢⁿ` is divisible by `Xᵢⁿ`; the quotient is the candidate.
  have hdiv : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣ P := by
    rcases subsingleton_or_nontrivial ι with hι | hι
    · exact X_pow_dvd_of_subsingleton ι k i n d hPhom
    obtain ⟨j, hji⟩ := exists_ne i
    obtain ⟨m, Q, hQ, hQj⟩ := DegreeZeroLocalization.exists_awayMk
      (MvPolynomial.isHomogeneous_X k j) (variableFractionOfGlobalSection ι k d j s)
    -- The two charts agree on their overlap, which clears to the cross equation.
    have hg₂ := polynomialVariableCechDenominator_mem ι k ![i, j]
    have hpair := leftPairFace_eq_rightPairFace ι k d i j s
    rw [hPi, hQj] at hpair
    replace hpair := ((DegreeZeroLocalization.faceMap_awayMk (MvPolynomial.isHomogeneous_X k j)
        (MvPolynomial.isHomogeneous_X k i) _ _ hg₂ n P hP
        (X_pow_smul_mem_natShift ι k d j n hP)).symm.trans hpair).trans
      (DegreeZeroLocalization.faceMap_awayMk (MvPolynomial.isHomogeneous_X k i)
        (MvPolynomial.isHomogeneous_X k j) _ _ hg₂ m Q hQ
        (X_pow_smul_mem_natShift ι k d i m hQ))
    rw [DegreeZeroLocalization.awayMk_eq_awayMk_iff _ (isSMulRegular_pairDenominator ι k i j),
      ← X_mul_X_eq_pairDenominator] at hpair
    simp only [smul_eq_mul] at hpair
    have key : (MvPolynomial.X i ^ m * MvPolynomial.X j ^ n : MvPolynomial ι k) *
          (MvPolynomial.X j ^ m * P) =
        (MvPolynomial.X i ^ m * MvPolynomial.X j ^ n : MvPolynomial ι k) *
          (MvPolynomial.X i ^ n * Q) := by
      linear_combination hpair
    exact X_pow_dvd_of_cross_mul ι k hji.symm n m P Q
      (((MvPolynomial.isRegular_X_pow m).mul (MvPolynomial.isRegular_X_pow n)).left key)
  let p : MvPolynomial.homogeneousSubmodule ι k d :=
    ⟨MvPolynomial.divMonomial P (Finsupp.single i n),
      divMonomial_single_mem_homogeneousSubmodule ι k i n d P hPhom⟩
  have hXp : MvPolynomial.X i ^ n * (p : MvPolynomial ι k) = P :=
    X_pow_mul_divMonomial_single ι k i n P hdiv
  have hi_fraction : variableFractionOfGlobalSection ι k d i s =
      polynomialVariableFraction ι k d p i := by
    rw [hPi]
    refine (DegreeZeroLocalization.mk_eq_mk_iff _ _).mpr ⟨1, ?_⟩
    simp [hXp]
  -- Every chart agrees with `p`, after the injective face to the overlap with the chart of `Xᵢ`.
  have ha_fraction : ∀ a, variableFractionOfGlobalSection ι k d a s =
      polynomialVariableFraction ι k d p a := by
    intro a
    apply rightPairFace_injective ι k d i a
    rw [← leftPairFace_eq_rightPairFace ι k d i a s, hi_fraction,
      ← variableFractionOfGlobalSection_polynomial,
      ← variableFractionOfGlobalSection_polynomial]
    exact leftPairFace_eq_rightPairFace ι k d i a _
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
  have hsections := congr_arg (fun t => t.1 xa)
    (congr_arg (moduleAwayToSection (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (MvPolynomial.X a)) (ha_fraction a))
  rw [moduleAwayToSection_variableFractionOfGlobalSection,
    ← variableFractionOfGlobalSection_polynomial,
    moduleAwayToSection_variableFractionOfGlobalSection] at hsections
  exact hsections.symm

/-- Distinct homogeneous polynomials define distinct global sections: on one chart they are
`p / 1` and `q / 1`, and a power of the variable cancels from the localized equation. -/
theorem polynomialToNatGlobalSections_injective
    (ι k : Type u) [CommRing k] [Nonempty ι] (d : ℕ) :
    Function.Injective (polynomialToNatGlobalSections ι k d) := by
  intro p q hpq
  let i : ι := Classical.choice inferInstance
  have hchart := congr_arg (variableFractionOfGlobalSection ι k d i) hpq
  rw [variableFractionOfGlobalSection_polynomial,
    variableFractionOfGlobalSection_polynomial, polynomialVariableFraction,
    polynomialVariableFraction, DegreeZeroLocalization.mk_eq_mk_iff] at hchart
  obtain ⟨⟨u, t, rfl⟩, hu⟩ := hchart
  apply Subtype.ext
  exact (MvPolynomial.isRegular_X_pow t).left (by simpa [smul_eq_mul] using hu)

/-- Concrete additive comparison between degree-`d` homogeneous polynomials and global sections
of the natural-shift model of `O(d)`. -/
noncomputable def polynomialNatGlobalSectionsAddEquiv
    (ι k : Type u) [CommRing k] [Nonempty ι] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d ≃+
      polynomialNatGlobalSections ι k d :=
  AddEquiv.ofBijective (polynomialToNatGlobalSections ι k d)
    ⟨polynomialToNatGlobalSections_injective ι k d,
      polynomialToNatGlobalSections_surjective ι k d⟩

/-- Global sections of the integer-indexed twisting sheaf `O(d)`. -/
abbrev polynomialTwistingGlobalSections (ι k : Type u) [CommRing k] (d : ℕ) :=
  (twistingSheaf (polynomialGrading ι k) (d : ℤ)).val.obj
    (op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))

/-- For a nonnegative twist, transport global sections from the natural-shift model to the
integer-indexed twisting sheaf. -/
noncomputable def polynomialNatToTwistingGlobalSectionsAddEquiv
    (ι k : Type u) [CommRing k] (d : ℕ) :
    polynomialNatGlobalSections ι k d ≃+
      polynomialTwistingGlobalSections ι k d :=
  (asIso ((twistingSheafOfNatIso (polynomialGrading ι k) d).hom.app
    (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))).addCommGroupIsoToAddEquiv.symm

/-- The concrete global-section comparison requested for polynomial projective space:
degree-`d` homogeneous polynomials are exactly `Γ(Proj k[Xᵢ], O(d))`. -/
noncomputable def polynomialTwistingGlobalSectionsAddEquiv
    (ι k : Type u) [CommRing k] [Nonempty ι] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d ≃+
      polynomialTwistingGlobalSections ι k d :=
  (polynomialNatGlobalSectionsAddEquiv ι k d).trans
    (polynomialNatToTwistingGlobalSectionsAddEquiv ι k d)

/-- Global sections equipped with the base-ring module structure transported through the
explicit polynomial comparison.  This avoids pretending that a separate base-ring action is
definitionally present in Mathlib's sheaf-of-modules section type. -/
noncomputable def polynomialTwistingGlobalSectionsModule
    (ι k : Type u) [CommRing k] [Nonempty ι] (d : ℕ) : ModuleCat.{u} k := by
  let e := polynomialTwistingGlobalSectionsAddEquiv ι k d
  letI : Module k (polynomialTwistingGlobalSections ι k d) := e.symm.module k
  exact ModuleCat.of k (polynomialTwistingGlobalSections ι k d)

/-- The concrete comparison as an isomorphism of `k`-modules, using the transported action made
explicit by `polynomialTwistingGlobalSectionsModule`. -/
noncomputable def polynomialTwistingGlobalSectionsModuleIso
    (ι k : Type u) [CommRing k] [Nonempty ι] (d : ℕ) :
    ModuleCat.of k (MvPolynomial.homogeneousSubmodule ι k d) ≅
      polynomialTwistingGlobalSectionsModule ι k d := by
  let e := polynomialTwistingGlobalSectionsAddEquiv ι k d
  letI : Module k (polynomialTwistingGlobalSections ι k d) := e.symm.module k
  exact LinearEquiv.toModuleIso (e.symm.linearEquiv k).symm

end AlgebraicGeometry.Proj
