/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ProjectiveSpace
import DerivedAlgGeo.Algebra.MvPolynomial.LaurentHomotopy
import DerivedAlgGeo.Algebra.Module.GradedModule.PowersCongr

/-!
# The block homotopy on the variable Čech cover

The block projections and the contracting homotopy of #340 live at monomial denominators
`Xᵞ`, while the Čech complex of the variable cover names its denominators as products
`∏ₐ X_{x a}`. The two are equal ring elements, and this file carries the whole toolkit across
that equality: `tupleExponent` is the exponent vector of a Čech tuple,
`DegreeZeroLocalization.powersCongr` transports a degree-zero localization along an equality of
denominators, and the Čech-level `cechBlockProj` and `cechHomotopy` are the monomial-level maps
conjugated by that transport.

The payoff is the three identities the vanishing computation runs on, now stated against
`polynomialVariableCechFace` itself:

* `cechFace_cechBlockProj` — the Čech faces commute with the block projections;
* `cechHomotopy_cechFace_zero` — the homotopy retracts the cone face on a block (`i₀ ∉ F`);
* `cechHomotopy_cechFace_succ` — the homotopy commutes with every other face, unrestricted.

together with `sum_cechBlockProj` (the finitely many blocks of a tuple exhaust its term) and
`cechBlockProj_eq_zero_of_not_subset` (a block off the tuple's support is zero), which are what
the reassembly of per-block primitives sums over.

## Implementation notes

`powersCongr` is defined by `subst` and every one of its equations is proved by `subst` plus
proof irrelevance — the transported element never moves, only its type's name does. The face
transport `powersCongr_faceMap` takes equalities for both denominators *and* the face's
multiplier, because the Čech side multiplies by `X i` and the monomial side by
`monomial (single i 1) 1`; the two are definitionally equal, but keeping the equality explicit
lets one lemma serve every instantiation.

The `Fin.cons` combinatorics is isolated in two lemmas — the `0`-face of a cone tuple is the
base tuple, and the `j.succ`-face of a cone tuple is the cone over the `j`-face — so the
vanishing computation never touches `succAbove` directly.

## Tags

Čech complex, contracting homotopy, block decomposition, projective space
-/

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The exponent vector of a Čech tuple -/

variable (ι k : Type u) [Field k]

/-- The exponent vector of the Čech denominator of a tuple: one for each occurrence of each
variable. -/
noncomputable def tupleExponent {n : ℕ} (x : Fin n → ι) : ι →₀ ℕ :=
  ∑ a, Finsupp.single (x a) 1

/-- The Čech denominator is the monomial with exponent `tupleExponent`. This is the equality
everything in this file transports along. -/
theorem tupleDenominator_eq {n : ℕ} (x : Fin (n + 1) → ι) :
    polynomialVariableCechDenominator ι k x =
      MvPolynomial.monomial (tupleExponent ι x) (1 : k) := by
  classical
  rw [polynomialVariableCechDenominator, tupleExponent]
  induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
        show (MvPolynomial.X (x a) : MvPolynomial ι k) =
          MvPolynomial.monomial (Finsupp.single (x a) 1) 1 from rfl,
        MvPolynomial.monomial_mul, one_mul]

variable {ι}

/-- Prepending a cone point adds one power of its variable. -/
theorem tupleExponent_cons {n : ℕ} (i₀ : ι) (y : Fin n → ι) :
    tupleExponent ι (Fin.cons i₀ y) = Finsupp.single i₀ 1 + tupleExponent ι y := by
  rw [tupleExponent, tupleExponent, Fin.sum_univ_succ]
  simp

/-- Dropping the `j`-th index removes one power of its variable. Oriented with the dropped
variable on the left, which is the shape the face splittings consume. -/
theorem tupleExponent_succAbove {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    tupleExponent ι x = Finsupp.single (x j) 1 + tupleExponent ι (x ∘ j.succAbove) := by
  rw [tupleExponent, tupleExponent,
    Fin.sum_univ_succAbove (fun a => Finsupp.single (x a) 1) j]
  rfl

/-- The cone denominator in monomial form, split at the cone variable. -/
theorem tupleDenominator_cons_eq {n : ℕ} (i₀ : ι) (y : Fin (n + 1) → ι) :
    polynomialVariableCechDenominator ι k (Fin.cons i₀ y) =
      MvPolynomial.monomial (Finsupp.single i₀ 1 + tupleExponent ι y) (1 : k) := by
  rw [tupleDenominator_eq, tupleExponent_cons]

/-! ## The `Fin.cons` combinatorics of the cone -/

/-- The `0`-face of a cone tuple is the base tuple. -/
theorem cons_comp_succAbove_zero {n : ℕ} (i₀ : ι) (x : Fin (n + 1) → ι) :
    (Fin.cons i₀ x : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = x := by
  funext i
  simp [Fin.succAbove_zero]

/-- The `j.succ`-face of a cone tuple is the cone over the `j`-face. -/
theorem cons_comp_succAbove_succ {n : ℕ} (i₀ : ι) (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (Fin.cons i₀ x : Fin (n + 3) → ι) ∘ (j.succ).succAbove =
      Fin.cons i₀ (x ∘ j.succAbove) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp
  · simp

/-! ## The Čech term in monomial form -/

variable {σM : Type u} [SetLike σM (MvPolynomial ι k)]
  [AddSubgroupClass σM (MvPolynomial ι k)] {𝓜 : ℕ → σM}
  [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] {d : ℤ}


variable (ι)

/-- The Čech term of a tuple, presented at the monomial denominator. -/
noncomputable def cechTermEquiv (𝓜 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] {n : ℕ} (x : Fin (n + 1) → ι) :
    cechTerm ι k 𝓜 x ≃+
      DegreeZeroLocalization (polynomialGrading ι k)
        𝓜
        (.powers (MvPolynomial.monomial (tupleExponent ι x) (1 : k))) :=
  DegreeZeroLocalization.powersCongr (tupleDenominator_eq ι k x)

/-- The comparison carries a Čech face to the monomial-level face at the same variable. -/
theorem cechTermEquiv_cechFace (𝓜 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2))
    (z : cechTerm ι k 𝓜 (x ∘ j.succAbove)) :
    cechTermEquiv ι k 𝓜 x (cechFace ι k 𝓜 x j z) =
      laurentFace 𝓜 (tupleExponent_succAbove x j)
        (cechTermEquiv ι k 𝓜 (x ∘ j.succAbove) z) :=
  DegreeZeroLocalization.powersCongr_faceMap
    (tupleDenominator_eq ι k (x ∘ j.succAbove)) (tupleDenominator_eq ι k x) rfl
    (MvPolynomial.isHomogeneous_X k (x j)) (monomial_single_mem (x j) 1)
    (polynomialVariableCechDenominator_succAbove_mem ι k x j) _
    (polynomialVariableCechDenominator_succAbove ι k x j) _ z

/-! ## The block projections on Čech terms -/

/-- The block projection of a Čech term: the monomial-level `blockProj` conjugated by the
denominator comparison. -/
noncomputable def cechBlockProj (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    (x : Fin (n + 1) → ι) (F : Finset ι) :
    cechTerm ι k 𝓜 x →+ cechTerm ι k 𝓜 x :=
  ((cechTermEquiv ι k 𝓜 x).symm.toAddMonoidHom.comp
    (blockProjHom h𝓜 (tupleExponent ι x) F)).comp
    (cechTermEquiv ι k 𝓜 x).toAddMonoidHom

theorem cechBlockProj_apply (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    (x : Fin (n + 1) → ι) (F : Finset ι)
    (z : cechTerm ι k 𝓜 x) :
    cechBlockProj ι k h𝓜 x F z =
      (cechTermEquiv ι k 𝓜 x).symm
        (blockProj h𝓜 (tupleExponent ι x) F (cechTermEquiv ι k 𝓜 x z)) :=
  rfl

/-- The finitely many blocks of a tuple exhaust its term. -/
theorem sum_cechBlockProj (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ} (x : Fin (n + 1) → ι)
    (z : cechTerm ι k 𝓜 x) :
    ∑ F ∈ (tupleExponent ι x).support.powerset, cechBlockProj ι k h𝓜 x F z = z := by
  have h := sum_blockProj h𝓜 (tupleExponent ι x) (cechTermEquiv ι k 𝓜 x z)
  calc ∑ F ∈ (tupleExponent ι x).support.powerset, cechBlockProj ι k h𝓜 x F z
      = (cechTermEquiv ι k 𝓜 x).symm
          (∑ F ∈ (tupleExponent ι x).support.powerset,
            blockProj h𝓜 (tupleExponent ι x) F (cechTermEquiv ι k 𝓜 x z)) := by
        rw [map_sum]
        rfl
    _ = z := by rw [h, AddEquiv.symm_apply_apply]

/-- The block projections are idempotent, transported from `blockProj_blockProj_self`. -/
theorem cechBlockProj_cechBlockProj_self (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    (x : Fin (n + 1) → ι) (F : Finset ι) (z : cechTerm ι k 𝓜 x) :
    cechBlockProj ι k h𝓜 x F (cechBlockProj ι k h𝓜 x F z) =
      cechBlockProj ι k h𝓜 x F z := by
  rw [cechBlockProj_apply, cechBlockProj_apply, AddEquiv.apply_symm_apply,
    blockProj_blockProj_self]

/-- A block off the tuple's support is zero. -/
theorem cechBlockProj_eq_zero_of_not_subset (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    (x : Fin (n + 1) → ι)
    {F : Finset ι} (h : ¬ F ⊆ (tupleExponent ι x).support)
    (z : cechTerm ι k 𝓜 x) :
    cechBlockProj ι k h𝓜 x F z = 0 := by
  rw [cechBlockProj_apply, blockProj_eq_zero_of_not_subset h𝓜 h, map_zero]

/-- **The Čech faces commute with the block projections.** The transported form of
`laurentFace_blockProj`: the differential preserves every block. -/
theorem cechFace_cechBlockProj (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    (x : Fin (n + 2) → ι) (j : Fin (n + 2))
    (F : Finset ι) (z : cechTerm ι k 𝓜 (x ∘ j.succAbove)) :
    cechFace ι k 𝓜 x j (cechBlockProj ι k h𝓜 (x ∘ j.succAbove) F z) =
      cechBlockProj ι k h𝓜 x F (cechFace ι k 𝓜 x j z) := by
  apply (cechTermEquiv ι k 𝓜 x).injective
  rw [cechTermEquiv_cechFace, cechBlockProj_apply, cechBlockProj_apply,
    AddEquiv.apply_symm_apply, cechTermEquiv_cechFace,
    laurentFace_blockProj h𝓜 (tupleExponent_succAbove x j) F,
    AddEquiv.apply_symm_apply]

/-! ## The homotopy map on Čech terms -/

/-- The homotopy map on Čech terms: the monomial-level `laurentHomotopy` conjugated by the
denominator comparisons of the cone tuple and the base tuple. -/
noncomputable def cechHomotopy (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι) {n : ℕ} (y : Fin (n + 1) → ι) :
    cechTerm ι k 𝓜 (Fin.cons i₀ y) →+
      cechTerm ι k 𝓜 y :=
  ((cechTermEquiv ι k 𝓜 y).symm.toAddMonoidHom.comp
    (laurentHomotopy h𝓜 i₀ (tupleExponent ι y))).comp
    (DegreeZeroLocalization.powersCongr (tupleDenominator_cons_eq k i₀ y)).toAddMonoidHom

theorem cechHomotopy_apply (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι) {n : ℕ} (y : Fin (n + 1) → ι)
    (z : cechTerm ι k 𝓜 (Fin.cons i₀ y)) :
    cechHomotopy ι k h𝓜 i₀ y z =
      (cechTermEquiv ι k 𝓜 y).symm
        (laurentHomotopy h𝓜 i₀ (tupleExponent ι y)
          (DegreeZeroLocalization.powersCongr (tupleDenominator_cons_eq k i₀ y) z)) :=
  rfl

/-! ## Transport along an equality of tuples

The faces of a cone tuple land at tuples like `(i₀ :: x) ∘ (j.succ).succAbove`, which equal
`i₀ :: (x ∘ j.succAbove)` only propositionally. The transport, and the one dependent-rewriting
lemma every use reduces to: a cochain takes transported values at equal tuples. -/

/-- Transport a Čech term along an equality of tuples. -/
noncomputable def cechTermCongr (𝓜 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] {n : ℕ} {x₁ x₂ : Fin (n + 1) → ι} (h : x₁ = x₂) :
    cechTerm ι k 𝓜 x₁ ≃+ cechTerm ι k 𝓜 x₂ :=
  DegreeZeroLocalization.powersCongr
    (congrArg (polynomialVariableCechDenominator ι k) h)

/-- **A cochain takes transported values at equal tuples.** This is the whole of the dependent
rewriting the vanishing computation needs. -/
theorem cechTermCongr_apply_section (𝓜 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] {n : ℕ}
    (s : ∀ x : Fin (n + 1) → ι, cechTerm ι k 𝓜 x)
    {x₁ x₂ : Fin (n + 1) → ι} (h : x₁ = x₂) :
    cechTermCongr ι k 𝓜 h (s x₁) = s x₂ := by
  subst h; rfl

theorem cechTermCongr_symm_apply_section (𝓜 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] {n : ℕ}
    (s : ∀ x : Fin (n + 1) → ι, cechTerm ι k 𝓜 x)
    {x₁ x₂ : Fin (n + 1) → ι} (h : x₁ = x₂) :
    (cechTermCongr ι k 𝓜 h).symm (s x₂) = s x₁ := by
  subst h; rfl

/-- The block projections commute with tuple transport. -/
theorem cechTermCongr_cechBlockProj (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    {x₁ x₂ : Fin (n + 1) → ι} (h : x₁ = x₂)
    (F : Finset ι) (z : cechTerm ι k 𝓜 x₁) :
    cechTermCongr ι k 𝓜 h (cechBlockProj ι k h𝓜 x₁ F z) =
      cechBlockProj ι k h𝓜 x₂ F (cechTermCongr ι k 𝓜 h z) := by
  subst h; rfl

/-! ## The homotopy identities on Čech terms -/

variable {ι k}

/-- `laurentHomotopy_laurentFace_comm` with the enlarged denominator's exponent named by a
hypothesis rather than fixed as `γ₀ + single e 1`. The Čech caller's exponent is
`tupleExponent x`, which equals that sum only propositionally. -/
theorem laurentHomotopy_laurentFace_comm' (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ e : ι)
    {γ₀ γx : ι →₀ ℕ}
    (hγx : γx = γ₀ + Finsupp.single e 1)
    (htop : Finsupp.single i₀ 1 + γx = Finsupp.single e 1 + (Finsupp.single i₀ 1 + γ₀))
    (hbot : γx = Finsupp.single e 1 + γ₀)
    (z : DegreeZeroLocalization (polynomialGrading ι k)
      𝓜
      (.powers (MvPolynomial.monomial (Finsupp.single i₀ 1 + γ₀) (1 : k)))) :
    laurentHomotopy h𝓜 i₀ γx (laurentFace 𝓜 htop z) =
      laurentFace 𝓜 hbot (laurentHomotopy h𝓜 i₀ γ₀ z) := by
  subst hγx
  exact laurentHomotopy_laurentFace_comm h𝓜 i₀ e γ₀ htop hbot z

variable (ι k)

set_option maxHeartbeats 800000 in
/-- **The homotopy retracts the cone face on a block.** The Čech form of
`laurentHomotopy_laurentFace_blockProj`: for `i₀ ∉ F`, restricting a block-`F` element of the
base tuple along the `0`-face of the cone tuple and applying the homotopy gives it back. The
transport on the face's input names the tuple identity `(i₀ :: y) ∘ δ₀ = y`. -/
theorem cechHomotopy_cechFace_zero (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι)
    {F : Finset ι} (hi₀ : i₀ ∉ F)
    {n : ℕ} (y : Fin (n + 1) → ι) (z : cechTerm ι k 𝓜 y) :
    cechHomotopy ι k h𝓜 i₀ y
        (cechFace ι k 𝓜 (Fin.cons i₀ y) 0
          ((cechTermCongr ι k 𝓜 (cons_comp_succAbove_zero i₀ y)).symm
            (cechBlockProj ι k h𝓜 y F z))) =
      cechBlockProj ι k h𝓜 y F z := by
  rw [cechHomotopy_apply]
  have hface : DegreeZeroLocalization.powersCongr (tupleDenominator_cons_eq k i₀ y)
      (cechFace ι k 𝓜 (Fin.cons i₀ y) 0
        ((cechTermCongr ι k 𝓜 (cons_comp_succAbove_zero i₀ y)).symm
          (cechBlockProj ι k h𝓜 y F z))) =
      laurentFace 𝓜 (rfl : Finsupp.single i₀ 1 + tupleExponent ι y =
          Finsupp.single i₀ 1 + tupleExponent ι y)
        (DegreeZeroLocalization.powersCongr
          ((congrArg (polynomialVariableCechDenominator ι k)
            (cons_comp_succAbove_zero i₀ y)).trans (tupleDenominator_eq ι k y))
          ((cechTermCongr ι k 𝓜 (cons_comp_succAbove_zero i₀ y)).symm
            (cechBlockProj ι k h𝓜 y F z))) :=
    DegreeZeroLocalization.powersCongr_faceMap _ _
      (by rw [Fin.cons_zero]; rfl)
      _ (monomial_single_mem i₀ 1)
      (polynomialVariableCechDenominator_succAbove_mem ι k (Fin.cons i₀ y) 0) _
      (polynomialVariableCechDenominator_succAbove ι k (Fin.cons i₀ y) 0) _ _
  rw [hface, cechTermCongr,
    DegreeZeroLocalization.powersCongr_symm_trans _ _ (tupleDenominator_eq ι k y),
    cechBlockProj_apply, DegreeZeroLocalization.powersCongr]
  show (cechTermEquiv ι k 𝓜 y).symm
      (laurentHomotopy h𝓜 i₀ (tupleExponent ι y)
        (laurentFace 𝓜 rfl
          ((cechTermEquiv ι k 𝓜 y)
            ((cechTermEquiv ι k 𝓜 y).symm
              (blockProj h𝓜 (tupleExponent ι y) F (cechTermEquiv ι k 𝓜 y z)))))) = _
  rw [AddEquiv.apply_symm_apply,
    laurentHomotopy_laurentFace_blockProj h𝓜 hi₀ (tupleExponent ι y)
      (cechTermEquiv ι k 𝓜 y z)]

set_option maxHeartbeats 800000 in
/-- **The homotopy commutes with every other face.** The Čech form of
`laurentHomotopy_laurentFace_comm`, with no restriction on the block or the face's variable.
The transport on the face's input names the tuple identity
`(i₀ :: x) ∘ δ_{j.succ} = i₀ :: (x ∘ δⱼ)`. -/
theorem cechHomotopy_cechFace_succ (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι) {n : ℕ}
    (x : Fin (n + 2) → ι)
    (j : Fin (n + 2))
    (z : cechTerm ι k 𝓜 (Fin.cons i₀ (x ∘ j.succAbove))) :
    cechHomotopy ι k h𝓜 i₀ x
        (cechFace ι k 𝓜 (Fin.cons i₀ x) j.succ
          ((cechTermCongr ι k 𝓜 (cons_comp_succAbove_succ i₀ x j)).symm z)) =
      cechFace ι k 𝓜 x j
        (cechHomotopy ι k h𝓜 i₀ (x ∘ j.succAbove) z) := by
  have hsplitTop : Finsupp.single i₀ 1 + tupleExponent ι x =
      Finsupp.single (x j) 1 + (Finsupp.single i₀ 1 + tupleExponent ι (x ∘ j.succAbove)) := by
    rw [tupleExponent_succAbove x j, add_left_comm]
  have hface : DegreeZeroLocalization.powersCongr (tupleDenominator_cons_eq k i₀ x)
      (cechFace ι k 𝓜 (Fin.cons i₀ x) j.succ
        ((cechTermCongr ι k 𝓜 (cons_comp_succAbove_succ i₀ x j)).symm z)) =
      laurentFace 𝓜 hsplitTop
        (DegreeZeroLocalization.powersCongr
          ((congrArg (polynomialVariableCechDenominator ι k)
            (cons_comp_succAbove_succ i₀ x j)).trans
              (tupleDenominator_cons_eq k i₀ (x ∘ j.succAbove)))
          ((cechTermCongr ι k 𝓜 (cons_comp_succAbove_succ i₀ x j)).symm z)) :=
    DegreeZeroLocalization.powersCongr_faceMap _ _
      (by rw [Fin.cons_succ]; rfl)
      _ (monomial_single_mem (x j) 1)
      (polynomialVariableCechDenominator_succAbove_mem ι k (Fin.cons i₀ x) j.succ) _
      (polynomialVariableCechDenominator_succAbove ι k (Fin.cons i₀ x) j.succ) _ _
  rw [cechHomotopy_apply, hface, cechTermCongr,
    DegreeZeroLocalization.powersCongr_symm_trans _ _
      (tupleDenominator_cons_eq k i₀ (x ∘ j.succAbove)),
    laurentHomotopy_laurentFace_comm' h𝓜 i₀ (x j)
      ((tupleExponent_succAbove x j).trans (add_comm _ _)) hsplitTop
      (tupleExponent_succAbove x j)]
  apply (cechTermEquiv ι k 𝓜 x).injective
  rw [AddEquiv.apply_symm_apply, cechTermEquiv_cechFace, cechHomotopy_apply,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry.Proj
