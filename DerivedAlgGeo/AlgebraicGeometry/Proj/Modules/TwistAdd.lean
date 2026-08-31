/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistingSheaf

/-!
# The twists compose, on the sheaf side

`Shift.lean` proves that the graded identity `M(d)(e) = M(d + e)` is **false**. `intShift`
zero-extends, so with `d = 10`, `e = -5` and `n = 0` the double shift is `{0}` while the single
shift is `𝓜 5`; `eq_zero_of_mem_intShift_intShift_of_neg` is a theorem written for no purpose
other than to record that. Its note also says what to do about it:

> This is a fact about the *algebraic* model, not about the sheaf. `associatedSheaf` only ever
> reads these pieces through homogeneous localizations, where the missing degrees are inverted
> back in, so the sheaf-level composition `O(d)(e) ≅ O(d + e)` is not obstructed by this — but it
> cannot be obtained by transporting an algebraic identity, and has to be proved on the sheaf side.

This file is that proof, and `sheafTwistAddIso` is the integer analogue of `sheafNatTwistAddIso`
that `TwistingSheaf.lean` declined to assert for exactly this reason.

## The shape of the argument

The comparison is *pointwise the identity*. `Fiber` is `DegreeZeroLocalization`, which is a
submodule of `LocalizedModule S M`, and that ambient does not mention the grading at all — so the
two twists are subobjects of one object and `degreeZeroSubmodule_intShift_intShift` says their
carriers coincide. Nothing is transported; only the certificate changes.

What is left is the local-fraction condition, and the two directions are not symmetric:

* forward, nothing moves. The numerator's certificate is rebuilt through
  `mem_intShift_add_of_mem_intShift_intShift`, whose hypothesis-free existence is the useful
  half of `mem_intShift_add_iff_of_nonneg`;
* backward is where the content is. A fraction certified only for the single shift is rewritten as
  `τ^k · r / τ^k · t`, which raises its degree without changing the element until the double shift
  can certify it, and the neighbourhood shrinks to `V ⊓ D₊(τ)` so that **one** `τ` serves every
  point of it. The pointwise statement would not suffice: `isLocallyFraction` demands a single
  fraction on a whole neighbourhood, and a per-point choice of `τ` would not give one.

`exists_homogeneous_pos_not_mem` supplies the `τ`, and is where the geometry enters: a point of
`Proj` is exactly a relevant prime, so it misses a homogeneous element of positive degree.

## Scope

The composition only. Relating it to the *tensor* product — `F ⊗ O(d) ≅ F(d)`, and hence
`O(d) ⊗ O(e) ≅ O(d + e)` — is a separate comparison and is not here.
-/

noncomputable section

open scoped DirectSum Pointwise

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- Every point of `Proj` misses a homogeneous element of positive degree. -/
theorem exists_homogeneous_pos_not_mem (x : ProjectiveSpectrum 𝒜) :
    ∃ (m : ℕ) (t : A), 0 < m ∧ t ∈ 𝒜 m ∧ t ∉ x.asHomogeneousIdeal := by
  by_contra hcon
  have hcon' : ∀ (m : ℕ) (t : A), 0 < m → t ∈ 𝒜 m → t ∈ x.asHomogeneousIdeal := by
    intro m t hm ht
    by_contra h
    exact hcon ⟨m, t, hm, ht, h⟩
  refine x.not_irrelevant_le ?_
  intro a ha
  rw [← HomogeneousIdeal.mem_iff, x.asHomogeneousIdeal.isHomogeneous.mem_iff]
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h0 : (DirectSum.decompose 𝒜 a 0 : A) = 0 := by
      simpa [GradedRing.proj_apply] using (HomogeneousIdeal.mem_irrelevant_iff 𝒜 a).mp ha
    rw [h0]
    exact Ideal.zero_mem _
  · exact HomogeneousIdeal.mem_iff.mpr (hcon' i _ hi (SetLike.coe_mem _))

/-- The point misses `t`, phrased for the localization's denominators. -/
theorem mem_primeCompl_of_not_mem {x : ProjectiveSpectrum 𝒜} {t : A}
    (ht : t ∉ x.asHomogeneousIdeal) : t ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  fun h => ht (HomogeneousIdeal.mem_iff.mp h)

/-- **The two shifts have the same fiber at every point of `Proj`.** -/
theorem degreeZeroSubmodule_intShift_intShift (x : ProjectiveSpectrum 𝒜) (d e : ℤ) :
    degreeZeroSubmodule 𝒜 (intShift (intShift 𝓜 d) e)
        x.asHomogeneousIdeal.toIdeal.primeCompl =
      degreeZeroSubmodule 𝒜 (intShift 𝓜 (d + e))
        x.asHomogeneousIdeal.toIdeal.primeCompl := by
  obtain ⟨m, t, hm, ht, htx⟩ := exists_homogeneous_pos_not_mem 𝒜 x
  refine Submodule.ext fun z => ?_
  exact isDegreeZero_intShift_intShift_iff 𝒜 𝓜 _ hm ht (mem_primeCompl_of_not_mem 𝒜 htx) d e z

/-- The fiber comparison, as a linear equivalence. It is the identity on carriers. -/
noncomputable def fiberIntShiftAddEquiv (x : ProjectiveSpectrum 𝒜) (d e : ℤ) :
    ↥(Fiber 𝒜 (intShift (intShift 𝓜 d) e) x) ≃ₗ[HomogeneousLocalization 𝒜
        x.asHomogeneousIdeal.toIdeal.primeCompl]
      ↥(Fiber 𝒜 (intShift 𝓜 (d + e)) x) :=
  LinearEquiv.ofEq _ _ (degreeZeroSubmodule_intShift_intShift 𝒜 𝓜 x d e)

@[simp]
theorem fiberIntShiftAddEquiv_coe (x : ProjectiveSpectrum 𝒜) (d e : ℤ)
    (z : ↥(Fiber 𝒜 (intShift (intShift 𝓜 d) e) x)) :
    (fiberIntShiftAddEquiv 𝒜 𝓜 x d e z).1 = z.1 := rfl

/-- **Backward transfer of the local-fraction condition.**

The fraction certified for the single shift is rewritten with a power of `τ` in numerator and
denominator, which raises its degree until the double shift can certify it. The neighbourhood
shrinks to `V ⊓ D₊(τ)` so that one `τ` serves every point of it. -/
theorem pred_intShift_intShift_of_pred (d e : ℤ) {U : Opens X}
    (g : ∀ x : U, Fiber 𝒜 (intShift 𝓜 (d + e)) x.1)
    (hg : (isLocallyFraction 𝒜 (intShift 𝓜 (d + e))).pred g) :
    (isLocallyFraction 𝒜 (intShift (intShift 𝓜 d) e)).pred
      (fun x => (fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e).symm (g x)) := by
  intro x
  obtain ⟨V, hxV, incl, deg, r, t, ht, h⟩ := hg x
  obtain ⟨m, τ, hm, hτ, hτx⟩ := exists_homogeneous_pos_not_mem 𝒜 x.1
  set k : ℕ := (-e).toNat with hk_def
  have hkm : (0 : ℤ) ≤ ((deg + k * m : ℕ) : ℤ) + e := by
    have h1 : -e ≤ (k : ℤ) := by rw [hk_def]; exact Int.self_le_toNat _
    have h2 : k * 1 ≤ k * m := Nat.mul_le_mul_left k hm
    push_cast
    omega
  have hxb : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒜 τ := hτx
  refine ⟨V ⊓ ProjectiveSpectrum.basicOpen 𝒜 τ, ⟨hxV, hxb⟩,
    homOfLE (le_trans inf_le_left (leOfHom incl)), deg + k * m,
    ⟨τ ^ k • (r : M), ?_⟩, ⟨τ ^ k * (t : A), ?_⟩, ?_, ?_⟩
  · refine (mem_intShift_add_iff_of_nonneg 𝓜 d e (deg + k * m) hkm _).mpr ?_
    have hnum : τ ^ k • (r : M) ∈ intShift 𝓜 (d + e) (k * m + deg) :=
      SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded k hτ) r.2
    rwa [add_comm (k * m) deg] at hnum
  · have hden : τ ^ k * (t : A) ∈ 𝒜 (k * m + deg) :=
      SetLike.mul_mem_graded (SetLike.pow_mem_graded k hτ) t.2
    rwa [add_comm (k * m) deg] at hden
  · rintro ⟨y, hyV, hyb⟩
    have hτy : τ ∉ y.asHomogeneousIdeal := hyb
    have hty : (t : A) ∉ y.asHomogeneousIdeal := ht ⟨y, hyV⟩
    intro hc
    rcases y.isPrime.mem_or_mem hc with hc1 | hc2
    · exact hτy (y.isPrime.mem_of_pow_mem k hc1)
    · exact hty hc2
  · rintro ⟨y, hyV, hyb⟩
    refine DegreeZeroLocalization.ext ?_
    show (g (incl ⟨y, hyV⟩)).1 = _
    have hy : g (incl ⟨y, hyV⟩) =
        DegreeZeroLocalization.mk
          { deg := deg, num := r, den := t, den_mem := ht ⟨y, hyV⟩ } := h ⟨y, hyV⟩
    rw [hy]
    simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding]
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.mk_smul, smul_smul]
    rw [mul_comm]

/-- **Forward transfer of the local-fraction condition.**

Nothing moves: the fraction is the same, and only the numerator's membership certificate is
rebuilt, through the unconditional inclusion. -/
theorem pred_intShift_add_of_pred (d e : ℤ) {U : Opens X}
    (f : ∀ x : U, Fiber 𝒜 (intShift (intShift 𝓜 d) e) x.1)
    (hf : (isLocallyFraction 𝒜 (intShift (intShift 𝓜 d) e)).pred f) :
    (isLocallyFraction 𝒜 (intShift 𝓜 (d + e))).pred
      (fun x => fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e (f x)) := by
  intro x
  obtain ⟨V, hxV, incl, deg, r, t, ht, h⟩ := hf x
  refine ⟨V, hxV, incl, deg,
    ⟨(r : M), mem_intShift_add_of_mem_intShift_intShift 𝓜 d e deg r.2⟩, t, ht, ?_⟩
  intro y
  refine DegreeZeroLocalization.ext ?_
  show (f (incl y)).1 = _
  have hy : f (incl y) =
      DegreeZeroLocalization.mk
        { deg := deg, num := r, den := t, den_mem := ht y } := h y
  rw [hy]
  rfl

/-- **The two twists have the same sections over every open.** -/
noncomputable def sectionAddEquivIntShiftAdd (d e : ℤ) (U : Opens X) :
    (associatedSheafInType 𝒜 (intShift (intShift 𝓜 d) e)).1.obj (op U) ≃+
      (associatedSheafInType 𝒜 (intShift 𝓜 (d + e))).1.obj (op U) where
  toFun s := ⟨fun x => fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e (s.1 x),
    pred_intShift_add_of_pred 𝒜 𝓜 d e s.1 s.2⟩
  invFun s := ⟨fun x => (fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e).symm (s.1 x),
    pred_intShift_intShift_of_pred 𝒜 𝓜 d e s.1 s.2⟩
  left_inv s := by
    apply section_ext
    funext x
    exact (fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e).symm_apply_apply (s.1 x)
  right_inv s := by
    apply section_ext
    funext x
    exact (fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e).apply_symm_apply (s.1 x)
  map_add' s t := by
    apply section_ext
    funext x
    exact (fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e).map_add (s.1 x) (t.1 x)

/-- The section comparison is linear over the structure-sheaf sections. -/
noncomputable def sectionLinearEquivIntShiftAdd (d e : ℤ) (U : Opens X) :
    (associatedSheafInType 𝒜 (intShift (intShift 𝓜 d) e)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 (intShift 𝓜 (d + e))).1.obj (op U) :=
  { sectionAddEquivIntShiftAdd 𝒜 𝓜 d e U with
    map_smul' := fun r s => by
      apply section_ext
      funext x
      exact (fiberIntShiftAddEquiv 𝒜 𝓜 x.1 d e).map_smul
        (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (s.1 x) }

/-- **`O(d)(e) ≅ O(d + e)`, on the sheaf side.** -/
noncomputable def associatedSheafIntShiftAddIso (d e : ℤ) :
    associatedSheaf 𝒜 (intShift (intShift 𝓜 d) e) ≅
      associatedSheaf 𝒜 (intShift 𝓜 (d + e)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U ↦ (sectionLinearEquivIntShiftAdd 𝒜 𝓜 d e U.unop).toModuleIso)
      (by
        intro U V g
        ext s
        apply section_ext
        funext x
        rfl)


/-- **The integer twists compose.**

The statement `TwistingSheaf.lean` records as belonging "with the later quasi-coherence/basic-open
equivalence", and the integer analogue of `sheafNatTwistAddIso`. Definitionally this is
`associatedSheafIntShiftAddIso`; it is restated in twist language because that is how callers
meet it. -/
noncomputable def sheafTwistAddIso (d e : ℤ) :
    sheafTwist 𝒜 (intShift 𝓜 d) e ≅ sheafTwist 𝒜 𝓜 (d + e) :=
  associatedSheafIntShiftAddIso 𝒜 𝓜 d e

section Ring

variable [SetLike.GradedSMul 𝒜 𝒜]

/-- **`O(d)(e) ≅ O(d + e)`.**

The headline instance of `sheafTwistAddIso`, at the graded ring as a module over itself. -/
noncomputable def twistingSheafAddIso (d e : ℤ) :
    sheafTwist 𝒜 (intShift 𝒜 d) e ≅ twistingSheaf 𝒜 (d + e) :=
  sheafTwistAddIso 𝒜 𝒜 d e

end Ring

end AlgebraicGeometry.Proj
