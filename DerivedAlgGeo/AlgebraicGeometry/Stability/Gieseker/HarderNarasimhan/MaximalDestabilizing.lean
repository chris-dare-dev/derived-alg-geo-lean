/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.MuStability
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# The maximal destabilizing subobject for the μ-slope on `Coh X`

Harder–Narasimhan theory for the weak μ-slope rests on one lemma: every nonzero coherent sheaf
has a subobject whose slope is maximal among nonzero subobjects, chosen maximal among those
attaining that slope, and such a subobject is weak-semistable. This file proves it from two
named inputs and nothing else.

## What is supplied, and what is proved

`MuHNInput` carries exactly two facts, neither available at this pin:

* *subobject-chain termination*, `IsNoetherianObject F` for every coherent sheaf. `Coh X` on a
  noetherian variety is a noetherian category; the transfer lemma a geometric proof would use is
  `isNoetherianObject_of_fullFaithful_preservesMono` in `CategoryTheory/Abelian/QuasiAbelian.lean`,
  applied through `Coh.ι`.
* *slope boundedness*, Grothendieck's lemma: the μ-slopes of nonzero subobjects of a fixed `F`
  are bounded above.

Neither the maximal destabilizing subobject nor `HasHNProperty` is a field. Everything below is
derived.

## Two corrections to the shape of the second input

**The `WithTop ℝ` form of boundedness is vacuous.** Stated as `∃ μ₀ : WithTop ℝ, ∀ B ≠ 0,
slope B ≤ μ₀`, the hypothesis is satisfied by `μ₀ = ⊤` for every `F`, and carries no
information. The field below therefore takes a *real* bound and quantifies only over subobjects
of positive multiplicity — which is exactly Grothendieck's lemma, and leaves the
multiplicity-zero case where it belongs, in `slope_eq_top_iff_not_isPure`.

**No third input is needed.** One might expect boundedness not to give an attained maximum,
since slopes are quotients of integers and a bounded set of such is dense in general. It does
here, because multiplicity is additive and nonnegative, so `multiplicity B ≤ multiplicity F` for
every subobject: the denominators are bounded by a single integer. Every slope is then a multiple
of `1 / (multiplicity F)!`, and a set of such numbers bounded above has a greatest element. That
is `exists_slopeMax`, and it is why `MuHNInput` has two fields rather than three.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- **The two inputs sheaf-level Harder–Narasimhan theory needs**, neither provable at this pin.
See the module docstring for what would discharge each, and for why boundedness must be stated
with a real bound rather than in `WithTop ℝ`. -/
structure MuHNInput (P : PolarizedVarietyData k X) (h : MuPositivityData P) : Prop where
  /-- Ascending chains of subobjects terminate. `Coh X` on a noetherian variety is a noetherian
  category; no instance exists at this pin. -/
  noetherian : ∀ F : Coh X, IsNoetherianObject F
  /-- **Grothendieck's boundedness lemma**: the μ-slopes of the nonzero subobjects of positive
  multiplicity of a fixed sheaf are bounded above by a real number. Nothing in the tree supplies
  it. The bound is real, not `WithTop ℝ`, because `⊤` bounds everything. -/
  slope_bddAbove : ∀ F : Coh X, ∃ μ₀ : ℝ, ∀ B : Subobject F, ¬IsZero (B : Coh X) →
    0 < P.multiplicity (B : Coh X) →
      (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) / (P.multiplicity (B : Coh X) : ℝ) ≤ μ₀

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-! ### Multiplicity is bounded along monomorphisms -/

/-- **A subsheaf has multiplicity at most that of the ambient sheaf.** Additivity of multiplicity
on the short exact sequence defined by a monomorphism, together with nonnegativity of the
multiplicity of the cokernel. This is what bounds the denominators of the slopes, and so what
makes the maximal slope attained rather than merely bounded. -/
theorem multiplicity_le_of_mono (h : MuPositivityData P) {G F : Coh X} (i : G ⟶ F) [Mono i] :
    P.multiplicity G ≤ P.multiplicity F := by
  have hSE : (ShortComplex.mk i (cokernel.π i) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  have hadd := P.hilbertCoefficient_additive _ hSE P.dim
  have hnn := h.multiplicity_nonneg (cokernel i)
  change P.multiplicity F = P.multiplicity G + P.multiplicity (cokernel i) at hadd
  omega

/-- The subobject form of `multiplicity_le_of_mono`. -/
theorem multiplicity_subobject_le (h : MuPositivityData P) {F : Coh X} (B : Subobject F) :
    P.multiplicity (B : Coh X) ≤ P.multiplicity F :=
  multiplicity_le_of_mono h B.arrow

/-! ### The maximal slope is attained -/

/-- The slope of a nonzero subobject of positive multiplicity, as a real number. -/
private noncomputable def realSlope (P : PolarizedVarietyData k X) {F : Coh X}
    (B : Subobject F) : ℝ :=
  (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) / (P.multiplicity (B : Coh X) : ℝ)

private theorem topSlope_eq_coe_realSlope (h : MuPositivityData P) {F : Coh X}
    (B : Subobject F) (hB : 0 < P.multiplicity (B : Coh X)) :
    (P.weakSlopeData h).topSlope (B : Coh X) = ((realSlope P B : ℝ) : WithTop ℝ) :=
  weakSlopeData_topSlope_of_multiplicity_pos h hB

/-- **The maximal slope is attained.**

Either some nonzero subobject has multiplicity zero, and its slope is `⊤`, which dominates
everything; or every nonzero subobject has multiplicity between `1` and `multiplicity F`, so
every slope is an integer multiple of `1 / (multiplicity F)!`, and boundedness above of a set of
such numbers gives a greatest element. -/
theorem exists_slopeMax (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) :
    ∃ B : Subobject F, ¬IsZero (B : Coh X) ∧
      ∀ B' : Subobject F, ¬IsZero (B' : Coh X) →
        (P.weakSlopeData h).topSlope (B' : Coh X) ≤
          (P.weakSlopeData h).topSlope (B : Coh X) := by
  classical
  have htopne : ¬IsZero ((⊤ : Subobject F) : Coh X) := by
    intro hz
    exact hF (hz.of_iso (asIso (⊤ : Subobject F).arrow).symm)
  by_cases hzero : ∃ B : Subobject F, ¬IsZero (B : Coh X) ∧ P.multiplicity (B : Coh X) = 0
  · obtain ⟨B, hBne, hB0⟩ := hzero
    refine ⟨B, hBne, fun B' _ ↦ ?_⟩
    rw [weakSlopeData_topSlope_of_multiplicity_zero h hB0]
    exact le_top
  · push Not at hzero
    have hpos : ∀ B : Subobject F, ¬IsZero (B : Coh X) → 0 < P.multiplicity (B : Coh X) := by
      intro B hB
      have hne := hzero B hB
      have hnn := h.multiplicity_nonneg (B : Coh X)
      omega
    obtain ⟨μ₀, hμ₀⟩ := I.slope_bddAbove F
    set M : ℕ := (P.multiplicity F).toNat with hM
    set K : ℤ := (Nat.factorial M : ℤ) with hK
    have hKpos : 0 < K := by
      rw [hK]
      exact_mod_cast Nat.factorial_pos M
    have hdvd : ∀ B : Subobject F, ¬IsZero (B : Coh X) →
        P.multiplicity (B : Coh X) ∣ K := by
      intro B hB
      have h1 := hpos B hB
      have h2 := multiplicity_subobject_le h B
      have hnat : (P.multiplicity (B : Coh X)).toNat ∣ Nat.factorial M :=
        Nat.dvd_factorial (by omega) (by omega)
      have := Int.natCast_dvd_natCast.mpr hnat
      rwa [Int.toNat_of_nonneg (by omega)] at this
    -- the integer numerator of the slope over the common denominator `K`
    set g : Subobject F → ℤ := fun B ↦
      P.hilbertDegreeCoefficient (B : Coh X) * (K / P.multiplicity (B : Coh X)) with hg
    have hgslope : ∀ B : Subobject F, ¬IsZero (B : Coh X) →
        realSlope P B = (g B : ℝ) / (K : ℝ) := by
      intro B hB
      have h1 := hpos B hB
      have hmul : g B * P.multiplicity (B : Coh X) =
          P.hilbertDegreeCoefficient (B : Coh X) * K := by
        rw [hg, mul_assoc, Int.ediv_mul_cancel (hdvd B hB)]
      have hmr : (P.multiplicity (B : Coh X) : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (P.multiplicity (B : Coh X) : ℝ) := by exact_mod_cast h1
        exact ne_of_gt this
      have hKr : (K : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
        exact ne_of_gt this
      rw [realSlope, div_eq_div_iff hmr hKr]
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℝ)) hmul.symm
    have hbdd : ∃ b : ℤ, ∀ z : ℤ,
        (∃ B : Subobject F, ¬IsZero (B : Coh X) ∧ g B = z) → z ≤ b := by
      refine ⟨⌈μ₀ * (K : ℝ)⌉, ?_⟩
      rintro z ⟨B, hBne, rfl⟩
      have hle := hμ₀ B hBne (hpos B hBne)
      have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
      have : (g B : ℝ) / (K : ℝ) ≤ μ₀ := by
        rw [← hgslope B hBne]
        exact hle
      have hz : (g B : ℝ) ≤ μ₀ * (K : ℝ) := by
        rw [div_le_iff₀ hKr] at this
        exact this
      have hceil : (g B : ℝ) ≤ ((⌈μ₀ * (K : ℝ)⌉ : ℤ) : ℝ) := le_trans hz (Int.le_ceil _)
      exact_mod_cast hceil
    obtain ⟨n, ⟨B, hBne, hBg⟩, hmax⟩ :=
      Int.exists_greatest_of_bdd hbdd ⟨g (⊤ : Subobject F), ⟨⊤, htopne, rfl⟩⟩
    refine ⟨B, hBne, fun B' hB'ne ↦ ?_⟩
    rw [topSlope_eq_coe_realSlope h B' (hpos B' hB'ne),
      topSlope_eq_coe_realSlope h B (hpos B hBne), WithTop.coe_le_coe,
      hgslope B' hB'ne, hgslope B hBne]
    have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hle : g B' ≤ g B := by
      rw [hBg]
      exact hmax _ ⟨B', hB'ne, rfl⟩
    have hnum : (g B' : ℝ) ≤ (g B : ℝ) := by exact_mod_cast hle
    gcongr

/-! ### The maximal destabilizing subobject -/

/-- **The maximal destabilizing subobject**, as a property: nonzero, of maximal slope among
nonzero subobjects, and maximal in the subobject order among those attaining that slope. The
second clause is what makes the slope drop strictly on the quotient, which the recursion
building the filtration needs. -/
def IsMaximalDestabilizing (h : MuPositivityData P) (F : Coh X) (B : Subobject F) : Prop :=
  ¬IsZero (B : Coh X) ∧
    (∀ B' : Subobject F, ¬IsZero (B' : Coh X) →
      (P.weakSlopeData h).topSlope (B' : Coh X) ≤ (P.weakSlopeData h).topSlope (B : Coh X)) ∧
    ∀ B' : Subobject F, ¬IsZero (B' : Coh X) →
      (P.weakSlopeData h).topSlope (B' : Coh X) = (P.weakSlopeData h).topSlope (B : Coh X) →
        ¬B < B'

/-- **Every nonzero coherent sheaf has a maximal destabilizing subobject.**

`exists_slopeMax` attains the slope; the chain condition then picks a subobject maximal among
those attaining it. -/
theorem exists_maximalDestabilizing (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) : ∃ B : Subobject F, IsMaximalDestabilizing h F B := by
  classical
  obtain ⟨B₀, hB₀ne, hB₀max⟩ := exists_slopeMax h I hF
  haveI : IsNoetherianObject F := I.noetherian F
  have hwf : WellFounded ((· > ·) : Subobject F → Subobject F → Prop) :=
    (inferInstance : WellFoundedGT (Subobject F)).wf
  obtain ⟨Bmax, hBmem, hBmin⟩ := hwf.has_min
    {B' : Subobject F | ¬IsZero (B' : Coh X) ∧
      (P.weakSlopeData h).topSlope (B' : Coh X) =
        (P.weakSlopeData h).topSlope (B₀ : Coh X)} ⟨B₀, hB₀ne, rfl⟩
  obtain ⟨hBne, hBslope⟩ := hBmem
  refine ⟨Bmax, hBne, fun B' hB' ↦ ?_, fun B' hB' hB'slope hlt ↦ ?_⟩
  · rw [hBslope]
    exact hB₀max B' hB'
  · exact hBmin B' ⟨hB', by rw [hB'slope, hBslope]⟩ hlt

/-- **The maximal destabilizing subobject is weak-semistable.** A nonzero subobject of it is a
nonzero subobject of the ambient sheaf, so its slope cannot exceed the maximal one. -/
theorem maximalDestabilizing_isSemistable (h : MuPositivityData P) {F : Coh X}
    {B : Subobject F} (hB : IsMaximalDestabilizing h F B) :
    (P.weakSlopeData h).toWeakStabilityFunction.IsSemistable (B : Coh X) := by
  refine ⟨hB.1, fun C hC ↦ ?_⟩
  have hiso : ((Subobject.mk (C.arrow ≫ B.arrow) : Subobject F) : Coh X) ≅ (C : Coh X) :=
    Subobject.underlyingIso _
  have hCne : ¬IsZero ((Subobject.mk (C.arrow ≫ B.arrow) : Subobject F) : Coh X) := by
    intro hz
    exact hC (hz.of_iso hiso.symm)
  have hle := hB.2.1 (Subobject.mk (C.arrow ≫ B.arrow)) hCne
  rwa [(P.weakSlopeData h).topSlope_eq_of_iso hiso] at hle

/-- **The maximal slope is `⊤` exactly when the sheaf is not pure.**

This is the boundary case the `WithTop` valuation exists for, and it is what tells the
filtration recursion that the first factor of a pure sheaf has finite slope. -/
theorem topSlope_maximalDestabilizing_eq_top_iff (h : MuPositivityData P) {F : Coh X}
    (hF : ¬IsZero F) {B : Subobject F} (hB : IsMaximalDestabilizing h F B) :
    (P.weakSlopeData h).topSlope (B : Coh X) = ⊤ ↔ ¬P.IsPure F := by
  constructor
  · intro htop hpure
    have hpos : 0 < P.multiplicity (B : Coh X) :=
      hpure.2 (B : Coh X) B.arrow inferInstance hB.1
    rw [weakSlopeData_topSlope_of_multiplicity_pos h hpos] at htop
    exact (WithTop.coe_ne_top) htop
  · intro hnp
    have hex : ∃ (G : Coh X) (i : G ⟶ F), Mono i ∧ ¬IsZero G ∧ P.multiplicity G = 0 := by
      by_contra hcon
      refine hnp ⟨hF, fun G i hi hG ↦ ?_⟩
      have hnn := h.multiplicity_nonneg G
      have hne : P.multiplicity G ≠ 0 := fun h0 ↦ hcon ⟨G, i, hi, hG, h0⟩
      omega
    obtain ⟨G, i, hi, hGne, hG0⟩ := hex
    haveI := hi
    have hiso : ((Subobject.mk i : Subobject F) : Coh X) ≅ G := Subobject.underlyingIso i
    have hmk0 : P.multiplicity ((Subobject.mk i : Subobject F) : Coh X) = 0 := by
      rw [P.multiplicity_eq_of_iso hiso]
      exact hG0
    have hmkne : ¬IsZero ((Subobject.mk i : Subobject F) : Coh X) := by
      intro hz
      exact hGne (hz.of_iso hiso.symm)
    have hle := hB.2.1 (Subobject.mk i) hmkne
    rw [weakSlopeData_topSlope_of_multiplicity_zero h hmk0] at hle
    exact top_le_iff.mp hle

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
