/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.Splice

/-!
# The weak Harder–Narasimhan property for the μ-slope on `Coh X`

Every nonzero coherent sheaf has a Harder–Narasimhan filtration for the weak μ-slope. This is the
theorem the repository has carried as a hypothesis everywhere: `HasHNProperty` appears only as an
assumption in the abstract theory, and this is its first instance on a geometric category.

## The shape of the recursion, and why it is in two stages

Remove the maximal destabilizing subobject `B` from `E` and filter `E / B`; `splice` puts the
two together. What is delicate is termination, and a single induction on multiplicity does not
work: multiplicity is additive, so `multiplicity (E / B) = multiplicity E - multiplicity B`, and
when `B` has multiplicity zero — the torsion case, where `B` has slope `⊤` — nothing decreases.

The fix is that this can happen at most once. `multiplicity_pos_of_maximalDestabilizing` says the
quotient by the maximal destabilizing subobject is always pure, and for a *pure* sheaf every
nonzero subobject, `B` included, has positive multiplicity, so multiplicity does strictly
decrease at every later step. The recursion is therefore staged:

* `exists_filtration_of_pure` handles pure sheaves by induction on multiplicity;
* `exists_filtration` handles an arbitrary nonzero sheaf by splitting off the single torsion step
  first, after which the quotient is pure.

The chain condition in `MuHNInput` is what makes the maximal destabilizing subobject exist at
each step. It is *not* what makes the recursion stop; multiplicity is.

## The base case

`B = ⊤` means the sheaf is its own maximal destabilizing subobject, hence semistable, and
`AbelianWeakHNFiltration.ofSemistable` gives the one-step filtration. That is reused rather than
rebuilt.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-- A subobject whose arrow is an isomorphism is the top subobject, so a sheaf equal to its own
maximal destabilizing subobject is semistable. -/
theorem isSemistable_of_maximalDestabilizing_eq_top (h : MuPositivityData P) {F : Coh X}
    {B : Subobject F} (hB : IsMaximalDestabilizing h F B) (htop : B = ⊤) :
    (P.weakSlopeData h).toWeakStabilityFunction.IsSemistable F := by
  subst htop
  exact (P.weakSlopeData h).toWeakStabilityFunction.isSemistable_of_iso
    (asIso (⊤ : Subobject F).arrow) (maximalDestabilizing_isSemistable h hB)

/-- If the subobject is not everything, the quotient by it is nonzero. -/
theorem not_isZero_cokernel_of_ne_top {F : Coh X} {B : Subobject F} (hne : B ≠ ⊤) :
    ¬IsZero (cokernel (B : Subobject F).arrow) := by
  intro hz
  haveI : Epi (B : Subobject F).arrow := Preadditive.epi_of_isZero_cokernel _ hz
  haveI : IsIso (B : Subobject F).arrow := isIso_of_mono_of_epi _
  exact hne (Subobject.eq_top_of_isIso_arrow B)

/-- Multiplicity of the quotient by a subobject, from additivity. -/
theorem multiplicity_cokernel {F : Coh X} (B : Subobject F) :
    P.multiplicity (cokernel (B : Subobject F).arrow) =
      P.multiplicity F - P.multiplicity ((B : Subobject F) : Coh X) := by
  have hSE : (ShortComplex.mk (B : Subobject F).arrow (cokernel.π (B : Subobject F).arrow)
      (by simp)).ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hadd := multiplicity_shortExact (P := P) hSE
  change P.multiplicity F = P.multiplicity ((B : Subobject F) : Coh X) +
    P.multiplicity (cokernel (B : Subobject F).arrow) at hadd
  omega

/-- **The quotient by the maximal destabilizing subobject is pure.** -/
theorem isPure_cokernel (h : MuPositivityData P) {F : Coh X} {B : Subobject F}
    (hB : IsMaximalDestabilizing h F B) (hne : B ≠ ⊤) :
    P.IsPure (cokernel (B : Subobject F).arrow) := by
  refine ⟨not_isZero_cokernel_of_ne_top hne, fun G i hi hG ↦ ?_⟩
  haveI := hi
  have hiso : ((Subobject.mk i : Subobject (cokernel B.arrow)) : Coh X) ≅ G :=
    Subobject.underlyingIso i
  have hmkne : ¬IsZero ((Subobject.mk i : Subobject (cokernel B.arrow)) : Coh X) := by
    intro hz
    exact hG (hz.of_iso hiso.symm)
  have := multiplicity_pos_of_maximalDestabilizing h hB (Subobject.mk i) hmkne
  rwa [P.multiplicity_eq_of_iso hiso] at this

/-- **Pure sheaves have Harder–Narasimhan filtrations**, by induction on multiplicity. -/
theorem exists_filtration_of_pure (h : MuPositivityData P) (I : MuHNInput P h) :
    ∀ (n : ℕ) (F : Coh X), P.IsPure F → (P.multiplicity F).toNat ≤ n →
      Nonempty (AbelianWeakHNFiltration
        (P.weakSlopeData h).toWeakStabilityFunction F) := by
  intro n
  induction n with
  | zero =>
      intro F hF hle
      have := hF.multiplicity_pos
      omega
  | succ n ih =>
      intro F hF hle
      obtain ⟨B, hB⟩ := exists_maximalDestabilizing h I hF.not_isZero
      by_cases htop : B = ⊤
      · exact ⟨AbelianWeakHNFiltration.ofSemistable
          (isSemistable_of_maximalDestabilizing_eq_top h hB htop)⟩
      · have hQpure : P.IsPure (cokernel (B : Subobject F).arrow) := isPure_cokernel h hB htop
        have hBpos : 0 < P.multiplicity ((B : Subobject F) : Coh X) :=
          hF.2 ((B : Subobject F) : Coh X) B.arrow inferInstance hB.1
        have hQmult := multiplicity_cokernel (P := P) B
        have hQle : (P.multiplicity (cokernel (B : Subobject F).arrow)).toNat ≤ n := by
          have hFnn := h.multiplicity_nonneg F
          omega
        obtain ⟨G⟩ := ih (cokernel (B : Subobject F).arrow) hQpure hQle
        exact ⟨splice h hB G⟩

/-- **Every nonzero coherent sheaf has a Harder–Narasimhan filtration.**

A single torsion step is split off first: the quotient by the maximal destabilizing subobject is
always pure, so the pure recursion takes over from there. -/
theorem exists_filtration (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) :
    Nonempty (AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F) := by
  by_cases hpure : P.IsPure F
  · exact exists_filtration_of_pure h I _ F hpure le_rfl
  · obtain ⟨B, hB⟩ := exists_maximalDestabilizing h I hF
    by_cases htop : B = ⊤
    · exact ⟨AbelianWeakHNFiltration.ofSemistable
        (isSemistable_of_maximalDestabilizing_eq_top h hB htop)⟩
    · have hQpure : P.IsPure (cokernel (B : Subobject F).arrow) := isPure_cokernel h hB htop
      obtain ⟨G⟩ := exists_filtration_of_pure h I _ _ hQpure le_rfl
      exact ⟨splice h hB G⟩

/-- **The weak Harder–Narasimhan property for the μ-slope on `Coh X`.**

The abstract theory takes this as a hypothesis at every one of its use sites; this is its first
proof on a geometric category. -/
theorem hasHNProperty (h : MuPositivityData P) (I : MuHNInput P h) :
    (P.weakSlopeData h).toWeakStabilityFunction.HasHNProperty :=
  fun _ hF ↦ exists_filtration h I hF

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
