/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Order.Equivariance
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Isometry.Phase

/-!
# The abstract Bayer property

The geometric literature writes the Bayer property for tensoring by a line
bundle and shifting by an integer.  At the abstract slicing layer, the tensor
operation is simply a chosen autoequivalence action, while the shift is a
phase translation.  Keeping those two inputs explicit avoids importing a
scheme or pretending that `AutQuot C` is literally tensor by a line bundle.

## Quantifier order

`HasBayerProperty s q l` fixes one slicing `s`, one quotient
autoequivalence `q`, and one integer `l`, and asserts the single comparison

`s ≼ (q • s).phaseShift l`.

There is no existential quantifier over the twist or the integer.  This is the
quantifier order of arXiv:2607.28411v1, Definition 3.16; the geometric
instantiation `q = - ⊗ L` remains outside this repository.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The abstract Bayer property for a slicing, a chosen autoequivalence, and
an integer phase shift. -/
def HasBayerProperty (s : Slicing C) (q : AutQuot C) (l : ℤ) : Prop :=
  s.PrecedesWeak C ((q • s).phaseShift C (l : ℝ))

/-- Explicit name for the slicing-level abstraction. -/
abbrev SlicingBayerProperty (s : Slicing C) (q : AutQuot C) (l : ℤ) : Prop :=
  HasBayerProperty s q l

/-- Unfold the abstract Bayer property to its defining slicing comparison. -/
theorem hasBayerProperty_iff (s : Slicing C) (q : AutQuot C) (l : ℤ) :
    HasBayerProperty s q l ↔
      s.PrecedesWeak C ((q • s).phaseShift C (l : ℝ)) := Iff.rfl

/-- The identity autoequivalence with zero phase shift satisfies the Bayer
property by reflexivity of the weak slicing order. -/
theorem hasBayerProperty_one_zero (s : Slicing C) :
    HasBayerProperty s (1 : AutQuot C) 0 := by
  unfold HasBayerProperty
  have hzero : s.phaseShift C 0 = s := by
    refine Slicing.ext C ?_
    funext phi E
    change s.P (phi + 0) E = s.P phi E
    rw [add_zero]
  simpa only [Int.cast_zero, one_smul, hzero] using s.precedesWeak_refl C

/-- Bayer's property is invariant under simultaneous autoequivalence
transport, with the twist conjugated by the transporting element. -/
theorem hasBayerProperty_smul_iff (r q : AutQuot C) (s : Slicing C)
    (l : ℤ) :
    HasBayerProperty (r • s) (r * q * r⁻¹) l ↔ HasBayerProperty s q l := by
  change (r • s).PrecedesWeak C
      ((((r * q * r⁻¹) • (r • s))).phaseShift C (l : ℝ)) ↔
    s.PrecedesWeak C ((q • s).phaseShift C (l : ℝ))
  have hact : (r * q * r⁻¹) • (r • s) = r • (q • s) := by
    simp only [mul_smul, inv_smul_smul]
  rw [hact]
  have hshift : (r • (q • s)).phaseShift C (l : ℝ) =
      r • ((q • s).phaseShift C (l : ℝ)) := by
    induction r using _root_.Quotient.inductionOn with
    | _ Phi =>
      refine Slicing.ext C ?_
      funext phi E
      rfl
  rw [hshift]
  exact AutQuot.precedesWeak_smul_iff r s ((q • s).phaseShift C (l : ℝ))

universe u'

variable [IsTriangulated C]
variable {Lambda : Type u'} [AddCommGroup Lambda] {v : K₀ C →+ Lambda}

/-- The paper-facing Bayer property for a class-map stability condition and a
chosen compatible autoequivalence.  The lattice component of `q` moves the
charge; its underlying autoequivalence moves the slicing. -/
def BayerProperty (sigma : StabilityCondition.WithClassMap C v)
    (q : AutPairQuot v) (l : ℤ) : Prop :=
  CategoryTheory.Triangulated.Slicing.PrecedesWeak C sigma.slicing
    ((q • sigma).slicing.phaseShift C (l : ℝ))

/-- Express the paper-facing Bayer property through the reusable
slicing-level predicate and the forgetful homomorphism to `AutQuot`. -/
theorem bayerProperty_iff (sigma : StabilityCondition.WithClassMap C v)
    (q : AutPairQuot v) (l : ℤ) :
    BayerProperty sigma q l ↔
      HasBayerProperty sigma.slicing (AutPairQuot.toAutQuot q) l := by
  rw [BayerProperty, HasBayerProperty, AutPairQuot.smul_slicing]

/-- Upper-phase formulation of the paper-facing Bayer property.  For an
object semistable in the original slicing, its highest phase in the acted and
shifted slicing is at most its original phase. -/
theorem bayerProperty_iff_phiPlus_le
    (sigma : StabilityCondition.WithClassMap C v) (q : AutPairQuot v) (l : ℤ) :
    BayerProperty sigma q l ↔
      ∀ {E : C} {phi : ℝ} (_hE : sigma.slicing.P phi E)
        (hE0 : ¬IsZero E),
        ((q • sigma).slicing.phaseShift C (l : ℝ)).phiPlus C E hE0 ≤ phi := by
  unfold BayerProperty
  exact CategoryTheory.Triangulated.Slicing.precedesWeak_iff_phiPlus_le C
    sigma.slicing ((q • sigma).slicing.phaseShift C (l : ℝ))

/-- Lower-phase formulation of the paper-facing Bayer property.  For an
object semistable in the acted and shifted slicing, its lowest phase in the
original slicing is at least its acted phase. -/
theorem bayerProperty_iff_le_phiMinus
    (sigma : StabilityCondition.WithClassMap C v) (q : AutPairQuot v) (l : ℤ) :
    BayerProperty sigma q l ↔
      ∀ {E : C} {phi : ℝ}
        (_hE : ((q • sigma).slicing.phaseShift C (l : ℝ)).P phi E)
        (hE0 : ¬IsZero E), phi ≤ sigma.slicing.phiMinus C E hE0 := by
  unfold BayerProperty
  exact CategoryTheory.Triangulated.Slicing.precedesWeak_iff_le_phiMinus C
    sigma.slicing ((q • sigma).slicing.phaseShift C (l : ℝ))

/-- Lemma 3.17(2) at the representative level.  The inverse object map appears
explicitly because `a.Φ` is a chosen autoequivalence rather than only its
natural-isomorphism class.  The phase shift `[-l]` in the paper has been moved
to the right-hand side of the inequality. -/
theorem bayerProperty_mk_iff_inverse_phiPlus_le
    (sigma : StabilityCondition.WithClassMap C v) (a : AutPair v) (l : ℤ) :
    BayerProperty sigma (AutPairQuot.mk a) l ↔
      ∀ {E : C} {phi : ℝ} (_hE : sigma.slicing.P phi E)
        (hInv0 : ¬IsZero (a.Φ.e.inverse.obj E)),
        sigma.slicing.phiPlus C (a.Φ.e.inverse.obj E) hInv0 ≤ phi + l := by
  rw [bayerProperty_iff_phiPlus_le]
  constructor
  · intro h E phi hE hInv0
    have hE0 : ¬IsZero E := fun hZ ↦
      hInv0 (a.Φ.e.inverse.map_isZero hZ)
    have hBound := h hE hE0
    change ((CategoryTheory.Triangulated.Slicing.mapEquiv sigma.slicing a.Φ.e).phaseShift
      C (l : ℝ)).phiPlus
      C E hE0 ≤ phi at hBound
    rw [Slicing.phaseShift_phiPlus C
        (CategoryTheory.Triangulated.Slicing.mapEquiv sigma.slicing a.Φ.e)
        (l : ℝ) E hE0,
      CategoryTheory.Triangulated.mapEquiv_phiPlus a.Φ.e sigma.slicing E
        hE0 hInv0] at hBound
    exact (sub_le_iff_le_add.mp hBound)
  · intro h E phi hE hE0
    have hInv0 : ¬IsZero (a.Φ.e.inverse.obj E) := fun hZ ↦
      hE0 (IsZero.of_iso (a.Φ.e.functor.map_isZero hZ)
        (a.Φ.e.counitIso.app E).symm)
    have hBound := h hE hInv0
    change ((CategoryTheory.Triangulated.Slicing.mapEquiv sigma.slicing a.Φ.e).phaseShift
      C (l : ℝ)).phiPlus
      C E hE0 ≤ phi
    rw [Slicing.phaseShift_phiPlus C
        (CategoryTheory.Triangulated.Slicing.mapEquiv sigma.slicing a.Φ.e)
        (l : ℝ) E hE0,
      CategoryTheory.Triangulated.mapEquiv_phiPlus a.Φ.e sigma.slicing E
        hE0 hInv0]
    exact (sub_le_iff_le_add.mpr hBound)

/-- Preimage form of Lemma 3.17(3).  Semistability for the acted and shifted
slicing is rewritten as semistability of the inverse image in the original
slicing; the conclusion is the corresponding original lowest-phase bound. -/
theorem bayerProperty_mk_iff_inverse_le_phiMinus
    (sigma : StabilityCondition.WithClassMap C v) (a : AutPair v) (l : ℤ) :
    BayerProperty sigma (AutPairQuot.mk a) l ↔
      ∀ {E : C} {phi : ℝ}
        (_hE : sigma.slicing.P (phi + l) (a.Φ.e.inverse.obj E))
        (hE0 : ¬IsZero E), phi ≤ sigma.slicing.phiMinus C E hE0 := by
  rw [bayerProperty_iff_le_phiMinus]
  rfl

/-- Lemma 3.17(3) at the representative level.  For an original semistable
object, the lowest phase of its forward image is bounded below by `phi - l`.
Equivalently, shifting that image by `[l]` gives the paper's inequality
`phiMinus (a.Φ(F)[l]) ≥ phi`. -/
theorem bayerProperty_mk_iff_sub_le_functor_phiMinus
    (sigma : StabilityCondition.WithClassMap C v) (a : AutPair v) (l : ℤ) :
    BayerProperty sigma (AutPairQuot.mk a) l ↔
      ∀ {F : C} {phi : ℝ} (_hF : sigma.slicing.P phi F)
        (hMap0 : ¬IsZero (a.Φ.e.functor.obj F)),
        phi - l ≤ sigma.slicing.phiMinus C (a.Φ.e.functor.obj F) hMap0 := by
  rw [bayerProperty_iff_le_phiMinus]
  constructor
  · intro h F phi hF hMap0
    apply h (E := a.Φ.e.functor.obj F) (phi := phi - l) ?_ hMap0
    change sigma.slicing.P ((phi - (l : ℝ)) + l)
      (a.Φ.e.inverse.obj (a.Φ.e.functor.obj F))
    rw [sub_add_cancel]
    change sigma.slicing.P phi ((a.Φ.e.functor ⋙ a.Φ.e.inverse).obj F)
    exact ObjectProperty.prop_of_iso _ (a.Φ.e.unitIso.app F) hF
  · intro h E phi hE hE0
    change sigma.slicing.P (phi + l) (a.Φ.e.inverse.obj E) at hE
    have hMap0 : ¬IsZero
        (a.Φ.e.functor.obj (a.Φ.e.inverse.obj E)) := fun hZ ↦
      hE0 (IsZero.of_iso hZ (a.Φ.e.counitIso.app E).symm)
    have hBound := h hE hMap0
    have hPhase : sigma.slicing.phiMinus C
        (a.Φ.e.functor.obj (a.Φ.e.inverse.obj E)) hMap0 =
        sigma.slicing.phiMinus C E hE0 := by
      simpa using CategoryTheory.Triangulated.Slicing.phiMinus_congr
        sigma.slicing (a.Φ.e.counitIso.app E) hMap0 hE0
    rw [hPhase] at hBound
    simpa only [add_sub_cancel_right] using hBound

/-- The identity compatible autoequivalence with zero phase shift satisfies
the paper-facing Bayer property. -/
theorem bayerProperty_one_zero (sigma : StabilityCondition.WithClassMap C v) :
    BayerProperty sigma (1 : AutPairQuot v) 0 := by
  rw [bayerProperty_iff]
  simpa using hasBayerProperty_one_zero sigma.slicing

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
