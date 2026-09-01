/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.HarderNarasimhan.Heart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Weak heart--slicing equivalence: reverse-direction foundations

This file starts the reverse direction of the weak heart--slicing
correspondence.  The first reusable ingredient is the order-preserving
normalisation of the extended weak slope to a phase in `(0, 1]`:

`mu |-> arctan(mu) / pi + 1 / 2`, with `+infinity |-> 1`.

Unlike the ordinary argument, this definition assigns phase `1` to a
zero-charge semistable factor.  Its strict monotonicity is the precise bridge
which turns the strict `WithTop`-slope order in `WeakAbelianHNFiltration` into
strict phase order.

The second ingredient converts the subobject chain of a weak abelian HN
filtration into an ambient Postnikov tower.  This is independent of the
eventual analytic central-charge compatibility and is the categorical bridge
needed by the reverse construction.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-! ## Extended slopes as phases -/

/-- Normalize an extended weak slope to the standard phase interval.  The
finite branch is the inverse of `mu = -cot (pi * phi)`; the infinite branch
is the weak boundary phase `1`. -/
noncomputable def weakPhaseOfSlope : WithTop ℝ → ℝ :=
  WithTop.recTopCoe 1 (fun mu ↦ Real.arctan mu / Real.pi + 1 / 2)

@[simp]
theorem weakPhaseOfSlope_top : weakPhaseOfSlope (⊤ : WithTop ℝ) = 1 := rfl

@[simp]
theorem weakPhaseOfSlope_coe (mu : ℝ) :
    weakPhaseOfSlope (mu : WithTop ℝ) =
      Real.arctan mu / Real.pi + 1 / 2 := rfl

/-- Finite slopes have phase strictly between `0` and `1`. -/
theorem weakPhaseOfSlope_coe_mem_Ioo (mu : ℝ) :
    weakPhaseOfSlope (mu : WithTop ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [weakPhaseOfSlope_coe]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hl := (div_lt_div_iff_of_pos_right Real.pi_pos).2
    (Real.neg_pi_div_two_lt_arctan mu)
  have hu := (div_lt_div_iff_of_pos_right Real.pi_pos).2
    (Real.arctan_lt_pi_div_two mu)
  have hneg : (-(Real.pi / 2)) / Real.pi = -(1 / 2 : ℝ) := by
    field_simp
  have hpos : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by
    field_simp
  rw [hneg] at hl
  rw [hpos] at hu
  constructor <;> linarith

/-- Every extended slope has phase in `(0, 1]`. -/
theorem weakPhaseOfSlope_mem_Ioc (mu : WithTop ℝ) :
    weakPhaseOfSlope mu ∈ Set.Ioc (0 : ℝ) 1 := by
  induction mu using WithTop.recTopCoe with
  | top => simp
  | coe mu =>
      exact ⟨(weakPhaseOfSlope_coe_mem_Ioo mu).1,
        (weakPhaseOfSlope_coe_mem_Ioo mu).2.le⟩

/-- The slope-to-phase normalization is strictly increasing. -/
theorem weakPhaseOfSlope_strictMono : StrictMono weakPhaseOfSlope := by
  intro mu nu hmunu
  induction mu using WithTop.recTopCoe with
  | top => exact False.elim ((not_lt_of_ge le_top) hmunu)
  | coe mu =>
      induction nu using WithTop.recTopCoe with
      | top => exact (weakPhaseOfSlope_coe_mem_Ioo mu).2
      | coe nu =>
          rw [weakPhaseOfSlope_coe, weakPhaseOfSlope_coe]
          have hreal : mu < nu := by exact_mod_cast hmunu
          have hatan := Real.arctan_strictMono hreal
          simpa [add_comm] using
            add_lt_add_right
              ((div_lt_div_iff_of_pos_right Real.pi_pos).2 hatan) (1 / 2)

/-- Strict slope order is exactly strict normalized-phase order. -/
theorem weakPhaseOfSlope_lt_iff {mu nu : WithTop ℝ} :
    weakPhaseOfSlope mu < weakPhaseOfSlope nu ↔ mu < nu :=
  weakPhaseOfSlope_strictMono.lt_iff_lt

/-- Weak phase of a heart object, defined from its extended slope. -/
noncomputable def WeakStabilityFunction.phase {t : TStructure C}
    (W : WeakStabilityFunction t) (E : C) : ℝ :=
  weakPhaseOfSlope (W.slope E)

omit [IsTriangulated C] in
theorem WeakStabilityFunction.phase_mem_Ioc {t : TStructure C}
    (W : WeakStabilityFunction t) (E : C) :
    W.phase E ∈ Set.Ioc (0 : ℝ) 1 :=
  weakPhaseOfSlope_mem_Ioc _

omit [IsTriangulated C] in
theorem WeakStabilityFunction.phase_lt_phase_iff {t : TStructure C}
    (W : WeakStabilityFunction t) {E F : C} :
    W.phase E < W.phase F ↔ W.slope E < W.slope F :=
  weakPhaseOfSlope_lt_iff

omit [IsTriangulated C] in
theorem WeakStabilityFunction.phase_eq_of_iso {t : TStructure C}
    (W : WeakStabilityFunction t) {E F : C} (e : E ≅ F) :
    W.phase E = W.phase F := by
  unfold WeakStabilityFunction.phase
  rw [W.slope_eq_of_iso e]

/-! ## The heart phase predicate -/

/-- The phase slice determined by a weak stability function on a heart.
Zero objects belong to every slice; a nonzero member is weak-semistable and
its normalized extended slope is the requested phase. -/
def WeakStabilityFunction.heartPhasePredicate {t : TStructure C}
    (W : WeakStabilityFunction t) (phi : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ (W.IsSemistable E ∧ W.phase E = phi)

omit [IsTriangulated C] in
theorem WeakStabilityFunction.heartPhasePredicate_closedUnderIso
    {t : TStructure C} (W : WeakStabilityFunction t) (phi : ℝ) :
    (W.heartPhasePredicate phi).IsClosedUnderIsomorphisms := by
  refine ⟨?_⟩
  intro E F e hE
  rcases hE with hE | ⟨hEss, hphase⟩
  · exact Or.inl (hE.of_iso e.symm)
  · exact Or.inr ⟨W.isSemistable_of_iso e hEss, by
      rw [← hphase]
      exact (W.phase_eq_of_iso e).symm⟩

instance WeakStabilityFunction.heartPhasePredicate_instClosedUnderIso
    {t : TStructure C} (W : WeakStabilityFunction t) (phi : ℝ) :
    (W.heartPhasePredicate phi).IsClosedUnderIsomorphisms :=
  W.heartPhasePredicate_closedUnderIso phi

/-! ## Integer-normalized ambient phase predicates -/

/-- The representative of a real phase in the standard interval `(0, 1]`. -/
noncomputable def phaseBase (phi : ℝ) : ℝ :=
  toIocMod zero_lt_one (0 : ℝ) phi

/-- The integral translation carrying `phaseBase phi` back to `phi`. -/
noncomputable def phaseIndex (phi : ℝ) : ℤ :=
  toIocDiv zero_lt_one (0 : ℝ) phi

theorem phaseBase_mem (phi : ℝ) : phaseBase phi ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [phaseBase] using toIocMod_mem_Ioc zero_lt_one (0 : ℝ) phi

theorem phaseBase_add_phaseIndex (phi : ℝ) :
    phaseBase phi + phaseIndex phi = phi := by
  simpa [phaseBase, phaseIndex] using
    toIocMod_add_toIocDiv_mul zero_lt_one (0 : ℝ) phi

theorem phaseBase_add_one (phi : ℝ) : phaseBase (phi + 1) = phaseBase phi := by
  change toIocMod zero_lt_one (0 : ℝ) (phi + 1) =
    toIocMod zero_lt_one (0 : ℝ) phi
  convert toIocMod_add_intCast_mul zero_lt_one (0 : ℝ) phi 1 using 1 <;> ring

theorem phaseIndex_add_one (phi : ℝ) : phaseIndex (phi + 1) = phaseIndex phi + 1 := by
  change toIocDiv zero_lt_one (0 : ℝ) (phi + 1) =
    toIocDiv zero_lt_one (0 : ℝ) phi + 1
  convert toIocDiv_add_intCast_mul zero_lt_one (0 : ℝ) phi 1 using 1 <;> ring

theorem phaseBase_eq_of_mem_Ioc {phi : ℝ} (hphi : phi ∈ Set.Ioc (0 : ℝ) 1) :
    phaseBase phi = phi :=
  (toIocMod_eq_self zero_lt_one).2 (by simpa using hphi)

theorem phaseIndex_eq_zero_of_mem_Ioc {phi : ℝ}
    (hphi : phi ∈ Set.Ioc (0 : ℝ) 1) : phaseIndex phi = 0 :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc (hp := zero_lt_one) (a := (0 : ℝ))
    (b := phi) (n := (0 : ℤ)) (by simpa using hphi)

theorem phaseIndex_lt_phase (phi : ℝ) : (phaseIndex phi : ℝ) < phi := by
  have hbase := (phaseBase_mem phi).1
  nlinarith [phaseBase_add_phaseIndex phi]

theorem phase_le_phaseIndex_add_one (phi : ℝ) :
    phi ≤ (phaseIndex phi : ℝ) + 1 := by
  have hbase := (phaseBase_mem phi).2
  nlinarith [phaseBase_add_phaseIndex phi]

theorem phaseIndex_le_of_lt {phi₁ phi₂ : ℝ} (h : phi₂ < phi₁) :
    phaseIndex phi₂ ≤ phaseIndex phi₁ := by
  by_contra hle
  have hidx : phaseIndex phi₁ < phaseIndex phi₂ := lt_of_not_ge hle
  have hstep : (phaseIndex phi₁ : ℝ) + 1 ≤ phaseIndex phi₂ := by
    exact_mod_cast Int.add_one_le_iff.mpr hidx
  linarith [phaseIndex_lt_phase phi₂, phase_le_phaseIndex_add_one phi₁]

/-- A weak-semistable heart object of phase `psi`, shifted into cohomological
degree `n`.  The phase normalization functions `phaseBase` and `phaseIndex`
are shared with the ordinary reverse heart--slicing construction. -/
def WeakStabilityFunction.shiftedHeartPhasePredicate {t : TStructure C}
    (W : WeakStabilityFunction t) (psi : ℝ) (n : ℤ) : ObjectProperty C :=
  fun X ↦ IsZero X ∨
    (W.IsSemistable (X⟦(-n : ℤ)⟧) ∧ W.phase (X⟦(-n : ℤ)⟧) = psi)

/-- The ambient phase family induced by a weak stability function on a
heart: normalize into `(0, 1]`, then shift by the integral phase index. -/
def WeakStabilityFunction.ambientPhasePredicate {t : TStructure C}
    (W : WeakStabilityFunction t) (phi : ℝ) : ObjectProperty C :=
  W.shiftedHeartPhasePredicate (phaseBase phi) (phaseIndex phi)

omit [IsTriangulated C] in
theorem WeakStabilityFunction.shiftedHeartPhasePredicate_zero_iff
    {t : TStructure C} (W : WeakStabilityFunction t) (psi : ℝ) (X : C) :
    W.shiftedHeartPhasePredicate psi 0 X ↔ W.heartPhasePredicate psi X := by
  let e0 : X⟦(0 : ℤ)⟧ ≅ X := (shiftFunctorZero C ℤ).app X
  constructor
  · intro hX
    rcases hX with hX | ⟨hXss, hXphase⟩
    · exact Or.inl hX
    · exact Or.inr ⟨W.isSemistable_of_iso e0 hXss, by
        rw [← hXphase]
        exact (W.phase_eq_of_iso e0).symm⟩
  · intro hX
    rcases hX with hX | ⟨hXss, hXphase⟩
    · exact Or.inl hX
    · exact Or.inr ⟨W.isSemistable_of_iso e0.symm hXss, by
        rw [← hXphase]
        exact (W.phase_eq_of_iso e0.symm).symm⟩

omit [IsTriangulated C] in
/-- On the standard phase interval, the ambient predicate is exactly the
heart weak-semistability predicate. -/
theorem WeakStabilityFunction.ambientPhasePredicate_iff_of_mem_Ioc
    {t : TStructure C} (W : WeakStabilityFunction t) {phi : ℝ}
    (hphi : phi ∈ Set.Ioc (0 : ℝ) 1) (X : C) :
    W.ambientPhasePredicate phi X ↔ W.heartPhasePredicate phi X := by
  simpa [WeakStabilityFunction.ambientPhasePredicate,
    phaseBase_eq_of_mem_Ioc hphi, phaseIndex_eq_zero_of_mem_Ioc hphi] using
    W.shiftedHeartPhasePredicate_zero_iff phi X

omit [IsTriangulated C] in
theorem WeakStabilityFunction.shiftedHeartPhasePredicate_closedUnderIso
    {t : TStructure C} (W : WeakStabilityFunction t) (psi : ℝ) (n : ℤ) :
    (W.shiftedHeartPhasePredicate psi n).IsClosedUnderIsomorphisms := by
  refine ⟨?_⟩
  intro X Y e hX
  rcases hX with hX | ⟨hXss, hXphase⟩
  · exact Or.inl (hX.of_iso e.symm)
  · let eShift : X⟦(-n : ℤ)⟧ ≅ Y⟦(-n : ℤ)⟧ :=
      (shiftFunctor C (-n : ℤ)).mapIso e
    exact Or.inr ⟨W.isSemistable_of_iso eShift hXss, by
      rw [← hXphase]
      exact (W.phase_eq_of_iso eShift).symm⟩

omit [IsTriangulated C] in
theorem WeakStabilityFunction.ambientPhasePredicate_closedUnderIso
    {t : TStructure C} (W : WeakStabilityFunction t) (phi : ℝ) :
    (W.ambientPhasePredicate phi).IsClosedUnderIsomorphisms :=
  W.shiftedHeartPhasePredicate_closedUnderIso (phaseBase phi) (phaseIndex phi)

instance WeakStabilityFunction.ambientPhasePredicate_instClosedUnderIso
    {t : TStructure C} (W : WeakStabilityFunction t) (phi : ℝ) :
    (W.ambientPhasePredicate phi).IsClosedUnderIsomorphisms :=
  W.ambientPhasePredicate_closedUnderIso phi

omit [IsTriangulated C] in
theorem WeakStabilityFunction.shiftedHeartPhasePredicate_shift_iff
    {t : TStructure C} (W : WeakStabilityFunction t)
    (psi : ℝ) (n : ℤ) (X : C) :
    W.shiftedHeartPhasePredicate psi n X ↔
      W.shiftedHeartPhasePredicate psi (n + 1) (X⟦(1 : ℤ)⟧) := by
  let eShift :
      (X⟦(1 : ℤ)⟧)⟦(-(n + 1) : ℤ)⟧ ≅ X⟦(-n : ℤ)⟧ :=
    ((shiftFunctorAdd' C (1 : ℤ) (-(n + 1) : ℤ) (-n : ℤ) (by lia)).app X).symm
  constructor
  · intro hX
    rcases hX with hX | ⟨hXss, hXphase⟩
    · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hX)
    · exact Or.inr ⟨W.isSemistable_of_iso eShift.symm hXss, by
        rw [← hXphase]
        exact (W.phase_eq_of_iso eShift.symm).symm⟩
  · intro hX
    rcases hX with hX | ⟨hXss, hXphase⟩
    · exact Or.inl <|
        (((shiftFunctor C (-1 : ℤ)).map_isZero hX).of_iso
          (shiftShiftNeg (X := X) (i := (1 : ℤ))).symm)
    · exact Or.inr ⟨W.isSemistable_of_iso eShift hXss, by
        rw [← hXphase]
        exact (W.phase_eq_of_iso eShift).symm⟩

omit [IsTriangulated C] in
/-- Shifting by `[1]` raises the normalized ambient weak phase by `1`. -/
theorem WeakStabilityFunction.ambientPhasePredicate_shift_iff
    {t : TStructure C} (W : WeakStabilityFunction t) (phi : ℝ) (X : C) :
    W.ambientPhasePredicate phi X ↔
      W.ambientPhasePredicate (phi + 1) (X⟦(1 : ℤ)⟧) := by
  simpa [WeakStabilityFunction.ambientPhasePredicate,
    phaseBase_add_one phi, phaseIndex_add_one phi] using
    W.shiftedHeartPhasePredicate_shift_iff
      (phaseBase phi) (phaseIndex phi) X

omit [IsTriangulated C] in
/-- Shifting by an arbitrary integer translates the induced ambient weak
phase by that integer.  This is the iteration form needed to move HN towers
of pure t-cohomology objects to and from the heart. -/
theorem WeakStabilityFunction.ambientPhasePredicate_shift_int
    {t : TStructure C} (W : WeakStabilityFunction t)
    (phi : ℝ) (X : C) (n : ℤ) :
    W.ambientPhasePredicate phi X ↔
      W.ambientPhasePredicate (phi + (n : ℝ)) (X⟦n⟧) := by
  induction n using Int.induction_on generalizing phi X with
  | zero =>
      constructor
      · intro hX
        have hX' : W.ambientPhasePredicate phi (X⟦(0 : ℤ)⟧) :=
          (W.ambientPhasePredicate phi).prop_of_iso
            ((shiftFunctorZero C ℤ).app X).symm hX
        simpa using hX'
      · intro hX
        have hX' : W.ambientPhasePredicate phi (X⟦(0 : ℤ)⟧) := by
          simpa using hX
        exact (W.ambientPhasePredicate phi).prop_of_iso
          ((shiftFunctorZero C ℤ).app X) hX'
  | succ n ih =>
      constructor
      · intro hX
        let Y : C := X⟦(n : ℤ)⟧
        have h0 : W.ambientPhasePredicate (phi + (n : ℝ)) Y := by
          simpa [Y] using ((ih phi X).mp hX)
        have h1 : W.ambientPhasePredicate (phi + (n : ℝ) + 1) (Y⟦(1 : ℤ)⟧) :=
          (W.ambientPhasePredicate_shift_iff (phi + (n : ℝ)) Y).mp h0
        simpa [Y, Nat.cast_succ, add_assoc] using
          (W.ambientPhasePredicate (phi + (n : ℝ) + 1)).prop_of_iso
            ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by lia)).app X).symm h1
      · intro hX
        let Y : C := X⟦(n : ℤ)⟧
        have h1 : W.ambientPhasePredicate (phi + (n : ℝ) + 1) (Y⟦(1 : ℤ)⟧) := by
          simpa [Y, Nat.cast_succ, add_assoc] using
            (W.ambientPhasePredicate (phi + ((n + 1 : ℕ) : ℝ))).prop_of_iso
              ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by lia)).app X) hX
        have h0 : W.ambientPhasePredicate (phi + (n : ℝ)) Y :=
          (W.ambientPhasePredicate_shift_iff (phi + (n : ℝ)) Y).mpr h1
        exact (ih phi X).mpr (by simpa [Y] using h0)
  | pred n ih =>
      constructor
      · intro hX
        let Y : C := X⟦(-(n : ℤ))⟧
        have h0 : W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ)) Y := by
          simpa [Y] using ((ih phi X).mp hX)
        have h0' :
            W.ambientPhasePredicate ((phi + (-(n : ℤ) : ℝ) - 1) + 1)
              ((Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) := by
          simpa [Y, sub_eq_add_neg, add_assoc] using
            (W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ))).prop_of_iso
              (shiftNegShift (X := Y) (i := (1 : ℤ))).symm h0
        have h1 : W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ) - 1)
            (Y⟦(-1 : ℤ)⟧) :=
          (W.ambientPhasePredicate_shift_iff
            (phi + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧)).mpr h0'
        have h2 : W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ) - 1)
            ((shiftFunctor C (Int.negSucc n)).obj X) :=
          (W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ) - 1)).prop_of_iso
            ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ)
              (Int.negSucc n) (by lia)).app X).symm h1
        simpa [Y, Int.negSucc_eq, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc] using h2
      · intro hX
        let Y : C := X⟦(-(n : ℤ))⟧
        have hX' : W.ambientPhasePredicate (phi + (Int.negSucc n : ℝ))
            ((shiftFunctor C (Int.negSucc n)).obj X) := by
          simpa [Int.negSucc_eq, sub_eq_add_neg, add_comm,
            add_left_comm, add_assoc] using hX
        have h1 : W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ) - 1)
            (Y⟦(-1 : ℤ)⟧) := by
          have h2 : W.ambientPhasePredicate (phi + (Int.negSucc n : ℝ))
              ((shiftFunctor C (-1 : ℤ)).obj Y) :=
            (W.ambientPhasePredicate (phi + (Int.negSucc n : ℝ))).prop_of_iso
              ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ)
                (Int.negSucc n) (by lia)).app X) hX'
          simpa [Y, Int.negSucc_eq, sub_eq_add_neg, add_comm,
            add_left_comm, add_assoc] using h2
        have h0' :
            W.ambientPhasePredicate ((phi + (-(n : ℤ) : ℝ) - 1) + 1)
              ((Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) :=
          (W.ambientPhasePredicate_shift_iff
            (phi + (-(n : ℤ) : ℝ) - 1) (Y⟦(-1 : ℤ)⟧)).mp h1
        have h0 : W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ)) Y := by
          have h0'' : W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ))
              ((shiftFunctor C (1 : ℤ)).obj ((shiftFunctor C (-1 : ℤ)).obj Y)) := by
            simpa [sub_eq_add_neg, add_assoc] using h0'
          exact (W.ambientPhasePredicate (phi + (-(n : ℤ) : ℝ))).prop_of_iso
            (shiftNegShift (X := Y) (i := (1 : ℤ))) h0''
        exact (ih phi X).mpr (by simpa [Y] using h0)

/-! ## Abelian HN chains as ambient Postnikov towers -/

section HeartHNToAmbient

variable {t : TStructure C}

/-- The abelian structure on the full heart used to form successive
cokernels in a weak HN chain. -/
@[nolint defsWithUnderscore]
local instance : Abelian t.heart.FullSubcategory :=
  t.heartFullSubcategoryAbelian

/-- The inclusion between consecutive terms of a weak abelian HN chain. -/
noncomputable def WeakAbelianHNFiltration.factorInclusion
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) (j : Fin F.n) :
    (F.chain j.castSucc : t.heart.FullSubcategory) ⟶
      (F.chain j.succ : t.heart.FullSubcategory) :=
  Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
    (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))

instance WeakAbelianHNFiltration.factorInclusion_mono
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) (j : Fin F.n) :
    Mono (F.factorInclusion j) := by
  dsimp [WeakAbelianHNFiltration.factorInclusion]
  infer_instance

/-- The distinguished triangle attached to one consecutive quotient in a
weak abelian HN chain. -/
noncomputable def WeakAbelianHNFiltration.factorTriangle
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) (j : Fin F.n) : Triangle C := by
  let i := F.factorInclusion j
  let q := cokernel.π i
  let S : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk i q (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S] using ShortComplex.exact_cokernel i)
    (by dsimp [S, i]; infer_instance)
    (by dsimp [S, q]; infer_instance)
  let d := Classical.choose <|
    TStructure.heartFullSubcategory_shortExact_triangle (C := C) t
      S.f S.g S.zero (fun {A} a ha ↦
        ⟨hS.fIsKernel.lift (KernelFork.ofι a ha),
          hS.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)
  exact Triangle.mk i.hom q.hom d

theorem WeakAbelianHNFiltration.factorTriangle_distinguished
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) (j : Fin F.n) :
    F.factorTriangle j ∈ distTriang C := by
  let i := F.factorInclusion j
  let q := cokernel.π i
  let S : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk i q (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S] using ShortComplex.exact_cokernel i)
    (by dsimp [S, i]; infer_instance)
    (by dsimp [S, q]; infer_instance)
  exact Classical.choose_spec <|
    TStructure.heartFullSubcategory_shortExact_triangle (C := C) t
      S.f S.g S.zero (fun {A} a ha ↦
        ⟨hS.fIsKernel.lift (KernelFork.ofι a ha),
          hS.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)

/-- A weak abelian HN filtration gives an ambient HN filtration for the
heart phase predicate.  Its factors and phases are definitionally the
successive cokernels and normalized stored slopes. -/
noncomputable def WeakAbelianHNFiltration.toAmbientHN
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) :
    HNFiltration C W.heartPhasePredicate E.obj where
  n := F.n
  chain := ComposableArrows.mkOfObjOfMapSucc
    (fun i : Fin (F.n + 1) ↦ (F.chain i : t.heart.FullSubcategory).obj)
    (fun j : Fin F.n ↦ (F.factorInclusion j).hom)
  triangle := F.factorTriangle
  triangle_dist := F.factorTriangle_distinguished
  triangle_obj₁ := fun j ↦ ⟨Iso.refl _⟩
  triangle_obj₂ := fun j ↦ ⟨Iso.refl _⟩
  base_isZero := by
    change IsZero (F.chain ⟨0, by lia⟩ : t.heart.FullSubcategory).obj
    exact t.heart.ι.map_isZero <|
      (StabilityFunction.subobject_isZero_iff_eq_bot _).2 F.chain_bot
  top_iso := by
    let L := F.chain ⟨F.n, by lia⟩
    have hL : L = ⊤ := F.chain_top
    haveI : IsIso L.arrow :=
      (Subobject.isIso_arrow_iff_eq_top L).2 hL
    exact ⟨t.heart.ι.mapIso (asIso L.arrow)⟩
  φ := fun j ↦ weakPhaseOfSlope (F.μ j)
  hφ := by
    intro i j hij
    rw [weakPhaseOfSlope_lt_iff]
    exact F.μ_anti hij
  semistable := by
    intro j
    right
    constructor
    · change W.IsSemistable (F.factor j).obj
      exact F.factor_semistable j
    · unfold WeakStabilityFunction.phase
      change weakPhaseOfSlope (W.slope (F.factor j).obj) =
        weakPhaseOfSlope (F.μ j)
      exact congrArg weakPhaseOfSlope (F.factor_slope j)

/-- Relabel the semistable factors of an HN filtration without changing its
underlying Postnikov tower or phase function. -/
noncomputable def HNFiltration.relabelPhasePredicate
    {P Q : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hsemistable : ∀ j, Q (F.φ j) (F.toPostnikovTower.factor j)) :
    HNFiltration C Q E where
  toPostnikovTower := F.toPostnikovTower
  φ := F.φ
  hφ := F.hφ
  semistable := hsemistable

/-- A weak abelian HN filtration of a heart object is already an ambient HN
filtration for the integer-normalized weak phase family. -/
noncomputable def WeakAbelianHNFiltration.toAmbientNormalizedHN
    {W : WeakStabilityFunction t} {E : t.heart.FullSubcategory}
    (F : WeakAbelianHNFiltration W E) :
    HNFiltration C W.ambientPhasePredicate E.obj :=
  CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.relabelPhasePredicate
    F.toAmbientHN fun j ↦
    (W.ambientPhasePredicate_iff_of_mem_Ioc
      (weakPhaseOfSlope_mem_Ioc (F.μ j)) _).2 ((F.toAmbientHN).semistable j)

/-- Heart-level weak HN existence supplies ambient HN towers for every
object of that heart.  Zero heart objects use the empty tower. -/
noncomputable def WeakStabilityFunction.ambientHNOfHeart
    (W : WeakStabilityFunction t) (hHN : W.HasHNProperty)
    (E : t.heart.FullSubcategory) :
    HNFiltration C W.ambientPhasePredicate E.obj := by
  by_cases hE : IsZero E
  · exact HNFiltration.zero C E.obj (t.heart.ι.map_isZero hE)
  · exact (Classical.choice (hHN E hE)).toAmbientNormalizedHN

theorem WeakStabilityFunction.ambientHN_exists_of_mem_heart
    (W : WeakStabilityFunction t) (hHN : W.HasHNProperty)
    (E : C) (hE : t.heart E) :
    Nonempty (HNFiltration C W.ambientPhasePredicate E) :=
  ⟨W.ambientHNOfHeart hHN ⟨E, hE⟩⟩

end HeartHNToAmbient

/-! ## Packaging the reverse construction -/

/-- The two genuinely ambient obligations left after constructing weak phase
slices from heart data.  Heart-level HN gives the required towers on the
heart by `ambientHN_exists_of_mem_heart`; this package asks only for their
extension to all shifts and finite cohomological extensions, together with
Hom vanishing. -/
structure WeakStabilityFunction.ReverseSlicingObligations
    {t : TStructure C} (W : WeakStabilityFunction t) : Prop where
  /-- Morphisms from a higher weak phase to a lower one vanish. -/
  hom_vanishing : ∀ (phi₁ phi₂ : ℝ) (A B : C),
    phi₂ < phi₁ → W.ambientPhasePredicate phi₁ A →
      W.ambientPhasePredicate phi₂ B → ∀ f : A ⟶ B, f = 0
  /-- Every ambient object admits an HN filtration for the induced phases. -/
  hn_exists : ∀ E : C,
    Nonempty (HNFiltration C W.ambientPhasePredicate E)

/-- Construct the ambient slicing determined by a heart weak stability
function once its two ambient reverse obligations have been discharged. -/
noncomputable def WeakStabilityFunction.ReverseSlicingObligations.toSlicing
    {t : TStructure C} {W : WeakStabilityFunction t}
    (O : W.ReverseSlicingObligations) : Slicing C where
  P := W.ambientPhasePredicate
  closedUnderIso := W.ambientPhasePredicate_closedUnderIso
  zero_mem := fun _ ↦ Or.inl (isZero_zero C)
  shift_iff := W.ambientPhasePredicate_shift_iff
  hom_vanishing := O.hom_vanishing
  hn_exists := O.hn_exists

omit [IsTriangulated C] in
@[simp]
theorem WeakStabilityFunction.ReverseSlicingObligations.toSlicing_P
    {t : TStructure C} {W : WeakStabilityFunction t}
    (O : W.ReverseSlicingObligations) :
    O.toSlicing.P = W.ambientPhasePredicate := rfl

variable {Λ : Type*} [AddCommGroup Λ]

/-- Package the reverse slicing as a weak prestability condition.  The
remaining `compat` premise is deliberately stated in Definition 14.1's ray
language; the slope--phase analytic bridge discharges it independently of
the categorical HN assembly. -/
noncomputable def WeakStabilityFunction.ReverseSlicingObligations.toWeakPreStabilityCondition
    {t : TStructure C} {W : WeakStabilityFunction t}
    {v : K₀ C →+ Λ} (O : W.ReverseSlicingObligations) (Z : Λ →+ ℂ)
    (compat : ∀ (phi : ℝ) (E : C), W.ambientPhasePredicate phi E →
      ¬IsZero E → ∃ m : ℝ, 0 ≤ m ∧
        ((∀ n : ℤ, phi ≠ (n : ℝ)) → 0 < m) ∧
        Z (v (K₀.of C E)) =
          (m : ℂ) * Complex.exp ((Real.pi * phi : ℂ) * Complex.I)) :
    WeakPreStabilityCondition v where
  slicing := O.toSlicing
  Z := Z
  compat' := by
    simpa [WeakStabilityFunction.ReverseSlicingObligations.toSlicing] using compat

omit [IsTriangulated C] in
@[simp]
theorem WeakStabilityFunction.ReverseSlicingObligations.toWeakPreStabilityCondition_slicing
    {t : TStructure C} {W : WeakStabilityFunction t}
    {v : K₀ C →+ Λ} (O : W.ReverseSlicingObligations) (Z : Λ →+ ℂ)
    (compat : ∀ (phi : ℝ) (E : C), W.ambientPhasePredicate phi E →
      ¬IsZero E → ∃ m : ℝ, 0 ≤ m ∧
        ((∀ n : ℤ, phi ≠ (n : ℝ)) → 0 < m) ∧
        Z (v (K₀.of C E)) =
          (m : ℂ) * Complex.exp ((Real.pi * phi : ℂ) * Complex.I)) :
    (O.toWeakPreStabilityCondition Z compat).slicing = O.toSlicing := rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition
