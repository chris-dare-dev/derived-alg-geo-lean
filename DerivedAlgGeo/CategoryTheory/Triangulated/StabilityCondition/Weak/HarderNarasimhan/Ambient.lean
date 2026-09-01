/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.HomVanishing
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Ambient weak Harder--Narasimhan filtrations from a bounded heart

This file extends weak HN filtrations from the heart of a bounded
t-structure to every ambient object.  The construction follows the canonical
t-cohomological filtration.  An object with amplitude `[b, a]` receives an HN
tower whose phases lie in `(-a, 1-b]`.

The key point is strict separation between adjacent cohomological degrees.  A
pure degree-`a` object has phases in `(-a, 1-a]`, while the truncation below
degree `a` has phases strictly above `1-a`.  The generic Postnikov-splicing
operation can therefore concatenate their HN towers across the truncation
triangle.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- Shift an HN filtration for an induced ambient weak phase family by an
integer.  This is the non-circular analogue of `HNFiltration.shiftHN`: it uses
the shift law already proved directly for `ambientPhasePredicate`, before a
slicing has been assembled. -/
noncomputable def HNFiltration.shiftWeakAmbient {t : TStructure C}
    {W : WeakStabilityFunction t} {E : C}
    (F : HNFiltration C W.ambientPhasePredicate E) (a : ℤ) :
    HNFiltration C W.ambientPhasePredicate (E⟦a⟧) where
  n := F.n
  chain := F.chain ⋙ shiftFunctor C a
  triangle := fun i ↦ (Triangle.shiftFunctor C a).obj (F.triangle i)
  triangle_dist := fun i ↦ Triangle.shift_distinguished _ (F.triangle_dist i) a
  triangle_obj₁ := fun i ↦
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₁ i))⟩
  triangle_obj₂ := fun i ↦
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₂ i))⟩
  base_isZero := (shiftFunctor C a).map_isZero F.base_isZero
  top_iso := ⟨(shiftFunctor C a).mapIso (Classical.choice F.top_iso)⟩
  φ := fun j ↦ F.φ j + (a : ℝ)
  hφ := by
    intro i j hij
    change F.φ j + (a : ℝ) < F.φ i + (a : ℝ)
    linarith [F.hφ hij]
  semistable := fun j ↦
    (W.ambientPhasePredicate_shift_int
      (F.φ j) (F.toPostnikovTower.factor j) a).mp (F.semistable j)

omit [IsTriangulated C] in
@[simp]
theorem HNFiltration.shiftWeakAmbient_phase {t : TStructure C}
    {W : WeakStabilityFunction t} {E : C}
    (F : HNFiltration C W.ambientPhasePredicate E) (a : ℤ)
    (j : Fin F.n) :
    (CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.shiftWeakAmbient F a).φ j =
      F.φ j + (a : ℝ) := rfl

namespace WeakStabilityFunction

variable {t : TStructure C} (W : WeakStabilityFunction t)

/-- Heart-level HN existence supplies an ambient HN tower whose phases lie in
the standard interval `(0, 1]`.  Recording the bounds together with the tower
avoids making later amplitude arguments depend on a particular choice. -/
theorem ambientHN_exists_of_mem_heart_with_phase_bounds
    (hHN : W.HasHNProperty) (E : t.heart.FullSubcategory) :
    ∃ F : HNFiltration C W.ambientPhasePredicate E.obj,
      ∀ j : Fin F.n, F.φ j ∈ Set.Ioc (0 : ℝ) 1 := by
  by_cases hE : IsZero E
  · refine ⟨HNFiltration.zero C E.obj (t.heart.ι.map_isZero hE), ?_⟩
    exact fun j ↦ Fin.elim0 j
  · let G : WeakAbelianHNFiltration W E := Classical.choice (hHN E hE)
    refine ⟨G.toAmbientNormalizedHN, fun j ↦ ?_⟩
    change weakPhaseOfSlope (G.μ j) ∈ Set.Ioc (0 : ℝ) 1
    exact weakPhaseOfSlope_mem_Ioc _

/-- A pure object concentrated in t-degree `a` has an ambient weak HN tower
with phases in `(-a, 1-a]`. -/
theorem ambientHN_exists_of_pure
    (hHN : W.HasHNProperty) {E : C} (a : ℤ)
    (hLE : t.IsLE E a) (hGE : t.IsGE E a) :
    ∃ F : HNFiltration C W.ambientPhasePredicate E,
      (∀ j : Fin F.n, -(a : ℝ) < F.φ j) ∧
      (∀ j : Fin F.n, F.φ j ≤ 1 - (a : ℝ)) := by
  let H : t.heart.FullSubcategory := ⟨E⟦a⟧, by
    rw [t.mem_heart_iff]
    exact ⟨by simpa using t.isLE_shift E a a 0 (by lia),
      by simpa using t.isGE_shift E a a 0 (by lia)⟩⟩
  obtain ⟨FH, hFH⟩ :=
    W.ambientHN_exists_of_mem_heart_with_phase_bounds hHN H
  let FS : HNFiltration C W.ambientPhasePredicate (H.obj⟦(-a : ℤ)⟧) :=
    CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.shiftWeakAmbient FH (-a)
  let e : H.obj⟦(-a : ℤ)⟧ ≅ E :=
    ((shiftFunctorAdd' C a (-a : ℤ) 0 (by lia)).app E).symm.trans
      ((shiftFunctorZero C ℤ).app E)
  let F : HNFiltration C W.ambientPhasePredicate E :=
    CategoryTheory.Triangulated.HNFiltration.ofIso C FS e
  refine ⟨F, fun j ↦ ?_, fun j ↦ ?_⟩
  · dsimp [F, FS,
      CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.shiftWeakAmbient,
      CategoryTheory.Triangulated.HNFiltration.ofIso] at j ⊢
    have hj := hFH j
    push_cast
    linarith [hj.1]
  · dsimp [F, FS,
      CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.shiftWeakAmbient,
      CategoryTheory.Triangulated.HNFiltration.ofIso] at j ⊢
    have hj := hFH j
    push_cast
    linarith [hj.2]

/-- Objects whose t-cohomology is supported in degrees `[b, b+n]` admit an
ambient weak HN tower with all phases in `(-(b+n), 1-b]`.  The phase bounds
are the induction invariant that makes successive truncation triangles
strictly spliceable. -/
theorem ambientHN_exists_of_width
    (hHN : W.HasHNProperty) (b : ℤ) :
    ∀ n : ℕ, ∀ E : C,
      t.IsLE E (b + (n : ℤ)) → t.IsGE E b →
      ∃ F : HNFiltration C W.ambientPhasePredicate E,
        (∀ j : Fin F.n, -((b : ℝ) + (n : ℝ)) < F.φ j) ∧
        (∀ j : Fin F.n, F.φ j ≤ 1 - (b : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro E hLE hGE
      simpa using W.ambientHN_exists_of_pure hHN b (by simpa using hLE) hGE
  | succ n ih =>
      intro E hLE hGE
      let a : ℤ := b + (n : ℤ) + 1
      letI : t.IsLE E a := by
        simpa [a, Nat.cast_succ, add_assoc] using hLE
      letI : t.IsGE E b := hGE
      let X : C := (t.truncLT a).obj E
      let Y : C := (t.truncGE a).obj E
      have hXLE : t.IsLE X (b + (n : ℤ)) := by
        have h : t.IsLE X (a - 1) := by dsimp [X]; infer_instance
        simpa [a] using h
      have hXGE : t.IsGE X b := by dsimp [X]; infer_instance
      have hYLE : t.IsLE Y a := by dsimp [Y]; infer_instance
      have hYGE : t.IsGE Y a := by dsimp [Y]; infer_instance
      obtain ⟨GX, hGXlo, hGXhi⟩ := ih X hXLE hXGE
      obtain ⟨GY, hGYlo, hGYhi⟩ :=
        W.ambientHN_exists_of_pure hHN a hYLE hYGE
      have ha : (a : ℝ) = (b : ℝ) + (n : ℝ) + 1 := by
        dsimp [a]
        push_cast
        ring
      have hXgt : ∀ j : Fin GX.n, -(a : ℝ) < GX.φ j := by
        intro j
        linarith [hGXlo j]
      have hYgt : ∀ j : Fin GY.n, -(a : ℝ) < GY.φ j := hGYlo
      have hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j := by
        intro i j
        linarith [hGYhi i, hGXlo j]
      have hYupper : ∀ j : Fin GY.n, GY.φ j ≤ 1 - (b : ℝ) := by
        intro j
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith [hGYhi j]
      obtain ⟨G, hGlo, hGhi⟩ :=
        CategoryTheory.Triangulated.HNFiltration.exists_of_distinguished_triangle_phase_bounds
        (C := C) (fun phi ↦ W.ambientPhasePredicate_closedUnderIso phi)
        GX GY ((t.truncLTι a).app E) ((t.truncGEπ a).app E)
        ((t.truncGEδLT a).app E) (t.triangleLTGE_distinguished a E)
        (-(a : ℝ)) (1 - (b : ℝ)) hXgt hYgt hsep hGXhi hYupper
      refine ⟨G, fun j ↦ ?_, hGhi⟩
      have hlower : -((b : ℝ) + ((n + 1 : ℕ) : ℝ)) = -(a : ℝ) := by
        rw [Nat.cast_succ, ha]
        ring
      rw [hlower]
      exact hGlo j

/-- A bounded t-structure and weak HN filtrations on its heart determine HN
filtrations for the integer-normalized ambient weak phase family on every
object. -/
theorem ambientHN_exists_of_bounded
    (hbounded : CategoryTheory.Triangulated.TStructure.IsBounded t)
    (hHN : W.HasHNProperty) (E : C) :
    Nonempty (HNFiltration C W.ambientPhasePredicate E) := by
  obtain ⟨⟨b, hGE⟩, ⟨a, hLE⟩⟩ := hbounded E
  let b' : ℤ := min b a
  have hb'a : b' ≤ a := min_le_right _ _
  letI : t.IsGE E b := hGE
  have hGE' : t.IsGE E b' :=
    t.isGE_of_ge E b' b (min_le_left _ _)
  let n : ℕ := Int.toNat (a - b')
  have hn : b' + (n : ℤ) = a := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hb'a)]
    omega
  obtain ⟨F, -, -⟩ := W.ambientHN_exists_of_width hHN b' n E
    (by simpa [hn] using hLE) hGE'
  exact ⟨F⟩

/-- Global form of `ambientHN_exists_of_bounded`. -/
theorem ambientHN_of_bounded
    (hbounded : CategoryTheory.Triangulated.TStructure.IsBounded t)
    (hHN : W.HasHNProperty) :
    ∀ E : C, Nonempty (HNFiltration C W.ambientPhasePredicate E) :=
  fun E ↦ W.ambientHN_exists_of_bounded hbounded hHN E

end WeakStabilityFunction

/-! ## Boundedness of a heart tilt -/

open CategoryTheory.Triangulated.Tilting

/-- A Happel--Reiten--Smalø tilt of a bounded t-structure is bounded.  In the
aisle convention used by `HeartTorsionPair.tilt`, an original amplitude
interval `[b, a]` becomes the tilted interval `[b, a+1]`. -/
theorem heartTorsionPair_tilt_isBounded {t : TStructure C}
    (P : HeartTorsionPair t)
    (hbounded : CategoryTheory.Triangulated.TStructure.IsBounded t) :
    CategoryTheory.Triangulated.TStructure.IsBounded P.tilt := by
  intro E
  obtain ⟨⟨b, hGE⟩, ⟨a, hLE⟩⟩ := hbounded E
  letI : t.IsLE E a := hLE
  letI : t.IsGE E b := hGE
  have hTiltLE : P.tilt.IsLE E (a + 1) := by
    refine ⟨?_⟩
    rw [P.tilt_le]
    refine ⟨t.isLE_of_le E a (a + 1) (by lia), ?_⟩
    intro F hF f
    exact t.zero_of_isLE_of_isGE f (-1) 0 (by lia)
      (t.isLE_shift E a (a + 1) (-1) (by lia))
      (P.free_isGE F hF)
  have hTiltGE : P.tilt.IsGE E b := by
    refine ⟨?_⟩
    rw [P.tilt_ge]
    refine ⟨t.isGE_of_ge E (b - 1) b (by lia), ?_⟩
    intro T hT f
    exact t.zero_of_isLE_of_isGE f 0 1 (by lia)
      (P.tors_isLE T hT)
      (t.isGE_shift E b (b - 1) 1 (by lia))
  exact ⟨⟨b, hTiltGE⟩, ⟨a + 1, hTiltLE⟩⟩

end

end CategoryTheory.Triangulated.WeakStabilityCondition
