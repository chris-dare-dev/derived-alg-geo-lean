/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.IntervalHeart
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.BoundaryTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.ImageFactorisation

/-!
# Two-heart embeddings of owner interval categories

Every phase interval of width at most one embeds fully faithfully into two
adjacent abelian slicing hearts.  The left heart controls kernels and images;
the right half-open heart controls cokernels and coimages.  This is the owner
foundation for the quasi-abelian interval machinery used by target transport.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

open CategoryTheory.Triangulated.TStructure
open CategoryTheory.Triangulated.TStructure

/-- Owner interval objects lie in the left adjacent slicing heart
`P((a,a+1])`. -/
theorem Slicing.intervalProp_implies_leftHeart (s : Slicing C)
    {a b : ℝ} (hab : b - a ≤ 1) {E : C}
    (hE : s.intervalProp C a b E) :
    ((s.phaseShift C a).toTStructure C).heart E := by
  apply s.mem_phaseShiftHeart_of_intervalProp C hE
  linarith

/-- The dual half-open t-structure associated to an owner slicing.  Its
heart is `P([0,1))`. -/
def Slicing.toDualTStructure (s : Slicing C) :
    CategoryTheory.Triangulated.TStructure C where
  le n := s.geProp C (-n)
  ge n := s.ltProp C (1 - n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (-n' : ℝ) = -n + a := by linarith
    rw [phase]
    exact s.geProp_shift C _ X a hX
  ge_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (1 - n' : ℝ) = (1 - n) + a := by linarith
    rw [phase]
    exact s.ltProp_shift C _ X a hX
  zero' {X Y} f hX hY := by
    exact s.zero_of_geProp_ltProp C (by simpa using hX) (by simpa using hY) f
  le_zero_le := by
    simpa using s.geProp_anti C (show (-1 : ℝ) ≤ 0 by norm_num)
  ge_one_le := by
    simpa using s.ltProp_mono C (show (0 : ℝ) ≤ 1 by norm_num)
  exists_triangle_zero_one A := by
    obtain ⟨F⟩ := s.hn_exists A
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
      s.exists_dual_phase_truncation C A F
    exact ⟨X, Y, by simpa using hX, by simpa using hY, f, g, h, hT⟩

@[simp]
theorem Slicing.toDualTStructure_heart_iff (s : Slicing C) (E : C) :
    (s.toDualTStructure C).heart E ↔
      s.geProp C 0 E ∧ s.ltProp C 1 E := by
  change (s.toDualTStructure C).le 0 E ∧
      (s.toDualTStructure C).ge 0 E ↔ _
  simp only [Slicing.toDualTStructure, Int.cast_zero, neg_zero, sub_zero]

/-- Owner interval objects lie in the right adjacent half-open slicing heart
`P([b-1,b))`. -/
theorem Slicing.intervalProp_implies_rightHeart (s : Slicing C)
    {a b : ℝ} (hab : b - a ≤ 1) {E : C}
    (hE : s.intervalProp C a b E) :
    ((s.phaseShift C (b - 1)).toDualTStructure C).heart E := by
  rw [(s.phaseShift C (b - 1)).toDualTStructure_heart_iff C]
  constructor
  · rw [s.phaseShift_geProp_zero C]
    exact s.geProp_anti C (by linarith) E
      (s.geProp_of_gtProp C E (s.gtProp_of_intervalProp C hE))
  · rw [s.phaseShift_ltProp C]
    have heq : 1 + (b - 1) = b := by linarith
    rw [heq]
    exact s.ltProp_of_intervalProp C hE

/-- Fully faithful inclusion of an owner interval category into its left
adjacent heart. -/
abbrev Slicing.IntervalCat.toLeftHeart (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤
      ((s.phaseShift C a).toTStructure C).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_leftHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toLeftHeart_full (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_surjective {_ _} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toLeftHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

/-- Fully faithful inclusion of an owner interval category into its right
adjacent half-open heart. -/
abbrev Slicing.IntervalCat.toRightHeart (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤
      ((s.phaseShift C (b - 1)).toDualTStructure C).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_rightHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toRightHeart_full (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_surjective {_ _} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toRightHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

omit [IsTriangulated C] in
/-- A non-strict lower phase bound propagates through the third vertex of a
distinguished triangle. -/
theorem Slicing.phiMinus_gt_of_triangle_with_geProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE : ∀ hE : ¬IsZero E, a < s.phiMinus C E hE)
    {c : ℝ} (hK : s.geProp C c K) (hca : a < c + 1)
    {f : K ⟶ E} {g : E ⟶ Q} {h : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  let T := Triangle.mk f g h
  have hElower : s.gtProp C a E := by
    by_cases hEzero : IsZero E
    · exact Or.inl hEzero
    · exact s.gtProp_of_phiMinus_gt C hEzero (hE hEzero)
  have hKshift : s.geProp C (c + ((1 : ℤ) : ℝ)) (K⟦(1 : ℤ)⟧) :=
    s.geProp_shift C c K 1 hK
  have hKlower : s.gtProp C a (K⟦(1 : ℤ)⟧) := by
    rcases hKshift with hzero | ⟨F, hF, hge⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨F, hF, by push_cast at hge; linarith⟩
  have hQlower : s.gtProp C a Q := by
    simpa [T] using s.gtProp_of_triangle C a hElower hKlower
      (rot_of_distTriang T hT)
  exact s.phiMinus_gt_of_gtProp C hQ hQlower

omit [IsTriangulated C] in
/-- The third vertex stays in a thin owner interval when right-heart bounds
are available on the first and third vertices. -/
theorem Slicing.third_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab : a < b) {K E Q : C}
    (hE : s.intervalProp C a b E) (hK : s.geProp C (b - 1) K)
    (hQ : s.ltProp C b Q)
    {f : K ⟶ E} {g : E ⟶ Q} {h : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b Q := by
  by_cases hQzero : IsZero Q
  · exact Or.inl hQzero
  exact s.intervalProp_of_intrinsic_phases C hQzero
    (s.phiMinus_gt_of_triangle_with_geProp C hQzero
      (fun hEne => s.phiMinus_gt_of_intervalProp C hEne hE)
      hK (by linarith) hT)
    (s.phiPlus_lt_of_ltProp C hQzero hQ)

/-- A monomorphism in the left adjacent heart with interval target has an
interval source. -/
theorem Slicing.intervalProp_of_mono_leftHeart (s : Slicing C)
    {a b : ℝ} (hab : a < b)
    {X Y : ((s.phaseShift C a).toTStructure C).heart.FullSubcategory}
    (hY : s.intervalProp C a b Y.obj) (f : X ⟶ Y) [Mono f] :
    s.intervalProp C a b X.obj := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  obtain ⟨Q, q, δ, hT⟩ := exists_distinguished_triangle_of_heart_mono t f
  have hXgt : s.gtProp C a X.obj :=
    (s.phaseShift_gtProp_zero C a X.obj).mp
      (((s.phaseShift C a).toTStructure_heart_iff C X.obj).mp X.property).1
  have hQle : s.leProp C (a + 1) Q.obj := by
    simpa [add_comm] using
      (s.phaseShift_leProp C a 1 Q.obj).mp
        (((s.phaseShift C a).toTStructure_heart_iff C Q.obj).mp Q.property).2
  exact s.first_intervalProp_of_triangle C hab hY hQle hXgt hT

/-- An epimorphism in the right adjacent heart with interval source has an
interval target. -/
theorem Slicing.intervalProp_of_epi_rightHeart (s : Slicing C)
    {a b : ℝ} (hab : a < b)
    {X Y : ((s.phaseShift C (b - 1)).toDualTStructure C).heart.FullSubcategory}
    (hX : s.intervalProp C a b X.obj) (f : X ⟶ Y) [Epi f] :
    s.intervalProp C a b Y.obj := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  obtain ⟨K, i, δ, hT⟩ :=
    exists_distinguished_triangle_of_heart_epi t f
  have hKge : s.geProp C (b - 1) K.obj :=
    (s.phaseShift_geProp_zero C (b - 1) K.obj).mp
      (((s.phaseShift C (b - 1)).toDualTStructure_heart_iff C K.obj).mp K.property).1
  have hYlt : s.ltProp C b Y.obj := by
    have h := (s.phaseShift_ltProp C (b - 1) 1 Y.obj).mp
      (((s.phaseShift C (b - 1)).toDualTStructure_heart_iff C Y.obj).mp Y.property).2
    have heq : 1 + (b - 1) = b := by linarith
    rwa [heq] at h
  exact s.third_intervalProp_of_triangle C hab hX hKge hYlt hT

end CategoryTheory.Triangulated
