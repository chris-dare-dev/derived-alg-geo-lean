/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Presentation
import DerivedAlgGeo.CategoryTheory.Triangulated.PostnikovTower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The Grothendieck group of a pretriangulated category

The owner-controlled `K₀ C` is the free abelian group on objects of `C`,
quotiented by the relations `[B] = [A] + [D]` for distinguished triangles
`A ⟶ B ⟶ D ⟶ A⟦1⟧`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped BigOperators ZeroObject

universe u v u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The Grothendieck presentation associated to distinguished triangles. -/
abbrev triangulatedPresentation :
    GrothendieckPresentation C {T : Pretriangulated.Triangle C // T ∈ distTriang C} where
  left := fun r => r.1.obj₁
  middle := fun r => r.1.obj₂
  right := fun r => r.1.obj₃

/-- The Grothendieck group of a pretriangulated category. -/
abbrev K₀ : Type _ := (triangulatedPresentation C).Group

/-- The class of an object in the Grothendieck group. -/
def K₀.of (X : C) : K₀ C :=
  (triangulatedPresentation C).of X

/-- A distinguished triangle gives the relation `[B] = [A] + [D]`. -/
theorem K₀.of_triangle (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) :
    K₀.of C T.obj₂ = K₀.of C T.obj₁ + K₀.of C T.obj₃ :=
  (triangulatedPresentation C).of_relation ⟨T, hT⟩

/-- The class of the chosen zero object vanishes. -/
@[simp]
theorem K₀.of_zero : K₀.of C (0 : C) = 0 := by
  have h := K₀.of_triangle C (Pretriangulated.contractibleTriangle (0 : C))
    (Pretriangulated.contractible_distinguished (0 : C))
  exact (add_left_cancel
    (show K₀.of C (0 : C) + 0 = K₀.of C (0 : C) + K₀.of C (0 : C) by
      simpa [Pretriangulated.contractibleTriangle] using h)).symm

/-- Isomorphic objects have equal Grothendieck classes. -/
theorem K₀.of_iso {X Y : C} (e : X ≅ Y) : K₀.of C X = K₀.of C Y := by
  have hdist := Pretriangulated.isomorphic_distinguished _
    (Pretriangulated.contractible_distinguished X)
    (Pretriangulated.Triangle.mk e.hom (0 : Y ⟶ (0 : C)) 0)
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk e.hom (0 : Y ⟶ (0 : C)) 0)
      (Pretriangulated.contractibleTriangle X)
      (Iso.refl _) e.symm (Iso.refl _)
      (by
        change e.hom ≫ e.inv = (Iso.refl X).hom ≫ 𝟙 X
        rw [e.hom_inv_id]
        simp only [Iso.refl_hom, Category.id_comp])
      (by simp [Pretriangulated.contractibleTriangle, Pretriangulated.Triangle.mk])
      (by simp [Pretriangulated.contractibleTriangle, Pretriangulated.Triangle.mk]))
  have h := K₀.of_triangle C _ hdist
  simp only [Pretriangulated.Triangle.mk] at h
  rw [K₀.of_zero, add_zero] at h
  exact h.symm

/-- Every zero object has zero Grothendieck class. -/
@[simp]
theorem K₀.of_isZero {X : C} (hX : IsZero X) : K₀.of C X = 0 := by
  rw [K₀.of_iso C (hX.iso (isZero_zero C)), K₀.of_zero]

/-- Shifting by one negates the Grothendieck class. -/
@[simp]
theorem K₀.of_shift_one (X : C) : K₀.of C (X⟦(1 : ℤ)⟧) = -K₀.of C X := by
  have h := K₀.of_triangle C (Pretriangulated.contractibleTriangle X).rotate
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.contractible_distinguished X))
  have hzero : K₀.of C (Pretriangulated.contractibleTriangle X).rotate.obj₂ = 0 :=
    K₀.of_isZero C (isZero_zero C)
  rw [hzero] at h
  change 0 = K₀.of C X + K₀.of C (X⟦(1 : ℤ)⟧) at h
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h.symm)

/-- Shifting by minus one negates the Grothendieck class. -/
@[simp]
theorem K₀.of_shift_neg_one (X : C) : K₀.of C (X⟦(-1 : ℤ)⟧) = -K₀.of C X := by
  have hshift := K₀.of_shift_one C (X⟦(-1 : ℤ)⟧)
  have hiso := K₀.of_iso C ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app X)
  simp only [Functor.comp_obj] at hiso
  rw [hiso] at hshift
  exact (neg_eq_iff_eq_neg.mpr hshift).symm

private theorem K₀.of_shift_nonneg (X : C) (n : ℕ) :
    K₀.of C (X⟦(n : ℤ)⟧) = ((-1 : ℤ) ^ n) • K₀.of C X := by
  induction n with
  | zero => simpa using K₀.of_iso C ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
      calc
        K₀.of C (X⟦((n + 1 : ℕ) : ℤ)⟧) =
            K₀.of C ((X⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧) := by
          rw [Nat.cast_succ]
          simpa only [Functor.comp_obj] using (K₀.of_iso C
            (((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by lia)).app X).symm)).symm
        _ = -K₀.of C (X⟦(n : ℤ)⟧) := K₀.of_shift_one C _
        _ = -(((-1 : ℤ) ^ n) • K₀.of C X) := by rw [ih]
        _ = ((-1 : ℤ) ^ (n + 1)) • K₀.of C X := by simp [pow_succ']

private theorem K₀.of_shift_negative (X : C) (n : ℕ) :
    K₀.of C (X⟦(Int.negSucc n : ℤ)⟧) =
      ((-1 : ℤ) ^ (n + 1)) • K₀.of C X := by
  induction n with
  | zero => simpa using K₀.of_shift_neg_one C X
  | succ n ih =>
      calc
        K₀.of C (X⟦(Int.negSucc (n + 1) : ℤ)⟧) =
            K₀.of C ((X⟦(Int.negSucc n : ℤ)⟧)⟦(-1 : ℤ)⟧) := by
          simpa only [Functor.comp_obj] using (K₀.of_iso C
            (((shiftFunctorAdd' C (Int.negSucc n : ℤ) (-1 : ℤ)
              (Int.negSucc (n + 1) : ℤ) (by lia)).app X).symm)).symm
        _ = -K₀.of C (X⟦(Int.negSucc n : ℤ)⟧) := K₀.of_shift_neg_one C _
        _ = -(((-1 : ℤ) ^ (n + 1)) • K₀.of C X) := by rw [ih]
        _ = ((-1 : ℤ) ^ (n + 2)) • K₀.of C X := by simp [pow_succ']

/-- An integral shift changes a Grothendieck class only by its parity sign. -/
theorem K₀.of_shift_int (X : C) (n : ℤ) :
    K₀.of C (X⟦n⟧) = ((-1 : ℤ) ^ Int.natAbs n) • K₀.of C X := by
  cases n with
  | ofNat n => simpa using K₀.of_shift_nonneg C X n
  | negSucc n => simpa using K₀.of_shift_negative C X n

variable {C} in
/-- A function on objects is triangle-additive when it respects every
distinguished-triangle relation. -/
class IsTriangleAdditive {A : Type*} [AddCommGroup A] (f : C → A) : Prop where
  additive : ∀ T : Pretriangulated.Triangle C,
    T ∈ distTriang C → f T.obj₂ = f T.obj₁ + f T.obj₃

variable {C} in
instance {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] :
    (triangulatedPresentation C).IsAdditive f where
  additive := fun ⟨T, hT⟩ => IsTriangleAdditive.additive T hT

/-- Universal lift of a triangle-additive function. -/
def K₀.lift {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f] : K₀ C →+ A :=
  (triangulatedPresentation C).lift f

@[simp]
theorem K₀.lift_of {A : Type*} [AddCommGroup A] (f : C → A) [IsTriangleAdditive f]
    (X : C) : K₀.lift C f (K₀.of C X) = f X :=
  (triangulatedPresentation C).lift_of f X

/-- Additive maps from `K₀ C` are determined by object classes. -/
@[ext 1100]
theorem K₀.hom_ext {A : Type*} [AddCommGroup A] {f g : K₀ C →+ A}
    (h : ∀ X : C, f (K₀.of C X) = g (K₀.of C X)) : f = g :=
  (triangulatedPresentation C).hom_ext h

private theorem K₀.of_chain_succ {E : C} (P : PostnikovTower C E) (i : Fin P.n) :
    K₀.of C (P.chain.obj' (i.val + 1) (by lia)) =
      K₀.of C (P.chain.obj' i.val (by lia)) + K₀.of C (P.factor i) := by
  have h := K₀.of_triangle C (P.triangle i) (P.triangle_dist i)
  have h₂ := K₀.of_iso C (Classical.choice (P.triangle_obj₂ i))
  have h₁ := K₀.of_iso C (Classical.choice (P.triangle_obj₁ i))
  rwa [h₂, h₁] at h

private theorem K₀.of_chain_eq_partial_sum {E : C} (P : PostnikovTower C E)
    (k : ℕ) (hk : k ≤ P.n) :
    K₀.of C (P.chain.obj' k (by lia)) =
      ∑ i : Fin k, K₀.of C (P.factor ⟨i.val, by lia⟩) := by
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [show P.chain.obj' 0 (by lia) = P.chain.left from rfl]
    exact K₀.of_isZero C P.base_isZero
  | succ k ih =>
    rw [K₀.of_chain_succ C P ⟨k, by lia⟩, ih (by lia)]
    rw [Fin.sum_univ_castSucc]
    congr 1

/-- The class of the filtered object is the sum of the classes of the
Postnikov factors. -/
theorem K₀.of_postnikovTower_eq_sum {E : C} (P : PostnikovTower C E) :
    K₀.of C E = ∑ i : Fin P.n, K₀.of C (P.factor i) := by
  rw [show K₀.of C E = K₀.of C (P.chain.obj' P.n (by lia)) from by
    rw [show P.chain.obj' P.n (by lia) = P.chain.right from rfl]
    exact (K₀.of_iso C (Classical.choice P.top_iso)).symm]
  exact K₀.of_chain_eq_partial_sum C P P.n le_rfl

section ClassMap

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- The class of an object in a target lattice. -/
abbrev classOf (E : C) : Λ := v (K₀.of C E)

@[simp]
theorem classOf_id (E : C) : classOf C (AddMonoidHom.id (K₀ C)) E = K₀.of C E := rfl

@[simp]
theorem classOf_isZero {E : C} (hE : IsZero E) : classOf C v E = 0 := by
  simp [classOf, K₀.of_isZero C hE]

theorem classOf_triangle (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) :
    classOf C v T.obj₂ = classOf C v T.obj₁ + classOf C v T.obj₃ := by
  simp [classOf, K₀.of_triangle C T hT]

theorem classOf_iso {X Y : C} (e : X ≅ Y) : classOf C v X = classOf C v Y := by
  simp [classOf, K₀.of_iso C e]

@[simp]
theorem classOf_shift_one (E : C) : classOf C v (E⟦(1 : ℤ)⟧) = -classOf C v E := by
  simp [classOf]

@[simp]
theorem classOf_shift_neg_one (E : C) : classOf C v (E⟦(-1 : ℤ)⟧) = -classOf C v E := by
  simp [classOf]

theorem classOf_postnikovTower_eq_sum {E : C} (P : PostnikovTower C E) :
    classOf C v E = ∑ i : Fin P.n, classOf C v (P.factor i) := by
  simp [classOf, K₀.of_postnikovTower_eq_sum C P]

end ClassMap

end CategoryTheory.Triangulated
