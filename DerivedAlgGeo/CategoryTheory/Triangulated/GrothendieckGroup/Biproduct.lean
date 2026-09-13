/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic

/-!
# Finite biproducts in the triangulated Grothendieck group

The class of a finite biproduct is the sum of the classes of its summands.
The binary statement comes directly from the distinguished split triangle;
the finite statement only packages the resulting induction over a finite
indexing type.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped BigOperators ZeroObject

universe u v w

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The Grothendieck class of a binary biproduct is the sum of the two classes. -/
@[simp]
theorem K₀.of_biprod (X Y : C) :
    K₀.of C (X ⊞ Y) = K₀.of C X + K₀.of C Y := by
  simpa [Pretriangulated.binaryBiproductTriangle] using
    K₀.of_triangle C (Pretriangulated.binaryBiproductTriangle X Y)
      (Pretriangulated.binaryBiproductTriangle_distinguished X Y)

private def optionBiproductBicone {ι : Type} [Fintype ι] (X : Option ι → C) :
    BinaryBicone (X none) (⨁ fun i : ι => X (some i)) where
  pt := ⨁ X
  fst := biproduct.π X none
  snd := biproduct.lift fun i => biproduct.π X (some i)
  inl := biproduct.ι X none
  inr := biproduct.desc fun i => biproduct.ι X (some i)
  inl_fst := by simp
  inl_snd := by ext i; simp
  inr_fst := by ext i; simp
  inr_snd := by
    ext i j
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π]
    by_cases h : j = i
    · subst i
      simp
    · rw [biproduct.ι_π_ne X (fun h' => h (Option.some.inj h'))]
      simp only [Category.id_comp]
      rw [biproduct.ι_π_ne _ h]

private theorem optionBiproductBicone_total {ι : Type} [Fintype ι]
    (X : Option ι → C) :
    (optionBiproductBicone C X).fst ≫ (optionBiproductBicone C X).inl +
      (optionBiproductBicone C X).snd ≫ (optionBiproductBicone C X).inr = 𝟙 _ := by
  change biproduct.π X none ≫ biproduct.ι X none +
    biproduct.lift (fun i => biproduct.π X (some i)) ≫
      biproduct.desc (fun i => biproduct.ι X (some i)) = 𝟙 (⨁ X)
  have hrest :
      biproduct.lift (fun i => biproduct.π X (some i)) ≫
          biproduct.desc (fun i => biproduct.ι X (some i)) =
        ∑ i : ι, biproduct.π X (some i) ≫ biproduct.ι X (some i) :=
    biproduct.lift_desc (f := fun i => X (some i))
  rw [hrest]
  simpa only [Fintype.sum_option] using (biproduct.total (f := X))

private noncomputable def optionBiproductIso {ι : Type} [Fintype ι]
    (X : Option ι → C) :
    (⨁ X) ≅ X none ⊞ (⨁ fun i : ι => X (some i)) :=
  biprod.uniqueUpToIso _ _
    (isBinaryBilimitOfTotal (optionBiproductBicone C X)
      (optionBiproductBicone_total C X))

private theorem K₀.of_biproduct_induction :
    ∀ (ι : Type) [Fintype ι] (X : ι → C),
      K₀.of C (⨁ X) = ∑ i, K₀.of C (X i) := by
  apply Fintype.induction_empty_option
  · intro α β _ e ih X
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have hiso :
        K₀.of C (⨁ fun i : α => X (e i)) = K₀.of C (⨁ X) :=
      K₀.of_iso C (biproduct.whiskerEquiv e fun _ => Iso.refl _)
    rw [← hiso, ih]
    exact e.sum_comp (fun i => K₀.of C (X i))
  · intro X
    rw [K₀.of_isZero C]
    · simp
    · exact
        { unique_to := fun Y => ⟨⟨⟨0⟩, by
            intro f
            apply biproduct.hom_ext'
            intro i
            exact i.elim⟩⟩
          unique_from := fun Y => ⟨⟨⟨0⟩, by
            intro f
            apply biproduct.hom_ext
            intro i
            exact i.elim⟩⟩ }
  · intro ι _ ih X
    rw [K₀.of_iso C (optionBiproductIso C X), K₀.of_biprod, ih,
      Fintype.sum_option]

/-- The Grothendieck class of a finite biproduct is the sum of the classes of
its summands. -/
theorem K₀.of_biproduct {ι : Type w} [Fintype ι] (X : ι → C) :
    K₀.of C (⨁ X) = ∑ i, K₀.of C (X i) := by
  let e := Fintype.equivFin ι
  let Y : Fin (Fintype.card ι) → C := fun i => X (e.symm i)
  rw [K₀.of_iso C (biproduct.whiskerEquiv (f := X) (g := Y) e
      fun i => eqToIso (by simp [Y, e])),
    K₀.of_biproduct_induction]
  simpa [Y] using e.symm.sum_comp (fun i => K₀.of C (X i))

/-- A finite biproduct of copies of one object represents the corresponding
natural multiple of its Grothendieck class. -/
theorem K₀.of_biproduct_const {ι : Type w} [Fintype ι] (X : C) :
    K₀.of C (⨁ fun _ : ι => X) = Fintype.card ι • K₀.of C X := by
  rw [K₀.of_biproduct]
  simp

end CategoryTheory.Triangulated
