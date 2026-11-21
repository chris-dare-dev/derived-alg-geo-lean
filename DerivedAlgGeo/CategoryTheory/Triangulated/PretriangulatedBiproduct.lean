/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Cones of maps into a binary biproduct

In a pretriangulated category, let `X ⟶ P ⊞ Q ⟶ Z ⟶ X⟦1⟧` be a distinguished triangle. If the
component `X ⟶ Q` of its first map is invertible, then the composite `P ⟶ P ⊞ Q ⟶ Z` of the
inclusion and the second map is invertible: `Z` is a cone of `X ⟶ P ⊞ Q` that is identified
with `P`.

## Main results

* `CategoryTheory.Pretriangulated.isIso_inl_comp_of_isIso_snd`: the statement above, for an
  arbitrary identification of the middle object with `P ⊞ Q`.
* `CategoryTheory.Pretriangulated.isIso_map_inl_comp_of_isIso_map_snd` and
  `CategoryTheory.Pretriangulated.isIso_map_inr_comp_of_isIso_map_fst`: the same after applying
  a triangulated functor that preserves binary biproducts, which does not need the triangle to
  be a triangle of the target.
* `CategoryTheory.isIso_neg`: the negative of an isomorphism is an isomorphism.

## Implementation notes

Write `q` for the component `X ⟶ Q` and `p` for the component `X ⟶ P`. The first map is the
composite of `q` followed by the inclusion of `Q` with an automorphism of `P ⊞ Q` that adds
`p ∘ q⁻¹` to the first coordinate. The first factor is the first map of a distinguished triangle
by the biproduct triangle, so the morphism of triangles it induces has invertible first and
second components, and the five lemma `Pretriangulated.isIso₃_of_isIso₁₂` gives the third.
-/

namespace CategoryTheory

open Limits

/-- The negative of an isomorphism is an isomorphism. -/
lemma isIso_neg {C : Type*} [Category C] [Preadditive C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (-f) :=
  ⟨⟨-inv f, by simp, by simp⟩⟩

namespace Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
/-- If `T` is a distinguished triangle whose middle object is identified with `P ⊞ Q`, and the
component `T.obj₁ ⟶ Q` of its first map is invertible, then `P ⟶ P ⊞ Q ⟶ T.obj₃` is
invertible. -/
lemma isIso_inl_comp_of_isIso_snd {T : Triangle C} (hT : T ∈ distTriang C) {P Q : C}
    (e : T.obj₂ ≅ P ⊞ Q) (h : IsIso (T.mor₁ ≫ e.hom ≫ biprod.snd)) :
    IsIso (biprod.inl ≫ e.inv ≫ T.mor₂) := by
  obtain ⟨q, hq⟩ : ∃ q : T.obj₁ ⟶ Q, q = T.mor₁ ≫ e.hom ≫ biprod.snd := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : T.obj₁ ⟶ P, p = T.mor₁ ≫ e.hom ≫ biprod.fst := ⟨_, rfl⟩
  rw [← hq] at h
  have : IsIso q := h
  let T' : Triangle C := Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃
  have hT' : T' ∈ distTriang C :=
    isomorphic_distinguished _ hT T'
      (Triangle.isoMk T' T (Iso.refl _) e.symm (Iso.refl _) (by simp [T']) (by simp [T'])
        (by simp [T']))
  let T0 : Triangle C :=
    Triangle.mk (q ≫ biprod.inr : T.obj₁ ⟶ P ⊞ Q) biprod.fst (0 : P ⟶ T.obj₁⟦(1 : ℤ)⟧)
  have hT0 : T0 ∈ distTriang C :=
    isomorphic_distinguished _ (binaryBiproductTriangle_distinguished Q P) T0
      (Triangle.isoMk T0 (binaryBiproductTriangle Q P) (asIso q : T.obj₁ ≅ Q)
        (biprod.braiding P Q) (Iso.refl _) (by apply biprod.hom_ext <;> simp [T0])
        (by simp [T0]) (by simp [T0]))
  let σ : P ⊞ Q ⟶ P ⊞ Q := biprod.lift (biprod.fst + biprod.snd ≫ inv q ≫ p) biprod.snd
  have hσ : IsIso σ := by
    refine ⟨biprod.lift (biprod.fst - biprod.snd ≫ inv q ≫ p) biprod.snd, ?_, ?_⟩
    · ext <;> simp [σ]
    · ext <;> simp [σ]
  have comm : T0.mor₁ ≫ σ = 𝟙 _ ≫ T'.mor₁ := by
    apply biprod.hom_ext
    · simp [T0, σ, T', hp]
    · simp [T0, σ, T', ← hq]
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism T0 T' hT0 hT' (𝟙 _) σ comm
  have hc : IsIso c := by
    let φ : T0 ⟶ T' := Triangle.homMk T0 T' (𝟙 _) σ c comm hc₁ (by simpa using hc₂)
    exact isIso₃_of_isIso₁₂ φ hT0 hT' (show IsIso (𝟙 _) from inferInstance) hσ
  have hσinl : biprod.inl ≫ σ = biprod.inl := by apply biprod.hom_ext <;> simp [σ]
  have : biprod.inl ≫ e.inv ≫ T.mor₂ = c := by
    have := congrArg (fun f => biprod.inl ≫ f) hc₁
    simp only [T0, T', Triangle.mk_mor₂] at this
    rw [← Category.assoc, biprod.inl_fst, Category.id_comp, ← Category.assoc, hσinl] at this
    exact this.symm
  rw [this]
  exact hc

section Functor

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [PreservesBinaryBiproducts F]

set_option backward.defeqAttrib.useBackward true in
/-- Let `X ⟶ P ⊞ Q ⟶ Z ⟶ X⟦1⟧` be a distinguished triangle and `F` a triangulated functor that
preserves binary biproducts. If `F` of the component `X ⟶ Q` is invertible, then `F` of
`P ⟶ P ⊞ Q ⟶ Z` is invertible. -/
lemma isIso_map_inl_comp_of_isIso_map_snd {X P Q Z : C} (s : X ⟶ P ⊞ Q) (g : P ⊞ Q ⟶ Z)
    (δ : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk s g δ ∈ distTriang C)
    (h : IsIso (F.map (s ≫ biprod.snd))) : IsIso (F.map (biprod.inl ≫ g)) := by
  have hT' := F.map_distinguished _ hT
  let e : (F.mapTriangle.obj (Triangle.mk s g δ)).obj₂ ≅ F.obj P ⊞ F.obj Q := F.mapBiprod P Q
  have h2 : e.hom ≫ biprod.snd = F.map biprod.snd := by
    simp only [e, Functor.mapBiprod_hom]
    exact biprod.lift_snd _ _
  have h' : IsIso ((F.mapTriangle.obj (Triangle.mk s g δ)).mor₁ ≫ e.hom ≫ biprod.snd) := by
    rw [h2]
    change IsIso (F.map s ≫ F.map biprod.snd)
    rw [← F.map_comp]
    exact h
  have := isIso_inl_comp_of_isIso_snd hT' e h'
  have h3 : biprod.inl ≫ e.inv ≫ (F.mapTriangle.obj (Triangle.mk s g δ)).mor₂ =
      F.map (biprod.inl ≫ g) := by
    rw [F.map_comp]
    simp only [e, Functor.mapBiprod_inv, ← Category.assoc]
    congr 1
    exact biprod.inl_desc _ _
  rwa [h3] at this

set_option backward.defeqAttrib.useBackward true in
/-- Let `X ⟶ P ⊞ Q ⟶ Z ⟶ X⟦1⟧` be a distinguished triangle and `F` a triangulated functor that
preserves binary biproducts. If `F` of the component `X ⟶ P` is invertible, then `F` of
`Q ⟶ P ⊞ Q ⟶ Z` is invertible. -/
lemma isIso_map_inr_comp_of_isIso_map_fst {X P Q Z : C} (s : X ⟶ P ⊞ Q) (g : P ⊞ Q ⟶ Z)
    (δ : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk s g δ ∈ distTriang C)
    (h : IsIso (F.map (s ≫ biprod.fst))) : IsIso (F.map (biprod.inr ≫ g)) := by
  have hT' := F.map_distinguished _ hT
  let e : (F.mapTriangle.obj (Triangle.mk s g δ)).obj₂ ≅ F.obj Q ⊞ F.obj P :=
    F.mapBiprod P Q ≪≫ biprod.braiding _ _
  have h2 : e.hom ≫ biprod.snd = F.map biprod.fst := by
    simp only [e, Iso.trans_hom, Functor.mapBiprod_hom, Category.assoc, biprod.braiding_hom]
    rw [biprod.lift_snd]
    exact biprod.lift_fst _ _
  have h' : IsIso ((F.mapTriangle.obj (Triangle.mk s g δ)).mor₁ ≫ e.hom ≫ biprod.snd) := by
    rw [h2]
    change IsIso (F.map s ≫ F.map biprod.fst)
    rw [← F.map_comp]
    exact h
  have := isIso_inl_comp_of_isIso_snd hT' e h'
  have h3 : biprod.inl ≫ e.inv ≫ (F.mapTriangle.obj (Triangle.mk s g δ)).mor₂ =
      F.map (biprod.inr ≫ g) := by
    rw [F.map_comp]
    simp only [e, Iso.trans_inv, Functor.mapBiprod_inv, biprod.braiding_inv, ← Category.assoc]
    congr 1
    have hh : (biprod.inl ≫ biprod.lift biprod.snd biprod.fst : _ ⟶ F.obj P ⊞ F.obj Q) =
        biprod.inr := by
      apply biprod.hom_ext <;> simp
    rw [hh]
    exact biprod.inr_desc _ _
  rwa [h3] at this

end Functor

end Pretriangulated

end CategoryTheory
