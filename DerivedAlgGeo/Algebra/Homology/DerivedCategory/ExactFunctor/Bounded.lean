/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The derived functor of an exact functor on bounded objects

Let `F : A ⥤ B` be an exact functor between abelian categories and
`F.mapDerivedCategory : DerivedCategory A ⥤ DerivedCategory B` its derived
functor. Suppose `F` induces bijections on all `Ext` groups,

`Ext^n_A(X, Y) → Ext^n_B(F X, F Y)`   for all `X Y : A` and `n : ℕ`.

Then this file proves:

* `Functor.mapDerivedCategory_map_bijective_of_bounded`: the derived functor is
  fully faithful on bounded objects;
* `Functor.exists_bounded_iso_mapDerivedCategory_obj`: every bounded object of
  `DerivedCategory B` whose cohomology objects lie in the essential image of
  `F` is isomorphic to the image of a bounded object of `DerivedCategory A`.

Together these say that `Dᵇ(A) ⥤ Dᵇ_{F(A)}(B)` is an equivalence as soon as
`F` is an `Ext`-isomorphism on the hearts. Nothing here asks `F` to be full,
faithful, or an inclusion; both of those follow from the `Ext⁰` case.

## Proof

Everything is a dévissage on cohomological amplitude, run through
`DerivedCategory.bounded_induction`. The step is the five lemma applied to the
long exact `Hom` sequences of a distinguished triangle and of its image, with
`F.mapDerivedCategory` supplying the vertical maps. That lemma is stated twice,
once in each variable (`mapDerivedCategory_map_bijective_obj₃_left` and
`mapDerivedCategory_map_bijective_obj₃_right`), because `Hom` is contravariant
in the first variable and covariant in the second; both are proved for the
third object of a triangle, and the middle-object statements follow by inverse
rotation. Full faithfulness on `single` objects, the base case, is exactly the
`Ext` hypothesis once `Ext.mapExactFunctor_hom` and the vanishing of negative
`Ext` in both categories are unwound. Essential surjectivity is the standard
cone argument: a bounded object with cohomology in the essential image is an
extension of two objects of smaller amplitude that are already images, the
connecting morphism lifts by full faithfulness, and the image of a cone in `A`
is a cone in `B`.

## Why the hypothesis is `Ext`-bijectivity

For `F` the inclusion of a weak Serre subcategory this is the classical
statement that `Dᵇ(A) → Dᵇ_A(B)` is an equivalence; it is *not* automatic and
does need an input on `Ext`. Mathlib proves the `Ext` hypothesis in two cases
(`Functor.mapExt_bijective_of_preservesProjectiveObjects` and
`Functor.mapExt_bijective_of_preservesInjectiveObjects`); a geometric consumer
supplies it separately.

## Implementation notes

Every shift comparison isomorphism `(F.mapDerivedCategory.commShiftIso n).app X`
is given an explicit type `(F.mapDerivedCategory.obj X)⟦n⟧ ≅ …` before use.
Mathlib states it between `(F ⋙ shiftFunctor _ n).obj X` and
`(shiftFunctor _ n ⋙ F).obj X`, which are only definitionally the shifted
objects, and `rw`/`simp` do not see through `Functor.comp` at instance
transparency; the annotated `let`s keep every composite well-typed on the nose.
-/

universe w w' v v' u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace CategoryTheory.Functor

/-- Bijectivity of a functor on a hom-set only depends on the functor up to natural
isomorphism. -/
private lemma map_bijective_iff_of_natIso {C : Type*} {D : Type*} [Category* C] [Category* D]
    {G G' : C ⥤ D} (e : G ≅ G') (X Y : C) :
    Function.Bijective (G.map : (X ⟶ Y) → _) ↔ Function.Bijective (G'.map : (X ⟶ Y) → _) := by
  have h : (G'.map : (X ⟶ Y) → _) = ((e.app X).homCongr (e.app Y)) ∘ (G.map : (X ⟶ Y) → _) := by
    ext f
    simp [Iso.homCongr]
  rw [h, Equiv.comp_bijective]

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-! ### Transport of bijectivity along isomorphisms and shifts -/

section Transport

/-- Bijectivity of `F.mapDerivedCategory` on a hom-set is invariant under isomorphism of
the source object. -/
lemma mapDerivedCategory_map_bijective_iff_of_iso_left {E₁ E₂ : DerivedCategory A}
    (e : E₁ ≅ E₂) (W : DerivedCategory A) :
    Function.Bijective (F.mapDerivedCategory.map : (E₁ ⟶ W) → _) ↔
      Function.Bijective (F.mapDerivedCategory.map : (E₂ ⟶ W) → _) := by
  have h : (F.mapDerivedCategory.map : (E₂ ⟶ W) → _) =
      ((F.mapDerivedCategory.mapIso e).homCongr (Iso.refl _)) ∘
        (F.mapDerivedCategory.map : (E₁ ⟶ W) → _) ∘ (e.homCongr (Iso.refl W)).symm := by
    ext f
    simp [Iso.homCongr]
  rw [h, Equiv.comp_bijective, Equiv.bijective_comp]

/-- Bijectivity of `F.mapDerivedCategory` on a hom-set is invariant under isomorphism of
the target object. -/
lemma mapDerivedCategory_map_bijective_iff_of_iso_right (E : DerivedCategory A)
    {W₁ W₂ : DerivedCategory A} (e : W₁ ≅ W₂) :
    Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W₁) → _) ↔
      Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W₂) → _) := by
  have h : (F.mapDerivedCategory.map : (E ⟶ W₂) → _) =
      ((Iso.refl _).homCongr (F.mapDerivedCategory.mapIso e)) ∘
        (F.mapDerivedCategory.map : (E ⟶ W₁) → _) ∘ ((Iso.refl E).homCongr e).symm := by
    ext f
    simp [Iso.homCongr]
  rw [h, Equiv.comp_bijective, Equiv.bijective_comp]

/-- Bijectivity of `F.mapDerivedCategory` on a hom-set is invariant under shifting both
objects by the same integer, because the derived functor commutes with shifts. -/
lemma mapDerivedCategory_map_bijective_shift_iff (E W : DerivedCategory A) (a : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map : (E⟦a⟧ ⟶ W⟦a⟧) → _) ↔
      Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W) → _) := by
  have hs : Function.Bijective ((shiftFunctor (DerivedCategory A) a).map : (E ⟶ W) → _) :=
    ⟨(shiftFunctor _ a).map_injective, (shiftFunctor _ a).map_surjective⟩
  have hs' : Function.Bijective ((shiftFunctor (DerivedCategory B) a).map :
      (F.mapDerivedCategory.obj E ⟶ F.mapDerivedCategory.obj W) → _) :=
    ⟨(shiftFunctor _ a).map_injective, (shiftFunctor _ a).map_surjective⟩
  have h₁ : Function.Bijective ((shiftFunctor (DerivedCategory A) a ⋙ F.mapDerivedCategory).map :
      (E ⟶ W) → _) ↔ Function.Bijective (F.mapDerivedCategory.map : (E⟦a⟧ ⟶ W⟦a⟧) → _) :=
    Function.Bijective.of_comp_iff _ hs
  have h₂ : Function.Bijective ((F.mapDerivedCategory ⋙ shiftFunctor (DerivedCategory B) a).map :
      (E ⟶ W) → _) ↔ Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W) → _) :=
    Function.Bijective.of_comp_iff' hs' _
  rw [← h₁, ← h₂]
  exact map_bijective_iff_of_natIso (F.mapDerivedCategory.commShiftIso a) E W

/-- Shifting the source: bijectivity for all shifts of the target gives bijectivity for all
shifts of the source as well. -/
lemma mapDerivedCategory_map_bijective_shift_left {E W : DerivedCategory A}
    (h : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W⟦k⟧) → _))
    (m k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map : (E⟦m⟧ ⟶ W⟦k⟧) → _) := by
  have e₁ : (E⟦m⟧)⟦-m⟧ ≅ E :=
    (shiftFunctorCompIsoId (DerivedCategory A) m (-m) (by omega)).app E
  have e₂ : (W⟦k⟧)⟦-m⟧ ≅ W⟦k - m⟧ :=
    ((shiftFunctorAdd' (DerivedCategory A) k (-m) (k - m) (by omega)).app W).symm
  exact (mapDerivedCategory_map_bijective_shift_iff F _ _ (-m)).mp
    ((mapDerivedCategory_map_bijective_iff_of_iso_left F e₁ _).mpr
      ((mapDerivedCategory_map_bijective_iff_of_iso_right F _ e₂).mpr (h (k - m))))

/-- Bijectivity for all shifts of the target gives bijectivity for the target itself. -/
lemma mapDerivedCategory_map_bijective_of_forall_shift {E W : DerivedCategory A}
    (h : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W⟦k⟧) → _)) :
    Function.Bijective (F.mapDerivedCategory.map : (E ⟶ W) → _) :=
  (mapDerivedCategory_map_bijective_iff_of_iso_right F E
    ((shiftFunctorZero (DerivedCategory A) ℤ).app W)).mp (h 0)

end Transport

/-! ### The five lemma on the long exact `Hom` sequences of a distinguished triangle -/

section FiveLemma

variable (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
include hT

/-- **Contravariant cone closure.** If `F.mapDerivedCategory` is bijective on morphisms from
the first two objects of a distinguished triangle to all shifts of `W`, it is bijective on
morphisms from the third object to all shifts of `W`.

The five lemma is applied to the rows
`Hom(T₂⟦1⟧, W') → Hom(T₁⟦1⟧, W') → Hom(T₃, W') → Hom(T₂, W') → Hom(T₁, W')`
and their images, with `W' := W⟦k⟧`. -/
lemma mapDerivedCategory_map_bijective_obj₃_left (W : DerivedCategory A)
    (h₁ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (T.obj₁ ⟶ W⟦k⟧) → _))
    (h₂ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (T.obj₂ ⟶ W⟦k⟧) → _))
    (k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map : (T.obj₃ ⟶ W⟦k⟧) → _) := by
  have hT' := F.mapDerivedCategory.map_distinguished T hT
  -- Shift comparison isomorphisms, with their types normalised.
  let α₁ : (F.mapDerivedCategory.obj T.obj₁)⟦(1 : ℤ)⟧ ≅
      F.mapDerivedCategory.obj (T.obj₁⟦(1 : ℤ)⟧) :=
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).app T.obj₁).symm
  let α₂ : (F.mapDerivedCategory.obj T.obj₂)⟦(1 : ℤ)⟧ ≅
      F.mapDerivedCategory.obj (T.obj₂⟦(1 : ℤ)⟧) :=
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).app T.obj₂).symm
  -- The third morphism of the image triangle, and the zero composites of both triangles.
  let m₃ : F.mapDerivedCategory.obj T.obj₃ ⟶ (F.mapDerivedCategory.obj T.obj₁)⟦(1 : ℤ)⟧ :=
    F.mapDerivedCategory.map T.mor₃ ≫ α₁.inv
  have z₁₂ : F.mapDerivedCategory.map T.mor₁ ≫ F.mapDerivedCategory.map T.mor₂ = 0 :=
    comp_distTriang_mor_zero₁₂ _ hT'
  have z₂₃ : F.mapDerivedCategory.map T.mor₂ ≫ m₃ = 0 := comp_distTriang_mor_zero₂₃ _ hT'
  have z₃₁ : m₃ ≫ (F.mapDerivedCategory.map T.mor₁)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT'
  -- The two rows of the ladder.
  let f₁ : (T.obj₂⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) →+ (T.obj₁⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) :=
    Preadditive.leftComp (W⟦k⟧) (T.mor₁⟦(1 : ℤ)⟧')
  let f₂ : (T.obj₁⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) →+ (T.obj₃ ⟶ W⟦k⟧) := Preadditive.leftComp (W⟦k⟧) T.mor₃
  let f₃ : (T.obj₃ ⟶ W⟦k⟧) →+ (T.obj₂ ⟶ W⟦k⟧) := Preadditive.leftComp (W⟦k⟧) T.mor₂
  let f₄ : (T.obj₂ ⟶ W⟦k⟧) →+ (T.obj₁ ⟶ W⟦k⟧) := Preadditive.leftComp (W⟦k⟧) T.mor₁
  let g₁ : ((F.mapDerivedCategory.obj T.obj₂)⟦(1 : ℤ)⟧ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) →+
      ((F.mapDerivedCategory.obj T.obj₁)⟦(1 : ℤ)⟧ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) :=
    Preadditive.leftComp _ ((F.mapDerivedCategory.map T.mor₁)⟦(1 : ℤ)⟧')
  let g₂ : ((F.mapDerivedCategory.obj T.obj₁)⟦(1 : ℤ)⟧ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) →+
      (F.mapDerivedCategory.obj T.obj₃ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) :=
    Preadditive.leftComp _ m₃
  let g₃ : (F.mapDerivedCategory.obj T.obj₃ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) →+
      (F.mapDerivedCategory.obj T.obj₂ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) :=
    Preadditive.leftComp _ (F.mapDerivedCategory.map T.mor₂)
  let g₄ : (F.mapDerivedCategory.obj T.obj₂ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) →+
      (F.mapDerivedCategory.obj T.obj₁ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) :=
    Preadditive.leftComp _ (F.mapDerivedCategory.map T.mor₁)
  -- The vertical maps.
  let i₁ : (T.obj₂⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) →+
      ((F.mapDerivedCategory.obj T.obj₂)⟦(1 : ℤ)⟧ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) :=
    (Preadditive.leftComp _ α₂.hom).comp F.mapDerivedCategory.mapAddHom
  let i₂ : (T.obj₁⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) →+
      ((F.mapDerivedCategory.obj T.obj₁)⟦(1 : ℤ)⟧ ⟶ F.mapDerivedCategory.obj (W⟦k⟧)) :=
    (Preadditive.leftComp _ α₁.hom).comp F.mapDerivedCategory.mapAddHom
  let i₃ : (T.obj₃ ⟶ W⟦k⟧) →+ _ := F.mapDerivedCategory.mapAddHom
  let i₄ : (T.obj₂ ⟶ W⟦k⟧) →+ _ := F.mapDerivedCategory.mapAddHom
  let i₅ : (T.obj₁ ⟶ W⟦k⟧) →+ _ := F.mapDerivedCategory.mapAddHom
  have hi₁ : Function.Bijective i₁ := by
    have : (i₁ : (T.obj₂⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) → _) =
        (α₂.symm.homCongr (Iso.refl _)) ∘ F.mapDerivedCategory.map := by
      ext f; simp [i₁, Iso.homCongr, Preadditive.leftComp]
    rw [this, Equiv.comp_bijective]
    exact mapDerivedCategory_map_bijective_shift_left F h₂ 1 k
  have hi₂ : Function.Bijective i₂ := by
    have : (i₂ : (T.obj₁⟦(1 : ℤ)⟧ ⟶ W⟦k⟧) → _) =
        (α₁.symm.homCongr (Iso.refl _)) ∘ F.mapDerivedCategory.map := by
      ext f; simp [i₂, Iso.homCongr, Preadditive.leftComp]
    rw [this, Equiv.comp_bijective]
    exact mapDerivedCategory_map_bijective_shift_left F h₁ 1 k
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hi₁.2 hi₂ (h₂ k) (h₁ k).1
  · ext f
    simp [f₁, g₁, i₁, i₂, α₁, α₂, Preadditive.leftComp,
      Functor.commShiftIso_inv_naturality_assoc]
  · ext f
    simp [f₂, g₂, i₂, i₃, m₃, Preadditive.leftComp]
  · ext f
    simp [f₃, g₃, i₃, i₄, Preadditive.leftComp]
  · ext f
    simp [f₄, g₄, i₄, i₅, Preadditive.leftComp]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ : ∃ x : T.obj₂⟦(1 : ℤ)⟧ ⟶ W⟦k⟧, g = (-T.mor₁⟦(1 : ℤ)⟧') ≫ x :=
        Triangle.yoneda_exact₃ _ (rot_of_distTriang T hT) g hg
      exact ⟨-x, by simp [f₁, Preadditive.leftComp, hx]⟩
    · rintro ⟨x, rfl⟩
      simp [f₁, f₂, Preadditive.leftComp, comp_distTriang_mor_zero₃₁_assoc T hT]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.yoneda_exact₃ T hT g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [f₂, f₃, Preadditive.leftComp, comp_distTriang_mor_zero₂₃_assoc T hT]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ T hT g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [f₃, f₄, Preadditive.leftComp, comp_distTriang_mor_zero₁₂_assoc T hT]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ : ∃ x : (F.mapDerivedCategory.obj T.obj₂)⟦(1 : ℤ)⟧ ⟶
          F.mapDerivedCategory.obj (W⟦k⟧),
          g = (-(F.mapDerivedCategory.map T.mor₁)⟦(1 : ℤ)⟧') ≫ x :=
        Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT') g hg
      exact ⟨-x, by simp [g₁, Preadditive.leftComp, hx]⟩
    · rintro ⟨x, rfl⟩
      simp [g₁, g₂, Preadditive.leftComp, reassoc_of% z₃₁]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.yoneda_exact₃ _ hT' g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [g₂, g₃, Preadditive.leftComp, reassoc_of% z₂₃]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ _ hT' g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [g₃, g₄, Preadditive.leftComp, reassoc_of% z₁₂]

/-- **Covariant cone closure.** If `F.mapDerivedCategory` is bijective on morphisms from `V`
to all shifts of the first two objects of a distinguished triangle, it is bijective on
morphisms from `V` to all shifts of the third object.

The five lemma is applied, for the `k`-shifted triangle `S`, to the rows
`Hom(V, S₁) → Hom(V, S₂) → Hom(V, S₃) → Hom(V, S₁⟦1⟧) → Hom(V, S₂⟦1⟧)` and their images. -/
lemma mapDerivedCategory_map_bijective_obj₃_right (V : DerivedCategory A)
    (h₁ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (V ⟶ T.obj₁⟦k⟧) → _))
    (h₂ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (V ⟶ T.obj₂⟦k⟧) → _))
    (k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map : (V ⟶ T.obj₃⟦k⟧) → _) := by
  -- Work with the shifted triangle, whose objects are the `k`-shifts of those of `T`.
  have hS : (Triangle.shiftFunctor (DerivedCategory A) k).obj T ∈ distTriang _ :=
    Triangle.shift_distinguished T hT k
  set S := (Triangle.shiftFunctor (DerivedCategory A) k).obj T
  have hS' := F.mapDerivedCategory.map_distinguished S hS
  have hS₁ : ∀ j : ℤ, Function.Bijective (F.mapDerivedCategory.map : (V ⟶ S.obj₁⟦j⟧) → _) :=
    fun j ↦ (mapDerivedCategory_map_bijective_iff_of_iso_right F V
      ((shiftFunctorAdd' (DerivedCategory A) k j (k + j) rfl).app T.obj₁)).mp (h₁ (k + j))
  have hS₂ : ∀ j : ℤ, Function.Bijective (F.mapDerivedCategory.map : (V ⟶ S.obj₂⟦j⟧) → _) :=
    fun j ↦ (mapDerivedCategory_map_bijective_iff_of_iso_right F V
      ((shiftFunctorAdd' (DerivedCategory A) k j (k + j) rfl).app T.obj₂)).mp (h₂ (k + j))
  change Function.Bijective (F.mapDerivedCategory.map : (V ⟶ S.obj₃) → _)
  have hS₁₀ := (mapDerivedCategory_map_bijective_iff_of_iso_right F V
    ((shiftFunctorZero (DerivedCategory A) ℤ).app S.obj₁)).mp (hS₁ 0)
  have hS₂₀ := (mapDerivedCategory_map_bijective_iff_of_iso_right F V
    ((shiftFunctorZero (DerivedCategory A) ℤ).app S.obj₂)).mp (hS₂ 0)
  let β₁ : F.mapDerivedCategory.obj (S.obj₁⟦(1 : ℤ)⟧) ≅
      (F.mapDerivedCategory.obj S.obj₁)⟦(1 : ℤ)⟧ :=
    (F.mapDerivedCategory.commShiftIso (1 : ℤ)).app S.obj₁
  let β₂ : F.mapDerivedCategory.obj (S.obj₂⟦(1 : ℤ)⟧) ≅
      (F.mapDerivedCategory.obj S.obj₂)⟦(1 : ℤ)⟧ :=
    (F.mapDerivedCategory.commShiftIso (1 : ℤ)).app S.obj₂
  let m₃ : F.mapDerivedCategory.obj S.obj₃ ⟶ (F.mapDerivedCategory.obj S.obj₁)⟦(1 : ℤ)⟧ :=
    F.mapDerivedCategory.map S.mor₃ ≫ β₁.hom
  have z₁₂ : F.mapDerivedCategory.map S.mor₁ ≫ F.mapDerivedCategory.map S.mor₂ = 0 :=
    comp_distTriang_mor_zero₁₂ _ hS'
  have z₂₃ : F.mapDerivedCategory.map S.mor₂ ≫ m₃ = 0 := comp_distTriang_mor_zero₂₃ _ hS'
  have z₃₁ : m₃ ≫ (F.mapDerivedCategory.map S.mor₁)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hS'
  let f₁ : (V ⟶ S.obj₁) →+ (V ⟶ S.obj₂) := Preadditive.rightComp V S.mor₁
  let f₂ : (V ⟶ S.obj₂) →+ (V ⟶ S.obj₃) := Preadditive.rightComp V S.mor₂
  let f₃ : (V ⟶ S.obj₃) →+ (V ⟶ S.obj₁⟦(1 : ℤ)⟧) := Preadditive.rightComp V S.mor₃
  let f₄ : (V ⟶ S.obj₁⟦(1 : ℤ)⟧) →+ (V ⟶ S.obj₂⟦(1 : ℤ)⟧) :=
    Preadditive.rightComp V (S.mor₁⟦(1 : ℤ)⟧')
  let g₁ : (F.mapDerivedCategory.obj V ⟶ F.mapDerivedCategory.obj S.obj₁) →+
      (F.mapDerivedCategory.obj V ⟶ F.mapDerivedCategory.obj S.obj₂) :=
    Preadditive.rightComp _ (F.mapDerivedCategory.map S.mor₁)
  let g₂ : (F.mapDerivedCategory.obj V ⟶ F.mapDerivedCategory.obj S.obj₂) →+
      (F.mapDerivedCategory.obj V ⟶ F.mapDerivedCategory.obj S.obj₃) :=
    Preadditive.rightComp _ (F.mapDerivedCategory.map S.mor₂)
  let g₃ : (F.mapDerivedCategory.obj V ⟶ F.mapDerivedCategory.obj S.obj₃) →+
      (F.mapDerivedCategory.obj V ⟶ (F.mapDerivedCategory.obj S.obj₁)⟦(1 : ℤ)⟧) :=
    Preadditive.rightComp _ m₃
  let g₄ : (F.mapDerivedCategory.obj V ⟶ (F.mapDerivedCategory.obj S.obj₁)⟦(1 : ℤ)⟧) →+
      (F.mapDerivedCategory.obj V ⟶ (F.mapDerivedCategory.obj S.obj₂)⟦(1 : ℤ)⟧) :=
    Preadditive.rightComp _ ((F.mapDerivedCategory.map S.mor₁)⟦(1 : ℤ)⟧')
  let i₁ : (V ⟶ S.obj₁) →+ _ := F.mapDerivedCategory.mapAddHom
  let i₂ : (V ⟶ S.obj₂) →+ _ := F.mapDerivedCategory.mapAddHom
  let i₃ : (V ⟶ S.obj₃) →+ _ := F.mapDerivedCategory.mapAddHom
  let i₄ : (V ⟶ S.obj₁⟦(1 : ℤ)⟧) →+
      (F.mapDerivedCategory.obj V ⟶ (F.mapDerivedCategory.obj S.obj₁)⟦(1 : ℤ)⟧) :=
    (Preadditive.rightComp _ β₁.hom).comp F.mapDerivedCategory.mapAddHom
  let i₅ : (V ⟶ S.obj₂⟦(1 : ℤ)⟧) →+
      (F.mapDerivedCategory.obj V ⟶ (F.mapDerivedCategory.obj S.obj₂)⟦(1 : ℤ)⟧) :=
    (Preadditive.rightComp _ β₂.hom).comp F.mapDerivedCategory.mapAddHom
  have hi₄ : Function.Bijective i₄ := by
    have : (i₄ : (V ⟶ S.obj₁⟦(1 : ℤ)⟧) → _) =
        ((Iso.refl _).homCongr β₁) ∘ F.mapDerivedCategory.map := by
      ext f; simp [i₄, Iso.homCongr, Preadditive.rightComp]
    rw [this, Equiv.comp_bijective]
    exact hS₁ 1
  have hi₅ : Function.Bijective i₅ := by
    have : (i₅ : (V ⟶ S.obj₂⟦(1 : ℤ)⟧) → _) =
        ((Iso.refl _).homCongr β₂) ∘ F.mapDerivedCategory.map := by
      ext f; simp [i₅, Iso.homCongr, Preadditive.rightComp]
    rw [this, Equiv.comp_bijective]
    exact hS₂ 1
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS₁₀.2 hS₂₀ hi₄ hi₅.1
  · ext f
    simp [f₁, g₁, i₁, i₂, Preadditive.rightComp]
  · ext f
    simp [f₂, g₂, i₂, i₃, Preadditive.rightComp]
  · ext f
    simp [f₃, g₃, i₃, i₄, m₃, Preadditive.rightComp]
  · ext f
    simp [f₄, g₄, i₄, i₅, β₁, β₂, Preadditive.rightComp, Functor.commShiftIso_hom_naturality]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ S hS g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [f₁, f₂, Preadditive.rightComp, comp_distTriang_mor_zero₁₂ S hS]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₃ S hS g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [f₂, f₃, Preadditive.rightComp, comp_distTriang_mor_zero₂₃ S hS]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₁ S hS g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [f₃, f₄, Preadditive.rightComp, comp_distTriang_mor_zero₃₁ S hS]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ hS' g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [g₁, g₂, Preadditive.rightComp, z₁₂]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₃ _ hS' g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [g₂, g₃, Preadditive.rightComp, z₂₃]
  · intro g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₁ _ hS' g hg
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp [g₃, g₄, Preadditive.rightComp, z₃₁]

/-- Cone closure in the first variable for the middle object of a distinguished triangle,
by inverse rotation. -/
lemma mapDerivedCategory_map_bijective_obj₂_left (W : DerivedCategory A)
    (h₁ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (T.obj₁ ⟶ W⟦k⟧) → _))
    (h₃ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (T.obj₃ ⟶ W⟦k⟧) → _))
    (k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map : (T.obj₂ ⟶ W⟦k⟧) → _) :=
  mapDerivedCategory_map_bijective_obj₃_left F T.invRotate (inv_rot_of_distTriang T hT) W
    (fun j ↦ mapDerivedCategory_map_bijective_shift_left F h₃ (-1) j) h₁ k

/-- Cone closure in the second variable for the middle object of a distinguished triangle,
by inverse rotation. -/
lemma mapDerivedCategory_map_bijective_obj₂_right (V : DerivedCategory A)
    (h₁ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (V ⟶ T.obj₁⟦k⟧) → _))
    (h₃ : ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (V ⟶ T.obj₃⟦k⟧) → _))
    (k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map : (V ⟶ T.obj₂⟦k⟧) → _) :=
  mapDerivedCategory_map_bijective_obj₃_right F T.invRotate (inv_rot_of_distTriang T hT) V
    (fun j ↦ (mapDerivedCategory_map_bijective_iff_of_iso_right F V
      ((shiftFunctorAdd' (DerivedCategory A) (-1) j (-1 + j) rfl).app T.obj₃)).mp
        (h₃ (-1 + j)))
    h₁ k

end FiveLemma

/-! ### The base case: single objects and `Ext` -/

open scoped ZeroObject

section Single

/-- Negative `Ext` vanishes in both categories, so `F.mapDerivedCategory` is trivially
bijective on morphisms `(singleFunctor A 0).obj X ⟶ ((singleFunctor A 0).obj Y)⟦k⟧`
for `k < 0`. -/
lemma mapDerivedCategory_map_bijective_single_of_neg (X Y : A) (k : ℤ) (hk : k < 0) :
    Function.Bijective (F.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor A 0).obj X ⟶
        ((DerivedCategory.singleFunctor A 0).obj Y)⟦k⟧) → _) := by
  have h₁ : ((DerivedCategory.singleFunctor A 0).obj X).IsLE 0 := inferInstance
  have h₂ : (((DerivedCategory.singleFunctor A 0).obj Y)⟦k⟧).IsGE (-k) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 k (-k) (by omega)
  have h₁' : (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsLE 0 :=
    mapDerivedCategory_isLE F _ 0 h₁
  have h₂' : (F.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor A 0).obj Y)⟦k⟧)).IsGE (-k) :=
    mapDerivedCategory_isGE F _ (-k) h₂
  constructor
  · intro f g _
    rw [DerivedCategory.TStructure.t.zero f 0 (-k) (by omega),
      DerivedCategory.TStructure.t.zero g 0 (-k) (by omega)]
  · intro g
    exact ⟨0, by
      rw [DerivedCategory.TStructure.t.zero (F.mapDerivedCategory.map 0) 0 (-k) (by omega),
        DerivedCategory.TStructure.t.zero g 0 (-k) (by omega)]⟩

variable [HasExt.{w} A] [HasExt.{w'} B]

/-- Unwinding `Ext.mapExactFunctor_hom`: bijectivity of `F.mapExtAddHom X Y n` is
bijectivity of `F.mapDerivedCategory` on morphisms
`(singleFunctor A 0).obj X ⟶ ((singleFunctor A 0).obj Y)⟦n⟧`. -/
lemma mapDerivedCategory_map_bijective_single_iff_mapExt_bijective (X Y : A) (n : ℕ) :
    Function.Bijective (F.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor A 0).obj X ⟶
        ((DerivedCategory.singleFunctor A 0).obj Y)⟦(n : ℤ)⟧) → _) ↔
      Function.Bijective (F.mapExtAddHom X Y n) := by
  let eX : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj X) ≅
      (DerivedCategory.singleFunctor B 0).obj (F.obj X) :=
    (F.mapDerivedCategorySingleFunctor 0).app X
  let eY : F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor A 0).obj Y)⟦(n : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor B 0).obj (F.obj Y))⟦(n : ℤ)⟧ :=
    (F.mapDerivedCategory.commShiftIso (n : ℤ)).app ((DerivedCategory.singleFunctor A 0).obj Y) ≪≫
      (shiftFunctor (DerivedCategory B) (n : ℤ)).mapIso ((F.mapDerivedCategorySingleFunctor 0).app Y)
  have h : (F.mapExtAddHom X Y n : Abelian.Ext X Y n → _) =
      (Abelian.Ext.homEquiv (C := B)).symm ∘ (eX.homCongr eY) ∘
        (F.mapDerivedCategory.map :
          ((DerivedCategory.singleFunctor A 0).obj X ⟶
            ((DerivedCategory.singleFunctor A 0).obj Y)⟦(n : ℤ)⟧) → _) ∘
        (Abelian.Ext.homEquiv (C := A)) := by
    ext e
    simp only [Function.comp_apply, Functor.mapExtAddHom_apply]
    change (e.mapExactFunctor F).hom = Abelian.Ext.homEquiv (Abelian.Ext.homEquiv.symm _)
    rw [Equiv.apply_symm_apply, Abelian.Ext.mapExactFunctor_hom, Iso.homCongr_apply]
    exact congrArg (fun z ↦ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ z)
      (Category.assoc _ _ _)
  rw [h, Equiv.comp_bijective, Equiv.comp_bijective, Equiv.bijective_comp]

variable (hF : ∀ (X Y : A) (n : ℕ), Function.Bijective (F.mapExtAddHom X Y n))
include hF

/-- Under the `Ext` hypothesis, `F.mapDerivedCategory` is bijective on all morphisms between
degree-zero single objects and their shifts. -/
lemma mapDerivedCategory_map_bijective_single (X Y : A) (k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map :
      ((DerivedCategory.singleFunctor A 0).obj X ⟶
        ((DerivedCategory.singleFunctor A 0).obj Y)⟦k⟧) → _) := by
  rcases lt_or_ge k 0 with hk | hk
  · exact mapDerivedCategory_map_bijective_single_of_neg F X Y k hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact (mapDerivedCategory_map_bijective_single_iff_mapExt_bijective F X Y n).mpr (hF X Y n)

/-- Under the `Ext` hypothesis, `F.mapDerivedCategory` is bijective on morphisms from any
bounded object to any shift of a degree-zero single object: the first-variable
dévissage. -/
lemma mapDerivedCategory_map_bijective_bounded_single {E : DerivedCategory A}
    (hE : DerivedCategory.TStructure.t.bounded E) (Y : A) (k : ℤ) :
    Function.Bijective (F.mapDerivedCategory.map :
      (E ⟶ ((DerivedCategory.singleFunctor A 0).obj Y)⟦k⟧) → _) := by
  refine DerivedCategory.bounded_induction (⊤ : ObjectProperty A)
    (fun E ↦ ∀ (Y : A) (k : ℤ), Function.Bijective (F.mapDerivedCategory.map :
      (E ⟶ ((DerivedCategory.singleFunctor A 0).obj Y)⟦k⟧) → _)) ?_ ?_ ?_ hE
    (fun _ ↦ trivial) Y k
  · intro E E' e h Y k
    exact (mapDerivedCategory_map_bijective_iff_of_iso_left F e _).mp (h Y k)
  · intro n X _ Y k
    exact (mapDerivedCategory_map_bijective_iff_of_iso_left F
      (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app X) _).mp
      (mapDerivedCategory_map_bijective_shift_left F
        (mapDerivedCategory_map_bijective_single F hF X Y) (-n) k)
  · intro T hT h₁ h₃ Y k
    exact mapDerivedCategory_map_bijective_obj₂_left F T hT _ (h₁ Y) (h₃ Y) k

/-- **Full faithfulness on bounded objects.** If `F` induces bijections on all `Ext`
groups, then `F.mapDerivedCategory` is bijective on morphisms between bounded objects:
the second-variable dévissage, on top of the first. -/
theorem mapDerivedCategory_map_bijective_of_bounded {E E' : DerivedCategory A}
    (hE : DerivedCategory.TStructure.t.bounded E)
    (hE' : DerivedCategory.TStructure.t.bounded E') :
    Function.Bijective (F.mapDerivedCategory.map : (E ⟶ E') → _) := by
  refine mapDerivedCategory_map_bijective_of_forall_shift F ?_
  refine DerivedCategory.bounded_induction (⊤ : ObjectProperty A)
    (fun E' ↦ ∀ k : ℤ, Function.Bijective (F.mapDerivedCategory.map : (E ⟶ E'⟦k⟧) → _))
    ?_ ?_ ?_ hE' (fun _ ↦ trivial)
  · intro W W' e h k
    exact (mapDerivedCategory_map_bijective_iff_of_iso_right F E
      ((shiftFunctor _ k).mapIso e)).mp (h k)
  · intro n Y _ k
    have e : ((DerivedCategory.singleFunctor A n).obj Y)⟦k⟧ ≅
        ((DerivedCategory.singleFunctor A 0).obj Y)⟦-n + k⟧ :=
      (shiftFunctor _ k).mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app Y).symm ≪≫
        ((shiftFunctorAdd' (DerivedCategory A) (-n) k (-n + k) rfl).app _).symm
    exact (mapDerivedCategory_map_bijective_iff_of_iso_right F E e).mpr
      (mapDerivedCategory_map_bijective_bounded_single F hF hE Y (-n + k))
  · intro T hT h₁ h₃ k
    exact mapDerivedCategory_map_bijective_obj₂_right F T hT E h₁ h₃ k

/-- **Essential surjectivity onto the cohomological image.** If `F` induces bijections on
all `Ext` groups, every bounded object of `DerivedCategory B` whose cohomology objects lie
in the essential image of `F` is isomorphic to the image of a bounded object of
`DerivedCategory A`.

The cone step: for a distinguished triangle `E₁ ⟶ E ⟶ E₃ ⟶ E₁⟦1⟧` with `E₁ ≅ F X` and
`E₃ ≅ F Z` for bounded `X`, `Z`, the connecting morphism lifts to `g : Z ⟶ X⟦1⟧` by full
faithfulness; a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with third morphism `g` has
bounded `Y`, and its image is isomorphic to the given triangle by
`isIso₂_of_isIso₁₃`. -/
theorem exists_bounded_iso_mapDerivedCategory_obj {E' : DerivedCategory B}
    (hE' : DerivedCategory.TStructure.t.bounded E')
    (hP : DerivedCategory.cohomologyIn F.essImage E') :
    ∃ E : DerivedCategory A, DerivedCategory.TStructure.t.bounded E ∧
      Nonempty (F.mapDerivedCategory.obj E ≅ E') := by
  haveI : F.essImage.ContainsZero :=
    ⟨F.obj 0, F.map_isZero (isZero_zero A), F.obj_mem_essImage 0⟩
  refine DerivedCategory.bounded_induction F.essImage
    (fun E' ↦ ∃ E : DerivedCategory A, DerivedCategory.TStructure.t.bounded E ∧
      Nonempty (F.mapDerivedCategory.obj E ≅ E')) ?_ ?_ ?_ hE' hP
  · rintro E₁ E₂ e ⟨E, hE, ⟨φ⟩⟩
    exact ⟨E, hE, ⟨φ ≪≫ e⟩⟩
  · rintro n Y ⟨X, ⟨e⟩⟩
    refine ⟨(DerivedCategory.singleFunctor A n).obj X,
      ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, ⟨?_⟩⟩
    exact (F.mapDerivedCategorySingleFunctor n).app X ≪≫
      (DerivedCategory.singleFunctor B n).mapIso e
  · rintro T hT ⟨X, hX, ⟨e₁⟩⟩ ⟨Z, hZ, ⟨e₃⟩⟩
    have hX1 : DerivedCategory.TStructure.t.bounded (X⟦(1 : ℤ)⟧) :=
      DerivedCategory.TStructure.t.bounded.le_shift 1 X hX
    let α : (F.mapDerivedCategory.obj X)⟦(1 : ℤ)⟧ ≅ F.mapDerivedCategory.obj (X⟦(1 : ℤ)⟧) :=
      ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).app X).symm
    -- Lift the connecting morphism of `T` along `F.mapDerivedCategory`.
    obtain ⟨g, hg⟩ := (mapDerivedCategory_map_bijective_of_bounded F hF hZ hX1).2
      (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫ α.hom)
    obtain ⟨Y, f, h, hTY⟩ := distinguished_cocone_triangle₂ g
    have hT' := F.mapDerivedCategory.map_distinguished _ hTY
    have comm : (F.mapDerivedCategory.mapTriangle.obj (Triangle.mk f h g)).mor₃ ≫
        e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ T.mor₃ := by
      change (F.mapDerivedCategory.map g ≫ α.inv) ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ T.mor₃
      rw [hg]
      simp only [assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id, comp_id]
    obtain ⟨b, hb₁, hb₂⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ hT' hT e₁.hom e₃.hom comm
    refine ⟨Y, ?_, ?_⟩
    · obtain ⟨Y', hY', ⟨e⟩⟩ :=
        DerivedCategory.TStructure.t.bounded.ext_of_isTriangulatedClosed₂' _ hTY hX hZ
      exact DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm hY'
    · let φ : F.mapDerivedCategory.mapTriangle.obj (Triangle.mk f h g) ⟶ T :=
        Triangle.homMk _ _ e₁.hom b e₃.hom hb₁ hb₂ comm
      have : IsIso φ.hom₂ := isIso₂_of_isIso₁₃ φ hT' hT
        (show IsIso e₁.hom from inferInstance) (show IsIso e₃.hom from inferInstance)
      exact ⟨@asIso _ _ _ _ _ this⟩

end Single

end CategoryTheory.Functor
