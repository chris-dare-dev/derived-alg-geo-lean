/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Presentation
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The Grothendieck group of an abelian category

`K₀Ab A` is the free abelian group on the objects of `A` modulo the relations
`[X₂] = [X₁] + [X₃]` coming from short exact sequences.

## Why this file did not exist, and what it replaces

`GrothendieckPresentation` (`Presentation.lean`) is generic in its generator and
relation types — it mentions no category at all — but it was instantiated only
once, at distinguished triangles (`Basic.lean`).  The abelian instantiation is
three lines, and its absence is why the repository grew several hand-rolled
copies of the same universal property written out longhand: a function on
objects together with `map_zero`, `map_iso` and `map_additive` fields **is**
an additive map out of `K₀Ab`, and nothing else.

With `K₀Ab` those three fields stop being data.  `of_isZero`, `of_iso` and
`of_shortExact` are theorems here, proved once, and every consumer gets them
through `AddMonoidHom` instead of restating them.

## Placement

This file sits under `Triangulated/GrothendieckGroup/` because that is where
`Presentation.lean` lives, and it consumes nothing triangulated.  Neither does
`Presentation.lean`.  The honest home for both is `CategoryTheory/GrothendieckGroup/`;
moving them is a rename of an existing directory and is deliberately not bundled
into this change.

## Main results

* `K₀Ab` and `K₀Ab.of`;
* `K₀Ab.of_shortExact` — the defining relation;
* `K₀Ab.of_isZero` and `K₀Ab.of_iso` — proved, not assumed;
* `K₀Ab.lift` / `K₀Ab.hom_ext` — the universal property, inherited from
  `GrothendieckPresentation`.
-/

universe v u

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits ZeroObject

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Objects of an abelian category, related by its short exact sequences. -/
abbrev abelianPresentation :
    GrothendieckPresentation A {S : ShortComplex A // S.ShortExact} where
  left := fun r ↦ r.1.X₁
  middle := fun r ↦ r.1.X₂
  right := fun r ↦ r.1.X₃

/-- **The Grothendieck group of an abelian category.** -/
abbrev K₀Ab : Type _ := (abelianPresentation A).Group

namespace K₀Ab

variable {A}

/-- The class of an object. -/
def of (X : A) : K₀Ab A := (abelianPresentation A).of X

/-- **The defining relation**: a short exact sequence splits the middle class. -/
theorem of_shortExact (S : ShortComplex A) (hS : S.ShortExact) :
    of S.X₂ = of S.X₁ + of S.X₃ :=
  (abelianPresentation A).of_relation ⟨S, hS⟩

/-- **A zero object has zero class.**  Proved from the short exact sequence
`X ⟶ X ⟶ X` on a zero object, which forces `[X] = [X] + [X]`. -/
theorem of_isZero {X : A} (hX : IsZero X) : of X = 0 := by
  have hzero : (𝟙 X) ≫ (𝟙 X) = 0 := by
    rw [Category.comp_id]; exact hX.eq_of_src _ _
  have hS : (ShortComplex.mk (𝟙 X) (𝟙 X) hzero).ShortExact :=
    { mono_f := inferInstance
      epi_g := inferInstance
      exact := ShortComplex.exact_of_isZero_X₂ _ hX }
  have h := of_shortExact _ hS
  simpa using h

@[simp]
theorem of_zero : of (0 : A) = 0 := of_isZero (isZero_zero A)

/-- **Isomorphic objects have the same class.**  Proved from the short exact
sequence `X ≅ Y ⟶ 0`, not assumed as a field. -/
theorem of_iso {X Y : A} (e : X ≅ Y) : of X = of Y := by
  have hzero : e.hom ≫ (0 : Y ⟶ 0) = 0 := by simp
  have hS : (ShortComplex.mk e.hom (0 : Y ⟶ (0 : A)) hzero).ShortExact :=
    { mono_f := inferInstance
      epi_g := (isZero_zero A).epi _
      exact := (ShortComplex.exact_iff_epi _ rfl).2 inferInstance }
  have h := of_shortExact _ hS
  simp only [of_zero, add_zero] at h
  exact h.symm

/-- The universal additive map out of `K₀Ab`. -/
def lift {G : Type*} [AddCommGroup G] (f : A → G)
    [(abelianPresentation A).IsAdditive f] : K₀Ab A →+ G :=
  (abelianPresentation A).lift f

@[simp]
theorem lift_of {G : Type*} [AddCommGroup G] (f : A → G)
    [(abelianPresentation A).IsAdditive f] (X : A) : lift f (of X) = f X :=
  (abelianPresentation A).lift_of f X

/-- **The universal property in the form producers actually want**: a function
on objects that is additive on short exact sequences induces a hom, with the
additivity supplied as a proof rather than as an instance.

This is what replaces a `map_zero` / `map_iso` / `additive` field triple. Note
that only *additivity* is required: `of_isZero` and `of_iso` then give the other
two for free, so a producer that used to carry three fields now carries one
proof. -/
noncomputable def liftOf {G : Type*} [AddCommGroup G] (f : A → G)
    (h : ∀ S : ShortComplex A, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) :
    K₀Ab A →+ G :=
  letI : (abelianPresentation A).IsAdditive f := ⟨fun r ↦ h r.1 r.2⟩
  lift f

@[simp]
theorem liftOf_of {G : Type*} [AddCommGroup G] (f : A → G)
    (h : ∀ S : ShortComplex A, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) (X : A) :
    liftOf f h (of X) = f X := by
  letI : (abelianPresentation A).IsAdditive f := ⟨fun r ↦ h r.1 r.2⟩
  exact lift_of f X

/-- Additive maps out of `K₀Ab` are determined by object classes. -/
@[ext 1100]
theorem hom_ext {G : Type*} [AddCommGroup G] {f g : K₀Ab A →+ G}
    (h : ∀ X : A, f (of X) = g (of X)) : f = g :=
  (abelianPresentation A).hom_ext h

end K₀Ab

end CategoryTheory
