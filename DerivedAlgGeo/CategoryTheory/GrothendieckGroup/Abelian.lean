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

## Main definitions

* `CategoryTheory.abelianPresentation`: the objects of `A`, related by its short
  exact sequences, as a `GrothendieckPresentation`.
* `CategoryTheory.K₀Ab` and `CategoryTheory.K₀Ab.of`: the Grothendieck group
  and the class of an object.
* `CategoryTheory.K₀Ab.lift` and `CategoryTheory.K₀Ab.liftOf`: the universal
  additive map out of `K₀Ab`, with additivity supplied as an instance or as a
  proof.

## Main results

* `CategoryTheory.K₀Ab.of_shortExact` — the defining relation;
* `CategoryTheory.K₀Ab.of_isZero` and `CategoryTheory.K₀Ab.of_iso` — proved, not
  assumed;
* `CategoryTheory.K₀Ab.lift_of`, `CategoryTheory.K₀Ab.liftOf_of` and
  `CategoryTheory.K₀Ab.hom_ext` — the universal property, inherited from
  `GrothendieckPresentation`.

## Implementation notes

### Why the abelian instantiation

`GrothendieckPresentation` (`Presentation.lean`) is generic in its generator and
relation types — it mentions no category at all.  Its instantiation at
distinguished triangles is `K₀` (`Triangulated/GrothendieckGroup/Basic.lean`);
its instantiation at short exact sequences is this file, and it takes three
lines.  A function on objects together
with vanishing on zero objects, invariance under isomorphism and additivity on
short exact sequences **is** an additive map out of `K₀Ab`, and nothing else.

With `K₀Ab` those three properties are not data.  `of_isZero`, `of_iso` and
`of_shortExact` are theorems here, proved once, and every consumer gets them
through `AddMonoidHom` instead of restating them.

### Placement

This file and `Presentation.lean` sit under `CategoryTheory/GrothendieckGroup/`
because neither consumes anything triangulated.  `K₀` itself, built on
`distTriang`, stays under `Triangulated/GrothendieckGroup/`, where it belongs.

The rule that places them — *a file belongs under `Triangulated/` only if it
uses something triangulated* — is the same one that puts `heartDatum` beside the
class datum it instantiates rather than beside the weak stability conditions
that consume it.

## References

The library's `GrothendieckPresentation`, and Mathlib's `ShortComplex.ShortExact`.

## Tags

Grothendieck group, abelian category, short exact sequence, universal property
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

Only *additivity* is required: `of_isZero` and `of_iso` give vanishing on zero
objects and invariance under isomorphism for free, so a producer supplies one
proof rather than three fields. -/
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
