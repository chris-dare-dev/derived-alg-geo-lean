/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Torsion pairs in an abelian category

A **torsion pair** on an abelian category `A` is a pair of full subcategories
`(T, F)`, closed under isomorphism, such that

* every map from a torsion object to a torsion-free object is zero, and
* every object sits in a short exact sequence `0 → tX → X → fX → 0` with
  `tX ∈ T` and `fX ∈ F`.

**Mathlib does not have this at the pin.** Every `Torsion` file in Mathlib is
about torsion in algebra — `Algebra/Group/Torsion.lean`,
`GroupTheory/Torsion.lean`, `RingTheory/Flat/TorsionFree.lean` and so on. There
is no torsion pair, torsion theory, or torsion class for abelian categories.
So this is built from scratch rather than wrapped.

## Why this is here

A torsion pair in the heart of a t-structure is the input to Happel–Reiten–Smalø
tilting, which is in turn the engine behind every construction of stability
conditions on a surface. This file is the input datum and its elementary
theory; the tilt itself is a separate, much larger obligation and is **not**
formalised here.

Nothing in this file needs algebraic geometry, a triangulated category, or the
rest of `StabilityCondition/`. It is abelian-category theory and imports only
Mathlib.

## Main results

* `tors_iff` / `free_iff` — each class is exactly the orthogonal of the other.
  This is the standard rigidity of the definition: the decomposition axiom is
  what upgrades "mutually orthogonal" to "mutually *determining*".
* `free_of_mono` / `tors_of_epi` — `F` is closed under subobjects, `T` under
  quotients. Both fall straight out of `tors_iff`/`free_iff`.
* `tors_of_shortExact` / `free_of_shortExact` — both classes are closed under
  extensions.
-/

namespace CategoryTheory.Triangulated.Tilting

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

variable (A : Type*) [Category A] [Abelian A]

/-- A torsion pair on an abelian category. -/
structure TorsionPair where
  /-- the torsion class -/
  tors : ObjectProperty A
  /-- the torsion-free class -/
  free : ObjectProperty A
  tors_isClosedUnderIsomorphisms : tors.IsClosedUnderIsomorphisms := by infer_instance
  free_isClosedUnderIsomorphisms : free.IsClosedUnderIsomorphisms := by infer_instance
  /-- no nonzero map from a torsion object to a torsion-free one -/
  hom_eq_zero : ∀ ⦃X Y : A⦄, tors X → free Y → ∀ f : X ⟶ Y, f = 0
  /-- every object is an extension of a torsion-free object by a torsion one -/
  exists_shortExact : ∀ X : A, ∃ (T F : A) (i : T ⟶ X) (p : X ⟶ F) (w : i ≫ p = 0),
    tors T ∧ free F ∧ (ShortComplex.mk i p w).ShortExact

namespace TorsionPair

attribute [instance] tors_isClosedUnderIsomorphisms free_isClosedUnderIsomorphisms

variable {A}
variable (P : TorsionPair A)

/-- An object that is both torsion and torsion-free is zero. -/
theorem isZero_of_tors_of_free {X : A} (hT : P.tors X) (hF : P.free X) : IsZero X :=
  (IsZero.iff_id_eq_zero X).mpr (P.hom_eq_zero hT hF (𝟙 X))

/-- **The torsion class is exactly the left orthogonal of the torsion-free
class.** The decomposition axiom is what makes this an `iff` rather than the
one implication `hom_eq_zero` states. -/
theorem tors_iff (X : A) :
    P.tors X ↔ ∀ ⦃Y : A⦄, P.free Y → ∀ f : X ⟶ Y, f = 0 := by
  refine ⟨fun hX _ hY f => P.hom_eq_zero hX hY f, fun h => ?_⟩
  obtain ⟨T, F, i, p, w, hT, hF, hS⟩ := P.exists_shortExact X
  have hp : p = 0 := h hF p
  have : Mono i := hS.mono_f
  have : Epi i := hS.exact.epi_f hp
  have : IsIso i := isIso_of_mono_of_epi i
  exact prop_of_iso P.tors (asIso i) hT

/-- **The torsion-free class is exactly the right orthogonal of the torsion
class.** -/
theorem free_iff (Y : A) :
    P.free Y ↔ ∀ ⦃X : A⦄, P.tors X → ∀ f : X ⟶ Y, f = 0 := by
  refine ⟨fun hY _ hX f => P.hom_eq_zero hX hY f, fun h => ?_⟩
  obtain ⟨T, F, i, p, w, hT, hF, hS⟩ := P.exists_shortExact Y
  have hi : i = 0 := h hT i
  have : Epi p := hS.epi_g
  have : Mono p := hS.exact.mono_g hi
  have : IsIso p := isIso_of_mono_of_epi p
  exact prop_of_iso P.free (asIso p).symm hF

/-- The torsion-free class is closed under subobjects. -/
theorem free_of_mono {X Y : A} (i : X ⟶ Y) [Mono i] (hY : P.free Y) : P.free X := by
  rw [P.free_iff]
  intro T hT f
  have h : f ≫ i = 0 ≫ i := by rw [zero_comp]; exact P.hom_eq_zero hT hY _
  exact (cancel_mono i).mp h

/-- The torsion class is closed under quotients. -/
theorem tors_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] (hX : P.tors X) : P.tors Y := by
  rw [P.tors_iff]
  intro F hF f
  have h : p ≫ f = p ≫ 0 := by rw [comp_zero]; exact P.hom_eq_zero hX hF _
  exact (cancel_epi p).mp h

/-- The torsion class is closed under extensions. -/
theorem tors_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : P.tors S.X₁) (h₃ : P.tors S.X₃) : P.tors S.X₂ := by
  rw [P.tors_iff]
  intro Y hY f
  obtain ⟨g, hg⟩ :=
    CokernelCofork.IsColimit.desc' hS.gIsCokernel f (P.hom_eq_zero h₁ hY (S.f ≫ f))
  have hg0 : g = 0 := P.hom_eq_zero h₃ hY g
  simp only [CokernelCofork.π_ofπ] at hg
  rw [← hg, hg0, comp_zero]

/-- The torsion-free class is closed under extensions. -/
theorem free_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : P.free S.X₁) (h₃ : P.free S.X₃) : P.free S.X₂ := by
  rw [P.free_iff]
  intro T hT f
  obtain ⟨g, hg⟩ :=
    KernelFork.IsLimit.lift' hS.fIsKernel f (P.hom_eq_zero hT h₃ (f ≫ S.g))
  have hg0 : g = 0 := P.hom_eq_zero hT h₁ g
  simp only [KernelFork.ι_ofι] at hg
  rw [← hg, hg0, zero_comp]

/-! ### Uniqueness of the decomposition

The short exact sequence in `exists_shortExact` is not extra data: its two ends
are determined up to isomorphism by `X`, because each is characterised by an
orthogonality condition the other class cannot satisfy. The statement below is
the piece that gets used — the torsion end is the largest torsion subobject. -/

/-- A torsion subobject of `X` factors through any torsion/torsion-free
decomposition of `X`: the torsion end is *maximal* among torsion subobjects. -/
theorem exists_factor_of_tors {S : ShortComplex A} (hS : S.ShortExact)
    (h₃ : P.free S.X₃) {T : A} (hT : P.tors T) (f : T ⟶ S.X₂) :
    ∃ g : T ⟶ S.X₁, g ≫ S.f = f := by
  obtain ⟨g, hg⟩ :=
    KernelFork.IsLimit.lift' hS.fIsKernel f (P.hom_eq_zero hT h₃ (f ≫ S.g))
  simp only [KernelFork.ι_ofι] at hg
  exact ⟨g, hg⟩

/-! ### Non-vacuity

A `structure` with no inhabitant makes every theorem above vacuously true, so
the two degenerate torsion pairs are constructed rather than asserted to exist.
They are also the extremes the general theory is bracketed by. -/

open ZeroObject in
variable (A) in
/-- The torsion pair in which every object is torsion and only the zero objects
are torsion-free. -/
def allTors : TorsionPair A where
  tors _ := True
  free X := IsZero X
  tors_isClosedUnderIsomorphisms := ⟨fun _ _ => trivial⟩
  free_isClosedUnderIsomorphisms := ⟨fun e hX => IsZero.of_iso hX e.symm⟩
  hom_eq_zero := by
    intro _ _ _ hY f
    exact hY.eq_of_tgt f 0
  exists_shortExact X := by
    have hepi : Epi (0 : X ⟶ (0 : A)) := ⟨fun g h _ => (isZero_zero A).eq_of_src g h⟩
    refine ⟨X, 0, 𝟙 X, 0, comp_zero, trivial, isZero_zero A, ?_⟩
    exact { exact := (ShortComplex.exact_iff_epi _ rfl).mpr inferInstance
            mono_f := inferInstance
            epi_g := hepi }

open ZeroObject in
variable (A) in
/-- The torsion pair in which only the zero objects are torsion and every
object is torsion-free. -/
def allFree : TorsionPair A where
  tors X := IsZero X
  free _ := True
  tors_isClosedUnderIsomorphisms := ⟨fun e hX => IsZero.of_iso hX e.symm⟩
  free_isClosedUnderIsomorphisms := ⟨fun _ _ => trivial⟩
  hom_eq_zero := by
    intro _ _ hX _ f
    exact hX.eq_of_src f 0
  exists_shortExact X := by
    have hmono : Mono (0 : (0 : A) ⟶ X) := ⟨fun g h _ => (isZero_zero A).eq_of_tgt g h⟩
    refine ⟨0, X, 0, 𝟙 X, zero_comp, isZero_zero A, trivial, ?_⟩
    exact { exact := (ShortComplex.exact_iff_mono _ rfl).mpr inferInstance
            mono_f := hmono
            epi_g := inferInstance }

end TorsionPair

end CategoryTheory.Triangulated.Tilting
