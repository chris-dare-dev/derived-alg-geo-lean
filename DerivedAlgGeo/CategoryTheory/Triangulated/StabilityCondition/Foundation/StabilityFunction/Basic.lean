/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Stability functions on abelian categories

This file introduces the repository-owned stability-function interface.  Its
central charge is additive on short exact sequences and sends every nonzero
object to the semi-closed upper half-plane.  Phase, stability, and
semistability are then defined intrinsically from that charge.

The module is Mathlib-only and is the canonical stability-function interface
for this repository.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe u v

namespace CategoryTheory.Triangulated

/-- The semi-closed upper half-plane used for central charges: positive
imaginary part together with the negative real axis. -/
def semiClosedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re < 0}

theorem semiClosedUpperHalfPlane_ne_zero {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : z ≠ 0 := by
  rcases hz with him | ⟨him, hre⟩
  · exact ne_of_apply_ne im him.ne'
  · exact ne_of_apply_ne re hre.ne

/-- The **closed** upper half-plane: the weak condition, which unlike
`semiClosedUpperHalfPlane` contains `0`.  That single difference is the whole of
the weak/strict distinction, and it is why μ-slope stability on a surface is weak
— a skyscraper has zero rank and zero degree, so its μ-charge is `0`. -/
def closedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re ≤ 0}

theorem semiClosedUpperHalfPlane_subset_closed :
    semiClosedUpperHalfPlane ⊆ closedUpperHalfPlane :=
  fun _ hz ↦ hz.imp id (fun h ↦ ⟨h.1, h.2.le⟩)

theorem arg_pos_of_mem_semiClosedUpperHalfPlane {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : 0 < arg z := by
  rcases hz with him | ⟨him, hre⟩
  · refine lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) ?_
    exact fun h => him.ne' (arg_eq_zero_iff.mp h.symm).2
  · have hz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
    rw [hz, arg_ofReal_of_neg hre]
    exact Real.pi_pos

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- **What a positivity condition needs to know about a category.**

A charge condition speaks about *some* objects (the nonzero ones, or the nonzero
ones lying in a heart) and reads their class in *some* abelian group.  Those two
choices are the only thing that varies between the abelian-category theory and
the ambient/t-structure theory, so they are the parameters.

Making this a parameter rather than baking `K₀Ab` in is what stops the two
theories being two structures with the same fields: they are one structure at two
class data. -/
structure ClassDatum (O : Type*) (G : Type*) [AddCommGroup G] where
  /-- The objects the positivity condition speaks about. -/
  Relevant : O → Prop
  /-- The class of an object. -/
  cl : O → G

variable {O : Type*} {G : Type*} [AddCommGroup G]

/-- A charge is positive for `D` into `P` when every relevant object's class has
charge in `P`. -/
def IsPositive (D : ClassDatum O G) (P : Set ℂ) (Z : G →+ ℂ) : Prop :=
  ∀ E : O, D.Relevant E → Z (D.cl E) ∈ P

/-- **Strict positivity** — the half-plane that excludes `0`. -/
abbrev IsStabilityCharge (D : ClassDatum O G) (Z : G →+ ℂ) : Prop :=
  IsPositive D semiClosedUpperHalfPlane Z

/-- **Weak positivity** — the same with `0` allowed on the real axis. -/
abbrev IsWeakStabilityCharge (D : ClassDatum O G) (Z : G →+ ℂ) : Prop :=
  IsPositive D closedUpperHalfPlane Z

/-- **Strict implies weak**, once and for every class datum. -/
theorem IsStabilityCharge.weak {D : ClassDatum O G} {Z : G →+ ℂ}
    (h : IsStabilityCharge D Z) : IsWeakStabilityCharge D Z :=
  fun E hE ↦ semiClosedUpperHalfPlane_subset_closed (h E hE)

/-- **A stability function relative to a class datum.**  One structure; the
abelian and ambient theories are two instantiations of it. -/
structure StabilityFunctionOn (D : ClassDatum O G) where
  /-- The central charge, as a hom out of the class group. -/
  Z : G →+ ℂ
  /-- Relevant objects have charge in the strict half-plane. -/
  nonzero_mem : IsStabilityCharge D Z

/-- **A weak stability function relative to a class datum.** -/
structure WeakStabilityFunctionOn (D : ClassDatum O G) where
  /-- The central charge, as a hom out of the class group. -/
  Z : G →+ ℂ
  /-- Relevant objects have charge in the closed half-plane. -/
  nonzero_mem : IsWeakStabilityCharge D Z

/-- **Every stability function is a weak one**, at any class datum. -/
def StabilityFunctionOn.toWeak {D : ClassDatum O G} (Z : StabilityFunctionOn D) :
    WeakStabilityFunctionOn D where
  Z := Z.Z
  nonzero_mem := Z.nonzero_mem.weak

@[simp]
theorem StabilityFunctionOn.toWeak_Z {D : ClassDatum O G} (Z : StabilityFunctionOn D) :
    Z.toWeak.Z = Z.Z := rfl

/-- The class datum of an abelian category: nonzero objects, classes in `K₀Ab`. -/
def abelianDatum : ClassDatum A (K₀Ab A) where
  Relevant E := ¬IsZero E
  cl := K₀Ab.of

/-- **An additive central charge on an abelian category** whose nonzero values
lie in the semi-closed upper half-plane.

This is `StabilityFunctionOn` at `abelianDatum`, not a structure of its own.
`charge` remains available as an abbreviation and `map_zero` / `map_iso` /
`additive` remain available as theorems, so consumers are unaffected. -/
abbrev StabilityFunction := StabilityFunctionOn (abelianDatum A)

variable {A}

@[simp]
theorem abelianDatum_cl (E : A) : (abelianDatum A).cl E = K₀Ab.of E := rfl

@[simp]
theorem abelianDatum_relevant (E : A) : (abelianDatum A).Relevant E ↔ ¬IsZero E := Iff.rfl

variable (A)

namespace StabilityFunction

variable {A}

/-- The central charge on objects. -/
abbrev charge (Z : StabilityFunction A) (E : A) : ℂ := Z.Z (K₀Ab.of E)

@[simp]
theorem charge_apply (Z : StabilityFunction A) (E : A) :
    Z.charge E = Z.Z (K₀Ab.of E) := rfl

/-- **Zero objects have zero charge** — a theorem now, not a field. -/
theorem map_zero (Z : StabilityFunction A) (E : A) (hE : IsZero E) :
    Z.charge E = 0 := by
  rw [charge_apply, K₀Ab.of_isZero hE]
  exact Z.Z.map_zero

/-- **Isomorphic objects have the same charge** — a theorem now, not a field. -/
theorem map_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.charge E = Z.charge F := by
  rw [charge_apply, charge_apply, K₀Ab.of_iso e]

/-- **The charge is additive on short exact sequences** — a theorem now, not a
field. -/
theorem additive (Z : StabilityFunction A) (S : ShortComplex A) (hS : S.ShortExact) :
    Z.charge S.X₂ = Z.charge S.X₁ + Z.charge S.X₃ := by
  rw [charge_apply, charge_apply, charge_apply, K₀Ab.of_shortExact S hS, map_add]

/-- Two stability functions with the same charge on objects are equal.  This now
needs `K₀Ab.hom_ext` rather than structure eta: equal charges on generators is
what forces the two homs to agree. -/
@[ext]
theorem ext {Z W : StabilityFunction A} (hcharge : Z.charge = W.charge) : Z = W := by
  obtain ⟨Z, _⟩ := Z
  obtain ⟨W, _⟩ := W
  simp only [StabilityFunctionOn.mk.injEq]
  exact K₀Ab.hom_ext (fun X ↦ congrFun hcharge X)

/-- The phase of an object, normalized to lie in `(0, 1]` when the object is
nonzero.  The phase of a zero object is `0`. -/
def phase (Z : StabilityFunction A) (E : A) : ℝ :=
  arg (Z.charge E) / Real.pi

theorem phase_pos (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E) :
    0 < Z.phase E := by
  exact div_pos
    (arg_pos_of_mem_semiClosedUpperHalfPlane (Z.nonzero_mem E hE))
    Real.pi_pos

theorem phase_le_one (Z : StabilityFunction A) (E : A) : Z.phase E ≤ 1 := by
  exact div_le_one_of_le₀ (arg_le_pi (Z.charge E)) Real.pi_pos.le

theorem phase_mem_Ioc (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E) :
    Z.phase E ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨Z.phase_pos E hE, Z.phase_le_one E⟩

/-- A nonzero object is semistable when no nonzero subobject has larger
phase. -/
def IsSemistable (Z : StabilityFunction A) (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) →
    Z.phase (B : A) ≤ Z.phase E

/-- A nonzero object is stable when every nonzero proper subobject has strictly
smaller phase. -/
def IsStable (Z : StabilityFunction A) (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) → B ≠ ⊤ →
    Z.phase (B : A) < Z.phase E

theorem exists_destabilizing_of_not_semistable (Z : StabilityFunction A)
    (E : A) (hE : ¬IsZero E) (h : ¬Z.IsSemistable E) :
    ∃ B : Subobject E, ¬IsZero (B : A) ∧ Z.phase E < Z.phase (B : A) := by
  simp only [IsSemistable, not_and_or, not_forall, not_le, exists_prop] at h
  rcases h with h | ⟨B, hB, hphase⟩
  · exact absurd hE h
  · exact ⟨B, hB, hphase⟩

theorem charge_eq_of_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.charge E = Z.charge F :=
  Z.map_iso e

theorem phase_eq_of_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.phase E = Z.phase F := by
  simp only [phase, Z.charge_eq_of_iso e]

theorem isSemistable_of_iso (Z : StabilityFunction A) {E F : A}
    (e : E ≅ F) (h : Z.IsSemistable E) : Z.IsSemistable F := by
  refine ⟨fun hF => h.1 (hF.of_iso e), fun B hB => ?_⟩
  let B' : Subobject E := Subobject.mk (B.arrow ≫ e.inv)
  have hB' : ¬IsZero (B' : A) := by
    intro hzero
    exact hB (hzero.of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv)).symm)
  have hle := h.2 B' hB'
  rw [Z.phase_eq_of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv))] at hle
  rwa [Z.phase_eq_of_iso e] at hle

theorem isSemistable_iff_of_iso (Z : StabilityFunction A) {E F : A}
    (e : E ≅ F) : Z.IsSemistable E ↔ Z.IsSemistable F :=
  ⟨Z.isSemistable_of_iso e, Z.isSemistable_of_iso e.symm⟩

end StabilityFunction

end CategoryTheory.Triangulated
