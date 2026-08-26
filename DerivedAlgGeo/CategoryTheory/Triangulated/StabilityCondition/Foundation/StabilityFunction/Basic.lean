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

/-- **Strict positivity**, as a predicate on a charge rather than a structure
field.  Stating it this way is what lets the weak and strict theories share one
carrier: they are two predicates on the same `K₀Ab A →+ ℂ`, not two structures
with duplicated formal fields. -/
def IsStabilityCharge {A : Type u} [Category.{v} A] [Abelian A]
    (Z : K₀Ab A →+ ℂ) : Prop :=
  ∀ E : A, ¬IsZero E → Z (K₀Ab.of E) ∈ semiClosedUpperHalfPlane

/-- **Weak positivity**: the same statement with `0` allowed on the real axis. -/
def IsWeakStabilityCharge {A : Type u} [Category.{v} A] [Abelian A]
    (Z : K₀Ab A →+ ℂ) : Prop :=
  ∀ E : A, ¬IsZero E → Z (K₀Ab.of E) ∈ closedUpperHalfPlane

/-- An additive central charge on an abelian category whose nonzero values lie
in the semi-closed upper half-plane.

The charge is an `AddMonoidHom` out of `K₀Ab A`, not a bare function on objects
with `map_zero` / `map_iso` / `additive` carried as fields.  Those three fields
were exactly the universal property of the Grothendieck group written out
longhand; they are now theorems (`map_zero`, `map_iso`, `additive` below) proved
once in `CategoryTheory/GrothendieckGroup/Abelian.lean`, and every consumer keeps
its existing call shape.

`charge` remains available as an abbreviation, so `Z.charge E` still means what
it always did. -/
structure StabilityFunction where
  /-- The central charge, as a hom out of the Grothendieck group. -/
  Z : K₀Ab A →+ ℂ
  /-- Every nonzero object has charge in the allowed half-plane. -/
  nonzero_mem : IsStabilityCharge Z

variable {A}

/-- **Strict implies weak.**  With positivity a predicate this is one line;
between two structures it needed a `toWeak` definition of its own. -/
theorem IsStabilityCharge.weak {Z : K₀Ab A →+ ℂ} (h : IsStabilityCharge Z) :
    IsWeakStabilityCharge Z :=
  fun E hE ↦ semiClosedUpperHalfPlane_subset_closed (h E hE)

variable (A)

/-- A **weak** stability function on an abelian category: an additive charge
whose nonzero values lie in the closed upper half-plane.

This is what a polarised **surface** gives to `Coh X` through μ-slope: a
skyscraper has zero rank and zero degree, so its charge is `0`, which the strict
condition forbids and this one allows. -/
structure WeakStabilityFunction where
  /-- The central charge, as a hom out of the Grothendieck group. -/
  Z : K₀Ab A →+ ℂ
  /-- Every nonzero object has charge in the closed upper half-plane. -/
  nonzero_mem : IsWeakStabilityCharge Z

namespace StabilityFunction

variable {A}

/-- **Every stability function is a weak one.** -/
def toWeak (Z : StabilityFunction A) : WeakStabilityFunction A where
  Z := Z.Z
  nonzero_mem := Z.nonzero_mem.weak

@[simp]
theorem toWeak_Z (Z : StabilityFunction A) : Z.toWeak.Z = Z.Z := rfl

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
  simp only [StabilityFunction.mk.injEq]
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
