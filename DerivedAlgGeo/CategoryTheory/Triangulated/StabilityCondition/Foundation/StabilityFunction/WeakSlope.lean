/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.PhaseGeometry

/-!
# μ-slope on a surface: the weak slope data

`SlopeData` is the **curve** case, and its own docstring says so: its field
`degree_pos_of_rank_zero` is false on a surface, where a skyscraper has `c₁ = 0`
and hence degree `0`. This file supplies the structure a surface lane may
instantiate.

## The single difference

```
SlopeData      degree_pos_of_rank_zero    : … → 0 < degree E
WeakSlopeData  degree_nonneg_of_rank_zero : … → 0 ≤ degree E
```

That `0 ≤` in place of `0 <` is the whole of the weakening, and it is exactly the
skyscraper: rank zero and degree zero, so charge `0`, which
`semiClosedUpperHalfPlane` excludes and `closedUpperHalfPlane` admits. The charge
is therefore a `WeakStabilityFunctionOn (abelianDatum A)` and not a
`StabilityFunctionOn (abelianDatum A)`.

`SlopeData.toWeakSlopeData` (in `Slope.lean`) forgets `0 < d` to `0 ≤ d`, so this
is a genuine weakening with the curve case as an instance, not a second parallel
structure.

## The order bridge survives

`phase_le_iff_slope_le` carries a **positive-rank** hypothesis on both objects,
and at positive rank the charge lies in the *open* upper half-plane, where the
argument behaves exactly as it does in the strict theory. Nothing in that proof
touches the degree hypothesis: it goes through `phaseCross` and the sign of
`rank E * degree F - degree E * rank F`. So the order bridge is stated once here,
and `SlopeData` inherits it through `toWeakSlopeData`.

## What breaks, and why that is the content rather than a defect

`SlopeCutoff.lean`'s chain does **not** survive. `phase_eq_one_of_rank_zero` and
`mem_hnTors_of_rank_zero` both derive from `degree_pos_of_rank_zero`: a rank-zero
object of positive degree lands on the negative real axis, so has phase one, so
lies in `T β` for every `β < 1`. With only `0 ≤ degree` a degree-zero rank-zero
object — the skyscraper — has charge exactly `0`, and `arg 0 = 0`, so it has **no
phase** and cannot be placed by any phase comparison.

That is not a gap to route around with an extra hypothesis. It is the
mathematical content of the weakening, and it is why the weak Harder–Narasimhan
theory (`WeakAbelianHNFiltration`, `Weak/HarderNarasimhan/Heart.lean`) exists. On
a K3 surface the skyscrapers are precisely the objects the surface case is about,
so a hypothesis excluding them would exclude the subject.

## What is supplied and what is proved

`rank_nonneg` and `degree_nonneg_of_rank_zero` are **fields**: they are the
geometric input, unprovable here because `A` is an arbitrary abelian category.
Everything else in this file is proved. Unlike `SlopeData`'s
`degree_pos_of_rank_zero`, both fields *do* hold on a polarised surface, so the
structure has geometric inhabitants.

This file delivers the charge and the slope order on a surface. It does **not**
deliver a cutoff to read them against: `hnTorsProperty`, `hnFreeProperty` and
`hnTorsionPair` are all defined on the strict `StabilityFunction`, and there are
no weak counterparts yet.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Rank and degree data on an abelian category, in the form a polarised
**surface** supplies: rank is nonnegative, and a nonzero object of rank zero has
degree at least zero. See the module docstring — the single difference from
`SlopeData` is `0 ≤` where it has `0 <`, and that is exactly the skyscraper. -/
structure WeakSlopeData (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The rank, as a hom out of the Grothendieck group. -/
  rankHom : K₀Ab A →+ ℤ
  /-- The degree, as a hom out of the Grothendieck group. -/
  degreeHom : K₀Ab A →+ ℤ
  /-- Rank is nonnegative — geometric input. -/
  rank_nonneg : ∀ E : A, 0 ≤ rankHom (K₀Ab.of E)
  /-- A nonzero object of rank zero has nonnegative degree — geometric input,
  and what puts torsion sheaves on the *closed* nonpositive real axis rather
  than the strictly negative one. **True on a surface**, where a skyscraper has
  `c₁ = 0` and so degree `0`. -/
  degree_nonneg_of_rank_zero : ∀ E : A, ¬IsZero E → rankHom (K₀Ab.of E) = 0 →
    0 ≤ degreeHom (K₀Ab.of E)

namespace WeakSlopeData

variable (D : WeakSlopeData A)

/-- The rank of an object. -/
abbrev rank (E : A) : ℤ := D.rankHom (K₀Ab.of E)

/-- The degree of an object. -/
abbrev degree (E : A) : ℤ := D.degreeHom (K₀Ab.of E)

/-! ### The six formal properties

These are `K₀Ab.of_isZero`, `of_iso` and `of_shortExact` composed with a hom, so
they are free of both geometric fields. The names and argument shapes match
`SlopeData`'s. -/

theorem rank_zero (E : A) (hE : IsZero E) : D.rank E = 0 := by
  rw [rank, K₀Ab.of_isZero hE, map_zero]

theorem degree_zero (E : A) (hE : IsZero E) : D.degree E = 0 := by
  rw [degree, K₀Ab.of_isZero hE, map_zero]

theorem rank_iso {E F : A} (e : E ≅ F) : D.rank E = D.rank F := by
  rw [rank, rank, K₀Ab.of_iso e]

theorem degree_iso {E F : A} (e : E ≅ F) : D.degree E = D.degree F := by
  rw [degree, degree, K₀Ab.of_iso e]

theorem rank_additive (S : ShortComplex A) (hS : S.ShortExact) :
    D.rank S.X₂ = D.rank S.X₁ + D.rank S.X₃ := by
  rw [rank, rank, rank, K₀Ab.of_shortExact S hS, map_add]

theorem degree_additive (S : ShortComplex A) (hS : S.ShortExact) :
    D.degree S.X₂ = D.degree S.X₁ + D.degree S.X₃ := by
  rw [degree, degree, degree, K₀Ab.of_shortExact S hS, map_add]

/-- The charge `-degree + i * rank`. -/
def charge (E : A) : ℂ := ⟨-(D.degree E : ℝ), (D.rank E : ℝ)⟩

@[simp] theorem charge_re (E : A) : (D.charge E).re = -(D.degree E : ℝ) := rfl

@[simp] theorem charge_im (E : A) : (D.charge E).im = (D.rank E : ℝ) := rfl

/-- A nonzero object has charge in the **closed** upper half-plane. Two cases,
both immediate: positive rank gives `0 < im`, the first disjunct; rank zero gives
`im = 0` together with `re = -degree ≤ 0`, the second. A skyscraper realises the
boundary case `charge = 0`, which is why the half-plane here must be the closed
one. -/
theorem charge_mem_closedUpperHalfPlane {E : A} (hE : ¬IsZero E) :
    D.charge E ∈ closedUpperHalfPlane := by
  rcases lt_or_eq_of_le (D.rank_nonneg E) with hpos | hzero
  · left
    simpa using (by exact_mod_cast hpos : (0 : ℝ) < (D.rank E : ℝ))
  · right
    refine ⟨by simpa using (by exact_mod_cast hzero.symm : ((D.rank E : ℤ) : ℝ) = 0), ?_⟩
    have hdeg : 0 ≤ D.degree E := D.degree_nonneg_of_rank_zero E hE hzero.symm
    have : (0 : ℝ) ≤ (D.degree E : ℝ) := by exact_mod_cast hdeg
    simpa using this

/-- **μ-slope on a surface is a weak stability function.**

There is no `WeakStabilityFunction A` abbreviation to land in: the name
`WeakStabilityFunction` is already taken, by the t-structure-indexed structure in
`Weak/Basic/Definitions.lean`. The datum is written out instead. -/
noncomputable def toWeakStabilityFunction : WeakStabilityFunctionOn (abelianDatum A) where
  Z := K₀Ab.liftOf D.charge (fun S hS ↦ by
    apply Complex.ext
    · simp [D.degree_additive S hS]
      ring
    · simp [D.rank_additive S hS])
  nonzero_mem E hE := by
    rw [abelianDatum_cl, K₀Ab.liftOf_of]
    exact D.charge_mem_closedUpperHalfPlane hE

@[simp]
theorem toWeakStabilityFunction_Z (E : A) :
    D.toWeakStabilityFunction.Z (K₀Ab.of E) = D.charge E := by
  simp [toWeakStabilityFunction]

/-- The **slope** `degree / rank`. It is junk at rank zero, where the classical
slope is `+∞`; every statement below asks for positive rank. -/
def slope (E : A) : ℝ := (D.degree E : ℝ) / (D.rank E : ℝ)

/-- The **phase**, normalised to `(0, 1]` on objects of nonzero charge. Unlike
the strict theory's `StabilityFunction.phase`, this is *not* positive on every
nonzero object: a skyscraper has charge `0` and so phase `0`. -/
def phase (E : A) : ℝ := arg (D.charge E) / Real.pi

theorem phase_eq_arg_div_pi (E : A) :
    D.phase E = arg (D.toWeakStabilityFunction.Z (K₀Ab.of E)) / Real.pi := by
  rw [phase, toWeakStabilityFunction_Z]

theorem phaseCross_charge (E F : A) :
    phaseCross (D.charge E) (D.charge F)
      = (D.rank E : ℝ) * (D.degree F : ℝ) - (D.degree E : ℝ) * (D.rank F : ℝ) := by
  simp [phaseCross]
  ring

theorem charge_ne_zero_of_rank_pos {E : A} (hE : 0 < D.rank E) : D.charge E ≠ 0 := by
  intro h
  have him : (D.charge E).im = 0 := by rw [h]; rfl
  rw [charge_im] at him
  have : (0 : ℝ) < (D.rank E : ℝ) := by exact_mod_cast hE
  linarith

theorem arg_pos_of_rank_pos {E : A} (hE : 0 < D.rank E) : 0 < arg (D.charge E) := by
  refine arg_pos_of_mem_semiClosedUpperHalfPlane ?_
  left
  have : (0 : ℝ) < (D.rank E : ℝ) := by exact_mod_cast hE
  simpa using this

/-- **The phase order is the slope order** on objects of positive rank, on a
surface exactly as on a curve.

At positive rank the charge lies in the *open* upper half-plane, so the degree
field plays no part: the proof runs through `phaseCross`, whose value
`rank E * degree F - degree E * rank F` is nonnegative exactly when
`degree E / rank E ≤ degree F / rank F`. This is the statement `SlopeData`
inherits through `SlopeData.toWeakSlopeData`. -/
theorem phase_le_iff_slope_le {E F : A} (hE : 0 < D.rank E) (hF : 0 < D.rank F) :
    D.phase E ≤ D.phase F ↔ D.slope E ≤ D.slope F := by
  have hEr : (0 : ℝ) < (D.rank E : ℝ) := by exact_mod_cast hE
  have hFr : (0 : ℝ) < (D.rank F : ℝ) := by exact_mod_cast hF
  have hcross : 0 ≤ phaseCross (D.charge E) (D.charge F) ↔ D.slope E ≤ D.slope F := by
    rw [phaseCross_charge, slope, slope, div_le_div_iff₀ hEr hFr]
    constructor <;> intro h <;> linarith
  have harg : arg (D.charge E) ≤ arg (D.charge F) ↔ D.slope E ≤ D.slope F := by
    refine ⟨fun h => hcross.mp ?_, fun h => ?_⟩
    · refine phaseCross_nonneg_of_arg_le ?_ (D.charge_ne_zero_of_rank_pos hE)
        (D.charge_ne_zero_of_rank_pos hF) h
      simpa using hEr.le
    · exact arg_le_of_phaseCross_nonneg (D.charge_ne_zero_of_rank_pos hE)
        (D.charge_ne_zero_of_rank_pos hF) (D.arg_pos_of_rank_pos hF) (hcross.mpr h)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [phase, phase]
  constructor
  · intro h
    refine harg.mp ?_
    have hmul := mul_le_mul_of_nonneg_right h hpi.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi), div_mul_cancel₀ _ (ne_of_gt hpi)] at hmul
  · intro h
    have hle := harg.mpr h
    gcongr

end WeakSlopeData

end CategoryTheory.Triangulated
