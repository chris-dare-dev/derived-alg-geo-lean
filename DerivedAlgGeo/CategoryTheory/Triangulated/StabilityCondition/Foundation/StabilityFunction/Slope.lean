/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.PhaseGeometry

/-!
# Slope stability is a stability function

Rank and degree data on an abelian category — what a polarised **curve** gives to
`Coh X`, with `degree` the usual degree — determine the charge

```
Z (E) = -degree E + i * rank E
```

and **that charge is a stability function**: it is additive on short exact
sequences because rank and degree are, and a nonzero object lands in the
semi-closed upper half-plane because rank is nonnegative and a nonzero object of
rank zero has positive degree.

So μ-slope stability is not a parallel theory: it is the repository's own
`StabilityFunction`, and the phase, semistability, and Harder–Narasimhan
machinery already built on that interface applies to it unchanged.

## The order bridge

`phase_le_iff_slope_le`: on objects of positive rank the phase order **is** the
slope order. The computation is one line through `phaseCross`,

```
phaseCross (Z E) (Z F) = rank E * degree F - degree E * rank F,
```

which is nonnegative exactly when `degree E / rank E ≤ degree F / rank F`. That
is what lets a torsion pair cut by a slope be read as one cut by a phase, which
is the form the tilting machinery consumes.

## What is data and what is proved

`rank_nonneg` and `degree_pos_of_rank_zero` are **fields**: they are the
geometric input, not provable here, since `A` is an arbitrary abelian category.

**They are the CURVE case, not the surface case, and an earlier version of this
docstring said surface.** On a curve a nonzero torsion sheaf has degree equal to
its length, which is positive. On a **surface** it is false: a dimension-zero
sheaf — a skyscraper — has `c₁ = 0`, hence `degree = c₁ · ω = 0`, so
`degree_pos_of_rank_zero` fails on exactly those objects.

The consequence is not cosmetic. μ-slope on a surface is a **weak** stability
function, not a stability function: a skyscraper has zero rank and zero degree, so
its charge is `0`, which `semiClosedUpperHalfPlane` excludes. That is why the weak
theory exists, and it is why a surface lane must not instantiate `SlopeData`.

The slope itself is `degree / rank`, which is junk at rank zero where the
classical slope is `+∞`; every statement about it carries a positive-rank
hypothesis, and the torsion sheaves are handled by the charge rather than by the
slope.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Rank and degree data on an abelian category: what a polarised **curve** gives
to its category of coherent sheaves. See the module docstring — on a surface
`degree_pos_of_rank_zero` is false for skyscrapers. -/
structure SlopeData (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The rank. -/
  rank : A → ℤ
  /-- The degree, `c₁ · ω` in the geometric case. -/
  degree : A → ℤ
  /-- Rank is nonnegative — geometric input. -/
  rank_nonneg : ∀ E : A, 0 ≤ rank E
  /-- Zero objects have rank zero. -/
  rank_zero : ∀ E : A, IsZero E → rank E = 0
  /-- Zero objects have degree zero. -/
  degree_zero : ∀ E : A, IsZero E → degree E = 0
  /-- Rank is an isomorphism invariant. -/
  rank_iso : ∀ {E F : A}, (E ≅ F) → rank E = rank F
  /-- Degree is an isomorphism invariant. -/
  degree_iso : ∀ {E F : A}, (E ≅ F) → degree E = degree F
  /-- Rank is additive on short exact sequences. -/
  rank_additive : ∀ S : ShortComplex A, S.ShortExact → rank S.X₂ = rank S.X₁ + rank S.X₃
  /-- Degree is additive on short exact sequences. -/
  degree_additive : ∀ S : ShortComplex A, S.ShortExact → degree S.X₂ = degree S.X₁ + degree S.X₃
  /-- A nonzero object of rank zero has positive degree — geometric input, and
  what puts torsion sheaves on the negative real axis. -/
  degree_pos_of_rank_zero : ∀ E : A, ¬IsZero E → rank E = 0 → 0 < degree E

namespace SlopeData

variable (D : SlopeData A)

/-- The charge `-degree + i * rank`. -/
def charge (E : A) : ℂ := ⟨-(D.degree E : ℝ), (D.rank E : ℝ)⟩

@[simp] theorem charge_re (E : A) : (D.charge E).re = -(D.degree E : ℝ) := rfl

@[simp] theorem charge_im (E : A) : (D.charge E).im = (D.rank E : ℝ) := rfl

theorem charge_mem_semiClosedUpperHalfPlane {E : A} (hE : ¬IsZero E) :
    D.charge E ∈ semiClosedUpperHalfPlane := by
  rcases lt_or_eq_of_le (D.rank_nonneg E) with hpos | hzero
  · left
    simpa using (by exact_mod_cast hpos : (0 : ℝ) < (D.rank E : ℝ))
  · right
    refine ⟨by simpa using (by exact_mod_cast hzero.symm : ((D.rank E : ℤ) : ℝ) = 0), ?_⟩
    have hdeg : 0 < D.degree E := D.degree_pos_of_rank_zero E hE hzero.symm
    have : (0 : ℝ) < (D.degree E : ℝ) := by exact_mod_cast hdeg
    simpa using this

/-- **Slope stability is a stability function.**

`map_zero` and `map_iso` are gone: they were consequences of additivity all
along, and `K₀Ab` proves them once.  Only the additivity of `charge` on short
exact sequences is supplied here, and it is the same two-line computation the
`additive` field used to carry. -/
noncomputable def toStabilityFunction : StabilityFunction A where
  Z := K₀Ab.liftOf D.charge (fun S hS ↦ by
    apply Complex.ext
    · simp [D.degree_additive S hS]
      ring
    · simp [D.rank_additive S hS])
  nonzero_mem E hE := by
    rw [abelianDatum_cl, K₀Ab.liftOf_of]
    exact D.charge_mem_semiClosedUpperHalfPlane hE

@[simp]
theorem toStabilityFunction_charge (E : A) :
    D.toStabilityFunction.charge E = D.charge E := by
  simp [toStabilityFunction, StabilityFunction.charge, abelianDatum_cl]

/-- The **slope** `degree / rank`. It is junk at rank zero, where the classical
slope is `+∞`; every statement below asks for positive rank. -/
def slope (E : A) : ℝ := (D.degree E : ℝ) / (D.rank E : ℝ)

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

/-- **The phase order is the slope order** on objects of positive rank.

`phaseCross` turns the comparison of arguments into the sign of
`rank E * degree F - degree E * rank F`, which is the comparison of slopes once
both ranks are positive. -/
theorem phase_le_iff_slope_le {E F : A} (hE : 0 < D.rank E) (hF : 0 < D.rank F) :
    D.toStabilityFunction.phase E ≤ D.toStabilityFunction.phase F ↔ D.slope E ≤ D.slope F := by
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
  rw [StabilityFunction.phase, StabilityFunction.phase, toStabilityFunction_charge,
    toStabilityFunction_charge]
  constructor
  · intro h
    refine harg.mp ?_
    have hmul := mul_le_mul_of_nonneg_right h hpi.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi), div_mul_cancel₀ _ (ne_of_gt hpi)] at hmul
  · intro h
    have hle := harg.mpr h
    gcongr

end SlopeData

end CategoryTheory.Triangulated
