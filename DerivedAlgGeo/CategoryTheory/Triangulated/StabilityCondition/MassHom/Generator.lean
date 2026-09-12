/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Basic
import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Generator reduction for mass--Hom bounds

The test objects satisfying a mass--Hom bound form a thick subcategory: the
property is invariant under shifts, closed under the middle term of a
distinguished triangle, and inherited by retracts.  The universal property of
`ObjectProperty.triangEnvelope` therefore extends a bound from a classical
generating collection to its thick envelope.

This is the generator half of Halpern--Leistner--Robotis,
arXiv:2501.00710v2, Lemma 2.8.  The stable-object half is kept in a separate
leaf because it needs Jordan--Hölder input rather than thick closure.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.SerreFunctor
open scoped ENNReal ZeroObject

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

noncomputable section

universe w v u u'

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [Pretriangulated C] [IsTriangulated C]
  [HomFinite k C]
variable {Λ : Type u'} [AddCommGroup Λ] {v₀ : K₀ C →+ Λ}
variable {σ : StabilityCondition.WithClassMap C v₀}
variable {A B D F : C}

namespace HasMassHomBoundFor

omit [IsTriangulated C] in
/-- The middle vector space of a finite-dimensional exact pair has dimension
at most the sum of the two outer dimensions. -/
private theorem finrank_middle_le_of_exact
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module k U] [Module k V] [Module k W]
    [Module.Finite k U] [Module.Finite k V] [Module.Finite k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : Function.Exact f g) :
    Module.finrank k V ≤ Module.finrank k U + Module.finrank k W := by
  have hrank := g.finrank_range_add_finrank_ker
  have hker : Module.finrank k (LinearMap.ker g) =
      Module.finrank k (LinearMap.range f) := by
    rw [h.linearMap_ker_eq]
  calc
    Module.finrank k V =
        Module.finrank k (LinearMap.range g) +
          Module.finrank k (LinearMap.ker g) := hrank.symm
    _ = Module.finrank k (LinearMap.range g) +
        Module.finrank k (LinearMap.range f) := by rw [hker]
    _ ≤ Module.finrank k W + Module.finrank k U :=
      Nat.add_le_add (LinearMap.range g).finrank_le f.finrank_range_le
    _ = Module.finrank k U + Module.finrank k W := Nat.add_comm _ _

omit [IsTriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- A retract of a test object inherits its mass--Hom bound. -/
theorem retract (hB : σ.HasMassHomBoundFor (k := k) B)
    (r : CategoryTheory.Retract A B) :
    σ.HasMassHomBoundFor (k := k) A := by
  obtain ⟨K, hK, hbound⟩ := hB
  refine ⟨K, hK, fun F ↦ ?_⟩
  have hinj : Function.Injective (Linear.leftComp k F r.r) := by
    refine Function.LeftInverse.injective (g := Linear.leftComp k F r.i) ?_
    intro f
    simp [← Category.assoc]
  have hdim : Module.finrank k (A ⟶ F) ≤ Module.finrank k (B ⟶ F) :=
    (Linear.leftComp k F r.r).finrank_le_finrank_of_injective hinj
  calc
    (Module.finrank k (A ⟶ F) : ℝ) ≤
        (Module.finrank k (B ⟶ F) : ℝ) := by exact_mod_cast hdim
    _ ≤ K * (stabilityMass σ F).toReal := hbound F

/-- Shifting a test object by any integer preserves its mass--Hom bound. -/
theorem shift (hA : σ.HasMassHomBoundFor (k := k) A) (n : ℤ) :
    σ.HasMassHomBoundFor (k := k) (A⟦n⟧) := by
  induction n using Int.induction_on with
  | zero =>
      exact hA.congr ((shiftFunctorZero C ℤ).app A).symm
  | succ n ih =>
      exact ih.shift_one.congr
        ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) (by omega)).app A).symm
  | pred n ih =>
      exact ih.shift_neg_one.congr
        ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ)
          (-(n : ℤ) - 1) rfl).app A).symm

omit [IsTriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- The zero object satisfies a mass--Hom bound with constant one. -/
theorem of_isZero (hA : IsZero A) :
    σ.HasMassHomBoundFor (k := k) A := by
  refine ⟨1, one_pos, fun F ↦ ?_⟩
  haveI : Subsingleton (A ⟶ F) := ⟨fun f g ↦ hA.eq_of_src f g⟩
  rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, one_mul]
  exact ENNReal.toReal_nonneg

omit [IsTriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- In a distinguished triangle, bounds for the first and third test objects
give a bound for the middle test object. -/
theorem triangle_middle (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : σ.HasMassHomBoundFor (k := k) T.obj₁)
    (h₃ : σ.HasMassHomBoundFor (k := k) T.obj₃) :
    σ.HasMassHomBoundFor (k := k) T.obj₂ := by
  obtain ⟨K₁, hK₁, hb₁⟩ := h₁
  obtain ⟨K₃, hK₃, hb₃⟩ := h₃
  refine ⟨K₁ + K₃, add_pos hK₁ hK₃, fun F ↦ ?_⟩
  have hexact : Function.Exact
      (Linear.leftComp k F T.mor₂) (Linear.leftComp k F T.mor₁) := by
    apply LinearMap.exact_of_comp_of_mem_range
    · apply LinearMap.ext
      intro f
      simp [Linear.leftComp, ← Category.assoc,
        comp_distTriang_mor_zero₁₂ T hT]
    · intro f hf
      change T.mor₁ ≫ f = 0 at hf
      obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f hf
      exact ⟨g, by simpa [Linear.leftComp] using hg.symm⟩
  have hdim : Module.finrank k (T.obj₂ ⟶ F) ≤
      Module.finrank k (T.obj₃ ⟶ F) + Module.finrank k (T.obj₁ ⟶ F) := by
    exact finrank_middle_le_of_exact
      (Linear.leftComp k F T.mor₂) (Linear.leftComp k F T.mor₁) hexact
  calc
    (Module.finrank k (T.obj₂ ⟶ F) : ℝ) ≤
        (Module.finrank k (T.obj₃ ⟶ F) : ℝ) +
          (Module.finrank k (T.obj₁ ⟶ F) : ℝ) := by exact_mod_cast hdim
    _ ≤ K₃ * (stabilityMass σ F).toReal +
        K₁ * (stabilityMass σ F).toReal := add_le_add (hb₃ F) (hb₁ F)
    _ = (K₁ + K₃) * (stabilityMass σ F).toReal := by ring

end HasMassHomBoundFor

/-- The object property of tests which admit some mass--Hom constant. -/
def massHomBoundedTests
    (s : StabilityCondition.WithClassMap C v₀) : ObjectProperty C :=
  fun A ↦ s.HasMassHomBoundFor (k := k) A

/-- A mass--Hom bound on a generating collection extends to its thick
triangulated envelope. -/
theorem HasMassHomBound.triangEnvelope (G : ObjectProperty C)
    (hG : σ.HasMassHomBound (k := k) G) :
    σ.HasMassHomBound (k := k) G.triangEnvelope := by
  let P : ObjectProperty C := massHomBoundedTests (k := k) σ
  letI : P.IsStableUnderRetracts :=
    ⟨fun r hB ↦ HasMassHomBoundFor.retract hB r⟩
  letI : P.ContainsZero :=
    ⟨⟨0, isZero_zero C, HasMassHomBoundFor.of_isZero (isZero_zero C)⟩⟩
  letI : P.IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun _ hA ↦ HasMassHomBoundFor.shift hA n⟩⟩
  letI : P.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' <| by
    intro T hT h₁ h₃
    exact HasMassHomBoundFor.triangle_middle T hT h₁ h₃
  letI : P.IsTriangulated := {}
  have hGP : G ≤ P := hG
  have hle : G.triangEnvelope ≤ P :=
    (ObjectProperty.triangEnvelope_le_iff (P := G) (Q := P)).2 hGP
  exact fun A hA ↦ hle A hA

end

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
