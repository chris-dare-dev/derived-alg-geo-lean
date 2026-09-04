/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action.PreStability
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Foundations.FiniteLength
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.UniformContinuity
import MathFormalContract

/-!
# The lifted linear action on stability conditions

This module extends the `G̃L⁺(2, ℝ)` action from prestability conditions to
`StabilityCondition.WithClassMap C v`.

The additional obligation is that `Slicing.IsLocallyFinite` survives phase
relabelling. It quantifies **one** radius `η` over **all** centres `t`, while
a normalized shift distorts windows.

Three ingredients close it:

1. `NormalizedShift.exists_radius` (`WeakStabilityCondition/StabilityCondition/Phase/UniformContinuity.lean`) — uniform continuity,
   giving one radius `η'` whose every window maps to width `< 2η`.
2. `relabel_intervalProp` (`WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Action/Slicing.lean`) — interval subcategories are
   reindexed exactly, so the relabelled window at `(t-η', t+η')` *is* the
   original at `(f⁻¹(t-η'), f⁻¹(t+η'))`.
3. `interval_thinFiniteLength_of_inclusion_strict`
   (`WeakStabilityCondition/StabilityCondition/Symmetry/Autoequivalence/Foundations/FiniteLength.lean`)
   — the shrinking lemma. It is stated for two *different* slicings related by
   `intervalProp ≤ intervalProp`, which is exactly the shape (2) produces.

Together these convert a local-finiteness witness for the original slicing
into a uniform witness for the relabelled slicing.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- **Local finiteness survives phase relabelling.**

The window radius changes — `η` becomes the `η'` supplied by uniform
continuity — but a single radius still works for every centre, which is what
`IsLocallyFinite` demands. -/
theorem relabel_isLocallyFinite (f : NormalizedShift) (s : Slicing C)
    (hs : s.IsLocallyFinite C) : (relabel C f s).IsLocallyFinite C := by
  obtain ⟨η, hη, hη2, hlf⟩ := hs.intervalFinite
  obtain ⟨η', hη'0, hη'M, hwidth⟩ :=
    NormalizedShift.exists_radius f⁻¹ (w := 2 * η) (M := 1 / 2) (by linarith) (by norm_num)
  refine ⟨⟨η', hη'0, hη'M, ?_⟩⟩
  intro t
  set A := f⁻¹.toOrderIso (t - η') with hA
  set B := f⁻¹.toOrderIso (t + η') with hB
  have hAB : B - A < 2 * η := hwidth t
  set u := (A + B) / 2 with hu
  have hlt : A < B := f⁻¹.toOrderIso.lt_iff_lt.mpr (by linarith)
  have ha2 : u - η ≤ A := by simp only [hu]; linarith
  have hb2 : B ≤ u + η := by simp only [hu]; linarith
  haveI : Fact (u - η < u + η) := ⟨by linarith⟩
  haveI : Fact ((u + η) - (u - η) ≤ 1) := ⟨by linarith⟩
  haveI : Fact (t - η' < t + η') := ⟨by linarith⟩
  haveI : Fact ((t + η') - (t - η') ≤ 1) := ⟨by linarith⟩
  have hle : (relabel C f s).intervalProp C (t - η') (t + η')
      ≤ s.intervalProp C (u - η) (u + η) := by
    intro E hE
    rw [relabel_intervalProp] at hE
    exact s.intervalProp_mono C ha2 hb2 E hE
  exact fun E => interval_finiteLength_of_inclusion (C := C)
    (s₁ := relabel C f s) (s₂ := s) hle (hlf u) E

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- `x = (T, f)` acting on a full stability condition. Slicing and charge are
transported by `actPre`; local finiteness is `relabel_isLocallyFinite`. -/
def actStab (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v where
  toWithClassMap := actPre C v x σ.toWithClassMap
  locallyFinite := relabel_isLocallyFinite C x.shift σ.slicing σ.locallyFinite

@[simp]
theorem actStab_slicing (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (actStab C v x σ).slicing = x • σ.slicing := rfl

@[simp]
theorem actStab_Z (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (actStab C v x σ).Z a = actC x.mat (σ.Z a) := rfl

/-- **The §8 action.** `G̃L⁺(2, ℝ)` acts on stability conditions. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := one_way)
        (frontier := ["gltilde-universal-cover"])
        (note := "Lemma 8.2 names GLTilde as the universal covering space of GL+(2,R). Here it is CONSTRUCTED as a group of compatible pairs (T, f); the covering-space facts are proved separately -- GLTilde.universalCoverData (IsCoveringMap, surjectivity, SimplyConnectedSpace) and exact_deckHom_toMatHom (the Z deck group). The open residual is only that Mathlib has no bundled universal-cover predicate at this pin to instantiate, so cite those declarations rather than implying a larger bundled API. PRESENTATION DIVERGENCE: the paper's is a RIGHT action; this is the corresponding LEFT action of the inverse pair, which is faithful but is not literally the paper's form. The paper's statement implies this one; not conversely.")]
instance stabMulAction : MulAction GLTilde (StabilityCondition.WithClassMap C v) where
  smul := actStab C v
  one_smul σ := by
    refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
    · show (actStab C v 1 σ).slicing = σ.slicing
      rw [actStab_slicing]
      exact one_smul _ _
    · ext a
      show (actStab C v 1 σ).Z a = σ.Z a
      rw [actStab_Z]
      simp
  mul_smul x y σ := by
    refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
    · show (actStab C v (x * y) σ).slicing = (actStab C v x (actStab C v y σ)).slicing
      rw [actStab_slicing, actStab_slicing, actStab_slicing]
      exact mul_smul _ _ _
    · ext a
      show (actStab C v (x * y) σ).Z a = (actStab C v x (actStab C v y σ)).Z a
      rw [actStab_Z, actStab_Z, actStab_Z, GLTilde.mul_mat, actC_mul]

@[simp]
theorem smul_stab_slicing (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

@[simp]
theorem smul_stab_Z (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
