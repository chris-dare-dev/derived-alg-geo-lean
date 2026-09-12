/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.MassTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action.Continuous

/-!
# Mass--Hom bounds

For a stability condition `σ` and a property `T` of test objects, a mass--Hom
bound says that every `A ∈ T` admits a positive constant `K_A` such that

`dim_k Hom(A, F) ≤ K_A m_σ(F)`

for every object `F`.  Taking `T = ⊤` is Halpern--Leistner--Robotis,
Definition 2.7; for a proper scheme the intended geometric test class is
`Perf(X)`.

The constant is existential rather than data.  Hom-finiteness is an explicit
ambient hypothesis: this abstract file neither supplies it nor derives it from
triangulated structure.

This file also records the formal invariances needed downstream.  Isomorphisms
and simultaneous shifts preserve both sides exactly.  Compatible `k`-linear
autoequivalences preserve mass exactly while transporting the test class.
The lifted `GL⁺(2, ℝ)` action fixes objects and changes mass by a uniform
operator-norm factor.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.SerreFunctor
open scoped ENNReal

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

noncomputable section

universe w v u u'

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- A mass--Hom bound for one test object.  The positive constant is a
propositionally existential witness, not chosen data.

The `HomFinite` argument is intentionally explicit even though `finrank` is
junk-total without it; the declaration-level lint exception prevents that
mathematical guard from being erased as a syntactically unused argument. -/
@[nolint unusedArguments]
def HasMassHomBoundFor [HomFinite k C]
    (σ : StabilityCondition.WithClassMap C v) (A : C) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ F : C,
    (Module.finrank k (A ⟶ F) : ℝ) ≤ K * (stabilityMass σ F).toReal

/-- A mass--Hom bound on a property `T` of test objects. -/
def HasMassHomBound [HomFinite k C]
    (σ : StabilityCondition.WithClassMap C v) (T : ObjectProperty C) : Prop :=
  ∀ A : C, T A → σ.HasMassHomBoundFor (k := k) A

/-- The original all-object form of the mass--Hom bound. -/
abbrev HasGlobalMassHomBound [HomFinite k C]
    (σ : StabilityCondition.WithClassMap C v) : Prop :=
  σ.HasMassHomBound (k := k) ⊤

namespace HasMassHomBound

variable [HomFinite k C]
variable {σ : StabilityCondition.WithClassMap C v}
variable {T T' : ObjectProperty C}

omit [IsTriangulated C] in
/-- Restricting the test class preserves a mass--Hom bound. -/
theorem anti (h : σ.HasMassHomBound (k := k) T) (hTT' : T' ≤ T) :
    σ.HasMassHomBound (k := k) T' :=
  fun A hA ↦ h A (hTT' A hA)

omit [IsTriangulated C] in
/-- The all-object spelling exposes the same objectwise predicate. -/
theorem top_iff :
    σ.HasGlobalMassHomBound (k := k) ↔
      ∀ A : C, σ.HasMassHomBoundFor (k := k) A := by
  simp [HasGlobalMassHomBound, HasMassHomBound]

end HasMassHomBound

namespace HasMassHomBoundFor

variable [HomFinite k C]
variable {σ : StabilityCondition.WithClassMap C v}
variable {A A' F F' : C}

omit [IsTriangulated C] [HomFinite k C] in
/-- The pointwise inequality is invariant under isomorphism of both the test
and target objects. -/
theorem bound_congr (eA : A ≅ A') (eF : F ≅ F') {K : ℝ}
    (h : (Module.finrank k (A ⟶ F) : ℝ) ≤
      K * (stabilityMass σ F).toReal) :
    (Module.finrank k (A' ⟶ F') : ℝ) ≤
      K * (stabilityMass σ F').toReal := by
  have hdim := (Linear.homCongr k eA eF).finrank_eq
  have hmass := stabilityMass_congr σ eF
  rw [← hdim, ← hmass]
  exact h

omit [IsTriangulated C] in
/-- A mass--Hom bound depends on its test object only up to isomorphism. -/
theorem congr (h : σ.HasMassHomBoundFor (k := k) A) (e : A ≅ A') :
    σ.HasMassHomBoundFor (k := k) A' := by
  obtain ⟨K, hK, hbound⟩ := h
  exact ⟨K, hK, fun F ↦ bound_congr (k := k) e (Iso.refl F) (hbound F)⟩

/-- On a semistable object the mass--Hom inequality has the normal form
`dim Hom(A,F) ≤ K_A ‖Z(F)‖`. -/
theorem exists_semistable_bound
    (h : σ.HasMassHomBoundFor (k := k) A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : C) (φ : ℝ), σ.slicing.P φ F →
      (Module.finrank k (A ⟶ F) : ℝ) ≤ K * ‖σ.charge F‖ := by
  obtain ⟨K, hK, hbound⟩ := h
  refine ⟨K, hK, fun F φ hF ↦ ?_⟩
  simpa [stabilityMass_eq_ofReal_norm_charge σ hF] using hbound F

section Shift

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

omit [HomFinite k C] in
/-- Simultaneously shifting both variables by one preserves a mass--Hom
inequality. -/
theorem bound_shift_one {K : ℝ}
    (h : (Module.finrank k (A ⟶ F) : ℝ) ≤
      K * (stabilityMass σ F).toReal) :
    (Module.finrank k (A⟦(1 : ℤ)⟧ ⟶ F⟦(1 : ℤ)⟧) : ℝ) ≤
      K * (stabilityMass σ (F⟦(1 : ℤ)⟧)).toReal := by
  have hdim := (homLinearEquivOfFullyFaithful (k := k) (shiftFunctor C (1 : ℤ))
    (shiftEquiv C (1 : ℤ)).fullyFaithfulFunctor A F).finrank_eq
  have hdimR :
      (Module.finrank k (A ⟶ F) : ℝ) =
        (Module.finrank k (A⟦(1 : ℤ)⟧ ⟶ F⟦(1 : ℤ)⟧) : ℝ) := by
    exact_mod_cast hdim
  rw [← hdimR, stabilityMass_shift_one]
  exact h

omit [HomFinite k C] in
/-- Simultaneously shifting both variables by minus one preserves a mass--Hom
inequality. -/
theorem bound_shift_neg_one {K : ℝ}
    (h : (Module.finrank k (A ⟶ F) : ℝ) ≤
      K * (stabilityMass σ F).toReal) :
    (Module.finrank k (A⟦(-1 : ℤ)⟧ ⟶ F⟦(-1 : ℤ)⟧) : ℝ) ≤
      K * (stabilityMass σ (F⟦(-1 : ℤ)⟧)).toReal := by
  have hdim := (homLinearEquivOfFullyFaithful (k := k) (shiftFunctor C (-1 : ℤ))
    (shiftEquiv C (-1 : ℤ)).fullyFaithfulFunctor A F).finrank_eq
  have hdimR :
      (Module.finrank k (A ⟶ F) : ℝ) =
        (Module.finrank k (A⟦(-1 : ℤ)⟧ ⟶ F⟦(-1 : ℤ)⟧) : ℝ) := by
    exact_mod_cast hdim
  rw [← hdimR, stabilityMass_shift_neg_one]
  exact h

/-- Shifting the test object by one preserves a mass--Hom bound. -/
theorem shift_one (h : σ.HasMassHomBoundFor (k := k) A) :
    σ.HasMassHomBoundFor (k := k) (A⟦(1 : ℤ)⟧) := by
  obtain ⟨K, hK, hbound⟩ := h
  refine ⟨K, hK, fun F ↦ ?_⟩
  have hb := bound_shift_one (k := k) (σ := σ) (A := A)
    (F := F⟦(-1 : ℤ)⟧) (K := K) (hbound _)
  exact bound_congr (k := k) (σ := σ) (Iso.refl _)
    ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by omega)).app F) hb

/-- Shifting the test object by minus one preserves a mass--Hom bound. -/
theorem shift_neg_one (h : σ.HasMassHomBoundFor (k := k) A) :
    σ.HasMassHomBoundFor (k := k) (A⟦(-1 : ℤ)⟧) := by
  obtain ⟨K, hK, hbound⟩ := h
  refine ⟨K, hK, fun F ↦ ?_⟩
  have hb := bound_shift_neg_one (k := k) (σ := σ) (A := A)
    (F := F⟦(1 : ℤ)⟧) (K := K) (hbound _)
  exact bound_congr (k := k) (σ := σ) (Iso.refl _)
    ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app F) hb

end Shift

end HasMassHomBoundFor

/-! ## Compatible autoequivalences -/

namespace HasMassHomBound

open WeakStabilityCondition.StabilityCondition.GroupAction

variable [HomFinite k C]
variable {σ : StabilityCondition.WithClassMap C v}
variable {T : ObjectProperty C}

/-- A compatible `k`-linear autoequivalence transports a mass--Hom bound to
the canonical inverse-image test property. -/
theorem autPair_act (a : AutPair v)
    [a.Φ.e.inverse.Linear k]
    (h : σ.HasMassHomBound (k := k) T) :
    (a.act σ).HasMassHomBound (k := k)
      (T.inverseImage a.Φ.e.inverse) := by
  intro A hA
  obtain ⟨K, hK, hbound⟩ := h (a.Φ.e.inverse.obj A) hA
  refine ⟨K, hK, fun F ↦ ?_⟩
  have hdim := (homLinearEquivOfFullyFaithful (k := k) a.Φ.e.inverse
    a.Φ.e.fullyFaithfulInverse A F).finrank_eq
  have hdimR :
      (Module.finrank k (A ⟶ F) : ℝ) =
        (Module.finrank k
          (a.Φ.e.inverse.obj A ⟶ a.Φ.e.inverse.obj F) : ℝ) := by
    exact_mod_cast hdim
  rw [hdimR, a.act_stabilityMass]
  exact hbound _

/-- Autoequivalence transport is an equivalence for a replete test class.
The right side uses the canonical inverse-image property rather than a second
chosen presentation of the transported class. -/
theorem autPair_act_iff (a : AutPair v)
    [a.Φ.e.functor.Linear k] [a.Φ.e.inverse.Linear k]
    [T.IsClosedUnderIsomorphisms] :
    (a.act σ).HasMassHomBound (k := k)
        (T.inverseImage a.Φ.e.inverse) ↔
      σ.HasMassHomBound (k := k) T := by
  constructor
  · intro h A hA
    have hTA : T (a.Φ.e.inverse.obj (a.Φ.e.functor.obj A)) :=
      T.prop_of_iso (a.Φ.e.unitIso.app A) hA
    obtain ⟨K, hK, hbound⟩ := h (a.Φ.e.functor.obj A) hTA
    refine ⟨K, hK, fun F ↦ ?_⟩
    have hdim := (homLinearEquivOfFullyFaithful (k := k) a.Φ.e.functor
      a.Φ.e.fullyFaithfulFunctor A F).finrank_eq
    have hdimR :
        (Module.finrank k (A ⟶ F) : ℝ) =
          (Module.finrank k
            (a.Φ.e.functor.obj A ⟶ a.Φ.e.functor.obj F) : ℝ) := by
      exact_mod_cast hdim
    rw [hdimR]
    calc
      (Module.finrank k
          (a.Φ.e.functor.obj A ⟶ a.Φ.e.functor.obj F) : ℝ)
          ≤ K * (stabilityMass (a.act σ) (a.Φ.e.functor.obj F)).toReal :=
        hbound _
      _ = K * (stabilityMass σ F).toReal := by
        rw [a.act_stabilityMass_functor_obj]
  · intro h
    exact h.autPair_act a

end HasMassHomBound

end

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap

/-! ## The lifted `GL⁺(2, ℝ)` action -/

namespace CategoryTheory.Triangulated.HNFiltration

noncomputable section

open WeakStabilityCondition.StabilityCondition.GroupAction

universe v u u'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Relabel an HN filtration along an arbitrary lifted linear action.  The
tower and factors are unchanged; only the phases are transported. -/
def relabelStability (x : GLTilde)
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    HNFiltration C (x • σ).slicing.P E where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := F.top_iso
  φ := fun i ↦ x.shift.toOrderIso (F.φ i)
  hφ := fun _ _ h ↦ x.shift.toOrderIso.lt_iff_lt.mpr (F.hφ h)
  semistable := by
    intro i
    change σ.slicing.P
      (x.shift⁻¹.toOrderIso (x.shift.toOrderIso (F.φ i))) _
    rw [NormalizedShift.inv_apply, OrderIso.symm_apply_apply]
    exact F.semistable i

end

end CategoryTheory.Triangulated.HNFiltration

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

noncomputable section

universe w v u u'

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

namespace HasMassHomBound

open WeakStabilityCondition.StabilityCondition.GroupAction

variable [HomFinite k C]
variable {σ : StabilityCondition.WithClassMap C v}
variable {T : ObjectProperty C}

/-- A strictly positive uniform expansion factor for the complex-plane action.
The harmless added `1` avoids exposing invertibility bookkeeping at every
mass--Hom consumer. -/
noncomputable def glMassBound (x : GLTilde) : ℝ :=
  ‖actCCLM x.mat‖ + 1

theorem glMassBound_pos (x : GLTilde) : 0 < glMassBound x := by
  unfold glMassBound
  positivity

/-- The lifted linear action expands every real HN mass by at most
`glMassBound x`. -/
theorem stabilityMass_smul_le (x : GLTilde)
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    (stabilityMass (x • σ) E).toReal ≤
      glMassBound x * (stabilityMass σ E).toReal := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_toReal_eq_sum (x • σ) (F.relabelStability x σ),
    stabilityMass_toReal_eq_sum σ F]
  calc
    (∑ i : Fin F.n, ‖(x • σ).charge (F.factor i)‖)
        ≤ ∑ i : Fin F.n, ‖actCCLM x.mat‖ * ‖σ.charge (F.factor i)‖ := by
          apply Finset.sum_le_sum
          intro i _
          change ‖actC x.mat (σ.charge (F.factor i))‖ ≤ _
          exact (actCCLM x.mat).le_opNorm _
    _ = ‖actCCLM x.mat‖ * ∑ i : Fin F.n, ‖σ.charge (F.factor i)‖ := by
      rw [Finset.mul_sum]
    _ ≤ glMassBound x * ∑ i : Fin F.n, ‖σ.charge (F.factor i)‖ := by
      apply mul_le_mul_of_nonneg_right
      · unfold glMassBound
        linarith
      · positivity

/-- The original mass is controlled by the mass after a lifted linear action,
using the expansion factor of the inverse element. -/
theorem stabilityMass_le_smul (x : GLTilde)
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    (stabilityMass σ E).toReal ≤
      glMassBound x⁻¹ * (stabilityMass (x • σ) E).toReal := by
  have h := stabilityMass_smul_le x⁻¹ (x • σ) E
  simpa using h

/-- A lifted linear action preserves the mass--Hom property, with constants
rescaled by the uniform inverse expansion factor. -/
theorem gltilde_smul (h : σ.HasMassHomBound (k := k) T) (x : GLTilde) :
    (x • σ).HasMassHomBound (k := k) T := by
  intro A hA
  obtain ⟨K, hK, hbound⟩ := h A hA
  refine ⟨K * glMassBound x⁻¹, mul_pos hK (glMassBound_pos x⁻¹), fun F ↦ ?_⟩
  calc
    (Module.finrank k (A ⟶ F) : ℝ)
        ≤ K * (stabilityMass σ F).toReal := hbound F
    _ ≤ K * (glMassBound x⁻¹ * (stabilityMass (x • σ) F).toReal) := by
      exact mul_le_mul_of_nonneg_left (stabilityMass_le_smul x σ F) hK.le
    _ = (K * glMassBound x⁻¹) * (stabilityMass (x • σ) F).toReal := by ring

/-- The mass--Hom property is invariant under the lifted linear group action. -/
theorem gltilde_smul_iff (x : GLTilde) :
    (x • σ).HasMassHomBound (k := k) T ↔
      σ.HasMassHomBound (k := k) T := by
  constructor
  · intro h
    simpa using h.gltilde_smul x⁻¹
  · intro h
    exact h.gltilde_smul x

end HasMassHomBound

end

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
