/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Generator
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.MassAdditivity
import DerivedAlgGeo.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Stable-object reduction for mass--Hom bounds

A stable object of phase `φ` is a nonzero simple object of the exact slice
`𝒫(φ)`, expressed intrinsically by distinguished triangles whose three terms
lie in that slice.  The one missing categorical input is isolated as
`Slicing.HasJordanHolderFiltrations`: every semistable object is a finite
extension of stable objects of the same phase.

The repository's local-finiteness field controls admissible subobjects in
thin interval categories, but the pinned libraries do not yet turn that
well-foundedness into a categorical Jordan--Hölder filtration.  Consequently
the named hypothesis below is explicit; it is not a field of a stability
condition and is not silently inferred from local finiteness.
The missing bridge is tracked by GitHub issue #1203.

Under this hypothesis, a bound on stable targets extends first across a
same-phase Jordan--Hölder filtration and then across the existing HN
filtration.  This is the stable-object half of Halpern--Leistner--Robotis,
arXiv:2501.00710v2, Lemma 2.8.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.SerreFunctor
open scoped ENNReal ZeroObject BigOperators

namespace CategoryTheory.Triangulated

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
variable {A F : C}

namespace Slicing

/-- A nonzero simple object in the exact phase slice `𝒫(φ)`, stated without
manufacturing an abelian-category instance on that slice. -/
def IsStableAt (s : Slicing C) (φ : ℝ) (E : C) : Prop :=
  s.P φ E ∧ ¬IsZero E ∧
    ∀ ⦃X Y : C⦄, s.P φ X → s.P φ Y →
      ∀ (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C → IsZero X ∨ IsZero Y

/-- The explicit Jordan--Hölder input used by stable-object reduction:
every semistable object is a finite extension of stable objects in its own
phase slice. -/
def HasJordanHolderFiltrations (s : Slicing C) : Prop :=
  ∀ (φ : ℝ) (E : C), s.P φ E →
    ExtensionClosure (s.IsStableAt φ) E

end Slicing

namespace StabilityCondition.WithClassMap

/-- A mass--Hom bound tested only on stable target objects. -/
@[nolint unusedArguments]
def HasStableMassHomBoundFor
    (σ : StabilityCondition.WithClassMap C v₀) (A : C) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (F : C) (φ : ℝ),
    σ.slicing.IsStableAt φ F →
      (Module.finrank k (A ⟶ F) : ℝ) ≤
        K * (stabilityMass σ F).toReal

/-- A stable-target mass--Hom bound on a property of test objects. -/
def HasStableMassHomBound
    (σ : StabilityCondition.WithClassMap C v₀)
    (T : ObjectProperty C) : Prop :=
  ∀ A : C, T A → σ.HasStableMassHomBoundFor (k := k) A

namespace HasStableMassHomBoundFor

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] [IsTriangulated C] in
/-- The Hom dimension of the middle term of a distinguished triangle is at
most the sum of the Hom dimensions of its endpoints. -/
private theorem finrank_hom_triangle_le (A : C) (T : Triangle C)
    (hT : T ∈ distTriang C) :
    Module.finrank k (A ⟶ T.obj₂) ≤
      Module.finrank k (A ⟶ T.obj₁) + Module.finrank k (A ⟶ T.obj₃) := by
  have hexact : Function.Exact
      (Linear.rightComp k A T.mor₁) (Linear.rightComp k A T.mor₂) := by
    apply LinearMap.exact_of_comp_of_mem_range
    · apply LinearMap.ext
      intro f
      simp [Linear.rightComp, Category.assoc,
        comp_distTriang_mor_zero₁₂ T hT]
    · intro f hf
      change f ≫ T.mor₂ = 0 at hf
      obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f hf
      exact ⟨g, by simpa [Linear.rightComp] using hg.symm⟩
  calc
    Module.finrank k (A ⟶ T.obj₂) =
        Module.finrank k (LinearMap.range (Linear.rightComp k A T.mor₁)) +
          Module.finrank k (LinearMap.range (Linear.rightComp k A T.mor₂)) :=
      hexact.finrank_eq_finrank_range_add_finrank_range
    _ ≤ Module.finrank k (A ⟶ T.obj₁) +
        Module.finrank k (A ⟶ T.obj₃) :=
      Nat.add_le_add
        (Linear.rightComp k A T.mor₁).finrank_range_le
        (LinearMap.range (Linear.rightComp k A T.mor₂)).finrank_le

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] [IsTriangulated C] in
/-- Iterating exact Hom sequences along the first `n` stages of a Postnikov
tower bounds the top Hom dimension by the sum over its factors. -/
private theorem finrank_hom_le_sum_postnikov_factors
    (A : C) {E : C} (P : PostnikovTower C E) :
    Module.finrank k (A ⟶ E) ≤
      ∑ i : Fin P.n, Module.finrank k (A ⟶ P.factor i) := by
  suffices h : ∀ n (hn : n ≤ P.n),
      Module.finrank k (A ⟶ P.chain.obj' n (by omega)) ≤
        ∑ i : Fin n,
          Module.finrank k (A ⟶ P.factor ⟨i.val, by omega⟩) by
    have htop := (Linear.homCongr k (Iso.refl A)
      (Classical.choice P.top_iso)).finrank_eq
    rw [← htop]
    exact h P.n le_rfl
  intro n
  induction n with
  | zero =>
      intro _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      change Module.finrank k (A ⟶ P.chain.left) ≤ 0
      haveI : Subsingleton (A ⟶ P.chain.left) :=
        ⟨fun f g ↦ P.base_isZero.eq_of_tgt f g⟩
      rw [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
      intro hn
      let i : Fin P.n := ⟨n, by omega⟩
      have hstep := finrank_hom_triangle_le (k := k) A (P.triangle i)
        (P.triangle_dist i)
      have h₁ := (Linear.homCongr k (Iso.refl A)
        (Classical.choice (P.triangle_obj₁ i))).finrank_eq
      have h₂ := (Linear.homCongr k (Iso.refl A)
        (Classical.choice (P.triangle_obj₂ i))).finrank_eq
      rw [h₂, h₁] at hstep
      calc
        Module.finrank k (A ⟶ P.chain.obj' (n + 1) (by omega)) ≤
            Module.finrank k (A ⟶ P.chain.obj' n (by omega)) +
              Module.finrank k (A ⟶ P.factor i) := hstep
        _ ≤ (∑ j : Fin n,
              Module.finrank k
                (A ⟶ P.factor ⟨j.val, by omega⟩)) +
            Module.finrank k (A ⟶ P.factor i) :=
          Nat.add_le_add_right (ih (by omega)) _
        _ = ∑ j : Fin (n + 1),
            Module.finrank k
              (A ⟶ P.factor ⟨j.val, by omega⟩) := by
          rw [Fin.sum_univ_castSucc]
          rfl

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- A fixed stable-target estimate extends to every semistable target of the
same phase when Jordan--Hölder filtrations are available. -/
private theorem bound_semistable_of_jordanHolder
    (hJH : σ.slicing.HasJordanHolderFiltrations)
    {K : ℝ} (hK : 0 < K)
    (hstable : ∀ (F : C) (φ : ℝ), σ.slicing.IsStableAt φ F →
      (Module.finrank k (A ⟶ F) : ℝ) ≤
        K * (stabilityMass σ F).toReal)
    (F : C) (φ : ℝ) (hF : σ.slicing.P φ F) :
    (Module.finrank k (A ⟶ F) : ℝ) ≤
      K * (stabilityMass σ F).toReal := by
  let Q : ObjectProperty C := fun E ↦
    σ.slicing.P φ E ∧
      (Module.finrank k (A ⟶ E) : ℝ) ≤
        K * (stabilityMass σ E).toReal
  have hle : ExtensionClosure (σ.slicing.IsStableAt φ) ≤ Q :=
    ExtensionClosure.le_of_closed
      (fun {E} hE ↦ by
        refine ⟨σ.slicing.zero_mem_of_isZero C φ E hE, ?_⟩
        haveI : Subsingleton (A ⟶ E) :=
          ⟨fun f g ↦ hE.eq_of_tgt f g⟩
        rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
        exact mul_nonneg hK.le ENNReal.toReal_nonneg)
      (fun E hE ↦ ⟨hE.1, hstable E φ hE⟩)
      (fun {X E Y f g h} hT hX hY ↦ by
        refine ⟨σ.slicing.semistable_of_triangle C φ hX.1 hY.1 hT, ?_⟩
        have hdim : Module.finrank k (A ⟶ E) ≤
            Module.finrank k (A ⟶ X) + Module.finrank k (A ⟶ Y) :=
          finrank_hom_triangle_le (k := k) A (Triangle.mk f g h) hT
        calc
          (Module.finrank k (A ⟶ E) : ℝ) ≤
              (Module.finrank k (A ⟶ X) : ℝ) +
                (Module.finrank k (A ⟶ Y) : ℝ) := by
            exact_mod_cast hdim
          _ ≤ K * (stabilityMass σ X).toReal +
              K * (stabilityMass σ Y).toReal :=
            add_le_add hX.2 hY.2
          _ = K * (stabilityMass σ E).toReal := by
            have hmass := stabilityMass_toReal_triangle_eq_add_of_same_phase
              σ (Triangle.mk f g h) hT φ hX.1 hY.1
            change (stabilityMass σ E).toReal =
              (stabilityMass σ X).toReal +
                (stabilityMass σ Y).toReal at hmass
            rw [hmass]
            ring)
  exact (hle F (hJH φ F hF)).2

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- A stable-target bound extends to the full mass--Hom bound under the named
Jordan--Hölder hypothesis. -/
theorem massHom (h : σ.HasStableMassHomBoundFor (k := k) A)
    (hJH : σ.slicing.HasJordanHolderFiltrations) :
    σ.HasMassHomBoundFor (k := k) A := by
  obtain ⟨K, hK, hstable⟩ := h
  refine ⟨K, hK, fun F ↦ ?_⟩
  obtain ⟨P⟩ := σ.slicing.hn_exists F
  have hdimNat := finrank_hom_le_sum_postnikov_factors (k := k) A P.toPostnikovTower
  have hdim : (Module.finrank k (A ⟶ F) : ℝ) ≤
      ∑ i : Fin P.n,
        (Module.finrank k (A ⟶ P.factor i) : ℝ) := by
    exact_mod_cast hdimNat
  have hfactor : ∀ i : Fin P.n,
      (Module.finrank k (A ⟶ P.factor i) : ℝ) ≤
        K * (stabilityMass σ (P.factor i)).toReal := fun i ↦
    bound_semistable_of_jordanHolder (k := k) hJH hK hstable
      (P.factor i) (P.φ i) (P.semistable i)
  have hmass : ∑ i : Fin P.n,
      (stabilityMass σ (P.factor i)).toReal =
        (stabilityMass σ F).toReal := by
    rw [stabilityMass_toReal_eq_sum σ P]
    apply Finset.sum_congr rfl
    intro i _
    rw [stabilityMass_eq_ofReal_norm_charge σ (P.semistable i),
      ENNReal.toReal_ofReal (norm_nonneg _)]
  calc
    (Module.finrank k (A ⟶ F) : ℝ) ≤
        ∑ i : Fin P.n,
          (Module.finrank k (A ⟶ P.factor i) : ℝ) := hdim
    _ ≤ ∑ i : Fin P.n,
        K * (stabilityMass σ (P.factor i)).toReal :=
      Finset.sum_le_sum fun i _ ↦ hfactor i
    _ = K * ∑ i : Fin P.n,
        (stabilityMass σ (P.factor i)).toReal := by
      rw [Finset.mul_sum]
    _ = K * (stabilityMass σ F).toReal := by rw [hmass]

end HasStableMassHomBoundFor

namespace HasMassHomBoundFor

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] [IsTriangulated C] in
/-- A full mass--Hom bound restricts to stable targets. -/
theorem stable (h : σ.HasMassHomBoundFor (k := k) A) :
    σ.HasStableMassHomBoundFor (k := k) A := by
  obtain ⟨K, hK, hbound⟩ := h
  exact ⟨K, hK, fun F _ _ ↦ hbound F⟩

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- Under Jordan--Hölder, testing a fixed source against all objects is
equivalent to testing it only against stable objects. -/
theorem stable_iff (hJH : σ.slicing.HasJordanHolderFiltrations) :
    σ.HasStableMassHomBoundFor (k := k) A ↔
      σ.HasMassHomBoundFor (k := k) A :=
  ⟨fun h ↦ h.massHom hJH, fun h ↦ h.stable⟩

end HasMassHomBoundFor

namespace HasStableMassHomBound

variable {T : ObjectProperty C}

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- Stable-target bounds on a test class give full mass--Hom bounds on that
class under Jordan--Hölder. -/
theorem massHom (h : σ.HasStableMassHomBound (k := k) T)
    (hJH : σ.slicing.HasJordanHolderFiltrations) :
    σ.HasMassHomBound (k := k) T :=
  fun A hA ↦ (h A hA).massHom hJH

/-- The two reductions combine: stable-target bounds on generators extend to
full bounds on their thick triangulated envelope. -/
theorem triangEnvelope (h : σ.HasStableMassHomBound (k := k) T)
    (hJH : σ.slicing.HasJordanHolderFiltrations) :
    σ.HasMassHomBound (k := k) T.triangEnvelope :=
  (h.massHom hJH).triangEnvelope T

end HasStableMassHomBound

end StabilityCondition.WithClassMap

end

end CategoryTheory.Triangulated
