/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.Consequences

/-!
# Mass--Hom bounds at finite stability distance

A finite full stability distance compares all HN masses by a uniform
exponential factor. Consequently the mass--Hom property is constant on every
finite-distance class and hence on every connected component. The locus is
open and closed in the existing Section 6 topology.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.SerreFunctor
open scoped ENNReal Topology

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

noncomputable section

universe w v u u'

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- The full-stability-distance class of `σ`. -/
def finiteDistanceClass (σ : StabilityCondition.WithClassMap C v) :
    Set (StabilityCondition.WithClassMap C v) :=
  {τ | stabilityDist σ τ < ⊤}

/-- A finite-distance class is open and closed in the existing stability
topology. The temporary pseudo-extended-metric instance has definitionally
that topology. -/
theorem isClopen_finiteDistanceClass
    (σ : StabilityCondition.WithClassMap C v) :
    IsClopen (finiteDistanceClass σ) := by
  letI : PseudoEMetricSpace (StabilityCondition.WithClassMap C v) :=
    stabilityPseudoEMetricSpace stabilityDistanceTopologyCompatible
  constructor
  · have h := (Metric.isClosed_eball_top : IsClosed
        (Metric.eball σ (⊤ : ℝ≥0∞)))
    change IsClosed {τ | stabilityDist τ σ < ⊤} at h
    simpa only [finiteDistanceClass, stabilityDist_comm] using h
  · have h := (Metric.isOpen_eball : IsOpen
        (Metric.eball σ (⊤ : ℝ≥0∞)))
    change IsOpen {τ | stabilityDist τ σ < ⊤} at h
    simpa only [finiteDistanceClass, stabilityDist_comm] using h

/-- Every connected component is contained in the finite-distance class of
any one of its points. -/
theorem connectedComponent_subset_finiteDistanceClass
    (σ : StabilityCondition.WithClassMap C v) :
    connectedComponent σ ⊆ finiteDistanceClass σ := by
  apply (isClopen_finiteDistanceClass σ).connectedComponent_subset
  simp [finiteDistanceClass, stabilityDist_self]

namespace HasMassHomBound

variable [HomFinite k C]
variable {σ τ : StabilityCondition.WithClassMap C v}
variable {T : ObjectProperty C}

/-- Transport a mass--Hom bound across a specified strict distance bound.
The bound constant is multiplied by `exp ε`. -/
theorem of_stabilityDist_lt (h : σ.HasMassHomBound (k := k) T)
    {ε : ℝ} (hε : 0 < ε)
    (hd : stabilityDist σ τ < ENNReal.ofReal ε) :
    τ.HasMassHomBound (k := k) T := by
  intro A hA
  obtain ⟨K, hK, hbound⟩ := h A hA
  refine ⟨K * Real.exp ε, mul_pos hK (Real.exp_pos ε), fun F ↦ ?_⟩
  by_cases hF : IsZero F
  · haveI : Subsingleton (A ⟶ F) :=
      ⟨fun f g ↦ by rw [hF.eq_of_tgt f 0, hF.eq_of_tgt g 0]⟩
    simp [Module.finrank_zero_of_subsingleton,
      (stabilityMass_eq_zero_iff τ F).2 hF]
  · calc
      (Module.finrank k (A ⟶ F) : ℝ)
          ≤ K * (stabilityMass σ F).toReal := hbound F
      _ ≤ K * (Real.exp ε * (stabilityMass τ F).toReal) := by
        exact mul_le_mul_of_nonneg_left
          (stabilityMass_toReal_lt_exp_mul_of_stabilityDist'
            σ τ hF hε hd).le hK.le
      _ = (K * Real.exp ε) * (stabilityMass τ F).toReal := by ring

/-- A mass--Hom bound transports across any finite full stability distance. -/
theorem of_finiteDistance (h : σ.HasMassHomBound (k := k) T)
    (hd : stabilityDist σ τ < ⊤) :
    τ.HasMassHomBound (k := k) T := by
  obtain ⟨ε, _hεnonneg, hdε, _⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hd
  have hε : 0 < ε := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdε)
  exact h.of_stabilityDist_lt hε hdε

/-- The mass--Hom property is invariant under finite full stability distance. -/
theorem finiteDistance_iff (hd : stabilityDist σ τ < ⊤) :
    τ.HasMassHomBound (k := k) T ↔
      σ.HasMassHomBound (k := k) T := by
  constructor
  · intro h
    exact h.of_finiteDistance (by simpa [stabilityDist_comm] using hd)
  · intro h
    exact h.of_finiteDistance hd

/-- The mass--Hom property is constant on connected components of the
stability space. -/
theorem of_mem_connectedComponent (h : σ.HasMassHomBound (k := k) T)
    (hτ : τ ∈ connectedComponent σ) :
    τ.HasMassHomBound (k := k) T :=
  h.of_finiteDistance (connectedComponent_subset_finiteDistanceClass σ hτ)

end HasMassHomBound

/-- The locus of stability conditions satisfying a mass--Hom bound for `T`. -/
def massHomLocus [HomFinite k C] (T : ObjectProperty C) :
    Set (StabilityCondition.WithClassMap C v) :=
  {σ | σ.HasMassHomBound (k := k) T}

/-- The mass--Hom locus is open. -/
theorem isOpen_massHomLocus [HomFinite k C] (T : ObjectProperty C) :
    IsOpen (massHomLocus (k := k) (v := v) T) := by
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  apply Filter.mem_of_superset
    ((stabilityCondition_isOpen_connectedComponent C σ).mem_nhds
      mem_connectedComponent)
  intro τ hτ
  exact HasMassHomBound.of_mem_connectedComponent hσ hτ

/-- The mass--Hom locus is closed. -/
theorem isClosed_massHomLocus [HomFinite k C] (T : ObjectProperty C) :
    IsClosed (massHomLocus (k := k) (v := v) T) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  apply Filter.mem_of_superset
    ((stabilityCondition_isOpen_connectedComponent C σ).mem_nhds
      mem_connectedComponent)
  intro τ hτ hτbound
  apply hσ
  exact (HasMassHomBound.finiteDistance_iff
    (connectedComponent_subset_finiteDistanceClass σ hτ)).mp hτbound

/-- The mass--Hom locus is clopen. -/
theorem isClopen_massHomLocus [HomFinite k C] (T : ObjectProperty C) :
    IsClopen (massHomLocus (k := k) (v := v) T) :=
  ⟨isClosed_massHomLocus T, isOpen_massHomLocus T⟩

end


end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
