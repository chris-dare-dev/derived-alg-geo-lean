/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Metric.Mass.Uniqueness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Basic

/-!
# Bridgeland specializations of mass uniqueness

The choice-free mass theorem is owned by the weak parent and is stated for a
bare slicing and additive charge. This file supplies the stronger Bridgeland
wrappers, including positivity consequences that fail for weak stability.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

omit [IsTriangulated C] in
/-- Every HN filtration of a zero object has zero mass. -/
theorem HNFiltration.mass_eq_zero_of_isZero
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hE : IsZero E) :
    F.mass σ = 0 :=
  F.classMass_eq_zero_of_isZero (σ.Z.comp v) hE

/-- **HN mass is independent of the chosen HN filtration.** -/
theorem HNFiltration.mass_eq_mass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F G : HNFiltration C σ.slicing.P E) : F.mass σ = G.mass σ :=
  F.classMass_eq_classMass (σ.Z.comp v) G

/-- The choice-free mass envelope is the mass sum of every HN filtration. -/
theorem stabilityMass_eq_mass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) : stabilityMass σ E = F.mass σ :=
  Slicing.classMass_eq_classMass σ.slicing (σ.Z.comp v) F

/-- The ordinary HN mass is always finite. -/
theorem stabilityMass_ne_top
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ E ≠ ⊤ :=
  Slicing.classMass_ne_top σ.slicing (σ.Z.comp v) E

theorem stabilityMass_lt_top
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ E < ⊤ :=
  Slicing.classMass_lt_top σ.slicing (σ.Z.comp v) E

/-- Real-valued form of the mass identification. -/
theorem stabilityMass_toReal_eq_sum
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (stabilityMass σ E).toReal =
      ∑ i : Fin F.n, ‖σ.charge (F.factor i)‖ :=
  Slicing.classMass_toReal_eq_sum σ.slicing (σ.Z.comp v) F

/-- A semistable object's mass is the norm of its charge. -/
theorem stabilityMass_eq_ofReal_norm_charge
    (σ : StabilityCondition.WithClassMap C v) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) :
    stabilityMass σ E = ENNReal.ofReal ‖σ.charge E‖ :=
  Slicing.classMass_eq_ofReal_norm_classCharge σ.slicing (σ.Z.comp v) hP

/-- Split off the highest-phase HN factor and retain the mass identity. -/
theorem exists_headTail_stabilityMass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C σ.slicing.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      stabilityMass σ E =
        stabilityMass σ (F.factor ⟨0, hn⟩) + stabilityMass σ Y ∧
      G.n = F.n - 1 :=
  Slicing.exists_headTail_classMass σ.slicing (σ.Z.comp v) F hn

/-- Split off the highest-phase HN factor while retaining phase indices. -/
theorem HNFiltration.exists_headTail_mass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C σ.slicing.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (stabilityMass σ E).toReal =
        ‖σ.charge (F.factor ⟨0, hn⟩)‖ + (stabilityMass σ Y).toReal ∧
      G.n = F.n - 1 ∧
      ∀ j : Fin G.n, ∃ i : Fin F.n,
        i.val = j.val + 1 ∧ G.φ j = F.φ i :=
  HNFiltration.exists_headTail_classMass σ.slicing (σ.Z.comp v) F hn

/-- Mass vanishes exactly on zero objects. -/
@[simp]
theorem stabilityMass_eq_zero_iff
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ E = 0 ↔ IsZero E := by
  constructor
  · intro hmass
    by_contra hE
    exact (ne_of_gt (stabilityMass_pos σ hE)) hmass
  · intro hE
    obtain ⟨F⟩ := σ.slicing.hn_exists E
    rw [stabilityMass_eq_mass σ F,
      CategoryTheory.Triangulated.HNFiltration.mass_eq_zero_of_isZero σ F hE]

/-- The real-valued mass coordinate is strictly positive on nonzero objects. -/
theorem stabilityMass_toReal_pos
    (σ : StabilityCondition.WithClassMap C v) {E : C} (hE : ¬IsZero E) :
    0 < (stabilityMass σ E).toReal :=
  ENNReal.toReal_pos (ne_of_gt (stabilityMass_pos σ hE)) (stabilityMass_ne_top σ E)

end

end CategoryTheory.Triangulated
