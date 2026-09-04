/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Isometry.Phase
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Harder--Narasimhan mass

For an HN filtration `F` of `E`, its mass is the finite sum

```
  ∑ i, ‖Z(F.factor i)‖.
```

`WeakStabilityCondition/Foundation/Slicing/IntrinsicPhases.lean` proves that the
extreme phases of an HN filtration are intrinsic, but nothing exposes
uniqueness of the complete HN filtration.  Defining the
mass using `Classical.choice (s.hn_exists E)` would therefore make its
transport law depend on an arbitrary, non-functorial choice.  We first take
the supremum of the masses of all HN filtrations.  This is choice-free and
lives naturally in `ℝ≥0∞`.

`WeakStabilityCondition/StabilityCondition/Metric/Mass/Uniqueness.lean` subsequently proves that every term in this supremum
is equal, identifying `stabilityMass` with the usual finite Bridgeland mass.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal BigOperators

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- The finite mass sum attached to one HN filtration.

Stated over `StabilityCondition.WithClassMap` for uniformity with the rest of
the §8 track, but note that **the mass API never projects `locallyFinite`**:
Bridgeland §5 defines `m_σ` from the slicing and the charge alone. The parent
field is not a class, so Lean generates no coercion and dropping it would
require `.toWithClassMap` at every positional call site — hence this comment
rather than a weakening. `[IsTriangulated C]` *is* genuinely needed downstream,
for `someOctahedron` in `HNMassUniqueness`. -/
def HNFiltration.mass (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) : ℝ≥0∞ :=
  ∑ i : Fin F.n, ENNReal.ofReal ‖σ.charge (F.factor i)‖

omit [IsTriangulated C] in
/-- A nonzero semistable object has nonzero charge. -/
theorem StabilityCondition.WithClassMap.charge_ne_zero_of_semistable
    (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) (E : C)
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) : σ.charge E ≠ 0 := by
  obtain ⟨m, hm, hZ⟩ := σ.compat φ E hP hE
  rw [hZ]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hm)) (Complex.exp_ne_zero _)

omit [IsTriangulated C] in
/-- Every HN filtration of a nonzero object has strictly positive finite-sum mass. -/
theorem HNFiltration.mass_pos (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hE : ¬IsZero E) : 0 < F.mass σ := by
  obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hE
  have hZi : σ.charge (F.factor i) ≠ 0 :=
    σ.charge_ne_zero_of_semistable (F.φ i) (F.factor i) (F.semistable i) hi
  have hterm : 0 < ENNReal.ofReal ‖σ.charge (F.factor i)‖ :=
    ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hZi)
  change 0 < ∑ j : Fin F.n, ENNReal.ofReal ‖σ.charge (F.factor j)‖
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum
      (f := fun j : Fin F.n ↦ ENNReal.ofReal ‖σ.charge (F.factor j)‖)
      (fun _ _ ↦ zero_le) (Finset.mem_univ i))

omit [IsTriangulated C] in
@[simp]
theorem HNFiltration.mass_ofIso (σ : StabilityCondition.WithClassMap C v) {E E' : C}
    (F : HNFiltration C σ.slicing.P E) (e : E ≅ E') :
    HNFiltration.mass σ
      (CategoryTheory.Triangulated.HNFiltration.ofIso C F e) = F.mass σ :=
  rfl

/-- The choice-free HN mass envelope of an object.  Downstream,
`stabilityMass_eq_mass` identifies it with the mass of every HN filtration. -/
def stabilityMass (σ : StabilityCondition.WithClassMap C v) (E : C) : ℝ≥0∞ :=
  ⨆ F : HNFiltration C σ.slicing.P E, F.mass σ

omit [IsTriangulated C] in
/-- The mass envelope is positive on every nonzero object. -/
theorem stabilityMass_pos (σ : StabilityCondition.WithClassMap C v) {E : C}
    (hE : ¬IsZero E) : 0 < stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  exact lt_of_lt_of_le (CategoryTheory.Triangulated.HNFiltration.mass_pos σ F hE)
    (le_iSup (fun G : HNFiltration C σ.slicing.P E ↦ G.mass σ) F)

omit [IsTriangulated C] in
/-- The mass envelope depends on an object only up to isomorphism. -/
theorem stabilityMass_congr (σ : StabilityCondition.WithClassMap C v) {E E' : C}
    (e : E ≅ E') : stabilityMass σ E = stabilityMass σ E' := by
  apply le_antisymm
  · refine iSup_le fun F ↦ ?_
    exact le_iSup_of_le
      (CategoryTheory.Triangulated.HNFiltration.ofIso C F e) (by simp)
  · refine iSup_le fun F ↦ ?_
    exact le_iSup_of_le
      (CategoryTheory.Triangulated.HNFiltration.ofIso C F e.symm) (by simp)

end

end CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair

noncomputable section

open CategoryTheory.Triangulated

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

variable (a : CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair v)

/-- The charge of an acted stability condition is the original charge of the
inverse-image object. -/
theorem act_charge (σ : StabilityCondition.WithClassMap C v) (E : C) :
    (a.act σ).charge E = σ.charge (a.Φ.e.inverse.obj E) := by
  have hcl : a.lam (classOf C v E) = classOf C v (a.Φ.e.inverse.obj E) := by
    rw [classOf, ← a.compat, K₀.map_of]
  change σ.Z (a.lam (classOf C v E)) = σ.Z (classOf C v (a.Φ.e.inverse.obj E))
  rw [hcl]

/-- Mapping an HN filtration backward through the equivalence preserves its
finite mass sum. -/
theorem mass_map_inverse (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C (a.act σ).slicing.P E) :
    (F.mapF (P' := σ.slicing.P) a.Φ.e.inverse (fun _ _ h ↦ h)).mass σ =
      F.mass (a.act σ) := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  rw [a.act_charge σ]
  rfl

/-- Mapping an HN filtration forward through the equivalence preserves its
finite mass sum. -/
theorem mass_map_functor (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.mapF
        (P' := fun φ X ↦ σ.slicing.P φ (a.Φ.e.inverse.obj X))
        a.Φ.e.functor
        (fun _ X h ↦ ObjectProperty.prop_of_iso _ (a.Φ.e.unitIso.app X) h)).mass
        (a.act σ) = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  rw [a.act_charge σ]
  change ENNReal.ofReal
      ‖σ.charge (a.Φ.e.inverse.obj (a.Φ.e.functor.obj (F.factor i)))‖ =
    ENNReal.ofReal ‖σ.charge (F.factor i)‖
  have hcharge :
      σ.charge (a.Φ.e.inverse.obj (a.Φ.e.functor.obj (F.factor i))) =
        σ.charge (F.factor i) := by
    change σ.Z (classOf C v (a.Φ.e.inverse.obj (a.Φ.e.functor.obj (F.factor i)))) =
      σ.Z (classOf C v (F.factor i))
    have hcl := classOf_iso C v (a.Φ.e.unitIso.app (F.factor i))
    change classOf C v (F.factor i) =
      classOf C v (a.Φ.e.inverse.obj (a.Φ.e.functor.obj (F.factor i))) at hcl
    exact congrArg σ.Z hcl.symm
  rw [hcharge]

/-- Transport by a compatible autoequivalence replaces an object by its
inverse image and leaves the mass envelope unchanged. -/
theorem act_stabilityMass (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass (a.act σ) E = stabilityMass σ (a.Φ.e.inverse.obj E) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ ?_
    let G := F.mapF (P' := σ.slicing.P) a.Φ.e.inverse (fun _ _ h ↦ h)
    rw [← a.mass_map_inverse σ F]
    exact le_iSup (fun H : HNFiltration C σ.slicing.P (a.Φ.e.inverse.obj E) ↦
      H.mass σ) G
  · refine iSup_le fun F ↦ ?_
    let G₀ := F.mapF
      (P' := fun φ X ↦ σ.slicing.P φ (a.Φ.e.inverse.obj X))
      a.Φ.e.functor
      (fun _ X h ↦ ObjectProperty.prop_of_iso _ (a.Φ.e.unitIso.app X) h)
    let G := CategoryTheory.Triangulated.HNFiltration.ofIso C G₀
      (a.Φ.e.counitIso.app E)
    rw [← a.mass_map_functor σ F, ← HNFiltration.mass_ofIso (a.act σ) G₀
      (a.Φ.e.counitIso.app E)]
    exact le_iSup (fun H : HNFiltration C (a.act σ).slicing.P E ↦
      H.mass (a.act σ)) G

/-- Objectwise form of mass invariance, with the object moved forward. -/
theorem act_stabilityMass_functor_obj (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass (a.act σ) (a.Φ.e.functor.obj E) = stabilityMass σ E := by
  rw [a.act_stabilityMass σ]
  exact stabilityMass_congr σ (a.Φ.e.unitIso.app E).symm

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair
