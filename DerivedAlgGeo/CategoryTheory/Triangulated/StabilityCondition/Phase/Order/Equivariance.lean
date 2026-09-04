/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Order.Characterizations
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Foundations.FiniteLength
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap

/-!
# Equivariance of the slicing orders

Both slicing orders are invariant under simultaneous transport by a
triangulated autoequivalence.  The result is first proved for a representative
`TriEquiv` and then descends to the repository's honest quotient group
`AutQuot C`.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ## Phase bounds under transport -/

/-- Transport by an equivalence relabels objects but leaves the strict upper
phase bound unchanged. -/
theorem Slicing.mapEquiv_ltProp_iff (Phi : C ≌ C)
    [Phi.functor.Additive] [Phi.inverse.Additive]
    [Phi.functor.CommShift ℤ] [Phi.inverse.CommShift ℤ]
    [Phi.functor.IsTriangulated] [Phi.inverse.IsTriangulated]
    (s : Slicing C) (phi : ℝ) (E : C) :
    (s.mapEquiv Phi).ltProp C phi E ↔ s.ltProp C phi (Phi.inverse.obj E) := by
  constructor
  · rintro (hzero | ⟨F, hn, hlt⟩)
    · exact Or.inl (Phi.inverse.map_isZero hzero)
    · exact Or.inr ⟨CategoryTheory.Triangulated.HNFiltration.mapF
        (P' := s.P) F Phi.inverse (fun _ _ h ↦ h), hn, hlt⟩
  · rintro (hzero | ⟨F, hn, hlt⟩)
    · exact Or.inl (IsZero.of_iso (Phi.functor.map_isZero hzero)
        (Phi.counitIso.app E).symm)
    · exact Or.inr ⟨CategoryTheory.Triangulated.HNFiltration.ofIso C
        (CategoryTheory.Triangulated.HNFiltration.mapF F
        (P' := fun psi X ↦ s.P psi (Phi.inverse.obj X)) Phi.functor
        (fun _ X h ↦ ObjectProperty.prop_of_iso _ (Phi.unitIso.app X) h))
          (Phi.counitIso.app E), hn, hlt⟩

/-- Transport by an equivalence relabels objects but leaves the weak upper
phase bound unchanged. -/
theorem Slicing.mapEquiv_leProp_iff (Phi : C ≌ C)
    [Phi.functor.Additive] [Phi.inverse.Additive]
    [Phi.functor.CommShift ℤ] [Phi.inverse.CommShift ℤ]
    [Phi.functor.IsTriangulated] [Phi.inverse.IsTriangulated]
    (s : Slicing C) (phi : ℝ) (E : C) :
    (s.mapEquiv Phi).leProp C phi E ↔ s.leProp C phi (Phi.inverse.obj E) := by
  constructor
  · rintro (hzero | ⟨F, hn, hle⟩)
    · exact Or.inl (Phi.inverse.map_isZero hzero)
    · exact Or.inr ⟨CategoryTheory.Triangulated.HNFiltration.mapF
        (P' := s.P) F Phi.inverse (fun _ _ h ↦ h), hn, hle⟩
  · rintro (hzero | ⟨F, hn, hle⟩)
    · exact Or.inl (IsZero.of_iso (Phi.functor.map_isZero hzero)
        (Phi.counitIso.app E).symm)
    · exact Or.inr ⟨CategoryTheory.Triangulated.HNFiltration.ofIso C
        (CategoryTheory.Triangulated.HNFiltration.mapF F
        (P' := fun psi X ↦ s.P psi (Phi.inverse.obj X)) Phi.functor
        (fun _ X h ↦ ObjectProperty.prop_of_iso _ (Phi.unitIso.app X) h))
          (Phi.counitIso.app E), hn, hle⟩

end CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Simultaneous transport by a triangulated autoequivalence preserves and
reflects the strict slicing order. -/
theorem TriEquiv.precedes_act_iff (Phi : TriEquiv C) (s t : Slicing C) :
    (Phi.act s).Precedes C (Phi.act t) ↔ s.Precedes C t := by
  constructor
  · intro h phi E hE
    have hMap : (Phi.act s).P phi (Phi.e.functor.obj E) := by
      change s.P phi (Phi.e.inverse.obj (Phi.e.functor.obj E))
      exact ObjectProperty.prop_of_iso _ (Phi.e.unitIso.app E) hE
    have hBound := h phi (Phi.e.functor.obj E) hMap
    have hInv := (Slicing.mapEquiv_ltProp_iff Phi.e t phi
      (Phi.e.functor.obj E)).mp hBound
    exact (t.ltProp C phi).prop_of_iso (Phi.e.unitIso.app E).symm hInv
  · intro h phi E hE
    apply (Slicing.mapEquiv_ltProp_iff Phi.e t phi E).mpr
    exact h phi (Phi.e.inverse.obj E) hE
/-- Simultaneous transport by a triangulated autoequivalence preserves and
reflects the weak slicing order. -/
theorem TriEquiv.precedesWeak_act_iff (Phi : TriEquiv C) (s t : Slicing C) :
    (Phi.act s).PrecedesWeak C (Phi.act t) ↔ s.PrecedesWeak C t := by
  constructor
  · intro h phi E hE
    have hMap : (Phi.act s).P phi (Phi.e.functor.obj E) := by
      change s.P phi (Phi.e.inverse.obj (Phi.e.functor.obj E))
      exact ObjectProperty.prop_of_iso _ (Phi.e.unitIso.app E) hE
    have hBound := h phi (Phi.e.functor.obj E) hMap
    have hInv := (Slicing.mapEquiv_leProp_iff Phi.e t phi
      (Phi.e.functor.obj E)).mp hBound
    exact (t.leProp C phi).prop_of_iso (Phi.e.unitIso.app E).symm hInv
  · intro h phi E hE
    apply (Slicing.mapEquiv_leProp_iff Phi.e t phi E).mpr
    exact h phi (Phi.e.inverse.obj E) hE

/-- The quotient autoequivalence action preserves the strict slicing order. -/
theorem AutQuot.precedes_smul_iff (q : AutQuot C) (s t : Slicing C) :
    (q • s).Precedes C (q • t) ↔ s.Precedes C t := by
  induction q using _root_.Quotient.inductionOn with
  | _ Phi => exact Phi.precedes_act_iff s t

/-- The quotient autoequivalence action preserves the weak slicing order. -/
theorem AutQuot.precedesWeak_smul_iff (q : AutQuot C) (s t : Slicing C) :
    (q • s).PrecedesWeak C (q • t) ↔ s.PrecedesWeak C t := by
  induction q using _root_.Quotient.inductionOn with
  | _ Phi => exact Phi.precedesWeak_act_iff s t

universe u'

variable [IsTriangulated C]
variable {Lambda : Type u'} [AddCommGroup Lambda] (v : K₀ C →+ Lambda)

/-- Forgetting the compatible lattice automorphism turns the
`AutPairQuot` action's underlying slicing into the `AutQuot` action. -/
theorem AutPairQuot.smul_slicing (q : AutPairQuot v)
    (sigma : StabilityCondition.WithClassMap C v) :
    (q • sigma).slicing = (AutPairQuot.toAutQuot q) • sigma.slicing := by
  induction q using _root_.Quotient.inductionOn with
  | _ a => rfl

/-- The `AutPairQuot` action on stability conditions preserves the strict
slicing order.  The compatible class-lattice datum affects the charge but not
this comparison of the underlying slicings. -/
theorem AutPairQuot.precedes_smul_stability_iff (q : AutPairQuot v)
    (sigma tau : StabilityCondition.WithClassMap C v) :
    CategoryTheory.Triangulated.Slicing.Precedes
      C (q • sigma).slicing (q • tau).slicing ↔
      CategoryTheory.Triangulated.Slicing.Precedes
        C sigma.slicing tau.slicing := by
  induction q using _root_.Quotient.inductionOn with
  | _ a => exact a.Φ.precedes_act_iff sigma.slicing tau.slicing

/-- The `AutPairQuot` action on stability conditions preserves the weak
slicing order. -/
theorem AutPairQuot.precedesWeak_smul_stability_iff (q : AutPairQuot v)
    (sigma tau : StabilityCondition.WithClassMap C v) :
    CategoryTheory.Triangulated.Slicing.PrecedesWeak
      C (q • sigma).slicing (q • tau).slicing ↔
      CategoryTheory.Triangulated.Slicing.PrecedesWeak
        C sigma.slicing tau.slicing := by
  induction q using _root_.Quotient.inductionOn with
  | _ a => exact a.Φ.precedesWeak_act_iff sigma.slicing tau.slicing

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
