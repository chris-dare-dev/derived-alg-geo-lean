/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Transfer.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Order.Functoriality

/-!
# Phases and orders under preimage transfer

Once a raw preimage collection has been proved to be a slicing, its HN
filtrations map forward without changing their phases.  If the functor also
reflects zero objects, this identifies the intrinsic extreme phases, hence the
strict and weak phase windows.  This proves Lemmas 3.5 and 3.9 and the order
clause of Remark 3.14(3) of arXiv:2607.28411v1 at the categorical level.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A functor reflects zero objects.  This is the object-level consequence of
conservativity used by phase transfer. -/
def ReflectsZeroObjects (F : C ⥤ D) : Prop :=
  ∀ E : C, IsZero (F.obj E) → IsZero E

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasShift C ℤ] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- A faithful additive functor reflects zero objects. -/
theorem Functor.reflectsZeroObjects_of_faithful (F : C ⥤ D)
    [F.Additive] [F.Faithful] : ReflectsZeroObjects F := by
  intro E hFE
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  simpa using hFE.eq_of_src (F.map (𝟙 E)) 0

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasShift D ℤ] in
/-- A conservative additive functor reflects zero objects.  This is the exact
object-level use of conservativity in the source phase identities. -/
theorem Functor.reflectsZeroObjects_of_conservative (F : C ⥤ D)
    [F.Additive] [F.ReflectsIsomorphisms] : ReflectsZeroObjects F := by
  intro E hFE
  haveI : IsIso (F.map (0 : E ⟶ E)) := by
    rw [F.map_zero]
    exact (isIsoZero_iff_source_target_isZero (F.obj E) (F.obj E)).mpr
      ⟨hFE, hFE⟩
  haveI : IsIso (0 : E ⟶ E) :=
    Functor.ReflectsIsomorphisms.reflects F (0 : E ⟶ E)
  exact (isIsoZero_iff_source_target_isZero E E).mp
    (show IsIso (0 : E ⟶ E) from inferInstance) |>.1

variable (s : Slicing D) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated] (h : s.PreimageData F)

/-- An HN filtration for the preimage slicing maps to an HN filtration with
the same phases in the target slicing. -/
def HNFiltration.mapPreimage {E : C}
    (Fil : HNFiltration C (s.preimage F h).P E) :
    HNFiltration D s.P (F.obj E) :=
  CategoryTheory.Triangulated.HNFiltration.mapF Fil F (fun _ _ hE => hE)

@[simp]
theorem HNFiltration.mapPreimage_n {E : C}
    (Fil : HNFiltration C (s.preimage F h).P E) :
    (Fil.mapPreimage s F h).n = Fil.n := rfl

@[simp]
theorem HNFiltration.mapPreimage_phi {E : C}
    (Fil : HNFiltration C (s.preimage F h).P E) (j : Fin Fil.n) :
    (Fil.mapPreimage s F h).φ j = Fil.φ j := rfl

/-- The highest HN phase is computed after applying the detecting functor. -/
theorem Slicing.preimage_phiPlus (hzero : ReflectsZeroObjects F)
    (E : C) (hE : ¬IsZero E) :
    (s.preimage F h).phiPlus C E hE =
      s.phiPlus D (F.obj E) (fun hFE => hE (hzero E hFE)) := by
  obtain ⟨Fil, hn, hfirst, _⟩ :=
    (s.preimage F h).exists_hn_nonzero_boundaries C hE
  let Fil' := Fil.mapPreimage s F h
  have hfirst' : ¬IsZero (Fil'.triangle ⟨0, hn⟩).obj₃ := by
    intro hz
    exact hfirst (hzero _ hz)
  calc
    (s.preimage F h).phiPlus C E hE = Fil.φ ⟨0, hn⟩ :=
      (s.preimage F h).phiPlus_eq C E hE Fil hn hfirst
    _ = Fil'.φ ⟨0, hn⟩ := rfl
    _ = s.phiPlus D (F.obj E) (fun hFE => hE (hzero E hFE)) :=
      (s.phiPlus_eq D (F.obj E) (fun hFE => hE (hzero E hFE))
        Fil' hn hfirst').symm

/-- The lowest HN phase is computed after applying the detecting functor. -/
theorem Slicing.preimage_phiMinus (hzero : ReflectsZeroObjects F)
    (E : C) (hE : ¬IsZero E) :
    (s.preimage F h).phiMinus C E hE =
      s.phiMinus D (F.obj E) (fun hFE => hE (hzero E hFE)) := by
  obtain ⟨Fil, hn, _, hlast⟩ :=
    (s.preimage F h).exists_hn_nonzero_boundaries C hE
  let Fil' := Fil.mapPreimage s F h
  have hlast' : ¬IsZero (Fil'.triangle ⟨Fil'.n - 1, by simpa [Fil'] using hn⟩).obj₃ := by
    change ¬IsZero (F.obj (Fil.triangle ⟨Fil.n - 1, by lia⟩).obj₃)
    intro hz
    exact hlast (hzero _ hz)
  calc
    (s.preimage F h).phiMinus C E hE =
        Fil.φ ⟨Fil.n - 1, by lia⟩ :=
      (s.preimage F h).phiMinus_eq C E hE Fil hn hlast
    _ = Fil'.φ ⟨Fil'.n - 1, by simpa [Fil'] using hn⟩ := rfl
    _ = s.phiMinus D (F.obj E) (fun hFE => hE (hzero E hFE)) :=
      (s.phiMinus_eq D (F.obj E) (fun hFE => hE (hzero E hFE))
        Fil' (by simpa [Fil'] using hn) hlast').symm

/-- Strict upper phase windows are reflected by a preimage slicing. -/
theorem Slicing.preimage_ltProp_iff (hzero : ReflectsZeroObjects F)
    (phi : ℝ) (E : C) :
    (s.preimage F h).ltProp C phi E ↔ s.ltProp D phi (F.obj E) := by
  by_cases hE : IsZero E
  · exact iff_of_true (Or.inl hE) (Or.inl (F.map_isZero hE))
  · have hFE : ¬IsZero (F.obj E) := fun hz => hE (hzero E hz)
    constructor
    · intro hlt
      apply s.ltProp_of_phiPlus_lt D hFE
      rw [← s.preimage_phiPlus F h hzero E hE]
      exact (s.preimage F h).phiPlus_lt_of_ltProp C hE hlt
    · intro hlt
      apply (s.preimage F h).ltProp_of_phiPlus_lt C hE
      rw [s.preimage_phiPlus F h hzero E hE]
      exact s.phiPlus_lt_of_ltProp D hFE hlt

/-- Weak upper phase windows are reflected by a preimage slicing. -/
theorem Slicing.preimage_leProp_iff (hzero : ReflectsZeroObjects F)
    (phi : ℝ) (E : C) :
    (s.preimage F h).leProp C phi E ↔ s.leProp D phi (F.obj E) := by
  by_cases hE : IsZero E
  · exact iff_of_true (Or.inl hE) (Or.inl (F.map_isZero hE))
  · have hFE : ¬IsZero (F.obj E) := fun hz => hE (hzero E hz)
    constructor
    · intro hle
      apply s.leProp_of_phiPlus_le D hFE
      rw [← s.preimage_phiPlus F h hzero E hE]
      exact (s.preimage F h).phiPlus_le_of_leProp C hE hle
    · intro hle
      apply (s.preimage F h).leProp_of_phiPlus_le C hE
      rw [s.preimage_phiPlus F h hzero E hE]
      exact s.phiPlus_le_of_leProp D hFE hle

/-- Preimage transfer commutes with real phase translation.  The HN proofs on
the two sides may differ, but slicings are determined by their phase slices. -/
theorem Slicing.preimage_phaseShift (t : ℝ)
    (ht : Slicing.PreimageData (s.phaseShift D t) F) :
    Slicing.preimage (s.phaseShift D t) F ht =
      (s.preimage F h).phaseShift C t := by
  apply Slicing.ext
  rfl

/-- Canonical form of phase-shift compatibility, using the phase-shifted
lifting data derived from `h`. -/
theorem Slicing.preimage_phaseShift_self (t : ℝ) :
    Slicing.preimage (s.phaseShift D t) F (h.phaseShift t) =
      (s.preimage F h).phaseShift C t :=
  s.preimage_phaseShift F h t (h.phaseShift t)

/-- A family of preimage constructions satisfying the lifting criterion gives
the exact objectwise interface used by the slicing-order API. -/
def Slicing.preimageOrderData (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (H : ∀ s : Slicing D, s.PreimageData F)
    (hzero : ReflectsZeroObjects F) :
    SlicingOrderPreimageData (fun s => s.preimage F (H s)) F.obj where
  semistable_iff _ _ _ := Iff.rfl
  ltProp_iff s phi E := s.preimage_ltProp_iff F (H s) hzero phi E
  leProp_iff s phi E := s.preimage_leProp_iff F (H s) hzero phi E

/-- Genuine preimage transfer preserves the strict slicing order. -/
theorem Slicing.Precedes.preimage (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated]
    (H : ∀ s : Slicing D, s.PreimageData F)
    (hzero : ReflectsZeroObjects F) {s t : Slicing D}
    (hst : s.Precedes D t) :
    (s.preimage F (H s)).Precedes C (t.preimage F (H t)) :=
  (Slicing.preimageOrderData F H hzero).precedes hst

/-- Genuine preimage transfer preserves the weak slicing order. -/
theorem Slicing.PrecedesWeak.preimage (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated]
    (H : ∀ s : Slicing D, s.PreimageData F)
    (hzero : ReflectsZeroObjects F) {s t : Slicing D}
    (hst : s.PrecedesWeak D t) :
    (s.preimage F (H s)).PrecedesWeak C (t.preimage F (H t)) :=
  (Slicing.preimageOrderData F H hzero).precedesWeak hst

end CategoryTheory.Triangulated
