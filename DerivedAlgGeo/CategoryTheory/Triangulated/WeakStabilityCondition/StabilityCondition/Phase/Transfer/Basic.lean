/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseShift
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport

/-!
# Preimage transfer of slicings

For a functor `F : C ⥤ D` and a slicing `s` on `D`, the raw phase collection

`P_F(phi)(E) := s.P phi (F.obj E)`

is the common categorical core of both constructions in arXiv:2607.28411v1,
Definitions 3.1 and 3.6.  Remarks 3.2 and 3.7 explicitly warn that this raw
collection need not be a slicing, even when `F` is conservative.  Accordingly,
`Slicing.PreimageData` records precisely the two slicing axioms which do not
follow formally from functoriality and shift compatibility: Hom-vanishing and
HN existence.

This factorization is deliberately honest about the theorem boundary.  The
geometric inducing results (Propositions 3.3 and 3.8, via Appendix A) are
expected to construct `PreimageData`; bare adjunction and conservativity do not.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [HasShift E ℤ]
  [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- The raw inverse-image phase collection along a functor.

It is intentionally only an `ObjectProperty`, not a `Slicing`: conservativity
alone does not supply Hom-vanishing or HN filtrations. -/
def Slicing.preimagePhase (s : Slicing D) (F : C ⥤ D) (phi : ℝ) :
    ObjectProperty C := fun E => s.P phi (F.obj E)

/-- Source-facing name for Definition 3.1 of arXiv:2607.28411v1.  A geometric
pullback slicing is computed using the direct-image functor. -/
abbrev Slicing.pullbackPhaseCollection (s : Slicing D) (push : C ⥤ D) :=
  s.preimagePhase push

/-- Source-facing name for Definition 3.6 of arXiv:2607.28411v1.  A geometric
pushforward slicing is computed using the inverse-image functor. -/
abbrev Slicing.pushforwardPhaseCollection (s : Slicing D) (pull : C ⥤ D) :=
  s.preimagePhase pull

/-- The genuinely missing axioms for turning the raw inverse-image phase
collection into a slicing.

Closure under isomorphisms, zero membership, and the shift law follow from
`s` and `F.CommShift`.  The two fields here are exactly what remains. -/
structure Slicing.PreimageData (s : Slicing D) (F : C ⥤ D) : Prop where
  /-- Hom-vanishing for objects whose images lie in separated phase slices. -/
  hom_vanishing : ∀ (phi₁ phi₂ : ℝ) (A B : C), phi₂ < phi₁ →
    s.P phi₁ (F.obj A) → s.P phi₂ (F.obj B) → ∀ g : A ⟶ B, g = 0
  /-- HN filtrations in the source with factors detected by `F`. -/
  hn_exists : ∀ E : C, Nonempty (HNFiltration C (s.preimagePhase F) E)

/-- The identity functor satisfies the two non-formal preimage axioms. -/
theorem Slicing.preimageData_id (s : Slicing C) :
    s.PreimageData (Functor.id C) where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g :=
    s.hom_vanishing phi₁ phi₂ A B hphi hA hB g
  hn_exists E := s.hn_exists E

/-- Construct the genuine inverse-image slicing once the two non-formal axioms
have been supplied. -/
@[nolint unusedArguments]
def Slicing.preimage (s : Slicing D) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : s.PreimageData F) : Slicing C where
  P := s.preimagePhase F
  closedUnderIso phi := ⟨by
    intro X Y e hE
    change s.P phi (F.obj Y)
    exact ObjectProperty.prop_of_iso _ (F.mapIso e) hE⟩
  zero_mem phi := s.zero_mem_of_isZero D phi _ (F.map_isZero (isZero_zero C))
  shift_iff phi E := by
    change s.P phi (F.obj E) ↔
      s.P (phi + 1) (F.obj ((shiftFunctor C (1 : ℤ)).obj E))
    rw [s.shift_iff phi (F.obj E)]
    exact ⟨fun hE => ObjectProperty.prop_of_iso _
      ((F.commShiftIso (1 : ℤ)).app E).symm hE,
      fun hE => ObjectProperty.prop_of_iso _
        ((F.commShiftIso (1 : ℤ)).app E) hE⟩
  hom_vanishing := h.hom_vanishing
  hn_exists := h.hn_exists

/-- Preimage witnesses compose in the same contravariant order as their
functors.  The second witness is measured against the slicing constructed by
the first stage, so its HN filtrations already have exactly the phases needed
for the composite. -/
theorem Slicing.PreimageData.comp {s : Slicing E} {G : D ⥤ E}
    [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (hG : s.PreimageData G) {F : C ⥤ D}
    (hF : (s.preimage G hG).PreimageData F) :
    s.PreimageData (F ⋙ G) where
  hom_vanishing := hF.hom_vanishing
  hn_exists := hF.hn_exists

/-- A natural isomorphism of detecting functors transports the two non-formal
preimage axioms.  In particular, the HN factors are unchanged because phase
membership is invariant under the component isomorphisms. -/
theorem Slicing.PreimageData.ofIso {s : Slicing D} {F G : C ⥤ D}
    (hF : s.PreimageData F) (e : F ≅ G) : s.PreimageData G where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g :=
    hF.hom_vanishing phi₁ phi₂ A B hphi
      (ObjectProperty.prop_of_iso _ (e.app A).symm hA)
      (ObjectProperty.prop_of_iso _ (e.app B).symm hB) g
  hn_exists X := by
    have hphase : s.preimagePhase G = s.preimagePhase F := by
      funext phi Y
      apply propext
      exact ⟨ObjectProperty.prop_of_iso _ (e.app Y).symm,
        ObjectProperty.prop_of_iso _ (e.app Y)⟩
    rw [hphase]
    exact hF.hn_exists X

@[simp]
theorem Slicing.preimage_P (s : Slicing D) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : s.PreimageData F)
    (phi : ℝ) (E : C) :
    (s.preimage F h).P phi E ↔ s.P phi (F.obj E) := by
  rfl

@[simp]
theorem Slicing.preimage_id (s : Slicing C) :
    s.preimage (Functor.id C) s.preimageData_id = s := by
  apply Slicing.ext
  rfl

/-- Constructing a preimage slicing in two stages agrees with constructing it
along the composite functor.  The statement is independent of the proof terms
used to witness the slicing axioms. -/
@[simp]
theorem Slicing.preimage_comp (s : Slicing E) (G : D ⥤ E)
    [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (hG : s.PreimageData G) (F : C ⥤ D)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : (s.preimage G hG).PreimageData F) :
    s.preimage (F ⋙ G) (hG.comp hF) =
      (s.preimage G hG).preimage F hF := by
  apply Slicing.ext
  rfl

/-- Preimage slicings are invariant under a natural isomorphism of the
detecting functors. -/
theorem Slicing.preimage_iso (s : Slicing D) (F G : C ⥤ D)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (hF : s.PreimageData F) (e : F ≅ G) :
    s.preimage G (hF.ofIso e) = s.preimage F hF := by
  apply Slicing.ext
  funext phi X
  apply propext
  exact ⟨ObjectProperty.prop_of_iso _ (e.app X).symm,
    ObjectProperty.prop_of_iso _ (e.app X)⟩

/-- A triangulated equivalence supplies the two non-formal preimage axioms.

Unlike `Slicing.mapEquiv`, this theorem allows the source and target
categories to differ.  HN filtrations are transported through the inverse
functor and then identified with the original object by the unit isomorphism.
-/
theorem Slicing.preimageData_equivalence (s : Slicing D) (e : C ≌ D)
    [e.inverse.Additive]
    [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.functor.IsTriangulated] [e.inverse.IsTriangulated] :
    s.PreimageData e.functor where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g := by
    apply e.functor.map_injective
    simpa using s.hom_vanishing phi₁ phi₂ (e.functor.obj A)
      (e.functor.obj B) hphi hA hB (e.functor.map g)
  hn_exists E := by
    obtain ⟨Fil⟩ := s.hn_exists (e.functor.obj E)
    exact ⟨CategoryTheory.Triangulated.HNFiltration.ofIso C
      (HNFiltration.mapF
        (P' := fun phi X => s.P phi (e.functor.obj X)) Fil e.inverse
        (fun phi X h => ObjectProperty.prop_of_iso _
          (e.counitIso.app X).symm h))
      (e.unitIso.app E).symm⟩

/-- The preimage slicing along a triangulated equivalence is detected exactly
by the equivalence functor. -/
theorem Slicing.preimage_equivalence_P (s : Slicing D) (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.functor.IsTriangulated] [e.inverse.IsTriangulated]
    (phi : ℝ) (X : C) :
    (s.preimage e.functor (s.preimageData_equivalence e)).P phi X ↔
      s.P phi (e.functor.obj X) :=
  Iff.rfl

/-- For a faithful functor, target Hom-vanishing supplies the Hom component of
`PreimageData`; only HN existence remains to be proved. -/
def Slicing.PreimageData.ofFaithful (s : Slicing D) (F : C ⥤ D)
    [F.Additive] [F.Faithful]
    (hn : ∀ E : C, Nonempty (HNFiltration C (s.preimagePhase F) E)) :
    s.PreimageData F where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g := by
    apply F.map_injective
    simpa using s.hom_vanishing phi₁ phi₂ (F.obj A) (F.obj B)
      hphi hA hB (F.map g)
  hn_exists := hn

/-- The preimage lifting criterion is stable under a uniform translation of
all phases. -/
def Slicing.PreimageData.phaseShift {s : Slicing D} {F : C ⥤ D}
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (h : s.PreimageData F) (t : ℝ) :
    Slicing.PreimageData (s.phaseShift D t) F where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g :=
    h.hom_vanishing (phi₁ + t) (phi₂ + t) A B (by linarith) hA hB g
  hn_exists E := by
    obtain ⟨Fil⟩ := h.hn_exists E
    change Nonempty (HNFiltration C
      (fun psi X => s.P (psi + t) (F.obj X)) E)
    exact ⟨@CategoryTheory.Triangulated.HNFiltration.phaseShift C _ _ _ _ _ _
      (s.preimage F h) E Fil t⟩

/-- Source-facing genuine pullback name.  Its explicit `PreimageData` argument
is the formal reminder that conservativity alone is insufficient. -/
abbrev Slicing.pullback (s : Slicing D) (push : C ⥤ D) [push.Additive]
    [push.CommShift ℤ] [push.IsTriangulated] (h : s.PreimageData push) :
    Slicing C := s.preimage push h

/-- Source-facing genuine pushforward name. -/
abbrev Slicing.pushforward (s : Slicing D) (pull : C ⥤ D) [pull.Additive]
    [pull.CommShift ℤ] [pull.IsTriangulated] (h : s.PreimageData pull) :
    Slicing C := s.preimage pull h

end CategoryTheory.Triangulated
