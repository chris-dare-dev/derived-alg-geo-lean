/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.TwoHeartEmbedding
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Transfer.Basic

/-!
# Phase-indexed induced t-structures

Corollary A.23 of arXiv:2607.28411v1 does not construct a preimage slicing
directly from an adjunction.  It first applies Theorem A.17 at every real
phase and obtains a family of bounded t-structures on the source.  Formula
(A.8) recognizes their two halves by the target slicing:

* `D_X,phi^{<= 0}` consists of the objects whose image lies in `P_Y(>= phi)`;
* `D_X,phi^{>= 1}` consists of the objects whose image lies in `P_Y(< phi)`.

This file records that genuine intermediate output.  It also proves the
Hom-vanishing half of the preimage-slicing theorem from t-structure
orthogonality.  Constructing source HN filtrations by iterated phase
truncation is deliberately a separate theorem boundary; it is not hidden in
this structure.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The bounded output of applying the Polishchuk inducing theorem at every
real phase, expressed by the recognition formulas (A.8).

This is output data, not a replacement for the large-category hypotheses of
Theorem A.17.  In particular, the structure contains neither an adjunction
nor an HN-existence field. -/
structure Slicing.InducedTStructures (s : Slicing D) (F : C ⥤ D) where
  /-- The source t-structure induced at the phase `phi`. -/
  tStructure : ℝ → TStructure C
  /-- Formula (A.8), connective half. -/
  le_zero_iff (phi : ℝ) (E : C) :
    (tStructure phi).IsLE E 0 ↔ s.geProp D phi (F.obj E)
  /-- Formula (A.8), coconnective half. -/
  ge_one_iff (phi : ℝ) (E : C) :
    (tStructure phi).IsGE E 1 ↔ s.ltProp D phi (F.obj E)

namespace Slicing.InducedTStructures

/-- Phase-indexed recognition formulas are invariant under a natural
isomorphism of the detecting functor. -/
def ofIso {s : Slicing D} {F G : C ⥤ D}
    (h : s.InducedTStructures F) (e : F ≅ G) :
    s.InducedTStructures G where
  tStructure := h.tStructure
  le_zero_iff phi E :=
    (h.le_zero_iff phi E).trans
      ((s.geProp D phi).prop_iff_of_iso (e.app E))
  ge_one_iff phi E :=
    (h.ge_one_iff phi E).trans
      ((s.ltProp D phi).prop_iff_of_iso (e.app E))

/-- Formula (A.8) supplies Hom-vanishing for the raw preimage phase
collection.  This is the first non-formal slicing axiom in
`Slicing.PreimageData`. -/
theorem hom_vanishing {s : Slicing D} {F : C ⥤ D}
    (h : s.InducedTStructures F) :
    ∀ (phi₁ phi₂ : ℝ) (A B : C), phi₂ < phi₁ →
      s.P phi₁ (F.obj A) → s.P phi₂ (F.obj B) →
        ∀ g : A ⟶ B, g = 0 := by
  intro phi₁ phi₂ A B hphi hA hB g
  let t := h.tStructure phi₁
  apply t.zero_of_isLE_of_isGE g 0 1 (by omega)
  · exact (h.le_zero_iff phi₁ A).2 (s.geProp_of_semistable D hA)
  · apply (h.ge_one_iff phi₁ B).2
    exact s.ltProp_of_hn D
      (HNFiltration.single D (F.obj B) phi₂ hB) phi₁
      (fun _ ↦ by simpa [HNFiltration.single] using hphi)
      (by change 0 < 1; omega)

/-- Once the finite phase-truncation argument has supplied source HN
filtrations, the phase-indexed t-structures complete the genuine preimage
slicing data.  The only argument left explicit here is exactly the second
field of `Slicing.PreimageData`, not a disguised copy of the whole output. -/
theorem toPreimageData {s : Slicing D} {F : C ⥤ D}
    (h : s.InducedTStructures F)
    (hn : ∀ E : C, Nonempty (HNFiltration C (s.preimagePhase F) E)) :
    s.PreimageData F where
  hom_vanishing := h.hom_vanishing
  hn_exists := hn

end Slicing.InducedTStructures

/-- The identity functor gives an inhabited model of the phase-indexed
recognition formulas.  Its t-structure at `phi` is the dual half-open
t-structure `P([phi, phi + 1))`. -/
def Slicing.inducedTStructuresId (s : Slicing C) [IsTriangulated C] :
    s.InducedTStructures (Functor.id C) where
  tStructure phi := (s.phaseShift C phi).toDualTStructure C
  le_zero_iff phi E := by
    constructor
    · intro h
      have h' := h.le
      change (s.phaseShift C phi).geProp C (-((0 : ℤ) : ℝ)) E at h'
      exact (s.phaseShift_geProp_zero C phi E).mp (by simpa using h')
    · intro h
      refine ⟨?_⟩
      change (s.phaseShift C phi).geProp C (-((0 : ℤ) : ℝ)) E
      simpa using (s.phaseShift_geProp_zero C phi E).mpr h
  ge_one_iff phi E := by
    constructor
    · intro h
      have h' := h.ge
      change (s.phaseShift C phi).ltProp C (1 - ((1 : ℤ) : ℝ)) E at h'
      exact (s.phaseShift_ltProp_zero C phi E).mp (by simpa using h')
    · intro h
      refine ⟨?_⟩
      change (s.phaseShift C phi).ltProp C (1 - ((1 : ℤ) : ℝ)) E
      simpa using (s.phaseShift_ltProp_zero C phi E).mpr h

end CategoryTheory.Triangulated
