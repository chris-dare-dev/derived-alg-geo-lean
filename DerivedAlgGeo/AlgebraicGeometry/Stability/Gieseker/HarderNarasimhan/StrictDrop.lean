/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.Seesaw
import DerivedAlgGeo.CategoryTheory.SubobjectCorrespondence

/-!
# The slope drops strictly on the quotient by the maximal destabilizing subobject

This is the step that makes Harder–Narasimhan recursion work, and it carries two consequences at
once: the slopes of successive factors strictly decrease, and the recursion terminates.

## The statement

If `B` is maximal destabilizing in `F`, then every nonzero subobject of `F / B` has slope
strictly below that of `B`. In particular the maximal slope of `F / B` is strictly below that of
`B`, which is `StrictAnti` for the filtration, and `F / B` has no nonzero subobject of slope `⊤`,
so `F / B` is pure and its own maximal destabilizing subobject has positive multiplicity.

## The proof, and why it needs both halves of maximality

Take a nonzero `C ⊆ F / B` and pull it back to `pb ⊆ F`, which contains `B`. The correspondence
supplies the short exact sequence `0 ⟶ B ⟶ pb ⟶ C ⟶ 0`. Suppose the slope of `C` were at least
that of `B`. The see-saw inequality then puts the slope of `pb` at least that of `B`, while
maximality of the slope puts it at most; so they are equal, and `pb` attains the maximal slope
while strictly containing `B`. That contradicts the *second* clause of
`IsMaximalDestabilizing` — maximality in the subobject order among the subobjects attaining the
slope. The first clause alone is not enough, which is why that clause is carried.

## Termination

Because `F / B` is pure, the maximal destabilizing subobject of `F / B` has positive
multiplicity, and multiplicity is additive, so the multiplicity of the next quotient is strictly
smaller. That is the measure the recursion descends on; the chain condition of `MuHNInput` is
what makes the first step available at all, not what makes the recursion stop.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-- A subobject containing a nonzero subobject is itself nonzero. -/
theorem not_isZero_of_le {F : Coh X} {B C : Subobject F} (hBC : B ≤ C)
    (hB : ¬IsZero (B : Coh X)) : ¬IsZero (C : Coh X) := by
  intro hC
  exact hB (IsZero.of_mono (Subobject.ofLE B C hBC) hC)

/-- **The slope drops strictly past the maximal destabilizing subobject.**

Every nonzero subobject of the quotient has slope strictly below that of `B`. See the module
docstring: the proof uses the see-saw inequality together with *both* clauses of
`IsMaximalDestabilizing`. -/
theorem topSlope_lt_of_maximalDestabilizing (h : MuPositivityData P) {F : Coh X}
    {B : Subobject F} (hB : IsMaximalDestabilizing h F B)
    (C : Subobject (cokernel (B : Subobject F).arrow))
    (hC : ¬IsZero ((C : Subobject (cokernel B.arrow)) : Coh X)) :
    (P.weakSlopeData h).topSlope ((C : Subobject (cokernel B.arrow)) : Coh X) <
      (P.weakSlopeData h).topSlope ((B : Subobject F) : Coh X) := by
  classical
  set pb := (Subobject.pullback (cokernel.π B.arrow)).obj C with hpb
  have hBpb : B ≤ pb := CategoryTheory.Abelian.le_pullback_cokernel B C
  have hpbne : ¬IsZero ((pb : Subobject F) : Coh X) := not_isZero_of_le hBpb hB.1
  have hSE := CategoryTheory.Abelian.shortExact_ofLE_pullbackπ B C
  by_contra hcon
  push Not at hcon
  -- the see-saw puts the slope of the extension at least that of `B`
  have hseesaw := topSlope_le_of_shortExact h hSE hC hcon
  -- but the maximal slope puts it at most, so they agree
  have hle := hB.2.1 pb hpbne
  have heq : (P.weakSlopeData h).topSlope ((pb : Subobject F) : Coh X) =
      (P.weakSlopeData h).topSlope ((B : Subobject F) : Coh X) :=
    le_antisymm hle hseesaw
  -- so `pb` attains the maximal slope, and strictly contains `B`
  refine hB.2.2 pb hpbne heq (lt_of_le_of_ne hBpb ?_)
  intro hBeq
  -- if the pullback were `B` itself the quotient `C` would be zero
  apply hC
  haveI hepi : Epi (Subobject.pullbackπ (cokernel.π B.arrow) C) :=
    CategoryTheory.Abelian.epi_pullbackπ B C
  have hpbB : pb ≤ B := le_of_eq hBeq.symm
  haveI hiso : IsIso (Subobject.ofLE B pb hBpb) :=
    ⟨⟨Subobject.ofLE pb B hpbB,
      by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl],
      by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]⟩⟩
  have hzero : Subobject.pullbackπ (cokernel.π B.arrow) C = 0 := by
    have hcomp := CategoryTheory.Abelian.ofLE_pullbackπ_cokernel_eq_zero B C
    calc Subobject.pullbackπ (cokernel.π B.arrow) C
        = inv (Subobject.ofLE B pb hBpb) ≫ Subobject.ofLE B pb hBpb ≫
            Subobject.pullbackπ (cokernel.π B.arrow) C := by
          rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      _ = 0 := by rw [hcomp, comp_zero]
  rw [hzero] at hepi
  exact IsZero.of_epi_zero ((pb : Subobject F) : Coh X) _

/-- **The quotient by the maximal destabilizing subobject is pure.**

A nonzero subobject of multiplicity zero would have slope `⊤`, which
`topSlope_lt_of_maximalDestabilizing` forbids. This is what makes the recursion terminate: the
maximal destabilizing subobject of the quotient then has positive multiplicity, so by additivity
the next quotient has strictly smaller multiplicity. -/
theorem multiplicity_pos_of_maximalDestabilizing (h : MuPositivityData P) {F : Coh X}
    {B : Subobject F} (hB : IsMaximalDestabilizing h F B)
    (C : Subobject (cokernel (B : Subobject F).arrow))
    (hC : ¬IsZero ((C : Subobject (cokernel B.arrow)) : Coh X)) :
    0 < P.multiplicity ((C : Subobject (cokernel B.arrow)) : Coh X) := by
  have hnn := h.multiplicity_nonneg ((C : Subobject (cokernel B.arrow)) : Coh X)
  have hne : P.multiplicity ((C : Subobject (cokernel B.arrow)) : Coh X) ≠ 0 := by
    intro h0
    have hlt := topSlope_lt_of_maximalDestabilizing h hB C hC
    rw [weakSlopeData_topSlope_of_multiplicity_zero h h0] at hlt
    exact absurd hlt (by simp)
  omega

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
