/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Extrema

/-!
# The extremal phases are monotone along monomorphisms and epimorphisms

`Uniqueness/Extrema.lean` pins `φ⁺` and `φ⁻` down for a single object.  This
file compares them across a morphism:

* `phiPlus_le_of_mono` — a subobject cannot have a higher maximal phase than
  the object containing it, because its maximal destabilizing subobject is a
  semistable subobject of the ambient object.
* `phiMinus_le_of_epi` — a quotient cannot have a lower minimal phase than the
  object it comes from, because the composite onto the last HN factor of the
  quotient would be a nonzero epimorphism that `φ⁻` forces to vanish.

The two together are what turn Hom-vanishing against a semistable target into
Hom-vanishing against a general one: the image of a map is a quotient of the
source and a subobject of the target, so its own `φ⁻` and `φ⁺` are trapped
between theirs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

/-- The last HN factor, presented as a semistable quotient of the filtered
object at the lowest HN phase.  The quotient map is the last chain step read
through the isomorphism `chain n ≅ E`. -/
theorem exists_epi_to_semistable_phase_phiMinus {Z : StabilityFunction A}
    {E : A} (F : AbelianHNFiltration Z E) :
    ∃ (Q : A) (q : E ⟶ Q), Epi q ∧ Z.IsSemistable Q ∧ Z.phase Q = F.phiMinus := by
  have hn := F.nonempty
  let last : Fin F.n := ⟨F.n - 1, by lia⟩
  have hlast : F.chain last.succ = ⊤ := by
    have hindex : last.succ = ⟨F.n, by lia⟩ := Fin.ext (by simp [last]; lia)
    rw [hindex, F.chain_top]
  haveI : IsIso (F.chain last.succ).arrow := by
    rw [hlast]
    infer_instance
  refine ⟨cokernel (Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
      (le_of_lt (F.chain_strictMono last.castSucc_lt_succ))),
    inv (F.chain last.succ).arrow ≫
      cokernel.π (Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
        (le_of_lt (F.chain_strictMono last.castSucc_lt_succ))),
    inferInstance, F.factor_semistable last, ?_⟩
  exact F.factor_phase last

/-- **`φ⁺` is monotone along monomorphisms.**  The maximal destabilizing
subobject of the source maps to a semistable subobject of the target of the
same phase, and no semistable subobject exceeds `φ⁺`. -/
theorem phiPlus_le_of_mono {Z : StabilityFunction A} {X Y : A}
    (F : AbelianHNFiltration Z X) (G : AbelianHNFiltration Z Y)
    (i : X ⟶ Y) [Mono i] : F.phiPlus ≤ G.phiPlus := by
  have hn := F.nonempty
  set M : Subobject X := F.chain ⟨1, by lia⟩ with hM
  have hMss : Z.IsSemistable (M : A) := F.chain_one_isSemistable
  have hMphase : Z.phase (M : A) = F.phiPlus := F.phase_chain_one
  have hmap : Z.IsSemistable (((Subobject.map i).obj M : A)) :=
    Z.isSemistable_of_iso (StabilityFunction.Subobject.mapMonoIso i M).symm hMss
  have hle := G.semistable_phase_le_phiPlus hmap
  rwa [Z.phase_eq_of_iso (StabilityFunction.Subobject.mapMonoIso i M), hMphase]
    at hle

/-- **`φ⁻` is monotone along epimorphisms.**  A strict drop would make the
composite onto the last HN factor of the target a nonzero epimorphism that
`hom_eq_zero_to_semistable_of_phase_lt_phiMinus` forces to vanish. -/
theorem phiMinus_le_of_epi {Z : StabilityFunction A} {X Y : A}
    (F : AbelianHNFiltration Z X) (G : AbelianHNFiltration Z Y)
    (p : X ⟶ Y) [Epi p] : F.phiMinus ≤ G.phiMinus := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨Q, q, hq, hQ, hQphase⟩ := G.exists_epi_to_semistable_phase_phiMinus
  haveI := hq
  have hzero : p ≫ q = 0 :=
    F.hom_eq_zero_to_semistable_of_phase_lt_phiMinus hQ (hQphase ▸ hlt) (p ≫ q)
  exact hQ.1 (IsZero.of_epi_eq_zero (p ≫ q) hzero)

end AbelianHNFiltration

end CategoryTheory.Triangulated
