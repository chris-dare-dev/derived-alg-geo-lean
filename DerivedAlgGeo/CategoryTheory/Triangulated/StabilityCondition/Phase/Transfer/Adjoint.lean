/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CoreConsequences
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseCutClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The adjoint transposition behind Proposition 3.8

Proposition 3.8 of arXiv:2607.28411v1 proves that `f_♯𝒫` is a slicing under
the hypothesis (3.2), `f^* f_* 𝒫(φ) ⊆ 𝒫(≤ φ)`.  Its proof has one categorical
step and one appeal to Appendix A: the hypothesis of Corollary A.23 for
`Φ = f^*` is `f^* f_! 𝒫(φ) ⊆ 𝒫(≥ φ)`, and it is obtained from (3.2) by
transposing twice along the adjunctions `f_! ⊣ f^* ⊣ f_*`:

`Hom(f^* f_! E, G) ≅ Hom(f_! E, f_* G) ≅ Hom(E, f^* f_* G) = 0`

for `E ∈ 𝒫(φ)` and `G ∈ 𝒫(< φ)`.  This file proves that step for an
arbitrary functor `F` with a left adjoint `L` and a right adjoint `R`.

## Main definitions

* `Slicing.MapsSemistableLE`: an endofunctor sends every semistable object of
  phase `φ` into `𝒫(≤ φ)`.  At the comonad `f^* f_*` this is the paper's
  condition (3.2).
* `Slicing.MapsSemistableGE`: an endofunctor sends every semistable object of
  phase `φ` into `𝒫(≥ φ)`.  At the monad `f^* f_!` this is the bounded form
  of the Corollary A.23 hypothesis.

## Main results

* `Slicing.MapsSemistableLE.leProp_of_leProp`: the condition, stated on
  semistable objects, extends to every object with HN phases at most `t`, by
  applying the exact endofunctor to the HN filtration and using closure of the
  phase cut under towers.
* `Slicing.MapsSemistableGE.of_mapsSemistableLE`: the transposition itself.

## Implementation notes

The two predicates are stated for an arbitrary endofunctor rather than for
the comonad and monad of a pair of adjunctions, since neither statement uses
the adjunction structure; the adjunctions enter only in the transposition.
Theorem A.17 of the paper calls its hypothesis on `Φ Φ_L` the monad
hypothesis; `MapsSemistableGE` is the bounded phase-cut form in which
Corollary A.23 uses it.

The composite `R ⋙ F` must be exact, which is all the phase-cut half needs,
and `L` and `F` need only preserve zero morphisms, for the two
transpositions.  The proofs never use exactness of `R` or `F` separately, so
the hypothesis is stated on the composite, and the source category `C` needs
no triangulated structure at all.

What this file does not do is verify (3.2) geometrically or feed the
conclusion to the Appendix A machinery on `Dqc`; those are the remaining
steps of Proposition 3.8 and stay explicit.

## References

* arXiv:2607.28411v1, Proposition 3.8 and Corollary A.23.
* arXiv:2601.22994, Proposition 3.4, the smooth projective case over `ℂ`.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An endofunctor `G` sends every semistable object of phase `φ` into the
upper phase cut `𝒫(≤ φ)`.  For the comonad `G = f^* f_*` of the adjunction
`f^* ⊣ f_*` this is condition (3.2) of arXiv:2607.28411v1. -/
def Slicing.MapsSemistableLE (s : Slicing D) (G : D ⥤ D) : Prop :=
  ∀ (φ : ℝ) (E : D), s.P φ E → s.leProp D φ (G.obj E)

/-- An endofunctor `G` sends every semistable object of phase `φ` into the
lower phase cut `𝒫(≥ φ)`.  For the monad `G = f^* f_!` of the adjunction
`f_! ⊣ f^*` this is the bounded form of the hypothesis of Corollary A.23 of
arXiv:2607.28411v1. -/
def Slicing.MapsSemistableGE (s : Slicing D) (G : D ⥤ D) : Prop :=
  ∀ (φ : ℝ) (E : D), s.P φ E → s.geProp D φ (G.obj E)

variable {s : Slicing D}

/-- The condition extends from semistable objects to every object with HN
phases at most `t`: the exact endofunctor carries the HN filtration to a
Postnikov tower whose factors satisfy the cut by hypothesis, and
`Slicing.leProp_of_postnikovTower` closes up. -/
theorem Slicing.MapsSemistableLE.leProp_of_leProp {G : D ⥤ D} [G.Additive]
    [G.CommShift ℤ] [G.IsTriangulated] (h : s.MapsSemistableLE G) {t : ℝ} {E : D}
    (hE : s.leProp D t E) : s.leProp D t (G.obj E) := by
  rcases hE with hz | ⟨Fil, hn, hle⟩
  · exact s.leProp_of_isZero D (G.map_isZero hz) t
  · have hfac : ∀ i,
        s.leProp D t ((PostnikovTower.mapF Fil.toPostnikovTower G).factor i) := by
      intro i
      exact s.leProp_mono D ((Fil.phase_mem_range D hn i).2.trans hle) _
        (h (Fil.φ i) (Fil.factor i) (Fil.semistable i))
    exact s.leProp_of_postnikovTower D _ hfac

/-- **The adjoint transposition of Proposition 3.8.**  If the comonad `R ⋙ F`
of `F ⊣ R` satisfies (3.2), then the monad `L ⋙ F` of `L ⊣ F` satisfies the
Corollary A.23 hypothesis.  For `E ∈ 𝒫(φ)` and `G ∈ 𝒫(< φ)`, a morphism
`F L E ⟶ G` transposes to `E ⟶ F R G`, whose target lies in `𝒫(< φ)` by
`Slicing.MapsSemistableLE.leProp_of_leProp`, so it vanishes; transposing back
through the counits shows the original morphism vanishes, and
`Slicing.geProp_of_forall_hom_eq_zero` concludes. -/
theorem Slicing.MapsSemistableGE.of_mapsSemistableLE {L : D ⥤ C} {F : C ⥤ D} {R : D ⥤ C}
    [(R ⋙ F).Additive] [(R ⋙ F).CommShift ℤ] [(R ⋙ F).IsTriangulated]
    [L.PreservesZeroMorphisms] [F.PreservesZeroMorphisms]
    (adjL : L ⊣ F) (adjR : F ⊣ R) (h : s.MapsSemistableLE (R ⋙ F)) :
    s.MapsSemistableGE (L ⋙ F) := by
  intro φ E hE
  apply s.geProp_of_forall_hom_eq_zero D φ
  intro G hG g
  have hFRG : s.ltProp D φ ((R ⋙ F).obj G) := by
    rcases hG with hz | ⟨Fil, hn, hlt⟩
    · exact s.ltProp_of_isZero D ((R ⋙ F).map_isZero hz) φ
    · exact s.ltProp_of_leProp_of_lt D hlt _
        (h.leProp_of_leProp (Or.inr ⟨Fil, hn, le_rfl⟩))
  have hm : adjL.homEquiv E (R.obj G) (adjR.homEquiv (L.obj E) G g) = 0 :=
    s.zero_of_geProp_ltProp_general D φ (s.geProp_of_semistable D hE) hFRG _
  have hk : adjR.homEquiv (L.obj E) G g = 0 := by
    rw [← (adjL.homEquiv E (R.obj G)).symm_apply_apply (adjR.homEquiv (L.obj E) G g), hm,
      Adjunction.homEquiv_counit, L.map_zero, zero_comp]
  rw [← (adjR.homEquiv (L.obj E) G).symm_apply_apply g, hk, Adjunction.homEquiv_counit,
    F.map_zero, zero_comp]
  rfl

end CategoryTheory.Triangulated
