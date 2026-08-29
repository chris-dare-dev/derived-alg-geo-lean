/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.MidpointHeart
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.ImageFactorisation

/-!
# Image factorisations in owner slicing hearts

This module combines the repository-owned phase-bound API with the ForMathlib
abelian-heart bridge.  It places the image of a nonzero morphism in the two
overlapping phase windows used by the small-gap Hom-vanishing argument.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.TStructure
open CategoryTheory.Triangulated.TStructure

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- A nonzero morphism inside a shifted slicing heart has a nonzero abelian
image.  If the source is bounded below by `l` and the target is bounded above
by `u`, that image belongs to both overlapping old phase intervals
`(a,u)` and `(l,a+1)`. -/
theorem Slicing.exists_heart_image_factorisation_windows
    (s : Slicing C) {a l u : ℝ} (hau : a < u) (hua : u ≤ a + 1)
    (hla : l < a + 1) {δ : ℝ} (hδ : 0 < δ)
    {E F : C}
    (hEheart : ((s.phaseShift C a).toTStructure C).heart E)
    (hFheart : ((s.phaseShift C a).toTStructure C).heart F)
    (hE_lower : ∀ hE : ¬IsZero E, l < s.phiMinus C E hE)
    (hE_upper : ∀ hE : ¬IsZero E, s.phiPlus C E hE < u)
    (hF_lower : ∀ hF : ¬IsZero F, l < s.phiMinus C F hF)
    (hF_upper : ∀ hF : ¬IsZero F, s.phiPlus C F hF < u)
    {f : E ⟶ F} (hf : f ≠ 0) :
    let t := (s.phaseShift C a).toTStructure C
    ∃ (I K Q : t.heart.FullSubcategory)
      (p : (⟨E, hEheart⟩ : t.heart.FullSubcategory) ⟶ I)
      (i : I ⟶ (⟨F, hFheart⟩ : t.heart.FullSubcategory))
      (k : K ⟶ (⟨E, hEheart⟩ : t.heart.FullSubcategory))
      (q : (⟨F, hFheart⟩ : t.heart.FullSubcategory) ⟶ Q)
      (δp : I.obj ⟶ K.obj⟦(1 : ℤ)⟧)
      (δi : Q.obj ⟶ I.obj⟦(1 : ℤ)⟧),
      p ≫ i = ObjectProperty.homMk f ∧ Epi p ∧ Mono i ∧
        Triangle.mk k.hom p.hom δp ∈ distTriang C ∧
        Triangle.mk i.hom q.hom δi ∈ distTriang C ∧
        ¬IsZero I.obj ∧
        s.intervalProp C a u K.obj ∧
        s.intervalProp C a u I.obj ∧
        s.intervalProp C l (a + 1) I.obj ∧
        s.intervalProp C l (a + 1 + δ) Q.obj := by
  let t := (s.phaseShift C a).toTStructure C
  let EH : t.heart.FullSubcategory := ⟨E, hEheart⟩
  let FH : t.heart.FullSubcategory := ⟨F, hFheart⟩
  let fH : EH ⟶ FH := ObjectProperty.homMk f
  obtain ⟨I, K, Q, p, i, k, q, δp, δi, hfac, hp, hi, hTp, hTi⟩ :=
    exists_image_factorisation_triangles t fH
  have hIheart : t.heart I.obj := I.property
  have hKheart : t.heart K.obj := K.property
  have hQheart : t.heart Q.obj := Q.property
  rw [(s.phaseShift C a).toTStructure_heart_iff C] at hIheart hKheart hQheart
  have hEheart' := hEheart
  rw [(s.phaseShift C a).toTStructure_heart_iff C] at hEheart'
  have hIgt : s.gtProp C a I.obj :=
    (s.phaseShift_gtProp_zero C a I.obj).mp hIheart.1
  have hIle : s.leProp C (a + 1) I.obj := by
    simpa [add_comm] using (s.phaseShift_leProp C a 1 I.obj).mp hIheart.2
  have hKgt : s.gtProp C a K.obj :=
    (s.phaseShift_gtProp_zero C a K.obj).mp hKheart.1
  have hQle : s.leProp C (a + 1) Q.obj := by
    simpa [add_comm] using (s.phaseShift_leProp C a 1 Q.obj).mp hQheart.2
  have hIne : ¬IsZero I.obj := by
    intro hIZ
    have hi0 : i = 0 := by
      ext
      exact hIZ.eq_of_src i.hom 0
    apply hf
    have hfH0 : fH = 0 := by
      rw [← hfac, hi0]
      simp
    simpa [fH] using congrArg (fun g => g.hom) hfH0
  have hIupper : s.phiPlus C I.obj hIne < u :=
    s.phiPlus_lt_of_triangle_with_leProp C hIne hF_upper hQle
      (by linarith) hTi
  have hIlower : l < s.phiMinus C I.obj hIne :=
    s.phiMinus_gt_of_triangle_with_gtProp C hIne hE_lower hKgt hla hTp
  have hEne : ¬IsZero E := by
    intro hEZ
    exact hf (hEZ.eq_of_src f 0)
  have hEinterval : s.intervalProp C a u E :=
    s.intervalProp_of_intrinsic_phases C hEne
      (s.phiMinus_gt_of_gtProp C hEne
        ((s.phaseShift_gtProp_zero C a E).mp hEheart'.1))
      (hE_upper hEne)
  have hKinterval : s.intervalProp C a u K.obj :=
    s.first_intervalProp_of_triangle C hau hEinterval hIle hKgt hTp
  have hQinterval : s.intervalProp C l (a + 1 + δ) Q.obj := by
    by_cases hQne : IsZero Q.obj
    · exact Or.inl hQne
    · exact s.intervalProp_of_intrinsic_phases C hQne
        (s.phiMinus_gt_of_triangle_with_gtProp C hQne hF_lower hIgt hla hTi)
        ((s.phiPlus_le_of_leProp C hQne hQle).trans_lt (by linarith))
  refine ⟨I, K, Q, p, i, k, q, δp, δi, hfac, hp, hi, hTp, hTi, hIne,
    hKinterval, ?_, ?_, hQinterval⟩
  · exact s.intervalProp_of_intrinsic_phases C hIne
      (s.phiMinus_gt_of_gtProp C hIne hIgt) hIupper
  · exact s.intervalProp_of_intrinsic_phases C hIne hIlower
      (hIupper.trans_le hua)

end CategoryTheory.Triangulated
