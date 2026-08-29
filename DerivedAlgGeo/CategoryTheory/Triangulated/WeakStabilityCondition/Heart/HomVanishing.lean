/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Heart.EquivalenceReverse

/-!
# Hom vanishing for weak heart phases

This file discharges the Hom-vanishing half of the reverse weak
heart--slicing construction.  The key new ingredient is a weak-slope
see-saw for short exact sequences in the heart.  It treats the extended
value `⊤` explicitly: a nonzero heart object has slope `⊤` exactly on the
closed real boundary of the weak upper half-plane.

The see-saw feeds the standard kernel/image argument.  A nonzero morphism
between weak-semistable heart objects forces the source slope to be at most
the image slope and the image slope to be at most the target slope.  Hence a
morphism from strictly higher phase to strictly lower phase vanishes.  The
integer-normalized ambient statement then follows by shifting both objects
to the heart when their phase indices agree, and by t-structure orthogonality
when the indices differ.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

namespace WeakStabilityFunction

variable {t : TStructure C} (W : WeakStabilityFunction t)

/-! ## Weak-slope see-saw -/

omit [IsTriangulated C] in
/-- If the two ends of a heart triangle have ordered weak slopes, the middle
slope lies between them.  The four cases distinguish positive from vanishing
imaginary part at each end; the latter is the extended slope `⊤`. -/
theorem slope_between_of_triangle {A B Q : C}
    (hA : t.heart A) (hQ : t.heart Q)
    (hA0 : ¬IsZero A) (hQ0 : ¬IsZero Q)
    {f : A ⟶ B} {g : B ⟶ Q} {d : Q ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g d ∈ distTriang C)
    (hslope : W.slope A ≤ W.slope Q) :
    W.slope A ≤ W.slope B ∧ W.slope B ≤ W.slope Q := by
  have hcharge : W.charge B = W.charge A + W.charge Q :=
    W.charge_triangle hdist
  have him : (W.charge B).im = (W.charge A).im + (W.charge Q).im := by
    simpa using congrArg Complex.im hcharge
  have hre : (W.charge B).re = (W.charge A).re + (W.charge Q).re := by
    simpa using congrArg Complex.re hcharge
  rcases W.upper A hA hA0 with hAim | ⟨hAim, hAre⟩
  · rcases W.upper Q hQ hQ0 with hQim | ⟨hQim, hQre⟩
    · have hBim : 0 < (W.charge B).im := by rw [him]; positivity
      have hslope' :
          -(W.charge A).re / (W.charge A).im ≤
            -(W.charge Q).re / (W.charge Q).im := by
        have hslope'' := hslope
        rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hQim] at hslope''
        exact_mod_cast hslope''
      rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim,
        W.slope_of_im_pos hQim]
      have hcross := (div_le_div_iff₀ hAim hQim).1 hslope'
      constructor
      · exact_mod_cast (div_le_div_iff₀ hAim hBim).2 (by
          rw [him, hre]
          nlinarith)
      · exact_mod_cast (div_le_div_iff₀ hBim hQim).2 (by
          rw [him, hre]
          nlinarith)
    · have hBim : 0 < (W.charge B).im := by rw [him, hQim, add_zero]; exact hAim
      rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim,
        W.slope_of_im_nonpos (by rw [hQim]; simp)]
      constructor
      · exact_mod_cast (by
          rw [him, hre, hQim, add_zero]
          exact (div_le_div_iff₀ hAim hAim).2 (by nlinarith))
      · exact le_top
  · rcases W.upper Q hQ hQ0 with hQim | ⟨hQim, hQre⟩
    · rw [W.slope_of_im_nonpos (by rw [hAim]; simp),
        W.slope_of_im_pos hQim] at hslope
      exact False.elim ((not_le_of_gt (WithTop.coe_lt_top _)) hslope)
    · have hBim : (W.charge B).im = 0 := by rw [him, hAim, hQim, zero_add]
      rw [W.slope_of_im_nonpos (by rw [hAim]; simp),
        W.slope_of_im_nonpos (by rw [hBim]; simp),
        W.slope_of_im_nonpos (by rw [hQim]; simp)]
      exact ⟨le_rfl, le_rfl⟩

/-! ## Kernel and image bounds in the heart -/

section Heart

/-- The abelian structure on the full heart used for kernels and images. -/
local instance : Abelian t.heart.FullSubcategory :=
  t.heartFullSubcategoryAbelian

private theorem heartShortExact_distinguished
    (S : ShortComplex t.heart.FullSubcategory) (hS : S.ShortExact) :
    ∃ d : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧,
      Triangle.mk S.f.hom S.g.hom d ∈ distTriang C := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  exact TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t S.f S.g S.zero (fun {A} a ha ↦
      ⟨hS.fIsKernel.lift (KernelFork.ofι a ha),
        hS.fIsKernel.fac (KernelFork.ofι a ha)
          WalkingParallelPair.zero⟩)

/-- Every nonzero quotient of a weak-semistable heart object has slope at
least the slope of the source. -/
theorem slope_le_of_heart_epi
    {E Q : t.heart.FullSubcategory} (p : E ⟶ Q) [Epi p]
    (hE : W.IsSemistable E.obj) (hQ : ¬IsZero Q) :
    W.slope E.obj ≤ W.slope Q.obj := by
  by_cases hK : IsZero (kernel p)
  · letI : Mono p := Preadditive.mono_of_isZero_kernel p hK
    letI : IsIso p := isIso_of_mono_of_epi p
    exact le_of_eq <| W.slope_eq_of_iso (t.heart.ι.mapIso (asIso p))
  · let K := kernel p
    let S : ShortComplex t.heart.FullSubcategory :=
      ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (by simpa [S, K] using ShortComplex.exact_kernel p)
      (by dsimp [S]; infer_instance)
      (by dsimp [S]; infer_instance)
    obtain ⟨d, hd⟩ := heartShortExact_distinguished (C := C) S hS
    have hKobj : ¬IsZero K.obj := fun h ↦ hK <|
      ObjectProperty.FullSubcategory.isZero_of_obj_isZero h
    have hQobj : ¬IsZero Q.obj := fun h ↦ hQ <|
      ObjectProperty.FullSubcategory.isZero_of_obj_isZero h
    have hKQ : W.slope K.obj ≤ W.slope Q.obj :=
      hE.2 K.property Q.property hKobj hQobj
        (kernel.ι p).hom p.hom d hd
    exact (W.slope_between_of_triangle K.property Q.property
      hKobj hQobj hd hKQ).2

/-- Every nonzero subobject of a weak-semistable heart object has slope at
most the slope of the target. -/
theorem heart_subobject_slope_le
    {I F : t.heart.FullSubcategory} (i : I ⟶ F) [Mono i]
    (hF : W.IsSemistable F.obj) (hI : ¬IsZero I) :
    W.slope I.obj ≤ W.slope F.obj := by
  by_cases hQ : IsZero (cokernel i)
  · letI : Epi i := Preadditive.epi_of_isZero_cokernel i hQ
    letI : IsIso i := isIso_of_mono_of_epi i
    exact le_of_eq <| W.slope_eq_of_iso (t.heart.ι.mapIso (asIso i))
  · let Q := cokernel i
    let S : ShortComplex t.heart.FullSubcategory :=
      ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (by simpa [S, Q] using ShortComplex.exact_cokernel i)
      (by dsimp [S]; infer_instance)
      (by dsimp [S]; infer_instance)
    obtain ⟨d, hd⟩ := heartShortExact_distinguished (C := C) S hS
    have hIobj : ¬IsZero I.obj := fun h ↦ hI <|
      ObjectProperty.FullSubcategory.isZero_of_obj_isZero h
    have hQobj : ¬IsZero Q.obj := fun h ↦ hQ <|
      ObjectProperty.FullSubcategory.isZero_of_obj_isZero h
    have hIQ : W.slope I.obj ≤ W.slope Q.obj :=
      hF.2 I.property Q.property hIobj hQobj i.hom
        (cokernel.π i).hom d hd
    exact (W.slope_between_of_triangle I.property Q.property
      hIobj hQobj hd hIQ).1

/-- Hom vanishing for weak-semistable objects in the same heart: a morphism
from strictly higher normalized weak phase to lower phase is zero. -/
theorem heart_hom_zero_of_semistable_phase_gt
    {E F : t.heart.FullSubcategory}
    (hE : W.IsSemistable E.obj) (hF : W.IsSemistable F.obj)
    (hphase : W.phase F.obj < W.phase E.obj) (f : E ⟶ F) : f = 0 := by
  by_contra hf
  have hI : ¬IsZero (image f) := by
    intro hZ
    apply hf
    rw [← image.fac f]
    rw [hZ.eq_of_tgt (factorThruImage f) 0, zero_comp]
  have hsource : W.slope E.obj ≤ W.slope (image f).obj :=
    W.slope_le_of_heart_epi (factorThruImage f) hE hI
  have htarget : W.slope (image f).obj ≤ W.slope F.obj :=
    W.heart_subobject_slope_le (image.ι f) hF hI
  exact (not_lt_of_ge (hsource.trans htarget))
    ((W.phase_lt_phase_iff).1 hphase)

end Heart

/-! ## Ambient integer-normalized Hom vanishing -/

/-- Hom vanishing for the ambient phase predicates induced from a weak
stability function on a heart.  Equal phase indices reduce to the heart image
argument; distinct indices reduce to t-structure orthogonality. -/
theorem ambientPhasePredicate_hom_zero
    {phi₁ phi₂ : ℝ} {E F : C}
    (hE : W.ambientPhasePredicate phi₁ E)
    (hF : W.ambientPhasePredicate phi₂ F)
    (hgap : phi₂ < phi₁) (f : E ⟶ F) : f = 0 := by
  let n₁ := phaseIndex phi₁
  let n₂ := phaseIndex phi₂
  let psi₁ := phaseBase phi₁
  let psi₂ := phaseBase phi₂
  rcases hE with hEZ | ⟨hEss, hEphase⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨hFss, hFphase⟩
  · exact hFZ.eq_of_tgt f 0
  have hle : n₂ ≤ n₁ := phaseIndex_le_of_lt hgap
  by_cases hidx : n₂ = n₁
  · let EH : t.heart.FullSubcategory :=
      ⟨E⟦(-n₁ : ℤ)⟧, by simpa [n₁] using hEss.1⟩
    let FH : t.heart.FullSubcategory :=
      ⟨F⟦(-n₁ : ℤ)⟧, by simpa [n₁, n₂, hidx] using hFss.1⟩
    have hEss' : W.IsSemistable EH.obj := by
      simpa [EH, n₁] using hEss
    have hFss' : W.IsSemistable FH.obj := by
      simpa [FH, n₁, n₂, hidx] using hFss
    have hEphase' : W.phase EH.obj = psi₁ := by
      simpa [EH, psi₁, n₁] using hEphase
    have hFphase' : W.phase FH.obj = psi₂ := by
      simpa [FH, psi₂, n₁, n₂, hidx] using hFphase
    have hpsi : psi₂ < psi₁ := by
      have hphi₂ : phi₂ = psi₂ + (n₁ : ℝ) := by
        simpa [psi₂, n₁, n₂, hidx] using
          (phaseBase_add_phaseIndex phi₂).symm
      have hphi₁ : phi₁ = psi₁ + (n₁ : ℝ) := by
        simpa [psi₁, n₁] using (phaseBase_add_phaseIndex phi₁).symm
      linarith
    let g : EH.obj ⟶ FH.obj := (shiftFunctor C (-n₁ : ℤ)).map f
    have hg_zero : (ObjectProperty.homMk g : EH ⟶ FH) = 0 :=
      W.heart_hom_zero_of_semistable_phase_gt hEss' hFss' (by
        rw [hFphase', hEphase']
        exact hpsi) (ObjectProperty.homMk g)
    have hmap : g = 0 := congrArg (·.hom) hg_zero
    exact (shiftFunctor C (-n₁ : ℤ)).map_injective (by simpa [g] using hmap)
  · let EH : t.heart.FullSubcategory :=
      ⟨E⟦(-n₁ : ℤ)⟧, by simpa [n₁] using hEss.1⟩
    let FH : t.heart.FullSubcategory :=
      ⟨F⟦(-n₂ : ℤ)⟧, by simpa [n₂] using hFss.1⟩
    let d : ℤ := n₁ - n₂
    have hdpos : 0 < d := by
      dsimp [d]
      lia
    let eE : EH.obj⟦d⟧ ≅ E⟦(-n₂ : ℤ)⟧ :=
      ((shiftFunctorAdd' C (-n₁ : ℤ) d (-n₂ : ℤ) (by
        dsimp [d]
        lia)).app E).symm
    let g : EH.obj⟦d⟧ ⟶ FH.obj :=
      eE.hom ≫ (shiftFunctor C (-n₂ : ℤ)).map f
    haveI : t.IsLE EH.obj 0 := by simpa [EH, n₁] using hEss.1.1
    haveI : t.IsGE FH.obj 0 := by simpa [FH, n₂] using hFss.1.2
    haveI : t.IsLE (EH.obj⟦d⟧) (-d) :=
      t.isLE_shift EH.obj 0 d (-d) (by lia)
    have hg : g = 0 := by
      simpa using t.zero_of_isLE_of_isGE g (-d) 0 (by lia)
        (show t.IsLE (EH.obj⟦d⟧) (-d) by infer_instance)
        (show t.IsGE FH.obj 0 by infer_instance)
    have hshift : (shiftFunctor C (-n₂ : ℤ)).map f = 0 := by
      apply (cancel_epi eE.hom).mp
      simpa [g] using hg
    exact (shiftFunctor C (-n₂ : ℤ)).map_injective (by simpa using hshift)

/-- Once ambient HN existence is supplied, Hom vanishing no longer needs to
be an independent reverse-slicing premise. -/
theorem reverseSlicingObligationsOfHN
    (hHN : ∀ E : C, Nonempty (HNFiltration C W.ambientPhasePredicate E)) :
    W.ReverseSlicingObligations where
  hom_vanishing := fun _ _ _ _ hlt hA hB f ↦
    W.ambientPhasePredicate_hom_zero hA hB hlt f
  hn_exists := hHN

end WeakStabilityFunction

end

end CategoryTheory.Triangulated.WeakStabilityCondition
