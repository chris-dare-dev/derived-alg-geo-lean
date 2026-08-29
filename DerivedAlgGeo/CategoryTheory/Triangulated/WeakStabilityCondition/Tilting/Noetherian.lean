/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Cohomology.Sequence
import Mathlib.CategoryTheory.Subobject.NoetherianObject

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Noetherian zero-charge objects after phase tilting

This file proves the noetherianity part of the zero-charge comparison needed
for Proposition 14.16.  The tilted weak function has exactly the original
zero-charge objects.  A subobject of such an object in the tilted heart again
has zero charge; its quotient therefore has zero charge as well.  The
zero-charge comparison puts all three terms back in the original heart, so
the same distinguished triangle exhibits an original-heart subobject.

Consequently the original `NoetherianTorsionSubcategory` chain condition
applies to every tilted-heart subobject chain of a zero-charge object.  The
result is stated using Mathlib's standard `IsNoetherianObject`, which supplies
the well-founded subobject order used to choose maximal zero-charge
subobjects in the remaining torsion-pair assembly.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open CategoryTheory.Triangulated.Tilting
open scoped ZeroObject

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

/-- In a heart short exact sequence `0 → Q → E → N → 0`, if
`Q` is right-orthogonal to zero-charge objects, then every zero-charge
subobject of `E` maps monomorphically to `N`.

This is the kernel/image argument behind the injectivity sentence in the
proof of Proposition 14.16. -/
theorem mono_comp_of_zeroCharge_of_rightOrthogonal
    (t : TStructure C) (W : WeakStabilityFunction t)
    (S : ShortComplex t.heart.FullSubcategory) (hS : S.ShortExact)
    {A : t.heart.FullSubcategory} (a : A ⟶ S.X₂) [Mono a]
    (hA : W.zeroCharge A.obj)
    (hQ : rightOrthogonal t W.zeroCharge S.X₁.obj) : Mono (a ≫ S.g) := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let k : kernel (a ≫ S.g) ⟶ A := kernel.ι (a ≫ S.g)
  have hkzero : W.zeroCharge (kernel (a ≫ S.g)).obj := by
    obtain ⟨hK, -, QK, hQK, q, d, hd⟩ :=
      isHeartMono_of_mono t k
    exact W.zeroCharge_left hK hQK hA hd
  have hcomp : (k ≫ a) ≫ S.g = 0 := by
    simpa only [Category.assoc] using kernel.condition (a ≫ S.g)
  let u : kernel (a ≫ S.g) ⟶ S.X₁ :=
    hS.fIsKernel.lift (KernelFork.ofι (k ≫ a) hcomp)
  have hu_fac : u ≫ S.f = k ≫ a :=
    hS.fIsKernel.fac (KernelFork.ofι (k ≫ a) hcomp)
      WalkingParallelPair.zero
  have hu_zero_ambient : u.hom = 0 := hQ.2 _ hkzero u.hom
  have hu_zero : u = 0 := by
    ext
    exact hu_zero_ambient
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply (cancel_mono a).mp
  rw [← hu_fac, hu_zero, zero_comp]
  simp

/-- A morphism from an original zero-charge object to an original
phase-torsion object which is monic in the tilted heart is already monic in
the original heart.  Its original-heart kernel is again zero-charge, hence is
an object of the tilted heart; tilted monicity then forces that kernel to
vanish. -/
theorem mono_in_originalHeart_of_mono_in_phaseTilt
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {A N : sigma.slicing.toTStructure.heart.FullSubcategory}
    (hA : sigma.zeroCharge A.obj)
    (hN : phaseTors sigma.slicing beta N.obj)
    (f : A ⟶ N)
    (hmono : Mono (ObjectProperty.homMk f.hom :
      (⟨A.obj,
        ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
          beta hbeta0 hbeta1 A.obj).mpr hA).1⟩ :
          ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart.FullSubcategory)
        ⟶
      ⟨N.obj, (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tors_mem_tilt_heart
        hN⟩)) : Mono f := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let At : P.tilt.heart.FullSubcategory :=
    ⟨A.obj, ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 A.obj).mpr hA).1⟩
  let Nt : P.tilt.heart.FullSubcategory := ⟨N.obj, P.tors_mem_tilt_heart hN⟩
  let ft : At ⟶ Nt := ObjectProperty.homMk f.hom
  letI : Mono ft := by simpa [ft, At, Nt] using hmono
  let k : kernel f ⟶ A := kernel.ι f
  have hkzero : sigma.zeroCharge (kernel f).obj := by
    obtain ⟨hK, -, QK, hQK, q, d, hd⟩ := isHeartMono_of_mono t k
    exact sigma.weakStabilityFunctionOnHeart.zeroCharge_left hK hQK hA hd
  let Kt : P.tilt.heart.FullSubcategory :=
    ⟨(kernel f).obj,
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 (kernel f).obj).mpr hkzero).1⟩
  let kt : Kt ⟶ At := ObjectProperty.homMk k.hom
  have hktf : kt ≫ ft = 0 := by
    ext
    have hc := congrArg (fun u : kernel f ⟶ N => u.hom) (kernel.condition f)
    change (kernel.ι f).hom ≫ f.hom = 0 at hc
    exact hc
  have hkt : kt = 0 := (cancel_mono ft).mp (by simpa using hktf)
  apply Abelian.mono_of_kernel_ι_eq_zero
  ext
  simpa [kt, k] using congrArg (fun u : Kt ⟶ At ↦ u.hom) hkt

namespace WeakPreStabilityCondition

/-- Original zero-charge objects lie in the phase-torsion class at every
cutoff below `1`. -/
theorem zeroCharge_phaseTors
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (hbeta1 : beta < 1)
    {E : C} (hE : sigma.zeroCharge E) :
    phaseTors sigma.slicing beta E := by
  have hP := sigma.zeroCharge_mem_P_one hE.1 hE.2
  exact ⟨sigma.slicing.gtProp_of_semistable C hP hbeta1,
    sigma.slicing.leProp_of_semistable C hP le_rfl⟩

/-- A phase-compatible tilting envelope rotates to a zero-charge subobject of
`F[1]` in the tilted heart whose quotient is right-orthogonal to all
zero-charge objects.  This formalizes the first short exact sequence used in
the proof of Proposition 14.16. -/
theorem phaseTiltingEnvelope_gives_shiftedZeroChargeDecomposition
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {F : C}
    (hF : phaseFree sigma.slicing beta F)
    (henv : sigma.HasPhaseTiltingEnvelope beta F) :
    ∃ (A Q : C)
      (_ : (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt.heart
        (F⟦(1 : ℤ)⟧))
      (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
      (_ : rightOrthogonal
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge Q)
      (i : A ⟶ F⟦(1 : ℤ)⟧) (p : F⟦(1 : ℤ)⟧ ⟶ Q)
      (d : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk i p d ∈ distTriang C := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  obtain ⟨Ftilde, F0, hFtilde, hF0, i, p, d, hd, hhom⟩ := henv
  have hF0new : W.zeroCharge F0 :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 F0).mpr hF0
  have hQheart : P.tilt.heart (Ftilde⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hFtilde
  have hFheart : P.tilt.heart (F⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hF
  have hQorth : rightOrthogonal P.tilt W.zeroCharge (Ftilde⟦(1 : ℤ)⟧) := by
    refine ⟨hQheart, ?_⟩
    intro A0 hA0 f
    exact hhom A0
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 A0).mp hA0) f
  exact ⟨F0, Ftilde⟦(1 : ℤ)⟧, hFheart, hF0new, hQorth, d, -i⟦(1 : ℤ)⟧',
    -p⟦(1 : ℤ)⟧', by
      simpa [Triangle.rotate] using rot_of_distTriang (Triangle.mk i p d).rotate
        (rot_of_distTriang (Triangle.mk i p d) hd)⟩

/-- A phase-compatible envelope of an original semistable object has a
semistable middle term.  The middle term has no zero-charge subobjects by
strict phase separation (`1 > beta`), so the general saturation lemma applies
to the envelope's zero-charge quotient. -/
theorem phaseTiltingEnvelope_middle_semistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta1 : beta < 1) {F : C}
    (hFss : sigma.weakStabilityFunctionOnHeart.IsSemistable F)
    (henv : sigma.HasPhaseTiltingEnvelope beta F) :
    ∃ (Ftilde F0 : C) (_ : phaseFree sigma.slicing beta Ftilde)
      (_ : sigma.weakStabilityFunctionOnHeart.IsSemistable Ftilde)
      (_ : sigma.zeroCharge F0) (i : F ⟶ Ftilde) (p : Ftilde ⟶ F0)
      (d : F0 ⟶ F⟦(1 : ℤ)⟧),
        Triangle.mk i p d ∈ distTriang C ∧
          ∀ A0 : C, sigma.zeroCharge A0 →
            ∀ f : A0 ⟶ Ftilde⟦(1 : ℤ)⟧, f = 0 := by
  obtain ⟨Ftilde, F0, hFtilde, hF0, i, p, d, hd, hshiftHom⟩ := henv
  have hFtildeHeart : sigma.slicing.toTStructure.heart Ftilde :=
    mem_heart_of_bounds sigma.slicing hFtilde.1
      (sigma.slicing.leProp_mono C hbeta1.le Ftilde hFtilde.2)
  have hHom : ∀ A0 : C, sigma.weakStabilityFunctionOnHeart.zeroCharge A0 →
      ∀ f : A0 ⟶ Ftilde, f = 0 := by
    intro A0 hA0 f
    exact sigma.slicing.zero_of_gtProp_leProp_general C beta
      (sigma.zeroCharge_phaseTors beta hbeta1 hA0).1 hFtilde.2 f
  have hFtildeSS :=
    sigma.weakStabilityFunctionOnHeart.isSemistable_middle_of_zeroCharge_quotient
      (t := sigma.slicing.toTStructure) hFss hFtildeHeart hF0 hHom hd
  exact ⟨Ftilde, F0, hFtilde, hFtildeSS, hF0, i, p, d, hd, hshiftHom⟩

/-- A raw Definition 14.12 tilting envelope makes every increasing chain of
tilted zero-charge subobjects of `F[1]` terminate.

The raw middle term is not required to lie in the phase-cut free class.  For
each subobject `A ⟶ F[1]`, the envelope's Ext-vanishing and triangle
exactness instead give a lift `A ⟶ F⁰`.  Pulling `F⁰ ⟶ F[1]` back along
`A ⟶ F[1]` makes this lift canonical: the pullback maps epimorphically to
`A` and monomorphically to the original zero-charge object `F⁰`.  The
original noetherian hypothesis stabilizes the pullback chain, after which
epimorphic cancellation forces the given chain to stabilize. -/
theorem phaseTilt_zeroChargeChain_terminates_of_tiltingEnvelope
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    {F : C} (hF : phaseFree sigma.slicing beta F)
    (henv : sigma.HasTiltingEnvelope F)
    (c : SubobjectChain
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
      (F⟦(1 : ℤ)⟧)) : c.Terminates := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  obtain ⟨Fbar, F0, -, hF0, i, p, d, hd, hhom⟩ := henv
  have hFshift : P.tilt.heart (F⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hF
  have hF0new : W.zeroCharge F0 :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 F0).mpr hF0
  let F0H : H := ⟨F0, hF0new.1⟩
  let FH : H := ⟨F⟦(1 : ℤ)⟧, hFshift⟩
  let dH : F0H ⟶ FH := ObjectProperty.homMk d
  have propOld (j : ℕ) : sigma.zeroCharge (c.obj j) :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 (c.obj j)).mp (c.prop j)
  let AH (j : ℕ) : H := ⟨c.obj j, (c.toAmbient_mono j).1⟩
  let aH (j : ℕ) : AH j ⟶ FH := ObjectProperty.homMk (c.toAmbient j)
  have aH_mono (j : ℕ) : Mono (aH j) :=
    mono_of_isHeartMono P.tilt (aH j) (c.toAmbient_mono j)
  have liftExists (j : ℕ) : ∃ g : c.obj j ⟶ F0,
      c.toAmbient j = g ≫ d := by
    have hz : c.toAmbient j ≫ i⟦(1 : ℤ)⟧' = 0 :=
      hhom (c.obj j) (propOld j) (c.toAmbient j ≫ i⟦(1 : ℤ)⟧')
    exact Triangle.coyoneda_exact₁
      (Triangle.mk i p d) hd (c.toAmbient j) hz
  let liftToF0 (j : ℕ) : AH j ⟶ F0H :=
    ObjectProperty.homMk (Classical.choose (liftExists j))
  have liftToF0_fac (j : ℕ) : liftToF0 j ≫ dH = aH j := by
    ext
    exact (Classical.choose_spec (liftExists j)).symm
  let PB (j : ℕ) : H := pullback dH (aH j)
  let toF0 (j : ℕ) : PB j ⟶ F0H := pullback.fst dH (aH j)
  let toA (j : ℕ) : PB j ⟶ AH j := pullback.snd dH (aH j)
  have toF0_mono (j : ℕ) : Mono (toF0 j) := by
    dsimp [toF0]
    infer_instance
  let sec (j : ℕ) : AH j ⟶ PB j :=
    pullback.lift (liftToF0 j) (𝟙 (AH j)) (by simpa using liftToF0_fac j)
  have sec_toA (j : ℕ) : sec j ≫ toA j = 𝟙 (AH j) := by
    exact pullback.lift_snd (liftToF0 j) (𝟙 (AH j)) _
  have toA_epi (j : ℕ) : Epi (toA j) := by
    apply epi_of_epi_fac (sec_toA j)
  let stepH (j : ℕ) : AH j ⟶ AH (j + 1) :=
    ObjectProperty.homMk (c.step j)
  have stepH_mono (j : ℕ) : Mono (stepH j) :=
    mono_of_isHeartMono P.tilt (stepH j) (c.step_mono j)
  have aH_step (j : ℕ) : stepH j ≫ aH (j + 1) = aH j := by
    ext
    exact c.comm j
  let pbStep (j : ℕ) : PB j ⟶ PB (j + 1) :=
    pullback.lift (toF0 j) (toA j ≫ stepH j) (by
      rw [Category.assoc, aH_step j]
      exact pullback.condition)
  have pbStep_toF0 (j : ℕ) : pbStep j ≫ toF0 (j + 1) = toF0 j := by
    exact pullback.lift_fst _ _ _
  have pbStep_toA (j : ℕ) : pbStep j ≫ toA (j + 1) = toA j ≫ stepH j := by
    exact pullback.lift_snd _ _ _
  have pbStep_mono (j : ℕ) : Mono (pbStep j) := by
    apply mono_of_mono_fac (pbStep_toF0 j)
  have pbZero (j : ℕ) : W.zeroCharge (PB j).obj := by
    letI : Mono (toF0 j) := toF0_mono j
    exact (W.heartZeroCharge P.tilt).prop_of_mono (toF0 j) hF0new
  have pbOld (j : ℕ) : sigma.zeroCharge (PB j).obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 (PB j).obj).mp (pbZero j)
  let PBOld (j : ℕ) : t.heart.FullSubcategory := ⟨(PB j).obj, (pbOld j).1⟩
  let F0Old : t.heart.FullSubcategory := ⟨F0, hF0.1⟩
  let pbStepOld (j : ℕ) : PBOld j ⟶ PBOld (j + 1) :=
    ObjectProperty.homMk (pbStep j).hom
  have pbStepOld_mono (j : ℕ) : Mono (pbStepOld j) := by
    apply mono_in_originalHeart_of_mono_in_phaseTilt
      sigma beta hbeta0 hbeta1 (pbOld j)
        (sigma.zeroCharge_phaseTors beta hbeta1 (pbOld (j + 1)))
    apply mono_of_isHeartMono P.tilt
    exact isHeartMono_of_mono P.tilt (pbStep j)
  let toF0Old (j : ℕ) : PBOld j ⟶ F0Old :=
    ObjectProperty.homMk (toF0 j).hom
  have toF0Old_mono (j : ℕ) : Mono (toF0Old j) := by
    apply mono_in_originalHeart_of_mono_in_phaseTilt
      sigma beta hbeta0 hbeta1 (pbOld j)
        (sigma.zeroCharge_phaseTors beta hbeta1 hF0)
    apply mono_of_isHeartMono P.tilt
    exact isHeartMono_of_mono P.tilt (toF0 j)
  let cOld : SubobjectChain t sigma.zeroCharge F0 :=
    { obj := fun j => (PB j).obj
      prop := pbOld
      step := fun j => (pbStep j).hom
      toAmbient := fun j => (toF0 j).hom
      step_mono := fun j => isHeartMono_of_mono t (pbStepOld j)
      toAmbient_mono := fun j => isHeartMono_of_mono t (toF0Old j)
      comm := fun j => congrArg InducedCategory.Hom.hom (pbStep_toF0 j) }
  obtain ⟨n, hn⟩ := noetherian_mono (t := t)
    (fun X hX => by rw [hN0]; exact hX) N0.noetherian
    F0 hF0.1 cOld
  refine ⟨n, fun j hj => ?_⟩
  haveI pbStep_hom_iso : IsIso (pbStep j).hom := by
    exact hn j hj
  letI : IsIso (P.tilt.heart.ι.map (pbStep j)) := by
    change IsIso (pbStep j).hom
    infer_instance
  letI : IsIso (pbStep j) :=
    isIso_of_reflects_iso (pbStep j) P.tilt.heart.ι
  letI : Epi (toA (j + 1)) := toA_epi (j + 1)
  letI : Epi (pbStep j ≫ toA (j + 1)) := by infer_instance
  have stepH_epi : Epi (stepH j) := by
    exact epi_of_epi_fac (pbStep_toA j).symm
  have stepH_iso : IsIso (stepH j) := by
    letI : Mono (stepH j) := stepH_mono j
    letI : Epi (stepH j) := stepH_epi
    exact isIso_of_mono_of_epi (stepH j)
  simpa [stepH, AH] using (P.tilt.heart.ι.mapIso (asIso (stepH j))).isIso_hom

/-- **The semistable-reduction step of Proposition 19.5.**

Let `R` be an extension of a shifted old semistable `U[1]` by a zero-charge
object, and assume `U[1]` is right-orthogonal to tilted zero-charge objects.
After quotienting `R` by its maximal zero-charge subobject, the resulting
quotient is tilted semistable and has the same charge as `U[1]`.

The key diagram is the middle part of the kernel--cokernel sequence for the
composite from the maximal zero-charge subobject to the right-hand
zero-charge term.  The composite is monic by
`mono_comp_of_zeroCharge_of_rightOrthogonal`, so that middle sequence is
short exact and identifies the quotient as an extension of `U[1]` by a new
zero-charge object. -/
theorem phaseTilt_semistableQuotient_of_saturatedExtension
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1))
    {U V R : C}
    (hUfree : phaseFree sigma.slicing beta U)
    (hUss : sigma.weakStabilityFunctionOnHeart.IsSemistable U)
    (hUcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
        (U⟦(1 : ℤ)⟧) ≠ 0)
    (hV : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    (hR : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart R)
    (hUorth : rightOrthogonal
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
      (U⟦(1 : ℤ)⟧))
    {i : U⟦(1 : ℤ)⟧ ⟶ R} {p : R ⟶ V}
    {d : V ⟶ U⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hd : Triangle.mk i p d ∈ distTriang C) :
    ∃ (A B : C)
      (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
      (_ : rightOrthogonal
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge B)
      (a : A ⟶ R) (q : R ⟶ B) (delta : B ⟶ A⟦(1 : ℤ)⟧),
        Triangle.mk a q delta ∈ distTriang C ∧
          (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable B ∧
          (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge B =
            (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
              (U⟦(1 : ℤ)⟧) := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian P.tilt.heart.FullSubcategory :=
    P.tilt.heartFullSubcategoryAbelian
  have hUshift : P.tilt.heart (U⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hUfree
  let UH : P.tilt.heart.FullSubcategory := ⟨U⟦(1 : ℤ)⟧, hUshift⟩
  let RH : P.tilt.heart.FullSubcategory := ⟨R, hR⟩
  let VH : P.tilt.heart.FullSubcategory := ⟨V, hV.1⟩
  let iH : UH ⟶ RH := ObjectProperty.homMk i
  let pH : RH ⟶ VH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hd
  have hS : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := UH) (B := RH) (Q := VH)
        (f := iH) (g := pH) (δ := d) hd
  obtain ⟨A, B, hA, hB, a, q, delta, hAB⟩ := hdec R hR
  let AH : P.tilt.heart.FullSubcategory := ⟨A, hA.1⟩
  let BH : P.tilt.heart.FullSubcategory := ⟨B, hB.1⟩
  let aH : AH ⟶ RH := ObjectProperty.homMk a
  let qH : RH ⟶ BH := ObjectProperty.homMk q
  have haq : aH ≫ qH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hAB
  have hT : (ShortComplex.mk aH qH haq).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := AH) (B := RH) (Q := BH)
        (f := aH) (g := qH) (δ := delta) hAB
  letI : Mono aH := hT.mono_f
  letI : Epi pH := hS.epi_g
  have hcompMono : Mono (aH ≫ pH) := by
    exact mono_comp_of_zeroCharge_of_rightOrthogonal
      P.tilt W (ShortComplex.mk iH pH hip) hS aH hA hUorth
  letI : Mono (aH ≫ pH) := hcompMono
  let M := kernelCokernelCompMiddleShortComplex aH pH
  have hM : M.ShortExact :=
    kernelCokernelCompMiddleShortComplex_shortExact aH pH
  let eU : M.X₁ ≅ UH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel pH) hS.fIsKernel
  let eB : M.X₂ ≅ BH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel aH)
      hT.gIsCokernel
  let Vprime : P.tilt.heart.FullSubcategory := M.X₃
  let f' : UH ⟶ BH := eU.inv ≫ M.f ≫ eB.hom
  let g' : BH ⟶ Vprime := eB.inv ≫ M.g
  have hfg : f' ≫ g' = 0 := by
    simp [f', g', M]
  let T' : ShortComplex P.tilt.heart.FullSubcategory :=
    ShortComplex.mk f' g' hfg
  let eM : M ≅ T' := ShortComplex.isoMk eU eB (Iso.refl _)
  have hT' : T'.ShortExact := ShortComplex.shortExact_of_iso eM hM
  letI : Mono f' := hT'.mono_f
  letI : Epi g' := hT'.epi_g
  have hVprime : W.zeroCharge Vprime.obj := by
    have hVheart : W.heartZeroCharge P.tilt VH := hV
    have hprop : W.heartZeroCharge P.tilt (cokernel (aH ≫ pH)) := by
      exact (W.heartZeroCharge P.tilt).prop_of_epi
        (cokernel.π (aH ≫ pH)) hVheart
    exact hprop
  obtain ⟨d', hd'⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt f' g' hfg (fun {X} x hx => by
      exact ⟨hT'.fIsKernel.lift (KernelFork.ofι x hx),
        hT'.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  have hBcharge : W.charge B = W.charge (U⟦(1 : ℤ)⟧) := by
    have hsum := W.charge_triangle' hd'
    rw [hVprime.2, add_zero] at hsum
    simpa [BH, UH] using hsum
  have hBcharge0 : W.charge B ≠ 0 := hBcharge.symm ▸ hUcharge
  have hVprimeOld : sigma.zeroCharge Vprime.obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 Vprime.obj).mp hVprime
  have hTypeTwo : sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 B := by
    refine ⟨U, Vprime.obj, hUfree, hUss, hVprimeOld,
      f'.hom, g'.hom, d', ?_, ?_⟩
    · simpa [UH, BH] using hd'
    · intro _ A0 hA0 z
      exact hB.2 A0
        ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
          beta hbeta0 hbeta1 A0).mpr hA0) z
  have hBss : W.IsSemistable B :=
    sigma.isSemistable_of_isPhaseTiltTypeTwo beta hbeta0 hbeta1
      hB.1 hBcharge0 hTypeTwo
  exact ⟨A, B, hA, hB, a, q, delta, hAB, hBss, hBcharge⟩

/-- **Boundary-phase saturation.**

The maximal zero-charge quotient of an extension of `U[1]` by a zero-charge
object is semistable without assuming in advance that `U[1]` is
right-orthogonal to zero-charge objects.  Intersecting the maximal
zero-charge subobject with `U[1]` gives an original torsion object.  The
six-term original-cohomology sequence identifies the quotient of that
intersection with `Utilde[1]` and supplies an envelope
`U ⟶ Utilde ⟶ A0`.  Its inclusion into the maximal quotient forces the
envelope's right-orthogonality, so `Utilde` is semistable and the quotient is
of phase-tilt type two. -/
theorem phaseTilt_semistableQuotient_of_extension
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1))
    {U V R : C}
    (hUfree : phaseFree sigma.slicing beta U)
    (hUss : sigma.weakStabilityFunctionOnHeart.IsSemistable U)
    (hUcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
        (U⟦(1 : ℤ)⟧) ≠ 0)
    (hV : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    (hR : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart R)
    {i : U⟦(1 : ℤ)⟧ ⟶ R} {p : R ⟶ V}
    {d : V ⟶ U⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hd : Triangle.mk i p d ∈ distTriang C) :
    ∃ (A B : C)
      (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
      (_ : rightOrthogonal
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge B)
      (a : A ⟶ R) (q : R ⟶ B) (delta : B ⟶ A⟦(1 : ℤ)⟧),
        Triangle.mk a q delta ∈ distTriang C ∧
          (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable B ∧
          (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge B =
            (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
              (U⟦(1 : ℤ)⟧) := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  have hUshift : P.tilt.heart (U⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hUfree
  let UH : H := ⟨U⟦(1 : ℤ)⟧, hUshift⟩
  let RH : H := ⟨R, hR⟩
  let VH : H := ⟨V, hV.1⟩
  let iH : UH ⟶ RH := ObjectProperty.homMk i
  let pH : RH ⟶ VH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hd
  have hS : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := UH) (B := RH) (Q := VH)
        (f := iH) (g := pH) (δ := d) hd
  obtain ⟨A, B, hA, hB, a, q, delta, hAB⟩ := hdec R hR
  let AH : H := ⟨A, hA.1⟩
  let BH : H := ⟨B, hB.1⟩
  let aH : AH ⟶ RH := ObjectProperty.homMk a
  let qH : RH ⟶ BH := ObjectProperty.homMk q
  have haq : aH ≫ qH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hAB
  have hT : (ShortComplex.mk aH qH haq).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := AH) (B := RH) (Q := BH)
        (f := aH) (g := qH) (δ := delta) hAB
  letI : Mono iH := hS.mono_f
  letI : Mono aH := hT.mono_f
  let PB : H := pullback iH aH
  let kU : PB ⟶ UH := pullback.fst iH aH
  let kA : PB ⟶ AH := pullback.snd iH aH
  let sq : IsPullback kU kA iH aH := IsPullback.of_hasPullback iH aH
  letI : Mono kU := inferInstance
  letI : Mono kA := inferInstance
  have hPB : W.heartZeroCharge P.tilt PB :=
    (W.heartZeroCharge P.tilt).prop_of_mono kA hA
  have hPBOld : sigma.zeroCharge PB.obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 PB.obj).mp hPB
  have hPBtors : P.tors PB.obj :=
    sigma.zeroCharge_phaseTors beta hbeta1 hPBOld
  let IH : H := cokernel kU
  let piI : UH ⟶ IH := cokernel.π kU
  have hkpi : kU ≫ piI = 0 := cokernel.condition kU
  have hIseq : (ShortComplex.mk kU piI hkpi).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel kU)
      inferInstance inferInstance
  obtain ⟨dI, hdI⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt kU piI hkpi (fun {X} x hx => by
      exact ⟨hIseq.fIsKernel.lift (KernelFork.ofι x hx),
        hIseq.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  obtain ⟨Utilde, hUtildefree, u, r, du, hUtri, ⟨eI⟩⟩ :=
    P.exists_original_triangle_of_torsion_subobject_free_shift
      hUfree hPBtors IH.property hdI
  let cIB : IH ⟶ cokernel aH :=
    cokernel.map kU aH kA iH sq.w
  haveI : Mono cIB := Abelian.mono_cokernel_map_of_isPullback sq
  let eB : cokernel aH ≅ BH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel aH)
      hT.gIsCokernel
  let m : IH ⟶ BH := cIB ≫ eB.hom
  letI : Mono m := by dsimp [m]; infer_instance
  have hShiftHom : ∀ A0 : C, sigma.zeroCharge A0 →
      ∀ f : A0 ⟶ Utilde⟦(1 : ℤ)⟧, f = 0 := by
    intro A0 hA0 f
    have hA0new : W.zeroCharge A0 :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 A0).mpr hA0
    let A0H : H := ⟨A0, hA0new.1⟩
    let fH : A0H ⟶ IH := ObjectProperty.homMk (f ≫ eI.hom)
    have hfhm : fH ≫ m = 0 := by
      ext
      change (f ≫ eI.hom) ≫ m.hom = 0
      simpa only [Category.assoc] using
        hB.2 A0 hA0new (f ≫ eI.hom ≫ m.hom)
    have hfH : fH = 0 := by
      apply (cancel_mono m).mp
      simpa using hfhm
    have hfI : f ≫ eI.hom = 0 :=
      congrArg InducedCategory.Hom.hom hfH
    exact (cancel_mono eI.hom).mp (by simpa using hfI)
  have hUtildeHeart : sigma.slicing.toTStructure.heart Utilde :=
    mem_heart_of_bounds sigma.slicing hUtildefree.1
      (sigma.slicing.leProp_mono C hbeta1.le Utilde hUtildefree.2)
  have hHom : ∀ A0 : C, sigma.weakStabilityFunctionOnHeart.zeroCharge A0 →
      ∀ f : A0 ⟶ Utilde, f = 0 := by
    intro A0 hA0 f
    exact sigma.slicing.zero_of_gtProp_leProp_general C beta
      (sigma.zeroCharge_phaseTors beta hbeta1 hA0).1 hUtildefree.2 f
  have hUtildess : sigma.weakStabilityFunctionOnHeart.IsSemistable Utilde :=
    sigma.weakStabilityFunctionOnHeart.isSemistable_middle_of_zeroCharge_quotient
      (t := sigma.slicing.toTStructure) hUss hUtildeHeart hPBOld hHom hUtri
  let Vprime : H := cokernel m
  let gB : BH ⟶ Vprime := cokernel.π m
  have hmg : m ≫ gB = 0 := cokernel.condition m
  have hBV : (ShortComplex.mk m gB hmg).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel m)
      inferInstance inferInstance
  obtain ⟨dV, hdV⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt m gB hmg (fun {X} x hx => by
      exact ⟨hBV.fIsKernel.lift (KernelFork.ofι x hx),
        hBV.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  have hRcharge : W.charge R = W.charge (U⟦(1 : ℤ)⟧) := by
    have hsum := W.charge_triangle' hd
    rw [hV.2, add_zero] at hsum
    exact hsum
  have hBcharge : W.charge B = W.charge (U⟦(1 : ℤ)⟧) := by
    have hsum := W.charge_triangle' hAB
    rw [hA.2, zero_add] at hsum
    exact hsum.symm.trans hRcharge
  have hIcharge : W.charge IH.obj = W.charge (U⟦(1 : ℤ)⟧) := by
    have hsum := W.charge_triangle' hdI
    rw [hPB.2, zero_add] at hsum
    exact hsum.symm
  have hVcharge : W.charge Vprime.obj = 0 := by
    have hsum := W.charge_triangle' hdV
    rw [hBcharge, hIcharge] at hsum
    apply add_left_cancel (a := W.charge (U⟦(1 : ℤ)⟧))
    simpa using hsum.symm
  have hVprime : W.zeroCharge Vprime.obj := ⟨Vprime.property, hVcharge⟩
  have hVprimeOld : sigma.zeroCharge Vprime.obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 Vprime.obj).mp hVprime
  let fB : Utilde⟦(1 : ℤ)⟧ ⟶ B := eI.hom ≫ m.hom
  let dB : Vprime.obj ⟶ Utilde⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    dV ≫ eI.inv⟦(1 : ℤ)⟧'
  have hBtri : Triangle.mk fB gB.hom dB ∈ distTriang C := by
    refine isomorphic_distinguished _ hdV _ ?_
    exact Triangle.isoMk _ _ eI (Iso.refl _) (Iso.refl _)
      (by simp [fB]) (by simp) (by simp [dB, ← Functor.map_comp])
  have hTypeTwo : sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 B := by
    refine ⟨Utilde, Vprime.obj, hUtildefree, hUtildess, hVprimeOld,
      fB, gB.hom, dB, hBtri, ?_⟩
    intro _ A0 hA0 z
    exact hB.2 A0
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 A0).mpr hA0) z
  have hBss : W.IsSemistable B :=
    sigma.isSemistable_of_isPhaseTiltTypeTwo beta hbeta0 hbeta1
      hB.1 (hBcharge.symm ▸ hUcharge) hTypeTwo
  exact ⟨A, B, hA, hB, a, q, delta, hAB, hBss, hBcharge⟩

/-- **The chain-transfer step in Proposition 14.16.**

Suppose `0 → Q → E → N → 0` is short exact in the tilted heart,
`Q` is right-orthogonal to tilted zero-charge objects, and `N` is an original
phase-torsion object.  Every chain of zero-charge subobjects of `E` then maps
monomorphically to a chain of original zero-charge subobjects of `N`, so the
original noetherian torsion hypothesis forces it to terminate. -/
theorem phaseTilt_zeroChargeChain_terminates_of_rightOrthogonal
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    (S : ShortComplex
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart.FullSubcategory)
    (hS : S.ShortExact)
    (hQ : rightOrthogonal
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge S.X₁.obj)
    (hN : phaseTors sigma.slicing beta S.X₃.obj)
    (c : SubobjectChain
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
      S.X₂.obj) : c.Terminates := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : Abelian P.tilt.heart.FullSubcategory := P.tilt.heartFullSubcategoryAbelian
  have propOld (j : ℕ) : sigma.zeroCharge (c.obj j) :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 (c.obj j)).mp (c.prop j)
  let AH (j : ℕ) : P.tilt.heart.FullSubcategory :=
    ⟨c.obj j, (c.toAmbient_mono j).1⟩
  let AOld (j : ℕ) : t.heart.FullSubcategory :=
    ⟨c.obj j, (propOld j).1⟩
  let NOld : t.heart.FullSubcategory :=
    ⟨S.X₃.obj, mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0 S.X₃.obj hN.1) hN.2⟩
  let stepSharp (j : ℕ) : AH j ⟶ AH (j + 1) :=
    ObjectProperty.homMk (c.step j)
  have stepSharp_mono (j : ℕ) : Mono (stepSharp j) :=
    mono_of_isHeartMono P.tilt (stepSharp j) (c.step_mono j)
  let stepOld (j : ℕ) : AOld j ⟶ AOld (j + 1) :=
    ObjectProperty.homMk (c.step j)
  have stepOld_mono (j : ℕ) : Mono (stepOld j) := by
    apply mono_in_originalHeart_of_mono_in_phaseTilt
      sigma beta hbeta0 hbeta1 (propOld j)
        (sigma.zeroCharge_phaseTors beta hbeta1 (propOld (j + 1)))
    simpa [stepSharp, stepOld, AH, AOld] using stepSharp_mono j
  let aSharp (j : ℕ) : AH j ⟶ S.X₂ :=
    ObjectProperty.homMk (c.toAmbient j)
  have aSharp_mono (j : ℕ) : Mono (aSharp j) :=
    mono_of_isHeartMono P.tilt (aSharp j) (c.toAmbient_mono j)
  have compSharp_mono (j : ℕ) : Mono (aSharp j ≫ S.g) := by
    letI : Mono (aSharp j) := aSharp_mono j
    exact mono_comp_of_zeroCharge_of_rightOrthogonal
      P.tilt W S hS (aSharp j) (c.prop j) hQ
  let toNOld (j : ℕ) : AOld j ⟶ NOld :=
    ObjectProperty.homMk (c.toAmbient j ≫ S.g.hom)
  have toNOld_mono (j : ℕ) : Mono (toNOld j) := by
    apply mono_in_originalHeart_of_mono_in_phaseTilt
      sigma beta hbeta0 hbeta1 (propOld j) hN
    apply mono_of_isHeartMono P.tilt
    exact isHeartMono_of_mono P.tilt (aSharp j ≫ S.g)
  let cOld : SubobjectChain t sigma.zeroCharge S.X₃.obj :=
    { obj := c.obj
      prop := propOld
      step := c.step
      toAmbient := fun j => c.toAmbient j ≫ S.g.hom
      step_mono := fun j => isHeartMono_of_mono t (stepOld j)
      toAmbient_mono := fun j => isHeartMono_of_mono t (toNOld j)
      comm := fun j => by
        rw [← Category.assoc, c.comm j] }
  apply noetherian_mono (t := t)
    (fun X hX => by rw [hN0]; exact hX) N0.noetherian
    S.X₃.obj NOld.property cOld

/-- Zero-charge decompositions of shifted phase-free objects discharge the
relative-chain seam in the noetherian assembly.

For `E` in the tilted heart, compose the envelope subobject
`A⁰ ⟶ H⁻¹(E)[1]` with the canonical cohomology subobject
`H⁻¹(E)[1] ⟶ E`.  The kernel--cokernel sequence of this composite gives a
short exact sequence

`coker(A⁰ ⟶ H⁻¹(E)[1]) ⟶ coker(A⁰ ⟶ E) ⟶ H⁰(E)`.

Its left term is right-orthogonal by the supplied decomposition and its right
term is an original phase-torsion object, so
`phaseTilt_zeroChargeChain_terminates_of_rightOrthogonal` constructs a maximal
zero-charge subobject of the middle term.  The general pullback lemma
`hasZeroChargeDecomposition_of_reduction` then lifts that decomposition
across `A⁰ ⟶ E`. -/
theorem phaseTilt_hasZeroChargeDecompositions_of_freeShiftDecompositions
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    (hfreeDec : ∀ (F : C), phaseFree sigma.slicing beta F →
      ∃ (A Q : C)
        (_ : (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt.heart
          (F⟦(1 : ℤ)⟧))
        (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
        (_ : rightOrthogonal
          (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
          (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge Q)
        (i : A ⟶ F⟦(1 : ℤ)⟧) (p : F⟦(1 : ℤ)⟧ ⟶ Q)
        (d : Q ⟶ A⟦(1 : ℤ)⟧),
          Triangle.mk i p d ∈ distTriang C) :
    WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) := by
  intro E hE
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian P.tilt.heart.FullSubcategory :=
    P.tilt.heartFullSubcategoryAbelian
  let S := P.originalCohomologyShortComplex hE
  have hS : S.ShortExact := P.originalCohomologyShortComplex_shortExact hE
  let F : C := (P.originalHMinusOne hE).obj
  have hF : phaseFree sigma.slicing beta F := P.originalHMinusOne_free hE
  obtain ⟨A, Q, -, hA, hQ, a, q, d, hd⟩ :=
    hfreeDec F hF
  let AH : P.tilt.heart.FullSubcategory := ⟨A, hA.1⟩
  let QH : P.tilt.heart.FullSubcategory := ⟨Q, hQ.1⟩
  let aH : AH ⟶ S.X₁ := ObjectProperty.homMk a
  let qH : S.X₁ ⟶ QH := ObjectProperty.homMk q
  have haq : aH ≫ qH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hd
  have hEnvShort : (ShortComplex.mk aH qH haq).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := AH) (B := S.X₁) (Q := QH)
        (f := aH) (g := qH) (δ := d) hd
  letI : Mono aH := hEnvShort.mono_f
  letI : Mono S.f := hS.mono_f
  let R := cokernelCompShortComplex aH S.f
  have hR : R.ShortExact := cokernelCompShortComplex_shortExact aH S.f
  let eQ : R.X₁ ≅ QH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel aH)
      hEnvShort.gIsCokernel
  let eQambient : R.X₁.obj ≅ Q := P.tilt.heart.ι.mapIso eQ
  have hRQ : rightOrthogonal P.tilt W.zeroCharge R.X₁.obj :=
    rightOrthogonal_of_iso P.tilt eQambient hQ
  let eN : R.X₃ ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f)
      hS.gIsCokernel
  let eNambient : R.X₃.obj ≅ S.X₃.obj := P.tilt.heart.ι.mapIso eN
  have hSN : phaseTors sigma.slicing beta S.X₃.obj :=
    P.originalHZero_tors hE
  have hRN : phaseTors sigma.slicing beta R.X₃.obj :=
    ⟨gtProp_of_iso sigma.slicing eNambient.symm hSN.1,
      leProp_of_iso sigma.slicing eNambient.symm hSN.2⟩
  have haccR : ∀ c : SubobjectChain P.tilt W.zeroCharge R.X₂.obj,
      c.Terminates := fun c =>
    sigma.phaseTilt_zeroChargeChain_terminates_of_rightOrthogonal
      beta hbeta0 hbeta1 N0 hN0 R hR hRQ hRN c
  have hdecR := W.hasZeroChargeDecomposition_of_chainCondition
    (t := P.tilt) R.X₂.obj R.X₂.property haccR
  let r : S.X₂ ⟶ R.X₂ := cokernel.π (aH ≫ S.f)
  have har : (aH ≫ S.f) ≫ r = 0 := cokernel.condition (aH ≫ S.f)
  let Red : ShortComplex P.tilt.heart.FullSubcategory :=
    ShortComplex.mk (aH ≫ S.f) r har
  have hepiR : Epi r := by
    change Epi (coequalizer.π (aH ≫ S.f) 0)
    infer_instance
  have hRed : Red.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (aH ≫ S.f))
      inferInstance hepiR
  exact W.hasZeroChargeDecomposition_of_reduction
    (t := P.tilt) Red hRed hA hdecR

/-- Phase-compatible envelopes provide the shifted decompositions consumed
by `phaseTilt_hasZeroChargeDecompositions_of_freeShiftDecompositions`. -/
theorem phaseTilt_hasZeroChargeDecompositions_of_phaseEnvelopes
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    (henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasPhaseTiltingEnvelope beta F) :
    WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) := by
  apply sigma.phaseTilt_hasZeroChargeDecompositions_of_freeShiftDecompositions
    beta hbeta0 hbeta1 N0 hN0
  intro F hF
  exact sigma.phaseTiltingEnvelope_gives_shiftedZeroChargeDecomposition
    beta hbeta0 hbeta1 hF (henv F hF)

/-- Raw Definition 14.12 envelopes provide the phase-compatible shifted
decompositions needed after tilting.  The bridge does not strengthen the raw
middle term to a phase-free object: it first applies
`phaseTilt_zeroChargeChain_terminates_of_tiltingEnvelope`, then chooses a
maximal tilted zero-charge subobject. -/
theorem phaseTilt_hasZeroChargeDecompositions_of_tiltingEnvelopes
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    (henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasTiltingEnvelope F) :
    WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  apply sigma.phaseTilt_hasZeroChargeDecompositions_of_freeShiftDecompositions
    beta hbeta0 hbeta1 N0 hN0
  intro F hF
  obtain ⟨A, Q, hA, hQ, i, p, d, hd⟩ :=
    W.hasZeroChargeDecomposition_of_chainCondition
    (t := P.tilt) (F⟦(1 : ℤ)⟧) (P.free_shift_mem_tilt_heart hF)
      (fun c => sigma.phaseTilt_zeroChargeChain_terminates_of_tiltingEnvelope
        beta hbeta0 hbeta1 N0 hN0 hF (henv F hF) c)
  exact ⟨A, Q, P.free_shift_mem_tilt_heart hF, hA, hQ, i, p, d, hd⟩

/-- Every tilted-heart zero-charge object is noetherian when the original
zero-charge class is the torsion class of a noetherian torsion subcategory.

This is independent of the still-open construction of the zero-charge
torsion pair on the whole tilted heart: it proves the intrinsic
noetherianity of the objects which will form that torsion class. -/
theorem phaseTilt_isNoetherianObject_of_zeroCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN : N.pair.tors = sigma.zeroCharge)
    (E : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart.FullSubcategory)
    (hE : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E.obj) :
    IsNoetherianObject E := by
  let t := sigma.slicing.toTStructure
  let tsharp := (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian tsharp.heart.FullSubcategory :=
    tsharp.heartFullSubcategoryAbelian
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let step (i : ℕ) :
      (f i : tsharp.heart.FullSubcategory) ⟶
        (f (i + 1) : tsharp.heart.FullSubcategory) :=
    Subobject.ofLE (f i) (f (i + 1)) (f.monotone (Nat.le_succ i))
  have propNew (i : ℕ) : W.zeroCharge (f i : tsharp.heart.FullSubcategory).obj := by
    let Q : tsharp.heart.FullSubcategory := cokernel (f i).arrow
    let p : E ⟶ Q := cokernel.π (f i).arrow
    have hp : (f i).arrow ≫ p = 0 := cokernel.condition (f i).arrow
    have hshort : (ShortComplex.mk (f i).arrow p hp).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (f i).arrow)
        inferInstance inferInstance
    obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
      (C := C) tsharp (f i).arrow p hp (fun {X} a ha => by
        exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
          hshort.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)
    exact W.zeroCharge_left (f i : tsharp.heart.FullSubcategory).property
      Q.property hE hd
  have propOld (i : ℕ) : sigma.zeroCharge (f i : tsharp.heart.FullSubcategory).obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 (f i : tsharp.heart.FullSubcategory).obj).mp (propNew i)
  have step_mono_old (i : ℕ) : IsHeartMono t (step i).hom := by
    obtain ⟨hA, hB, Q, hQ, g, d, hd⟩ :=
      isHeartMono_of_mono tsharp (step i)
    have hQzero : W.zeroCharge Q :=
      W.zeroCharge_right hA hQ (propNew (i + 1)) hd
    have hQold : sigma.zeroCharge Q :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 Q).mp hQzero
    exact ⟨(propOld i).1, (propOld (i + 1)).1, Q, hQold.1, g, d, hd⟩
  have toAmbient_mono_old (i : ℕ) : IsHeartMono t (f i).arrow.hom := by
    obtain ⟨hA, -, Q, hQ, g, d, hd⟩ :=
      isHeartMono_of_mono tsharp (f i).arrow
    have hQzero : W.zeroCharge Q := W.zeroCharge_right hA hQ hE hd
    have hQold : sigma.zeroCharge Q :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 Q).mp hQzero
    have hEold : sigma.zeroCharge E.obj :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 E.obj).mp hE
    exact ⟨(propOld i).1, hEold.1, Q, hQold.1, g, d, hd⟩
  have prop (i : ℕ) : N.pair.tors (f i : tsharp.heart.FullSubcategory).obj := by
    rw [hN]
    exact propOld i
  let c : SubobjectChain t N.pair.tors E.obj :=
    { obj := fun i => (f i : tsharp.heart.FullSubcategory).obj
      prop := prop
      step := fun i => (step i).hom
      toAmbient := fun i => (f i).arrow.hom
      step_mono := step_mono_old
      toAmbient_mono := toAmbient_mono_old
      comm := fun i => by
        exact congrArg
          (fun k : (f i : tsharp.heart.FullSubcategory) ⟶ E => k.hom)
          (Subobject.ofLE_arrow (f.monotone (Nat.le_succ i))) }
  have hEold : sigma.zeroCharge E.obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 E.obj).mp hE
  obtain ⟨n, hn⟩ := N.noetherian E.obj hEold.1 c
  refine ⟨n, fun m hnm => ?_⟩
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      rw [ih]
      let u : (f m : tsharp.heart.FullSubcategory) ⟶
          (f (m + 1) : tsharp.heart.FullSubcategory) := step m
      haveI : IsIso u.hom := hn m hnm
      let e : (f m : tsharp.heart.FullSubcategory) ≅
          (f (m + 1) : tsharp.heart.FullSubcategory) :=
        { hom := u
          inv := ObjectProperty.homMk (inv u.hom)
          hom_inv_id := by ext; simp
          inv_hom_id := by ext; simp }
      exact Subobject.eq_of_comm e
        (Subobject.ofLE_arrow (f.monotone (Nat.le_succ m)))

/-- Once the original zero-charge objects have been made into a torsion pair
on the tilted heart, their intrinsic noetherianity upgrades that pair to a
`NoetherianTorsionSubcategory`.

The proof factors every chain of torsion subobjects through the torsion term
of the chosen torsion/free decomposition.  That term has zero charge, hence
is a noetherian object by
`phaseTilt_isNoetherianObject_of_zeroCharge`; stabilization in its standard
subobject lattice forces the original chain maps to be isomorphisms. -/
noncomputable def phaseTiltNoetherianTorsionSubcategory
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN : N.pair.tors = sigma.zeroCharge)
    (Psharp : HeartTorsionPair
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt)
    (hP : Psharp.tors =
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt where
  pair := Psharp
  noetherian E hE c := by
    let tsharp := (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
    let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
    letI : Abelian tsharp.heart.FullSubcategory :=
      tsharp.heartFullSubcategoryAbelian
    obtain ⟨hLE, hGE⟩ := (TStructure.mem_heart_iff tsharp E).mp hE
    obtain ⟨T, F, hT, hF, i, p, d, hd⟩ :=
      Psharp.exists_triangle E hLE hGE
    let TH : tsharp.heart.FullSubcategory :=
      ⟨T, (TStructure.mem_heart_iff tsharp T).mpr
        ⟨Psharp.tors_isLE T hT, Psharp.tors_isGE T hT⟩⟩
    let EH : tsharp.heart.FullSubcategory := ⟨E, hE⟩
    let FH : tsharp.heart.FullSubcategory :=
      ⟨F, (TStructure.mem_heart_iff tsharp F).mpr
        ⟨Psharp.free_isLE F hF, Psharp.free_isGE F hF⟩⟩
    let iH : TH ⟶ EH := ObjectProperty.homMk i
    let pH : EH ⟶ FH := ObjectProperty.homMk p
    have hip : iH ≫ pH = 0 := by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hd
    have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) tsharp (A := TH) (B := EH) (Q := FH)
        (f := iH) (g := pH) (δ := d) hd
    letI : Mono iH := hshort.mono_f
    let AH (j : ℕ) : tsharp.heart.FullSubcategory :=
      ⟨c.obj j, (c.toAmbient_mono j).1⟩
    let a (j : ℕ) : AH j ⟶ EH := ObjectProperty.homMk (c.toAmbient j)
    haveI a_mono (j : ℕ) : Mono (a j) :=
      mono_of_isHeartMono tsharp (a j) (c.toAmbient_mono j)
    have hap (j : ℕ) : a j ≫ pH = 0 := by
      ext
      exact Psharp.hom_eq_zero (c.prop j) hF (c.toAmbient j ≫ p)
    let g (j : ℕ) : AH j ⟶ TH :=
      hshort.fIsKernel.lift (KernelFork.ofι (a j) (hap j))
    have hgi (j : ℕ) : g j ≫ iH = a j :=
      hshort.fIsKernel.fac (KernelFork.ofι (a j) (hap j))
        WalkingParallelPair.zero
    haveI g_mono (j : ℕ) : Mono (g j) := by
      constructor
      intro X u w huw
      apply (cancel_mono (a j)).mp
      rw [← hgi j, ← Category.assoc, ← Category.assoc, huw]
    let stepH (j : ℕ) : AH j ⟶ AH (j + 1) :=
      ObjectProperty.homMk (c.step j)
    have hstep (j : ℕ) : stepH j ≫ g (j + 1) = g j := by
      apply (cancel_mono iH).mp
      rw [Category.assoc, hgi (j + 1), hgi j]
      ext
      exact c.comm j
    let sub (j : ℕ) : Subobject TH := Subobject.mk (g j)
    have hsub_succ (j : ℕ) : sub j ≤ sub (j + 1) :=
      Subobject.mk_le_mk_of_comm (stepH j) (hstep j)
    let subChain : ℕ →o Subobject TH :=
      ⟨sub, monotone_nat_of_le_succ hsub_succ⟩
    have hTzero : W.zeroCharge TH.obj := by
      rw [← hP]
      exact hT
    letI : IsNoetherianObject TH :=
      sigma.phaseTilt_isNoetherianObject_of_zeroCharge beta hbeta0 hbeta1
        N hN TH hTzero
    obtain ⟨n, hn⟩ :=
      monotone_chain_condition_of_isNoetherianObject subChain
    refine ⟨n, fun j hnj => ?_⟩
    let sj : AH j ⟶ AH (j + 1) := stepH j
    haveI : Mono sj :=
      mono_of_isHeartMono tsharp sj (c.step_mono j)
    have heq : Subobject.mk (g j) = Subobject.mk (g (j + 1)) := by
      change subChain j = subChain (j + 1)
      exact (hn j hnj).symm.trans (hn (j + 1) (by omega))
    haveI : IsIso sj := by
      by_contra hnot
      have hlt : Subobject.mk (g j) < Subobject.mk (g (j + 1)) :=
        Subobject.mk_lt_mk_of_comm sj (hstep j) hnot
      rw [heq] at hlt
      exact (lt_irrefl _) hlt
    simpa [sj, stepH] using
      (tsharp.heart.ι.mapIso (asIso sj)).isIso_hom

/-- Termination of zero-charge subobject chains in every tilted-heart object
produces the zero-charge torsion decompositions by the maximal-subobject
construction in `Noetherian.lean`.

This is the precise order-theoretic seam in the proof of Proposition 14.16:
the envelope argument is responsible only for this relative chain condition;
images, pullbacks, right orthogonality, and the resulting torsion pair are
then automatic. -/
theorem phaseTilt_hasZeroChargeDecompositions_of_chainCondition
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hacc : ∀ (E : C),
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E →
      ∀ c : SubobjectChain
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E,
        c.Terminates) :
    WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) :=
  WeakStabilityFunction.hasZeroChargeDecompositions_of_chainCondition
    (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) hacc

/-- The noetherian zero-charge obligation after tilting, assembled directly
from zero-charge decompositions in the tilted heart.  This removes the
intermediate `HeartTorsionPair` parameter from
`phaseTiltNoetherianTorsionSubcategory`: once the maximal-subobject argument
has produced the decompositions, both the torsion pair and its chain condition
are automatic. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfDecompositions
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN : N.pair.tors = sigma.zeroCharge)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt := by
  let tsharp := (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  exact sigma.phaseTiltNoetherianTorsionSubcategory beta hbeta0 hbeta1 N hN
    (W.zeroChargeTorsionPair tsharp hdec) rfl

/-- Definition 14.12(1) supplies the original noetherian torsion class, so
after the maximal-subobject argument has produced tilted zero-charge
decompositions, the full noetherian torsion obligation of Proposition 14.16
is assembled without any further input. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt := by
  let N := Classical.choose htilt.zeroCharge_noetherian
  have hN : N.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  exact sigma.phaseTiltNoetherianTorsionSubcategoryOfDecompositions
    beta hbeta0 hbeta1 N hN hdec

/-- The noetherian zero-charge torsion structure assembled from
Definition 14.12(1) and phase-compatible instances of its envelope clause.
Unlike the older chain-condition constructor, this version performs the
envelope reduction, reduced-chain argument, and pullback internally. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfPhaseEnvelopes
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasPhaseTiltingEnvelope beta F) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt := by
  let N := Classical.choose htilt.zeroCharge_noetherian
  have hN : N.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  exact sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
    beta hbeta0 hbeta1 htilt
      (sigma.phaseTilt_hasZeroChargeDecompositions_of_phaseEnvelopes
        beta hbeta0 hbeta1 N hN henv)

/-- The noetherian tilted zero-charge torsion structure constructed directly
from Definition 14.12.  Its raw envelope clause is restricted to the
phase-cut free class by `TiltingProperty.hasTiltingEnvelope_of_phaseFree`,
then converted to tilted zero-charge decompositions by chain termination. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfTiltingEnvelopes
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt := by
  let N := Classical.choose htilt.zeroCharge_noetherian
  have hN : N.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  let henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasTiltingEnvelope F :=
    fun F hF => TiltingProperty.hasTiltingEnvelope_of_phaseFree
      sigma htilt beta hbeta1 F hF
  exact sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
    beta hbeta0 hbeta1 htilt
      (sigma.phaseTilt_hasZeroChargeDecompositions_of_tiltingEnvelopes
        beta hbeta0 hbeta1 N hN henv)

/-- The full noetherian zero-charge torsion structure, with the relative
chain condition as its only remaining envelope-level input. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfChainCondition
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (hacc : ∀ (E : C),
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E →
      ∀ c : SubobjectChain
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E,
        c.Terminates) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt :=
  sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
    beta hbeta0 hbeta1 htilt
      (sigma.phaseTilt_hasZeroChargeDecompositions_of_chainCondition
        beta hbeta0 hbeta1 hacc)

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition
