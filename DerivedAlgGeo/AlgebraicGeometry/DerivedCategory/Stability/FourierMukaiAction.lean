/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelComposition
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.FourierMukai

/-!
# Algebraic-geometric Fourier--Mukai actions on stability conditions

This file applies the categorical stability action to geometric Fourier--Mukai
autoequivalences. Neutral kernels, duals, swaps, and convolution live in
`DerivedCategory/FourierMukai/`; the generic action lives under
`CategoryTheory/Triangulated/`. This file is the one Fourier--Mukai module that
imports the stability tree, which is why it sits under `DerivedCategory/Stability/`
rather than beside the neutral kernels.
-/

universe u

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open AlgebraicGeometry SchemeBaseChange

variable {S : Scheme.{u}}

section KernelAction

variable (X Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
  (σ : Z ⟶ Z) (p q : Z ⟶ X) (K : SchemeBoundedCoherentDerivedCategory Z.left)
  [HasCoherentPullback σ] [HasCoherentPullback p] [HasCoherentPullback q]
  [HasDerivedPushforward σ] [HasDerivedPushforward p] [HasDerivedPushforward q]
  [HasCoherentDerivedTensor Z]
  [HasPullbackSwap σ p q] [HasPushforwardSwap σ p q]
  [HasProjectionFormulaRight σ]
  [HasDerivedPullbackAdjunction p] [HasKernelDual Z K]
  [HasTwistedInversePullback q] [HasDualizingTwist q]

/-- A geometric kernel autoequivalence transports a stability condition. -/
noncomputable def geometricActStabOfDual
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)]
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    (lam : Λ →+ Λ)
    (hlam : ∀ x, v ((geometricCorrespondence X X Z p q).transformK₀
        (geometricDualKernelObj X Z σ q K) x) = lam (v x))
    (s : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v) :
    StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v :=
  (geometricKernelAutoequivalenceOfAdjoint X Z σ p q K).actStabOfDual v
    (geometricDualKernelOfAdjoint X Z σ p q K) lam hlam s

/-- A geometric kernel autoequivalence defines an element of the acting group. -/
noncomputable def geometricToAutPair
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)]
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    (lam : Λ ≃+ Λ)
    (hlam : ∀ x, v ((geometricCorrespondence X X Z p q).transformK₀
        (geometricDualKernelObj X Z σ q K) x) = lam (v x)) :
    GroupAction.AutPair v :=
  (geometricKernelAutoequivalenceOfAdjoint X Z σ p q K).toAutPair v
    (geometricDualKernelOfAdjoint X Z σ p q K) lam hlam

/-- The geometric group element acts by its Fourier--Mukai transport. -/
theorem geometricMk_toAutPair_smul
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)]
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    (lam : Λ ≃+ Λ)
    (hlam : ∀ x, v ((geometricCorrespondence X X Z p q).transformK₀
        (geometricDualKernelObj X Z σ q K) x) = lam (v x))
    (s : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v) :
    GroupAction.AutPairQuot.mk (geometricToAutPair X Z σ p q K v lam hlam) • s =
      geometricActStabOfDual X Z σ p q K v lam.toAddMonoidHom
        (fun x => hlam x) s :=
  rfl

end KernelAction

section CompositionAction

variable (X Z₁ Z₂ Z₃ : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z₁.left]
  [IsLocallyNoetherian Z₂.left] [IsLocallyNoetherian Z₃.left]
  (σ₁ : Z₁ ⟶ Z₁) (p₁ q₁ : Z₁ ⟶ X)
  (K₁ : SchemeBoundedCoherentDerivedCategory Z₁.left)
  (σ₂ : Z₂ ⟶ Z₂) (p₂ q₂ : Z₂ ⟶ X)
  (K₂ : SchemeBoundedCoherentDerivedCategory Z₂.left)
  (p₃ : Z₃ ⟶ X) (q₃ : Z₃ ⟶ X)
  [HasCoherentPullback σ₁] [HasCoherentPullback p₁] [HasCoherentPullback q₁]
  [HasDerivedPushforward σ₁] [HasDerivedPushforward p₁] [HasDerivedPushforward q₁]
  [HasCoherentDerivedTensor Z₁] [HasPullbackSwap σ₁ p₁ q₁]
  [HasPushforwardSwap σ₁ p₁ q₁] [HasProjectionFormulaRight σ₁]
  [HasDerivedPullbackAdjunction p₁] [HasKernelDual Z₁ K₁]
  [HasTwistedInversePullback q₁] [HasDualizingTwist q₁]
  [HasCoherentPullback σ₂] [HasCoherentPullback p₂] [HasCoherentPullback q₂]
  [HasDerivedPushforward σ₂] [HasDerivedPushforward p₂] [HasDerivedPushforward q₂]
  [HasCoherentDerivedTensor Z₂] [HasPullbackSwap σ₂ p₂ q₂]
  [HasPushforwardSwap σ₂ p₂ q₂] [HasProjectionFormulaRight σ₂]
  [HasDerivedPullbackAdjunction p₂] [HasKernelDual Z₂ K₂]
  [HasTwistedInversePullback q₂] [HasDualizingTwist q₂]
  [∀ E, IsIso ((geometricDualAdjointKernelData X Z₁ σ₁ p₁ q₁ K₁).adj.unit.app E)]
  [∀ E, IsIso ((geometricDualAdjointKernelData X Z₁ σ₁ p₁ q₁ K₁).adj.counit.app E)]
  [∀ E, IsIso ((geometricDualAdjointKernelData X Z₂ σ₂ p₂ q₂ K₂).adj.unit.app E)]
  [∀ E, IsIso ((geometricDualAdjointKernelData X Z₂ σ₂ p₂ q₂ K₂).adj.counit.app E)]
  [HasCoherentPullback p₃] [HasCoherentDerivedTensor Z₃]
  [HasDerivedPushforward q₃]
  (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]
  [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
  [HasCoherentPullback G.πXW] [HasCoherentDerivedTensor G.triple]
  [HasDerivedPushforward G.πYW] [HasDerivedPushforward G.πXW]
  [HasFlatBaseChange q₁ G.πYW G.πXY p₂] [HasProjectionFormula G.πYW]
  [HasMonoidalDerivedPullback G.πXY] [HasProjectionFormulaRight G.πXW]
  [HasCommonPullbackRoute p₁ G.πXY p₃ G.πXW]
  [HasCommonPushforwardRoute G.πYW q₂ G.πXW q₃]

/-- Geometric stability transport respects convolution of kernels. -/
theorem geometricActStabTrans
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    {lam₁ lam₂ : Λ →+ Λ}
    (h₁ : ∀ x, v (K₀.map
        (geometricKernelAutoequivalenceOfAdjoint X Z₁ σ₁ p₁ q₁ K₁).equiv.inverse x)
      = lam₁ (v x))
    (h₂ : ∀ x, v (K₀.map
        (geometricKernelAutoequivalenceOfAdjoint X Z₂ σ₂ p₂ q₂ K₂).equiv.inverse x)
      = lam₂ (v x))
    (s : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v) :
    (geometricKernelAutoequivalenceOfAdjoint X Z₂ σ₂ p₂ q₂ K₂).actStab v lam₂ h₂
        ((geometricKernelAutoequivalenceOfAdjoint X Z₁ σ₁ p₁ q₁ K₁).actStab
          v lam₁ h₁ s)
      = (geometricTransKernelAutoequivalence X Z₁ Z₂ Z₃ σ₁ p₁ q₁ K₁ σ₂ p₂ q₂ K₂
          p₃ q₃ G).actStab v (lam₁.comp lam₂)
          (hlam_trans v _ _ h₁ h₂) s :=
  KernelAutoequivalence.actStab_trans v _ _ _
    (geometricConvolutionData p₁ q₁ p₂ q₂ p₃ q₃ G) h₁ h₂ s

end CompositionAction

end AlgebraicGeometry.DerivedCategory.FourierMukai
