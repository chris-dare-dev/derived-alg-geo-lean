/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.FourierMukai.KernelSwap
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelConvolution

/-!
# Composing two geometric Fourier--Mukai transports

`KernelSwap.lean` gives a geometric kernel autoequivalence and shows it
transports a stability condition. `KernelConvolution.lean` gives the geometric
convolution of two kernels, with **no supplied fields** — its `conv` and
`compIso` are both derived. This file is the one statement that needs both:

> transporting along two geometric Fourier--Mukai transforms is transporting
> along the transform of their convolved kernel.

`Symmetry/Autoequivalence/FourierMukai` proves that abstractly
(`KernelAutoequivalence.actStab_trans`), for a *supplied* `ConvolutionData`.
Here the convolution data is `geometricConvolutionData` — assembled from the
geometric ledger — so nothing in this file is supplied at all.

## No new contracts

Every hypothesis below already exists: the two autoequivalences' own ledgers,
and the seven classical inputs `geometricConvolutionData` names (flat base
change, the two projection formulas, the monoidal pullback, and the two route
classes). **This file introduces no class and asks for no datum.** It is
composition of what the two ledgers already produce.

That is also why it is short. The mathematics was done in #466 abstractly and
in `KernelConvolution.lean` geometrically; what was missing was that the two
could be joined, which needed the geometric autoequivalence to exist at all
(`KernelSwap.lean`) and its exactness to be reachable by instance search.

## What this file does not assert

* **Nothing is constructed that was not already constructible.** Every input is
  a hypothesis, and the whole ledger below it remains uninhabited: no scheme is
  shown to admit any of these contracts.
* No monoid or group of geometric kernel autoequivalences. This is the
  associativity clause of an action and nothing more — the abstract file's
  docstring explains at length why no identity law follows, and none is claimed
  here either.
* Nothing about `toAutPair` or `AutPairQuot` for the geometric composite.
* No claim that any geometric transform is an equivalence; the invertibility of
  each assembled adjunction's unit and counit is assumed, as in `KernelSwap`.
-/

universe u

namespace AlgebraicGeometry.StabilityCondition.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section Composition

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

/-- **The composite of two geometric kernel autoequivalences.**

`KernelAutoequivalence.trans` at the two geometric autoequivalences and the
geometric convolution data. Its kernel is `convKernel G K₁' K₂'` for the two
adjoint-derived kernels, and its equivalence is the composite of the two.

Nothing is supplied: the convolution data comes from
`geometricConvolutionData`, whose own `conv` and `compIso` are derived. -/
@[reducible] noncomputable def geometricTransKernelAutoequivalence :
    Symmetry.KernelAutoequivalence
      (SchemeBoundedCoherentDerivedCategory X.left)
      (SchemeBoundedCoherentDerivedCategory Z₃.left) :=
  (geometricKernelAutoequivalenceOfAdjoint X Z₁ σ₁ p₁ q₁ K₁).trans
    (geometricKernelAutoequivalenceOfAdjoint X Z₂ σ₂ p₂ q₂ K₂)
    (geometricCorrespondence X X Z₃ p₃ q₃)
    (geometricConvolutionData p₁ q₁ p₂ q₂ p₃ q₃ G)

/-- **Transporting along two geometric transforms is transporting along the
convolved one.**

The composition law, geometrically. `KernelAutoequivalence.actStab_trans` at
the two geometric autoequivalences and the derived convolution data — so the
kernel that computes the composite action is `convKernel`, and the action on
stability conditions is tracked by kernels the whole way.

Conditional on both ledgers and on the invertibility of each assembled
adjunction's unit and counit; nothing here supplies any of it. -/
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
  Symmetry.KernelAutoequivalence.actStab_trans v _ _ _
    (geometricConvolutionData p₁ q₁ p₂ q₂ p₃ q₃ G) h₁ h₂ s

end Composition

end AlgebraicGeometry.StabilityCondition.FourierMukai
