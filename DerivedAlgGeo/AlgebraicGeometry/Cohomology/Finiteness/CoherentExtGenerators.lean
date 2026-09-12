/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.FiniteGenerators
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.RestrictedTwistPresentation
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear

/-!
# Coherent Ext-finiteness from restricted-twist presentations

This file connects the projective presentation lane to the generic quotient-generator
dévissage for Ext.  It gives two honest reductions:

1. coherent presentations whose middle terms have finite ambient Ext imply degreewise finite
   ambient Ext between arbitrary coherent sheaves;
2. the restricted-twist presentations constructed by a `ProjectivePresentation` reduce that
   hypothesis to finite ambient Ext from negative restricted twists, provided the
   closed-immersion pullback/pushforward counit is epi.

## Remaining geometric boundary

Neither premise in the second reduction is fabricated here.  At the current Mathlib pin:

* the standard closed-immersion comparison `ι^* ι_* F ≅ F` for module sheaves is unavailable,
  so the counit epimorphism cannot yet be discharged;
* a restricted twist is intrinsically invertible, but the pullback functor does not have the
  monoidal API needed to package a chosen `Scheme.Modules.LineBundleData`.  Consequently the
  line-bundle Ext-finiteness theorem cannot yet be applied to it;
* these theorems concern Ext in `X.Modules`.  Passing to Ext internal to `Coh X` still requires
  the non-affine `CoherentExtComparison X`;
* degreewise finiteness alone does not give the finite degree support required by
  `DerivedCategory.ExtFiniteBounded.of_ext`.  A geometric regularity/global-dimension bound
  remains necessary.

Thus the result advances the Serre/Dqc lane as far as the present APIs justify, without assuming
Grothendieck boundedness, postulating a class map, or installing a `MuHNInput` instance.
-/

universe u

open CategoryTheory CategoryTheory.Limits Abelian
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePresentation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.hasExt_of_hasDerivedCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- Degreewise ambient Ext-finiteness follows from coherent quotient presentations whose middle
terms have finite ambient Ext against every coherent target.

The kernel stays coherent because the presentation lives in `Coh X`; exactness is transported to
`X.Modules` by the exact inclusion. -/
theorem module_finite_ambientExt_of_coherent_presentations
    (hpresentation : ∀ F : Coh X,
      ∃ (S : ShortComplex (Coh X)) (_ : S.ShortExact) (_ : S.X₃ ≅ F),
        ∀ (G : Coh X) (n : ℕ), Module.Finite k
          (Ext.{u + 1} ((Coh.ι X).obj S.X₂) ((Coh.ι X).obj G) n))
    (F G : Coh X) (n : ℕ) :
    Module.Finite k (Ext.{u + 1} ((Coh.ι X).obj F) ((Coh.ι X).obj G) n) := by
  letI hExtStandard : HasExt.{u + 1} X.Modules := HasExt.standard X.Modules
  apply Ext.module_finite_of_quotient_generators (Q := Scheme.coherent X) ?_
    ((Coh.ι X).obj F) ((Coh.ι X).obj G) F.property G.property n
  intro M hM
  obtain ⟨S, hS, e, hfinite⟩ := hpresentation ⟨M, hM⟩
  refine ⟨S.map (Coh.ι X), Coh.shortExact_map_ι X hS, (Coh.ι X).mapIso e,
    S.X₁.property, ?_⟩
  intro N hN j
  exact hfinite ⟨N, hN⟩ j

/-- **Projective coherent Ext-finiteness reduced to the two missing restricted-twist inputs.**

The counit premise turns Serre's ambient projective-space quotient into a quotient on `X`.
The second premise asks only for degreewise ambient Ext-finiteness from the negative restricted
twists that occur in that quotient.  Finite coproduct compatibility and the long exact Ext
sequence then give the conclusion for all coherent source and target sheaves. -/
theorem module_finite_ambientExt_of_restrictedTwists
    (P : AlgebraicGeometry.ProjectivePresentation k X) [Nontrivial P.index]
    (hcounit : ∀ F : Coh X, Epi
      ((Scheme.Modules.pullbackPushforwardAdjunction P.embedding).counit.app
        ((Coh.ι X).obj F)))
    (htwist : ∀ (N : ℕ), 1 ≤ N → ∀ (G : Coh X) (n : ℕ), Module.Finite k
      (Ext.{u + 1}
        ((Coh.ι X).obj (P.restrictedTwist (-(N : ℤ)))) ((Coh.ι X).obj G) n))
    (F G : Coh X) (n : ℕ) :
    Module.Finite k (Ext.{u + 1} ((Coh.ι X).obj F) ((Coh.ι X).obj G) n) := by
  letI hExtStandard : HasExt.{u + 1} X.Modules := HasExt.standard X.Modules
  apply module_finite_ambientExt_of_coherent_presentations ?_ F G n
  intro E
  obtain ⟨S, hS, e, N, hN, I, hI, hmiddle⟩ :=
    P.exists_shortExact_coproduct_restrictedTwist_of_counit_epi E (hcounit E)
  refine ⟨S, hS, e, ?_⟩
  intro T j
  letI := Fintype.ofFinite I
  let A : I → X.Modules :=
    fun _ ↦ (Coh.ι X).obj (P.restrictedTwist (-(N : ℤ)))
  let eMiddle : (Coh.ι X).obj S.X₂ ≅ ∐ A :=
    (Coh.ι X).mapIso (eqToIso hmiddle) ≪≫
      PreservesCoproduct.iso (Coh.ι X)
        (fun _ : I ↦ P.restrictedTwist (-(N : ℤ)))
  letI : Module.Finite k (Ext.{u + 1} (∐ A) ((Coh.ι X).obj T) j) :=
    @Ext.module_finite_coproduct_left k _ X.Modules _ _ _ hExtStandard I inferInstance
      A ((Coh.ι X).obj T) j (fun _ ↦ htwist N hN T j)
  exact Module.Finite.equiv (Ext.precompLinearEquiv (S := k) eMiddle ((Coh.ι X).obj T) j)

end AlgebraicGeometry.ProjectivePresentation
