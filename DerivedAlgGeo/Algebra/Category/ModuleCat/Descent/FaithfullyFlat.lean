/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Descent.BaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Faithfully flat descent for modules

Let `φ : A ⟶ B` be a faithfully flat map of commutative rings. Modules have effective descent
along `φ`: the pseudofunctor of extension of scalars, `moduleCatAdjPseudofunctor.comp
Adj.forget₁` on `CommRingCatᵒᵖ`, is a stack for the singleton presieve `{φ.op}`, and
`ModuleCat A` is equivalent to the category of `B`-modules with descent data along `A ⟶ B`
(Stacks Project, Tag 023N).

This closes the TODO in the module docstring of `Mathlib.Algebra.Category.ModuleCat.Descent`:
"the general theory of descent implies that the pseudofunctor to `Cat` given by extension of
scalars has effective descent relative to faithfully flat maps".

## Main definitions

* `CommRingCat.moduleCatDescentEquivalence`: for `φ` faithfully flat, `ModuleCat A` is
  equivalent to `B`-modules with descent data along `φ`, by the comparison functor
  `toDescentData`.

## Main results

* `CommRingCat.isStackFor_moduleCat_of_faithfullyFlat`: the module pseudofunctor is a stack for
  `Presieve.singleton φ.op` when `φ` is faithfully flat.

## Implementation notes

Effective descent is not assumed. It is concluded from two proved facts through the
Bénabou–Roubaud criterion `Pseudofunctor.isStackFor_singleton_iff_isEquivalence_comparison`:
the base change morphisms of the chosen pullbacks are isomorphisms
(`isIso_baseChange_moduleCatAdjPseudofunctor`), and extension of scalars along a faithfully
flat map is comonadic (Mathlib's `comonadicExtendScalars`, the content of Stacks Tag 023M).
The chosen double and triple pullbacks of `φ.op` are the ones given by `HasPullbacks`
on `CommRingCatᵒᵖ`; the base change theorem holds for every chosen pullback, so the choice does
not matter.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N), Descent,
  Proposition 35.3.9; and Tag 023M (Lemma 35.3.6).
* A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent theory*,
  arXiv:math/0412512v4, Theorem 4.21.

## Tags

descent, faithfully flat, module, comonadic, stack
-/

universe u

open CategoryTheory Bicategory Opposite Limits

namespace CommRingCat

section

variable {X S : CommRingCat.{u}ᵒᵖ} (f : X ⟶ S)

/-- The pullback of `f` along itself in `CommRingCatᵒᵖ`, as a chosen pullback. -/
private noncomputable def chosenPullbackSelf : ChosenPullback f f where
  pullback := pullback f f
  p₁ := pullback.fst f f
  p₂ := pullback.snd f f
  condition := pullback.condition
  isLimit := pullbackIsPullback f f

/-- The triple pullback of `f` along itself in `CommRingCatᵒᵖ`, as a chosen triple pullback. -/
private noncomputable def chosenPullback₃Self :
    ChosenPullback₃ (chosenPullbackSelf f) (chosenPullbackSelf f) (chosenPullbackSelf f) where
  chosenPullback :=
    { pullback := pullback (pullback.snd f f) (pullback.fst f f)
      p₁ := pullback.fst (pullback.snd f f) (pullback.fst f f)
      p₂ := pullback.snd (pullback.snd f f) (pullback.fst f f)
      condition := pullback.condition (f := pullback.snd f f) (g := pullback.fst f f)
      isLimit := pullbackIsPullback (pullback.snd f f) (pullback.fst f f) }
  l :=
    { f := pullback.lift (pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f)
        (pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f) (by
          simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
      f_p₁ := by simp [chosenPullbackSelf]
      f_p₂ := by simp [chosenPullbackSelf]
      f_p := by simp [chosenPullbackSelf] }

end

/-- **Faithfully flat descent for modules** (Stacks Project, Tag 023N). If `φ : A ⟶ B` is a
faithfully flat map of commutative rings, the pseudofunctor of extension of scalars on
`CommRingCatᵒᵖ` is a stack for the singleton presieve `{φ.op}`: every `B`-module with descent
data along `φ` comes from an `A`-module, uniquely up to unique isomorphism.

This is the TODO of `Mathlib.Algebra.Category.ModuleCat.Descent`: "the general theory of descent
implies that the pseudofunctor to `Cat` given by extension of scalars has effective descent
relative to faithfully flat maps".

Faithful flatness cannot be weakened to flatness. The map `φ : ℤ ⟶ ℚ` is flat but not faithfully
flat, and `ℚ ⊗ (ℤ/2) = 0`, so `toDescentData` sends `ℤ/2` and `0` to isomorphic descent data
although `ℤ/2 ≇ 0`; descent along `φ` is not effective. -/
theorem isStackFor_moduleCat_of_faithfullyFlat {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.FaithfullyFlat) :
    (moduleCatAdjPseudofunctor.comp Adj.forget₁).IsStackFor (Presieve.singleton φ.op) := by
  rw [Pseudofunctor.isStackFor_singleton_iff_isEquivalence_comparison moduleCatAdjPseudofunctor φ.op
    (chosenPullbackSelf φ.op) (chosenPullback₃Self φ.op)
    (isIso_baseChange_moduleCatAdjPseudofunctor _) (isIso_baseChange_moduleCatAdjPseudofunctor _)]
  exact (comonadicExtendScalars hφ).eqv

/-- For a faithfully flat map `φ : A ⟶ B` of commutative rings, `ModuleCat A` is equivalent to the
category of `B`-modules with descent data along `φ`. The functor is the comparison functor
`toDescentData`, which sends `M` to `B ⊗[A] M` with its canonical descent datum
(Stacks Project, Tag 023N). -/
noncomputable def moduleCatDescentEquivalence {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.FaithfullyFlat) :
    ModuleCat.{u} A ≌
      (moduleCatAdjPseudofunctor.comp Adj.forget₁).DescentData (fun (_ : Unit) ↦ φ.op) :=
  have h := isStackFor_moduleCat_of_faithfullyFlat φ hφ
  have : ((moduleCatAdjPseudofunctor.comp Adj.forget₁).toDescentData
      (fun (_ : Unit) ↦ φ.op)).IsEquivalence := by
    rwa [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isStackFor_ofArrows_iff] at h
  ((moduleCatAdjPseudofunctor.comp Adj.forget₁).toDescentData (fun (_ : Unit) ↦ φ.op)).asEquivalence

end CommRingCat
