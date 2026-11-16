/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Yoneda
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Functor

/-!
# Representing objects of the Quot functor

A Quot scheme for `p : X ⟶ S` and `F` is an `S`-scheme `Q` with
`(quotFunctor p F).RepresentableBy Q`, Mathlib's Yoneda representability. It carries a universal
quotient over `Q`, and every point over `T` is the pullback of the universal quotient along the
classifying map `T ⟶ Q` (`Functor.RepresentableBy.homEquiv_eq`).

The one representability theorem proved here is for a zero module sheaf `F`: `F_T` is zero for
every `T`, so its only quotient is `F_T ↠ 0`, and the functor is represented by the terminal
object `S ⟶ S` of `Over S`.

## Main definitions

* `AlgebraicGeometry.quotFunctor.universalQuotient` — the universal quotient of a representing
  object.
* `AlgebraicGeometry.quotFunctorZeroRepresentableBy` — the Quot functor of a zero module sheaf
  is represented by `S ⟶ S`.

## Implementation notes

Finite type of a representing object is not part of representability. A statement that needs it
assumes `(quotFunctor p F).RepresentableBy Q` and `LocallyOfFiniteType Q.hom` separately.

## Tags

Quot scheme, representable functor, Yoneda, universal quotient
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}}

/-- The universal quotient carried by a representing object `Q` of `quotFunctor p F`: the point
over `Q` that corresponds to `𝟙 Q`. -/
def quotFunctor.universalQuotient {p : X ⟶ S} {F : X.Modules} {Q : Over S}
    (e : (quotFunctor p F).RepresentableBy Q) : (quotFunctor p F).obj (op Q) :=
  e.homEquiv (𝟙 Q)

/-- The pullback of a zero module sheaf is zero, so all its quotients are isomorphic. -/
private lemma subsingleton_quotFunctor_of_isZero (p : X ⟶ S) {F : X.Modules} (hF : IsZero F)
    (T : Over S) : Subsingleton ((quotFunctor p F).obj (op T)) := by
  have hG : IsZero (quotBaseChange p F T) := (Scheme.Modules.pullback _).map_isZero hF
  have : Subsingleton (Quotient (isIsomorphicSetoid
      (ModuleQuotient.IsFlatFinitePresentation (pullback.snd p T.hom)
        (G := quotBaseChange p F T)).FullSubcategory)) := by
    refine ⟨fun x y ↦ ?_⟩
    induction x using Quotient.inductionOn with | h r => ?_
    induction y using Quotient.inductionOn with | h s => ?_
    exact Quotient.sound ⟨ObjectProperty.isoMk _ (ModuleQuotient.isoMk
      ((hG.of_epi r.obj.hom).iso (hG.of_epi s.obj.hom)) (hG.eq_of_src _ _))⟩
  exact (equivShrink _).symm.subsingleton

/-- A zero module sheaf has exactly one flat, finitely presented quotient over every `T`, the
zero quotient, so its Quot functor is represented by the terminal object `S ⟶ S` of `Over S`.
For the chosen zero object this is `quotFunctorZeroRepresentableBy p (isZero_zero _)`. -/
def quotFunctorZeroRepresentableBy (p : X ⟶ S) {F : X.Modules} (hF : IsZero F) :
    (quotFunctor p F).RepresentableBy (Over.mk (𝟙 S)) where
  homEquiv {T} :=
    { toFun _ := quotFunctor.zeroPoint p F T
      invFun _ := Over.mkIdTerminal.from T
      left_inv _ := Over.mkIdTerminal.hom_ext _ _
      right_inv _ := (subsingleton_quotFunctor_of_isZero p hF T).elim _ _ }
  homEquiv_comp {T _} _ _ := (subsingleton_quotFunctor_of_isZero p hF T).elim _ _

end

end AlgebraicGeometry
