/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion

/-!
# Direct image on bounded coherent derived categories

Definition 3.1 of arXiv:2607.28411v1 pulls a stability condition on `Dᵇ(Y)`
back along a proper morphism `f : X → Y` through the direct image
`f_* : Dᵇ(X) ⥤ Dᵇ(Y)`.  This file supplies that functor on the genuine
bounded coherent derived fibers of scheme base changes, in the shape in which
`BoundedGeometry.lean` supplies the inverse image `f^*`.

The contract `HasCoherentPushforward f` records what a morphism must provide:
an exact pushforward on coherent sheaves that forgets to module-sheaf
pushforward.  Unlike `HasCoherentPullback`, it carries no derived functor as
a field.  An exact functor between abelian categories induces its derived
functor degreewise, so `coherentDerivedPushforward` is Mathlib's
`Functor.mapDerivedCategory`, and boundedness, the shift, and the triangulated
structure are theorems (`mapDerivedCategory_bounded` and Mathlib's instances)
rather than obligations of the instance.

Closed immersions into locally Noetherian schemes inhabit the contract through
`Coh.pushforward`.  Finite morphisms, the case Proposition 3.3 of the paper
needs, would inhabit it once coherence of `f_*` along a finite morphism is
proved; the contract is stated on an arbitrary morphism so that instance is an
addition, not a rewrite.

## Main definitions

* `SchemeBaseChange.HasCoherentPushforward`: the exact coherent pushforward
  contract.
* `SchemeBaseChange.coherentDerivedPushforward` and
  `SchemeBaseChange.boundedCoherentDerivedPushforward`: `f_*` on `D(Coh)` and
  on `Dᵇ(Coh)`.
* `SchemeBaseChange.hasCoherentPushforwardOfIsClosedImmersion`: closed
  immersions inhabit the contract.

## Main results

* `SchemeBaseChange.coherentDerivedPushforward_bounded`: `f_*` preserves
  bounded complexes.
* `SchemeBaseChange.boundedCoherentDerivedPushforwardCompInclusion` with the
  `CommShift` and `IsTriangulated` instances: the bounded restriction is a
  triangulated functor.

## Implementation notes

Identity and composition laws for `boundedCoherentDerivedPushforward` are not
stated.  They need `Modules.pushforwardId` and `Modules.pushforwardComp`
lifted through `Coh` and through `mapDerivedCategory`, which is the same
coherence work `GeometricDerivedPullbackIdentity` and
`GeometricDerivedPullbackComposition` record as pending for pullback; a
consumer needing the laws for pullback-of-stability composition is the right
place to add them.

The contract keeps the sheaf-level functor as data, as `HasCoherentPushforward`'s
mirror `HasCoherentPullback` does, although the comparison isomorphism
determines it up to isomorphism: an instance may then supply a functor
computed differently from the literal lift through `Coh.ι`, with only the
comparison to prove.  Additivity is derived from the comparison isomorphism
and faithfulness of `Coh.ι` rather than taken as a field.

## References

* arXiv:2607.28411v1, Definition 3.1, Remark 3.2, and Proposition 3.3.
* arXiv:2601.22994, Definition 3.1.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The geometric data needed to restrict module-sheaf pushforward to coherent
sheaves: an exact functor on coherent sheaves that forgets to module-sheaf
pushforward.  Exactness is the whole contract; it is what lets the derived
direct image be computed degreewise and preserve bounded objects.  Along a
proper morphism that is not affine, `f_*` is only left exact on coherent
sheaves and the derived direct image is not degreewise; such a morphism does
not inhabit this class, and Definition 3.1 of arXiv:2607.28411v1 in that
generality needs a right-derived functor the repository does not own. -/
class HasCoherentPushforward {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] where
  /-- Pushforward on coherent sheaves. -/
  sheafPushforward : Coh T.left ⥤ Coh U.left
  /-- Coherent pushforward preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits sheafPushforward
  /-- Coherent pushforward preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits sheafPushforward
  /-- After forgetting coherence, this is ordinary module-sheaf pushforward. -/
  comparison : sheafPushforward ⋙ Coh.ι U.left ≅ Coh.ι T.left ⋙ modulePushforward f

attribute [instance] HasCoherentPushforward.preservesFiniteLimits
  HasCoherentPushforward.preservesFiniteColimits

section Derived

variable {T U : SchemeBaseChange S} (f : T ⟶ U)
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [HasCoherentPushforward f]

/-- Coherent pushforward is additive.  Reflected through the faithful additive
inclusion `Coh.ι` from additivity of module-sheaf pushforward, using the
comparison isomorphism; `Functor.mapDerivedCategory` asks for additivity
separately from exactness, and this discharges it for every instance. -/
instance HasCoherentPushforward.sheafPushforward_additive :
    (HasCoherentPushforward.sheafPushforward f).Additive :=
  haveI : (HasCoherentPushforward.sheafPushforward f ⋙ Coh.ι U.left).Additive :=
    Functor.additive_of_iso (HasCoherentPushforward.comparison (f := f)).symm
  Functor.additive_of_comp_faithful _ (Coh.ι U.left)

/-- The direct image `f_*` on unbounded coherent derived categories: the
degreewise derived functor of the exact coherent pushforward. -/
def coherentDerivedPushforward :
    SchemeCoherentDerivedCategory T.left ⥤ SchemeCoherentDerivedCategory U.left :=
  (HasCoherentPushforward.sheafPushforward f).mapDerivedCategory

/-- Mathlib's `Functor.mapDerivedCategoryFactors` under the geometric name, so
a caller computing `f_*` on a complex rewrites here instead of unfolding
`coherentDerivedPushforward`. -/
def coherentDerivedPushforwardFactors :
    DerivedCategory.Q ⋙ coherentDerivedPushforward f ≅
      (HasCoherentPushforward.sheafPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (HasCoherentPushforward.sheafPushforward f).mapDerivedCategoryFactors

/-- The shift on the derived direct image is Mathlib's, supplied by name: after unfolding the
`def`, instance search would still not see through the wrapper (see
`.claude/references/instance-transparency.md`), and the triangulated instance below needs this
one to be Mathlib's term, not a re-derivation, to unify at all. -/
instance coherentDerivedPushforwardCommShift :
    (coherentDerivedPushforward f).CommShift ℤ := by
  dsimp [coherentDerivedPushforward]
  exact CategoryTheory.Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt
    (HasCoherentPushforward.sheafPushforward f)

instance coherentDerivedPushforward_isTriangulated :
    (coherentDerivedPushforward f).IsTriangulated := by
  dsimp [coherentDerivedPushforward]
  exact CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory
    (HasCoherentPushforward.sheafPushforward f)

/-- The derived direct image preserves canonical boundedness, because an exact
functor applied degreewise preserves strict complex bounds. -/
theorem coherentDerivedPushforward_bounded (E : SchemeCoherentDerivedCategory T.left)
    (hE : (DerivedCategory.TStructure.t (C := Coh T.left)).bounded E) :
    (DerivedCategory.TStructure.t (C := Coh U.left)).bounded
      ((coherentDerivedPushforward f).obj E) :=
  mapDerivedCategory_bounded _ E hE

/-- The direct image `f_* : Dᵇ(Coh X) ⥤ Dᵇ(Coh Y)` of Definition 3.1 of
arXiv:2607.28411v1, restricted from the unbounded direct image through
`coherentDerivedPushforward_bounded`. -/
def boundedCoherentDerivedPushforward :
    T.BoundedCoherentDerivedFiber ⥤ U.BoundedCoherentDerivedFiber :=
  (DerivedCategory.TStructure.t (C := Coh U.left)).bounded.lift
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedPushforward f)
    (fun E ↦ coherentDerivedPushforward_bounded f E.obj E.property)

instance boundedCoherentDerivedPushforward_additive :
    (boundedCoherentDerivedPushforward f).Additive := by
  dsimp [boundedCoherentDerivedPushforward]
  infer_instance

instance boundedCoherentDerivedPushforwardCommShift :
    (boundedCoherentDerivedPushforward f).CommShift ℤ := by
  dsimp [boundedCoherentDerivedPushforward]
  infer_instance

/-- The bounded lift forgets to the unbounded direct image.  This is the
isomorphism `isTriangulated_iff_comp_right` pivots on: the triangulated
structure on `Dᵇ(Coh)` is inherited through it rather than re-proved. -/
def boundedCoherentDerivedPushforwardCompInclusion :
    boundedCoherentDerivedPushforward f ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ coherentDerivedPushforward f :=
  (DerivedCategory.TStructure.t (C := Coh U.left)).bounded.liftCompιIso
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedPushforward f)
    (fun E ↦ coherentDerivedPushforward_bounded f E.obj E.property)

instance boundedCoherentDerivedPushforwardCompInclusion_commShift :
    NatTrans.CommShift (boundedCoherentDerivedPushforwardCompInclusion f).hom ℤ := by
  dsimp [boundedCoherentDerivedPushforwardCompInclusion]
  exact CategoryTheory.Functor.CommShift.ofComp_compatibility _ _

instance boundedCoherentDerivedPushforward_isTriangulated :
    (boundedCoherentDerivedPushforward f).IsTriangulated := by
  rw [CategoryTheory.Functor.isTriangulated_iff_comp_right
    (boundedCoherentDerivedPushforwardCompInclusion f)]
  infer_instance

end Derived

/-- Closed immersions into locally Noetherian schemes inhabit the contract:
`Coh.pushforward` is exact and lands in coherent sheaves, and its comparison
with module-sheaf pushforward is `Coh.pushforwardCompι`, an `Iso.refl`, so
nothing is transported.  This is the case Theorem 6.2 of arXiv:2607.28411v1
needs: it constructs stability conditions on a projective scheme `X` as the
pullbacks `ι^♯σ` along a closed embedding `ι : X ↪ Pⁿ` of stability
conditions `σ` on `Pⁿ`. -/
instance hasCoherentPushforwardOfIsClosedImmersion {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsClosedImmersion f.left] :
    HasCoherentPushforward f where
  sheafPushforward := Coh.pushforward f.left
  preservesFiniteLimits := inferInstance
  preservesFiniteColimits := inferInstance
  comparison := Coh.pushforwardCompι f.left

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
