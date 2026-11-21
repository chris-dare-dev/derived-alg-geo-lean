/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KInjective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.OpenImmersionPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.RightDerivedPushforward
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.ExtensionByZero

/-!
# The total direct image along any morphism

For a morphism `f : T ⟶ U` of scheme base changes, module-sheaf pushforward
`modulePushforward f : T.left.Modules ⥤ U.left.Modules` is only left exact. The category
`T.left.Modules` is Grothendieck abelian, so every complex has a K-injective resolution
(Stacks, Theorem 19.12.6, Tag 079P), and `kInjectiveDerivedFunctor` derives pushforward on the
unbounded derived categories. This is the total direct image `Rf_*` of Stacks, Section 20.28
(Tag 079V). It inhabits `RightDerivedPushforward f` for every `f`, with no supplied data: the
interface keeps its right-derived universal property, so the inhabitant is the derived functor.

Restriction to an open preserves K-injective complexes (Stacks, Tag 08BS), and `Rf_*` commutes
with restriction to an open of the target (Stacks, Tag 08FE).

## Main definitions

* `SchemeBaseChange.RightDerivedPushforward.ofKInjective`: the total direct image `Rf_*`.
* `SchemeBaseChange.modulePushforwardCompPullbackIso`: for a pullback square whose right edge
  `j` is an open immersion, `j^* ∘ f_* ≅ f'_* ∘ j'^*` on module sheaves.
* `SchemeBaseChange.RightDerivedPushforward.ofKInjectiveRestrictIso`: the same square
  commutes after deriving, `j^* ∘ Rf_* ≅ Rf'_* ∘ j'^*` (Stacks, Tag 08FE).

## Main results

* Instances: `Rf_*` commutes with shifts, is triangulated, and its unit is an isomorphism at
  every K-injective complex.
* An `example`: for a closed immersion, `Rf_*` agrees with the degreewise derived pushforward,
  through the existing uniqueness `RightDerivedPushforward.exactComparison`.
* `SchemeBaseChange.isKInjective_restrict`: restriction along an open immersion preserves
  K-injective complexes (Stacks, Tag 08BS).
* `SchemeBaseChange.isOpenImmersion_left_of_isPullback`: the base change of an open immersion
  of scheme base changes is one.

## Implementation notes

Tag 08BS is the K-injective preservation of Stacks, Tag 08BJ
(`isKInjective_mapHomologicalComplex_of_adjunction`) applied to the exact left adjoint
`Scheme.Modules.extendByZero` of restriction. Restriction in the derived API is module pullback,
so the result is transported along `Scheme.Modules.restrictFunctorIsoPullback`.

On module sheaves, the base change of restriction along pushforward is
`Scheme.Modules.pushforwardRestrictBaseChangeNatIso`, stated for the chosen pullback. An
arbitrary pullback square is compared with the chosen one through `IsPullback.isoPullback`;
pushforward along that isomorphism of schemes is an equivalence, so the unit of
`pullback ⊣ pushforward` along it is invertible.

Tag 08FE then follows from the universal property. `Rf_* ⋙ j^*` is a right derived functor of
`f_* ⋙ j^*`, because `kInjectiveDerivedFunctor` stays one after post-composition. Its
universal property gives a comparison to `j'^* ⋙ Rf'_*`. That comparison is invertible at every
K-injective complex `I`: both units are, the second because `j'^* I` is K-injective by 08BS.
Every object of the derived category is isomorphic to such an `I`.

The statement of 08FE takes the square in `SchemeBaseChange S` and needs only `j` to be an
open immersion; the open immersion `j'` and the exactness of its pullback are derived from the
square. For a general flat `j` this would be flat base change, which needs more hypotheses on
`f`.

## References

* [The Stacks project, Section 20.28](https://stacks.math.columbia.edu/tag/079V)
* [The Stacks project, Section 20.32](https://stacks.math.columbia.edu/tag/0D5U), Lemmas 20.32.1
  (Tag 08BS) and 20.32.4 (Tag 08FE)

## Tags

total direct image, right derived functor, K-injective complex, restriction, open immersion
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

namespace RightDerivedPushforward

/-- **The total direct image** `Rf_*` (Stacks, Section 20.28, Tag 079V): the right derived
functor of module-sheaf pushforward along `f`, computed by applying pushforward to a K-injective
resolution. Its universal property is the field `isRightDerived`. -/
@[stacks 079V]
def ofKInjective (f : T ⟶ U) : RightDerivedPushforward f where
  functor := kInjectiveDerivedFunctor (modulePushforward f)
  unit := kInjectiveDerivedFunctorComplexUnit (modulePushforward f)
  isRightDerived := inferInstance

/-- The total direct image commutes with shifts. -/
instance (f : T ⟶ U) : (ofKInjective f).functor.CommShift ℤ :=
  kInjectiveDerivedFunctorCommShift (modulePushforward f)

/-- The total direct image is a triangulated functor. -/
instance (f : T ⟶ U) : (ofKInjective f).functor.IsTriangulated :=
  kInjectiveDerivedFunctor_isTriangulated (modulePushforward f)

/-- K-injective complexes compute the total direct image: its unit is an isomorphism at a
K-injective complex. -/
instance (f : T ⟶ U) (K : CochainComplex T.left.Modules ℤ) [K.IsKInjective] :
    IsIso ((ofKInjective f).unit.app K) :=
  isIso_kInjectiveDerivedFunctorComplexUnit_app (modulePushforward f) K

/-- Along a closed immersion, pushforward is exact, and the total direct image agrees with the
degreewise derived pushforward through the uniqueness of right derived functors. -/
example (f : T ⟶ U) [IsClosedImmersion f.left] :
    (ofKInjective f).functor ≅ derivedPushforward f :=
  (ofKInjective f).exactComparison

end RightDerivedPushforward

/-- **Stacks, Lemma 20.32.1 (Tag 08BS)**: restriction along an open immersion carries
K-injective complexes to K-injective complexes. Restriction has the exact left adjoint
`Scheme.Modules.extendByZero`. -/
@[stacks 08BS]
theorem isKInjective_restrict {V W : SchemeBaseChange S} (j : V ⟶ W) [IsOpenImmersion j.left]
    (I : CochainComplex W.left.Modules ℤ) [I.IsKInjective] :
    ((complexPullback j).obj I).IsKInjective := by
  have : (Scheme.Modules.extendByZero j.left).IsLeftAdjoint :=
    (Scheme.Modules.extendByZeroAdjunction j.left).isLeftAdjoint
  have := isKInjective_mapHomologicalComplex_of_adjunction
    (Scheme.Modules.extendByZeroAdjunction j.left) I
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback j.left)
      (ComplexShape.up ℤ)).app I)

variable {T' U' : SchemeBaseChange S} {f : T ⟶ U} {f' : T' ⟶ U'} {j : U' ⟶ U} {j' : T' ⟶ T}

/-- In a pullback square of scheme base changes, the base change `j'` of an open immersion `j`
is an open immersion. -/
theorem isOpenImmersion_left_of_isPullback (sq : IsPullback f' j' j f)
    [IsOpenImmersion j.left] : IsOpenImmersion j'.left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq.map (Over.forget S))
    ‹IsOpenImmersion j.left›

/-- For a pullback square of scheme base changes whose right edge `j` is an open immersion,
pushforward along `f` followed by restriction along `j` is restriction along `j'` followed by
pushforward along `f'`. It is `Scheme.Modules.pushforwardRestrictBaseChangeNatIso`, transported
from the chosen pullback to the given square. -/
def modulePushforwardCompPullbackIso (sq : IsPullback f' j' j f) [IsOpenImmersion j.left] :
    modulePushforward f ⋙ modulePullback j ≅ modulePullback j' ⋙ modulePushforward f' := by
  have sq' : IsPullback j'.left f'.left f.left j.left := (sq.map (Over.forget S)).flip
  let e := sq'.isoPullback
  have : (Scheme.Modules.pushforward e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.hom)
      (Scheme.Modules.pushforward e.inv)
      ((Scheme.Modules.pushforwardId _).symm ≪≫
        Scheme.Modules.pushforwardCongr e.hom_inv_id.symm ≪≫
        (Scheme.Modules.pushforwardComp e.hom e.inv).symm)
      (Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
        Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫
        Scheme.Modules.pushforwardId _)).isEquivalence_functor
  exact Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback j.left).symm ≪≫
    Scheme.Modules.pushforwardRestrictBaseChangeNatIso j.left f.left ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback _) _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pullbackComp e.hom _) _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.pushforwardComp e.hom _) ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pullbackCongr sq'.isoPullback_hom_fst) _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.pushforwardCongr sq'.isoPullback_hom_snd)

namespace RightDerivedPushforward

/-- **Stacks, Lemma 20.32.4 (Tag 08FE)**: the total direct image commutes with restriction to
an open of the target. For a pullback square of scheme base changes whose right edge `j` is an
open immersion, `j^* ∘ Rf_* ≅ Rf'_* ∘ j'^*`.

Stacks states it for an open `V` of the target and `f⁻¹ V`; any pullback square of an open
immersion is isomorphic to that one. The open immersion `j'` is
`isOpenImmersion_left_of_isPullback`, which makes its derived pullback exact. -/
@[stacks 08FE]
def ofKInjectiveRestrictIso (sq : IsPullback f' j' j f) [IsOpenImmersion j.left] :
    haveI := isOpenImmersion_left_of_isPullback sq
    (ofKInjective f).functor ⋙ derivedPullback j ≅
      derivedPullback j' ⋙ (ofKInjective f').functor := by
  have := isOpenImmersion_left_of_isPullback sq
  let W := HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ)
  let RF := kInjectiveDerivedFunctor (modulePushforward f)
  let RF' := kInjectiveDerivedFunctor (modulePushforward f')
  let α : (complexPushforward f ⋙ SchemeDerivedCategory.Q U.left) ⋙ derivedPullback j ⟶
      SchemeDerivedCategory.Q T.left ⋙ RF ⋙ derivedPullback j :=
    Functor.whiskerRight (kInjectiveDerivedFunctorComplexUnit (modulePushforward f))
      (derivedPullback j) ≫ (Functor.associator _ _ _).hom
  let eC : complexPushforward f ⋙ complexPullback j ≅
      complexPullback j' ⋙ complexPushforward f' :=
    Functor.mapHomologicalComplexCompIso (modulePushforwardCompPullbackIso sq) _ ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm
  let e₁ : (complexPushforward f ⋙ SchemeDerivedCategory.Q U.left) ⋙ derivedPullback j ≅
      complexPullback j' ⋙ complexPushforward f' ⋙ SchemeDerivedCategory.Q U'.left :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (derivedPullbackFactors j) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eC _ ≪≫
      Functor.associator _ _ _
  let e₂ : complexPullback j' ⋙ SchemeDerivedCategory.Q T'.left ⋙ RF' ≅
      SchemeDerivedCategory.Q T.left ⋙ derivedPullback j' ⋙ RF' :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedPullbackFactors j').symm _ ≪≫ Functor.associator _ _ _
  let β := e₁.hom ≫ Functor.whiskerLeft (complexPullback j')
    (kInjectiveDerivedFunctorComplexUnit (modulePushforward f')) ≫ e₂.hom
  let τ := (RF ⋙ derivedPullback j).rightDerivedDesc α W (derivedPullback j' ⋙ RF') β
  have hτ (I : CochainComplex T.left.Modules ℤ) [I.IsKInjective] :
      IsIso (τ.app ((SchemeDerivedCategory.Q T.left).obj I)) := by
    have h := Functor.rightDerived_fac_app (RF ⋙ derivedPullback j) α W
      (derivedPullback j' ⋙ RF') β I
    have : ((complexPullback j').obj I).IsKInjective := isKInjective_restrict j' I
    have : IsIso (α.app I) := by
      simp only [α, NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
      infer_instance
    have : IsIso (β.app I) := by
      simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app]
      infer_instance
    rw [← h] at this
    exact IsIso.of_isIso_comp_left (α.app I) _
  have (E : T.DerivedFiber) : IsIso (τ.app E) := by
    obtain ⟨L, _, g, _⟩ := Cdg.HasKInjectiveResolutions.exists_kInjective_quasiIso
      ((SchemeDerivedCategory.Q T.left).objPreimage E)
    rw [NatTrans.isIso_app_iff_of_iso τ
      (((SchemeDerivedCategory.Q T.left).objObjPreimageIso E).symm ≪≫
        asIso ((SchemeDerivedCategory.Q T.left).map g))]
    exact hτ L
  exact @asIso _ _ _ _ τ (NatIso.isIso_of_isIso_app τ)

end RightDerivedPushforward

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
