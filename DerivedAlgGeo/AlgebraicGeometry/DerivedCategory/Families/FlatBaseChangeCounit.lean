/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FlatOverQuasiIso

/-!
# Derived base change of complexes flat over the base

Let `f : T ⟶ U` be a morphism of scheme base changes whose underlying morphism is the first
projection of a pullback square `T.left = U.left ×_B B'` along a flat `q : U.left ⟶ B`. For every
left-derived pullback `P` along `f`, the comparison `P.counit` from derived pullback to degreewise
pullback is an isomorphism at every strictly bounded-above complex whose terms are flat over `B`.
Degreewise pullback computes derived base change on such complexes.

## Main definitions

* `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.pullbackFstOver` — the projection
  `Y ×_T T' ⟶ Y` of a base change, as a morphism of scheme base changes over `T`.

## Main results

Both are in the namespace `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange`.

* `LeftDerivedPullback.isIso_counit_of_isFlatOver` — the counit of an arbitrary left-derived
  pullback along a flat base change is invertible at a strictly bounded-above complex with terms
  flat over the base.
* `LeftDerivedPullback.isIso_counit_of_flatOverBase` — the case of the chosen fibre product.

## Implementation notes

Every left-derived pullback along `f` is canonically isomorphic, compatibly with its counit, to
`arbitraryLeftDerivedPullback f` (`Functor.leftDerivedNatIso`), so the statement holds for one
inhabitant if and only if it holds for all of them. For the canonical K-flat inhabitant the
counit at `K` is degreewise pullback of the free-Yoneda augmentation `R K ⟶ K`, up to an
isomorphism. The resolution `R K` keeps the upper bound of `K`
(`isStrictlyLE_freeYonedaSheafCoproductTotalComplexFunctor_obj`) and its terms are flat over the
identity, hence over `B` because `q` is flat. Tor-independence for complexes flat over the base,
`Scheme.Modules.quasiIso_pullback_of_isPullback`, then shows the pulled-back augmentation is a
quasi-isomorphism.

Flatness of `q` enters only through the terms of the resolution. The upper bound is needed:
for unbounded complexes, termwise flatness does not give Tor-independence.

## References

* [Stacks, Tag 0DI5](https://stacks.math.columbia.edu/tag/0DI5), the base-change lemma for
  relatively perfect objects that this result serves.

## Tags

derived pullback, base change, flat morphism, Tor-independence
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/-- The first projection `Y ×_T T' ⟶ Y` of the base change of `q : Y ⟶ T` along `h : T' ⟶ T`,
as a morphism of scheme base changes over `T`. Derived base change along `h` is a left-derived
pullback along this morphism. -/
def pullbackFstOver {Y T T' : Scheme.{u}} (q : Y ⟶ T) (h : T' ⟶ T) :
    (Over.mk (Limits.pullback.fst q h ≫ q) : SchemeBaseChange T) ⟶ Over.mk q :=
  Over.homMk (Limits.pullback.fst q h)

@[simp]
theorem pullbackFstOver_left {Y T T' : Scheme.{u}} (q : Y ⟶ T) (h : T' ⟶ T) :
    (pullbackFstOver q h).left = Limits.pullback.fst q h :=
  rfl

variable {S : Scheme.{u}} {T U : SchemeBaseChange S} {f : T ⟶ U}

namespace LeftDerivedPullback

/-- **Derived base change of complexes flat over the base.** Let `f : T ⟶ U` have underlying
morphism the first projection of a pullback square along a flat `q : U.left ⟶ B`. For every
left-derived pullback `P` along `f`, the counit is invertible at a strictly bounded-above complex
whose terms are flat over `B`: the derived pullback is computed by degreewise pullback.

Flatness of `q` cannot be dropped. Over a field `k`, let `B = Spec k[x]`,
`U.left = Spec k[x, y] ⧸ (xy)`, which is not flat over `B`, and `B' ⟶ B` the origin. The module
`k[x, y] ⧸ (xy, y)` is flat over `B`, but its derived pullback to the fibre over the origin has
`Tor₂ⱼ = k` for every `j ≥ 1`, coming from the periodic resolution `⋯ → A --x--> A --y--> A` over
`A = k[x, y] ⧸ (xy)`, while its degreewise pullback is a single module. -/
theorem isIso_counit_of_isFlatOver (P : LeftDerivedPullback f) {B B' : Scheme.{u}}
    {q : U.left ⟶ B} {q' : T.left ⟶ B'} {h : B' ⟶ B} (H : IsPullback f.left q' q h) [Flat q]
    (K : CochainComplex U.left.Modules ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i, Scheme.Modules.IsFlatOver q (K.X i)) :
    IsIso (P.counit.app K) := by
  let W := HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)
  let A := arbitraryLeftDerivedPullback f
  let R := freeYonedaSchemeKFlatResolution U.left
  have hq : QuasiIso ((complexPullback f).map (R.comparison.app K)) := by
    have : (R.resolution.obj K).IsStrictlyLE b :=
      Scheme.Modules.isStrictlyLE_freeYonedaSheafCoproductTotalComplexFunctor_obj U.left K b
    have : ((𝟭 (CochainComplex U.left.Modules ℤ)).obj K).IsStrictlyLE b :=
      inferInstanceAs (K.IsStrictlyLE b)
    exact Scheme.Modules.quasiIso_pullback_of_isPullback H (R.comparison.app K) b b
      (R.comparison_quasiIso K) (fun i ↦ Scheme.Modules.IsFlatOver.of_isFlatOver_id
        (Scheme.Modules.freeYonedaSheafCoproductTotalComplexFunctor_obj_X_isFlatOverId
          U.left K i)) hK
  have hA : IsIso (A.counit.app K) := by
    have : IsIso ((SchemeDerivedCategory.Q T.left).map
        ((complexPullback f).map (R.comparison.app K))) :=
      Localization.inverts _ (HomologicalComplex.quasiIso _ _) _
        ((HomologicalComplex.mem_quasiIso_iff _).2 hq)
    change IsIso
      ((kFlatPullbackAcyclicResolution R f (kFlatPullbackAcyclic R f)).derivedFactors.hom.app K ≫
      (SchemeDerivedCategory.Q T.left).map ((complexPullback f).map (R.comparison.app K)))
    exact IsIso.comp_isIso' inferInstance this
  let θ := Functor.leftDerivedNatIso A.functor P.functor A.counit P.counit W (Iso.refl _)
  have hfac : θ.hom.app ((SchemeDerivedCategory.Q U.left).obj K) ≫ P.counit.app K =
      A.counit.app K := by
    have := Functor.leftDerivedNatTrans_app A.functor P.functor A.counit P.counit W (𝟙 _) K
    rwa [NatTrans.id_app, Category.comp_id] at this
  have : P.counit.app K = θ.inv.app _ ≫ A.counit.app K := by
    rw [← hfac, ← Category.assoc, ← NatTrans.comp_app, θ.inv_hom_id, NatTrans.id_app,
      Category.id_comp]
  rw [this]
  infer_instance

/-- **Derived base change of complexes flat over the base**, for the chosen fibre product: for
a flat `q : Y ⟶ T`, every `h : T' ⟶ T` and every left-derived pullback `P` along
`pullbackFstOver q h`, the counit is invertible at a strictly bounded-above complex whose terms
are flat over `T`. -/
theorem isIso_counit_of_flatOverBase {Y T' B : Scheme.{u}} (q : Y ⟶ B) (h : T' ⟶ B) [Flat q]
    (P : LeftDerivedPullback (pullbackFstOver q h)) (K : CochainComplex Y.Modules ℤ) (b : ℤ)
    [K.IsStrictlyLE b] (hK : ∀ i, Scheme.Modules.IsFlatOver q (K.X i)) :
    IsIso (P.counit.app K) :=
  P.isIso_counit_of_isFlatOver (IsPullback.of_hasPullback q h) K b hK

end LeftDerivedPullback

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
