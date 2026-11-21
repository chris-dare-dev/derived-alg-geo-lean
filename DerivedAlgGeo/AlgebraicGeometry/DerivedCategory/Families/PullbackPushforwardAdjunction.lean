/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Adjunction.Mates
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPullbackCoherence
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullbackResolution
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KInjectivePushforward

/-!
# Derived pullback is left adjoint to the total direct image

For a morphism `f : T ⟶ U` of scheme base changes, a pullback-acyclic resolution `R` of `f`
constructs the derived pullback `Lf^* = R.derivedFunctor`, and
`RightDerivedPushforward.ofKInjective f` is the total direct image `Rf_*`. This file proves
`Lf^* ⊣ Rf_*` (Stacks, Tag 079W) and derives two consequences: total direct images compose
(Stacks, Tag 0D5T), and a square of scheme base changes, given a comparison of its derived
pullbacks, has a base-change morphism `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` (Stacks, Tag 08HY),
compatible with pasting squares (Stacks, Tags 0ATL and 0ATM).

## Main definitions

* `SchemeBaseChange.PullbackAcyclicResolution.derivedAdjunction`: `Lf^* ⊣ Rf_*`.
* `SchemeBaseChange.LeftDerivedPullback.derivedAdjunction`: the same adjunction for any
  left-derived pullback, once some pullback-acyclic resolution of `f` exists.
* `SchemeBaseChange.RightDerivedPushforward.ofKInjectiveComp`: `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`,
  from a compositor `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`.
* `SchemeBaseChange.baseChangeMorphism`: the base-change morphism of a square, the mate of a
  comparison of derived pullbacks under the two adjunctions.

## Main results

* `SchemeBaseChange.PullbackAcyclicResolution.isLeftDerived_comp`: resolution-derived pullback
  stays left-derived after post-composition with any functor.
* `SchemeBaseChange.PullbackAcyclicResolution.derivedAdjunction_unit_fac_app` and
  `derivedAdjunction_counit_fac_app`: the unit and counit of `Lf^* ⊣ Rf_*` are induced by those of
  `f^* ⊣ f_*` on complexes.
* `SchemeBaseChange.baseChangeMorphism_counit`: the base-change morphism is adjoint to the
  composite `Lf'^* Lg^* Rf_* ⟶ Lg'^* Lf^* Rf_* ⟶ Lg'^*` of Stacks, Remark 20.28.3.
* `SchemeBaseChange.baseChangeMorphism_hcomp` (Stacks, Tag 0ATL) and
  `SchemeBaseChange.baseChangeMorphism_vcomp` (Stacks, Tag 0ATM): base-change morphisms
  compose when squares are pasted along a pullback edge, respectively along a pushforward edge.

## Implementation notes

The adjunction is Mathlib's `Adjunction.derived` applied to `f^* ⊣ f_*` on cochain complexes.
It needs both derived functors to be absolute. For `Rf_*` this is
`kInjectiveDerivedFunctor_comp_isRightDerivedFunctor_complexUnit`. For `Lf^*` it is
`isLeftDerived_comp`: a functor out of a localization is left-derived as soon as its
comparison is invertible on a functorial resolution, and that criterion survives
post-composition.

The pullback comparisons are data. Composition takes a compositor
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, and the base-change morphism a comparison
`Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*`. For exact pullbacks they come from
`SchemeBaseChange.derivedPullbackComp`; for arbitrary morphisms they await the K-flat
pullback theory. The commutativity of the square enters only through this comparison, so the
base-change morphism takes no proof of it. Being an isomorphism needs a cartesian square and
more, and is not proved here.

## References

* [The Stacks project, Section 20.28](https://stacks.math.columbia.edu/tag/079V)
* G. Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés, revisité*,
  C. R. Math. Acad. Sci. Paris 344 (2007)

## Tags

derived pullback, total direct image, adjunction, base change, mate
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

section General

/-- A functor out of a localization is a left derived functor as soon as its comparison is
invertible on a functorial resolution: a transformation `c : ρ ⟶ 𝟭 C` whose components lie in
`W`. -/
private lemma isLeftDerivedFunctor_of_resolution {C D E : Type*} [Category* C] [Category* D]
    [Category* E] {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W] {ρ : C ⥤ C}
    (c : ρ ⟶ 𝟭 C) (hc : ∀ K, W (c.app K)) {F : C ⥤ E} {F' : D ⥤ E} (α : L ⋙ F' ⟶ F)
    (hα : ∀ K, IsIso (α.app (ρ.obj K))) : F'.IsLeftDerivedFunctor α W := by
  have hL (K : C) : IsIso (L.map (c.app K)) := Localization.inverts L W _ (hc K)
  have hρα : IsIso (Functor.whiskerLeft ρ α) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hα
  let eL : ρ ⋙ L ≅ L := NatIso.ofComponents (fun K ↦ asIso (L.map (c.app K)))
    (fun g ↦ by simp)
  have uniq (G : D ⥤ E) (γ₁ γ₂ : G ⟶ F')
      (h : Functor.whiskerLeft L γ₁ ≫ α = Functor.whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ := by
    apply Localization.natTrans_ext L W
    intro K
    have := hL K
    have n₁ := γ₁.naturality (L.map (c.app K))
    have n₂ := γ₂.naturality (L.map (c.app K))
    dsimp at n₁ n₂
    rw [← cancel_epi (G.map (L.map (c.app K))), n₁, n₂, cancel_mono,
      ← cancel_mono (α.app (ρ.obj K))]
    exact congr_app h (ρ.obj K)
  have := Localization.full_whiskeringLeft L W E
  -- The lift is determined on the image of `L`, through the resolution.
  let γ₀ (G : D ⥤ E) (β : L ⋙ G ⟶ F) : L ⋙ G ⟶ L ⋙ F' :=
    (Functor.isoWhiskerRight eL G).inv ≫ (Functor.associator ρ L G).hom ≫
      Functor.whiskerLeft ρ β ≫ inv (Functor.whiskerLeft ρ α) ≫
      (Functor.associator ρ L F').inv ≫ (Functor.isoWhiskerRight eL F').hom
  have fac (G : D ⥤ E) (β : L ⋙ G ⟶ F) :
      Functor.whiskerLeft L (((Functor.whiskeringLeft _ _ E).obj L).preimage (γ₀ G β)) ≫ α =
        β := by
    ext K
    have h₁ := α.naturality (c.app K)
    have h₂ := β.naturality (c.app K)
    have h₃ := NatTrans.congr_app (((Functor.whiskeringLeft _ _ E).obj L).map_preimage
      (γ₀ G β)) K
    have := hL K
    dsimp at h₁ h₂ h₃ ⊢
    rw [h₃]
    simp only [γ₀, eL, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Category.id_comp,
      Category.assoc, NatIso.isIso_inv_app, NatIso.ofComponents_inv_app,
      NatIso.ofComponents_hom_app, asIso_inv, asIso_hom, Functor.map_inv]
    rw [h₁, IsIso.inv_hom_id_assoc, ← h₂, IsIso.inv_hom_id_assoc]
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  exact ⟨⟨IsTerminal.ofUniqueHom (fun G ↦ CostructuredArrow.homMk _ (fac G.left G.hom))
    (fun G m ↦ CostructuredArrow.hom_ext _ _
      (uniq _ _ _ ((CostructuredArrow.w m).trans (fac G.left G.hom).symm)))⟩⟩

end General

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U V : SchemeBaseChange S}

/-- The total direct image stays a right derived functor after post-composition with any
functor, in the form `Adjunction.derived` consumes. -/
private theorem ofKInjective_comp_isRightDerived (f : T ⟶ U) {E : Type*} [Category* E]
    (H : U.DerivedFiber ⥤ E) :
    ((RightDerivedPushforward.ofKInjective f).functor ⋙ H).IsRightDerivedFunctor
      (Functor.whiskerRight (RightDerivedPushforward.ofKInjective f).unit H ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ)) :=
  kInjectiveDerivedFunctor_comp_isRightDerivedFunctor_complexUnit (modulePushforward f) H

namespace PullbackAcyclicResolution

variable {f : T ⟶ U}

/-- **Absoluteness of resolution-derived pullback.** The functor `R.derivedFunctor` stays a left
derived functor of degreewise pullback after post-composition with any functor `H`: its
comparison is invertible on resolved complexes, and that property survives
post-composition. This is the hypothesis shape of `Adjunction.derived`. -/
theorem isLeftDerived_comp (R : PullbackAcyclicResolution f) {E : Type*} [Category* E]
    (H : T.DerivedFiber ⥤ E) :
    (R.derivedFunctor ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight R.counit H)
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_of_resolution _ R.comparison R.comparison_quasiIso _ fun K ↦ by
    simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Category.id_comp]
    infer_instance

/-- **Stacks, Lemma 20.28.1 (Tag 079W)**: derived pullback is left adjoint to the total direct
image, `Lf^* ⊣ Rf_*`. It is Mathlib's `Adjunction.derived` applied to `f^* ⊣ f_*` on cochain
complexes; both derived functors are absolute. -/
@[stacks 079W]
def derivedAdjunction (R : PullbackAcyclicResolution f) :
    R.derivedFunctor ⊣ (RightDerivedPushforward.ofKInjective f).functor :=
  haveI := R.isLeftDerived
  haveI := R.isLeftDerived_comp (RightDerivedPushforward.ofKInjective f).functor
  haveI := ofKInjective_comp_isRightDerived f R.derivedFunctor
  ((Scheme.Modules.pullbackPushforwardAdjunction f.left).mapHomologicalComplex
    (ComplexShape.up ℤ)).derived
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    R.counit (RightDerivedPushforward.ofKInjective f).unit

/-- The unit of `Lf^* ⊣ Rf_*` is induced by the unit of `f^* ⊣ f_*` on complexes. -/
@[reassoc]
lemma derivedAdjunction_unit_fac_app (R : PullbackAcyclicResolution f)
    (K : CochainComplex U.left.Modules ℤ) :
    R.derivedAdjunction.unit.app ((SchemeDerivedCategory.Q U.left).obj K) ≫
        (RightDerivedPushforward.ofKInjective f).functor.map (R.counit.app K) =
      (SchemeDerivedCategory.Q U.left).map
          (((Scheme.Modules.pullbackPushforwardAdjunction f.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K) ≫
        (RightDerivedPushforward.ofKInjective f).unit.app ((complexPullback f).obj K) := by
  haveI := R.isLeftDerived_comp (RightDerivedPushforward.ofKInjective f).functor
  exact Adjunction.derivedη_fac_app _
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)) _ _ K

/-- The counit of `Lf^* ⊣ Rf_*` is induced by the counit of `f^* ⊣ f_*` on complexes. -/
@[reassoc]
lemma derivedAdjunction_counit_fac_app (R : PullbackAcyclicResolution f)
    (K : CochainComplex T.left.Modules ℤ) :
    R.derivedFunctor.map ((RightDerivedPushforward.ofKInjective f).unit.app K) ≫
        R.derivedAdjunction.counit.app ((SchemeDerivedCategory.Q T.left).obj K) =
      R.counit.app ((complexPushforward f).obj K) ≫
        (SchemeDerivedCategory.Q T.left).map
          (((Scheme.Modules.pullbackPushforwardAdjunction f.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).counit.app K) := by
  haveI := ofKInjective_comp_isRightDerived f R.derivedFunctor
  exact Adjunction.derivedε_fac_app _
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ)) _ _ K

/-- Along a flat morphism, the identity resolution gives `Lf^* ⊣ Rf_*`. -/
example (f : T ⟶ U) [Flat f.left] :
    (ofFlat f).derivedFunctor ⊣ (RightDerivedPushforward.ofKInjective f).functor :=
  (ofFlat f).derivedAdjunction

/-- When pullback is exact, the degreewise derived pullback is left adjoint to `Rf_*`. -/
example (f : T ⟶ U) [IsExactPullback f] :
    derivedPullback f ⊣ (RightDerivedPushforward.ofKInjective f).functor :=
  (ofExact f).derivedAdjunction.ofNatIsoLeft (exactComparison f)

end PullbackAcyclicResolution

namespace LeftDerivedPullback

variable {f : T ⟶ U}

/-- Every left-derived pullback is left adjoint to the total direct image, once some
pullback-acyclic resolution `R` of `f` exists: by uniqueness of left derived functors,
`P.functor` is isomorphic to `R.derivedFunctor`. -/
def derivedAdjunction (P : LeftDerivedPullback f) (R : PullbackAcyclicResolution f) :
    P.functor ⊣ (RightDerivedPushforward.ofKInjective f).functor :=
  haveI := R.isLeftDerived
  R.derivedAdjunction.ofNatIsoLeft
    (Functor.leftDerivedUnique P.functor R.derivedFunctor R.counit P.counit
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)))

end LeftDerivedPullback

namespace RightDerivedPushforward

/-- **Stacks, Lemma 20.28.2 (Tag 0D5T)**: total direct images compose,
`R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`. Both sides are right adjoint to `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`.

The compositor `e` is the only non-formal input. It is data, a comparison of two derived
pullbacks, not an assertion that total direct images compose. For exact pullbacks it is
`SchemeBaseChange.derivedPullbackComp`; for arbitrary morphisms it is still to be supplied
by the K-flat pullback theory. -/
@[stacks 0D5T]
def ofKInjectiveComp {f : T ⟶ U} {g : U ⟶ V}
    (Rf : PullbackAcyclicResolution f) (Rg : PullbackAcyclicResolution g)
    (Rfg : PullbackAcyclicResolution (f ≫ g))
    (e : Rfg.derivedFunctor ≅ Rg.derivedFunctor ⋙ Rf.derivedFunctor) :
    (ofKInjective (f ≫ g)).functor ≅ (ofKInjective f).functor ⋙ (ofKInjective g).functor :=
  conjugateIsoEquiv Rfg.derivedAdjunction (Rg.derivedAdjunction.comp Rf.derivedAdjunction)
    e.symm

/-- For flat morphisms, the compositor of exact derived pullbacks makes total direct images
compose. -/
example (f : T ⟶ U) (g : U ⟶ V) [Flat f.left] [Flat g.left] :
    (ofKInjective (f ≫ g)).functor ≅ (ofKInjective f).functor ⋙ (ofKInjective g).functor :=
  ofKInjectiveComp (.ofExact f) (.ofExact g) (.ofExact (f ≫ g))
    (PullbackAcyclicResolution.exactComparison (f ≫ g) ≪≫ (derivedPullbackComp f g).symm ≪≫
      Functor.isoWhiskerRight (PullbackAcyclicResolution.exactComparison g).symm _ ≪≫
      Functor.isoWhiskerLeft _ (PullbackAcyclicResolution.exactComparison f).symm)

end RightDerivedPushforward

open RightDerivedPushforward

section BaseChange

/-- Whiskering a square at the top whiskers its mate on the right. -/
private lemma mateEquiv_whiskerTop {C D E F : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] {G G' : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F}
    {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (α : G ⟶ G') :
    mateEquiv adj₁ adj₂ (w.whiskerTop α) = (mateEquiv adj₁ adj₂ w).whiskerRight α := by
  ext d
  simp [mateEquiv_apply]

/-- Whiskering a square at the bottom whiskers its mate on the left. -/
private lemma mateEquiv_whiskerBottom {C D E F : Type*} [Category* C] [Category* D]
    [Category* E] [Category* F] {G : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (w : TwoSquare G L₁ L₂ H)
    (β : H ⟶ H') :
    mateEquiv adj₁ adj₂ (w.whiskerBottom β) = (mateEquiv adj₁ adj₂ w).whiskerLeft β := by
  ext d
  simp [mateEquiv_apply]

/-- The mate of the horizontal identity square is the vertical identity square. -/
private lemma mateEquiv_hId {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) : mateEquiv adj adj (TwoSquare.hId L) = TwoSquare.vId R := by
  ext d
  simp [mateEquiv_apply]

variable {X X' Y Y' : SchemeBaseChange S} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  {g' : X' ⟶ X}

/-- **Stacks, Remark 20.28.3 (Tag 08HY)**: the base-change morphism
`Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a square with vertical edges `f`, `f'` and horizontal edges
`g`, `g'`, as the mate of the pullback comparison `e : Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` under
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`.

For a commutative square `f' ≫ g = g' ≫ f`, the comparison `e` is the one the square induces
(for exact pullbacks, from `SchemeBaseChange.derivedPullbackComp`). The construction uses only
`e`, so it takes no proof of commutativity. It does not assert that the morphism is an
isomorphism. -/
@[stacks 08HY]
def baseChangeMorphism
    (Rf : PullbackAcyclicResolution f) (Rf' : PullbackAcyclicResolution f')
    (Rg : PullbackAcyclicResolution g) (Rg' : PullbackAcyclicResolution g')
    (e : Rg.derivedFunctor ⋙ Rf'.derivedFunctor ⟶ Rf.derivedFunctor ⋙ Rg'.derivedFunctor) :
    (ofKInjective f).functor ⋙ Rg.derivedFunctor ⟶
      Rg'.derivedFunctor ⋙ (ofKInjective f').functor :=
  mateEquiv Rf.derivedAdjunction Rf'.derivedAdjunction e

/-- The base-change morphism is adjoint to `Lf'^* Lg^* Rf_* ⟶ Lg'^* Lf^* Rf_* ⟶ Lg'^*`, the
comparison `e` followed by `Lg'^*` of the counit of `Lf^* ⊣ Rf_*` (Stacks, Remark 20.28.3). -/
@[reassoc]
lemma baseChangeMorphism_counit
    (Rf : PullbackAcyclicResolution f) (Rf' : PullbackAcyclicResolution f')
    (Rg : PullbackAcyclicResolution g) (Rg' : PullbackAcyclicResolution g')
    (e : Rg.derivedFunctor ⋙ Rf'.derivedFunctor ⟶ Rf.derivedFunctor ⋙ Rg'.derivedFunctor)
    (K : X.DerivedFiber) :
    Rf'.derivedFunctor.map ((baseChangeMorphism Rf Rf' Rg Rg' e).app K) ≫
        Rf'.derivedAdjunction.counit.app _ =
      e.app _ ≫ Rg'.derivedFunctor.map (Rf.derivedAdjunction.counit.app K) :=
  mateEquiv_counit _ _ e K

/-- A check of the orientation: on the identity square, with the identity comparison of
derived pullbacks, the base-change morphism is an isomorphism. -/
example (Rf : PullbackAcyclicResolution f) :
    let iY := PullbackAcyclicResolution.exactComparison (𝟙 Y) ≪≫ derivedPullbackId Y
    let iX := PullbackAcyclicResolution.exactComparison (𝟙 X) ≪≫ derivedPullbackId X
    IsIso (baseChangeMorphism Rf Rf (.ofExact (𝟙 Y)) (.ofExact (𝟙 X))
      (TwoSquare.whiskerBottom (TwoSquare.whiskerTop (TwoSquare.hId _) iY.hom) iX.inv)) := by
  intro iY iX
  rw [baseChangeMorphism, mateEquiv_whiskerBottom, mateEquiv_whiskerTop, mateEquiv_hId]
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vId]
  infer_instance

/-- **Stacks, Remark 20.28.4 (Tag 0ATL)**: base-change morphisms compose when two squares are
pasted along a pullback edge `l`. The top square has vertical edges `f`, `f'` and horizontal
edges `l`, `k`; the bottom square has vertical edges `g`, `g'` and horizontal edges `m`, `l`.
With the compositors `c` and `c'` of the composite vertical edges, the base-change morphism of
the outer rectangle is

`Lm^* R(f ≫ g)_* ≅ Lm^* Rg_* Rf_* ⟶ Rg'_* Ll^* Rf_* ⟶ Rg'_* Rf'_* Lk^* ≅ R(f' ≫ g')_* Lk^*`,

where the outer rectangle uses the pasted pullback comparison. -/
@[stacks 0ATL]
theorem baseChangeMorphism_hcomp {Z Z' : SchemeBaseChange S} {g₁ : Y ⟶ Z} {g₁' : Y' ⟶ Z'}
    {k : X' ⟶ X} {l : Y' ⟶ Y} {m : Z' ⟶ Z}
    (Rf : PullbackAcyclicResolution f) (Rf' : PullbackAcyclicResolution f')
    (Rg : PullbackAcyclicResolution g₁) (Rg' : PullbackAcyclicResolution g₁')
    (Rk : PullbackAcyclicResolution k) (Rl : PullbackAcyclicResolution l)
    (Rm : PullbackAcyclicResolution m)
    (Rfg : PullbackAcyclicResolution (f ≫ g₁)) (Rfg' : PullbackAcyclicResolution (f' ≫ g₁'))
    (c : Rfg.derivedFunctor ≅ Rg.derivedFunctor ⋙ Rf.derivedFunctor)
    (c' : Rfg'.derivedFunctor ≅ Rg'.derivedFunctor ⋙ Rf'.derivedFunctor)
    (eTop : Rl.derivedFunctor ⋙ Rf'.derivedFunctor ⟶ Rf.derivedFunctor ⋙ Rk.derivedFunctor)
    (eBot : Rm.derivedFunctor ⋙ Rg'.derivedFunctor ⟶ Rg.derivedFunctor ⋙ Rl.derivedFunctor) :
    baseChangeMorphism Rfg Rfg' Rm Rk
        (TwoSquare.whiskerLeft (TwoSquare.whiskerRight (TwoSquare.vComp eBot eTop) c'.hom)
          c.inv) =
      TwoSquare.whiskerTop
        (TwoSquare.whiskerBottom
          (TwoSquare.hComp (baseChangeMorphism Rf Rf' Rl Rk eTop)
            (baseChangeMorphism Rg Rg' Rm Rl eBot))
          (ofKInjectiveComp Rf' Rg' Rfg' c').inv)
        (ofKInjectiveComp Rf Rg Rfg c).hom := by
  rw [baseChangeMorphism, conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
    mateEquiv_hcomp]
  rfl

/-- **Stacks, Remark 20.28.5 (Tag 0ATM)**: base-change morphisms compose when two squares are
pasted along a pushforward edge `f'`. The right square has vertical edges `f`, `f'` and
horizontal edges `h`, `g`; the left square has vertical edges `f'`, `f''` and horizontal edges
`h'`, `g'`. With comparisons `d` and `d'` for the composite horizontal edges (in Stacks, the
compositor isomorphisms), the base-change morphism of the outer rectangle is

`L(h' ≫ h)^* Rf_* ⟶ Lh'^* Lh^* Rf_* ⟶ Lh'^* Rf'_* Lg^* ⟶ Rf''_* Lg'^* Lg^* ⟶ Rf''_* L(g' ≫ g)^*`,

where the outer rectangle uses the pasted pullback comparison. -/
@[stacks 0ATM]
theorem baseChangeMorphism_vcomp {X'' Y'' : SchemeBaseChange S} {f'' : X'' ⟶ Y''}
    {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} {g₂ : X' ⟶ X} {g₂' : X'' ⟶ X'}
    (Rf : PullbackAcyclicResolution f) (Rf' : PullbackAcyclicResolution f')
    (Rf'' : PullbackAcyclicResolution f'')
    (Rh : PullbackAcyclicResolution h) (Rh' : PullbackAcyclicResolution h')
    (Rg : PullbackAcyclicResolution g₂) (Rg' : PullbackAcyclicResolution g₂')
    (Rhh : PullbackAcyclicResolution (h' ≫ h)) (Rgg : PullbackAcyclicResolution (g₂' ≫ g₂))
    (d : Rhh.derivedFunctor ⟶ Rh.derivedFunctor ⋙ Rh'.derivedFunctor)
    (d' : Rg.derivedFunctor ⋙ Rg'.derivedFunctor ⟶ Rgg.derivedFunctor)
    (eR : Rh.derivedFunctor ⋙ Rf'.derivedFunctor ⟶ Rf.derivedFunctor ⋙ Rg.derivedFunctor)
    (eL : Rh'.derivedFunctor ⋙ Rf''.derivedFunctor ⟶ Rf'.derivedFunctor ⋙ Rg'.derivedFunctor) :
    baseChangeMorphism Rf Rf'' Rhh Rgg
        (TwoSquare.whiskerBottom (TwoSquare.whiskerTop (TwoSquare.hComp eR eL) d) d') =
      TwoSquare.whiskerLeft
        (TwoSquare.whiskerRight
          (TwoSquare.vComp (baseChangeMorphism Rf Rf' Rh Rg eR)
            (baseChangeMorphism Rf' Rf'' Rh' Rg' eL))
          d)
        d' := by
  rw [baseChangeMorphism, mateEquiv_whiskerBottom, mateEquiv_whiskerTop, mateEquiv_vcomp]
  rfl

end BaseChange

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
