/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Functoriality
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Constant
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback

/-!
# The augmentation of a simplicial scheme towards a scheme

An augmentation `a : X ⟶ c(Y)` of a simplicial scheme `X` towards a scheme `Y`
gives the morphism of ringed topoi `a : (Sh(X_total), 𝒪) ⟶ (Sh(Y), 𝒪_Y)` of
Stacks, Lemma 85.4.2 (Tag 0D70). It factors as the morphism `a_total` along the
map of simplicial schemes `X ⟶ c(Y)`, followed by the constant augmentation
`c(Y) ⟶ Y`. Accordingly

* `a^* = a_total^* ∘ c^*`, and `g_n⁻¹ (a^* G) ≅ a_n^* G`;
* `a_* = c_* ∘ a_total,*`; on sections over `V` it is the equalizer of
  `F(0, a_0⁻¹ V) ⇉ F(1, a_1⁻¹ V)`, that is, of `a_{0,*} F_0 ⇉ a_{1,*} F_1`.

When every `a_n` is flat, `a^*` is exact: exactness is checked after restriction
to each level, where `a^*` becomes the exact pullback `a_n^*`.

## Main definitions

* `AlgebraicGeometry.TotalSite.augPullback a`, `augPushforward a` and
  `augAdjunction a : augPullback a ⊣ augPushforward a`.
* `AlgebraicGeometry.TotalSite.augPullbackRestrictIso a n`: `g_n⁻¹ ∘ a^* ≅ a_n^*`.

## Main results

* `AlgebraicGeometry.TotalSite.isIso_of_isIso_restrict`: the restrictions to the
  levels jointly reflect isomorphisms.
* `AlgebraicGeometry.TotalSite.augPullback_preservesFiniteLimits`: `a^*` is exact
  when every `a_n` is flat.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace AlgebraicGeometry.TotalSite

variable {X : SimplicialObject Scheme.{u}}

/-- A morphism of modules on the total site is an isomorphism when all of its
restrictions to the levels are. -/
lemma isIso_of_isIso_restrict {M N : Modules X} (φ : M ⟶ N)
    (h : ∀ n, IsIso ((restrict X n).map φ)) : IsIso φ := by
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro x
    have h₁ : @IsIso (SheafOfModules (X.obj (op x.unop.level)).ringCatSheaf) _ _ _
        ((restrict X x.unop.level).map φ) := h x.unop.level
    haveI h₂ : IsIso ((SheafOfModules.forget (X.obj (op x.unop.level)).ringCatSheaf ⋙
        PresheafOfModules.toPresheaf _).map ((restrict X x.unop.level).map φ)) := by
      haveI := h₁
      exact Functor.map_isIso _ _
    exact (inferInstance : IsIso (((SheafOfModules.forget (X.obj (op x.unop.level)).ringCatSheaf ⋙
      PresheafOfModules.toPresheaf _).map ((restrict X x.unop.level).map φ)).app (op x.unop.opens)))
  exact isIso_of_reflects_iso φ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

/-- A functor into modules on the total site preserves finite limits as soon as
its composites with all the restrictions to levels do. -/
lemma preservesFiniteLimits_of_restrict {C : Type*} [Category* C] [HasFiniteLimits C]
    (L : C ⥤ Modules X) (h : ∀ n, PreservesFiniteLimits (L ⋙ restrict X n)) :
    PreservesFiniteLimits L where
  preservesFiniteLimits J _ _ := ⟨fun {K} => by
    haveI : IsIso (limit.post K L) := isIso_of_isIso_restrict _ fun n => by
      haveI := h n
      have e := limit.post_post K L (restrict X n)
      haveI : IsIso ((restrict X n).map (limit.post K L) ≫
          limit.post (K ⋙ L) (restrict X n)) := by
        rw [e]; infer_instance
      exact IsIso.of_isIso_comp_right _ (limit.post (K ⋙ L) (restrict X n))
    exact preservesLimit_of_isIso_post (F := K) (G := L)⟩

variable {Y : Scheme.{u}} (a : X ⟶ (SimplicialObject.const Scheme.{u}).obj Y)

/-- The pullback `a^*` along an augmentation: `a^* G` restricts to `a_n^* G` on
`X_n` (Stacks, Lemma 85.4.2, Tag 0D70). -/
noncomputable def augPullback : Y.Modules ⥤ Modules X :=
  constPullback Y ⋙ pullbackAlong a

/-- The pushforward `a_*` along an augmentation (Stacks, Lemma 85.4.2, Tag 0D70): the
equalizer of the two coface maps of `a_total,* F`, whose sections over `V` are
`F(0, a_0⁻¹ V) ⇉ F(1, a_1⁻¹ V)`. -/
noncomputable def augPushforward : Modules X ⥤ Y.Modules :=
  pushforwardAlong a ⋙ constPushforward Y

/-- `a^* ⊣ a_*`. -/
noncomputable def augAdjunction : augPullback a ⊣ augPushforward a :=
  (constAdjunction Y).comp (pullbackAlongAdjunction a)

/-- The restriction of `a^* G` to the level `n` is `a_n^* G`. -/
noncomputable def augPullbackRestrictIso (n : SimplexCategory) :
    augPullback a ⋙ restrict X n ≅ Scheme.Modules.pullback (a.app (op n)) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (constPullback Y)
    (pullbackAlongRestrictIso a n) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constPullbackRestrictIso Y n) _ ≪≫ Functor.leftUnitor _

lemma pullback_preservesFiniteLimits_of_flat {A B : Scheme.{u}} (g : A ⟶ B) [Flat g] :
    PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  @DerivedCategory.Families.SchemeBaseChange.modulePullback_preservesFiniteLimits_of_flat B
    (Over.mk g) (Over.mk (𝟙 B)) (Over.homMk g (by simp)) (inferInstance : Flat g)

/-- Pullback along an augmentation all of whose components are flat is exact. -/
lemma augPullback_preservesFiniteLimits [∀ n, Flat (a.app n)] :
    PreservesFiniteLimits (augPullback a) :=
  preservesFiniteLimits_of_restrict _ fun n =>
    letI := pullback_preservesFiniteLimits_of_flat (a.app (op n))
    preservesFiniteLimits_of_natIso (augPullbackRestrictIso a n).symm

end AlgebraicGeometry.TotalSite
