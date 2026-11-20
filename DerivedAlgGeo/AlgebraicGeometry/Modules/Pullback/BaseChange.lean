/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Base change of a module sheaf along a morphism of bases

For `p : X ⟶ S`, a module sheaf `F` on `X` and an `S`-scheme `T`, the base change `F_T` is the
pullback of `F` along the projection `X ×_S T ⟶ X`. A morphism `g : T' ⟶ T` over `S` induces
`X ×_S T' ⟶ X ×_S T`, and `X ×_S T'` is the pullback of `X ×_S T ⟶ T` along `g`, so `F_{T'}` is
the pullback of `F_T` along that morphism.

## Main definitions

* `AlgebraicGeometry.quotBaseChange`: the pullback `F_T` of `F` to `X ×_S T`.
* `AlgebraicGeometry.quotFunctor.baseChangeHom`: the morphism `X ×_S T' ⟶ X ×_S T` induced by
  `T' ⟶ T`.
* `AlgebraicGeometry.quotFunctor.baseChangeIso`: the comparison `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T`.

## Implementation notes

The comparison is built from `pullbackComp` and `pullbackCongr`, through the equation
`pullback.fst p T'.hom = baseChangeHom p g ≫ pullback.fst p T.hom`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)

/-- The pullback `F_T` of `F` to `X_T = X ×_S T`, along the projection `X_T ⟶ X`. -/
abbrev quotBaseChange (T : Over S) : (Limits.pullback p T.hom).Modules :=
  (Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj F

namespace quotFunctor

open Scheme.Modules

/-- The morphism `X ×_S T' ⟶ X ×_S T` induced by a morphism `T' ⟶ T` over `S`. -/
abbrev baseChangeHom {T' T : Over S} (g : T' ⟶ T) :
    Limits.pullback p T'.hom ⟶ Limits.pullback p T.hom :=
  pullback.map p T'.hom p T.hom (𝟙 X) g.left (𝟙 S) (by simp) (by simp)

lemma baseChangeHom_fst {T' T : Over S} (g : T' ⟶ T) :
    pullback.fst p T'.hom = baseChangeHom p g ≫ pullback.fst p T.hom := by
  simp

lemma baseChangeHom_id (T : Over S) : baseChangeHom p (𝟙 T) = 𝟙 _ := by
  ext <;> simp

lemma baseChangeHom_comp {T'' T' T : Over S} (k : T'' ⟶ T') (g : T' ⟶ T) :
    baseChangeHom p k ≫ baseChangeHom p g = baseChangeHom p (k ≫ g) := by
  ext <;> simp

/-- `X ×_S T'` is the pullback of `X ×_S T ⟶ T` along `T' ⟶ T`. -/
lemma isPullback_baseChangeHom {T' T : Over S} (g : T' ⟶ T) :
    IsPullback (baseChangeHom p g) (pullback.snd p T'.hom) (pullback.snd p T.hom)
      g.left := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback p T.hom)
  rw [← baseChangeHom_fst p g, Over.w g]
  exact IsPullback.of_hasPullback p T'.hom

/-- The comparison `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` for a morphism `T' ⟶ T` over `S`. -/
def baseChangeIso {T' T : Over S} (g : T' ⟶ T) :
    quotBaseChange p F T' ≅
      (Scheme.Modules.pullback (baseChangeHom p g)).obj (quotBaseChange p F T) :=
  (pullbackCongr (baseChangeHom_fst p g)).app F ≪≫
    ((pullbackComp (baseChangeHom p g) (pullback.fst p T.hom)).app F).symm

lemma baseChangeIso_hom {T' T : Over S} (g : T' ⟶ T) :
    (baseChangeIso p F g).hom = (pullbackCongr (baseChangeHom_fst p g)).hom.app F ≫
      (pullbackComp (baseChangeHom p g) (pullback.fst p T.hom)).inv.app F :=
  rfl

end quotFunctor

end

end AlgebraicGeometry
