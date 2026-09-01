/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Restricting presentations to over sites

Presentations, finite generating families, and quasicoherent presentation data for a sheaf of
modules on an arbitrary ringed site restrict to slice sites. The direct restriction first lands
on an iterated slice; `Over.iteratedSliceEquiv` and
`SheafOfModules.pushforwardPushforwardEquivalence` identify it with restriction to the domain
object.

Nothing in this construction requires a scheme or a topological space. Affine and coherent-sheaf
arguments import this module and add their geometric cover or finiteness input.

## Main results

* `SheafOfModules.Presentation.over` restricts one presentation along an object of a slice site;
* `SheafOfModules.GeneratingSections.over` restricts a family of generating sections and
  preserves finiteness of its index;
* `SheafOfModules.QuasicoherentData.over` restricts a full family of local presentations.
-/

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [hasSheafComposeOver : ∀ X,
    (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafifyOver : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [hasWeakSheafifyOver : ∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [wEqualsLocallyBijectiveOver : ∀ X,
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hasSheafComposeOverOver : ∀ X Y, ((J.over X).over Y).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafifyOverOver : ∀ X Y,
    HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [hasWeakSheafifyOverOver : ∀ X Y,
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [wEqualsLocallyBijectiveOverOver : ∀ X Y,
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option maxHeartbeats 1600000 in
/-- Restrict a presentation on `U` along an object `W ⟶ U` of the slice site.

The direct restriction has target `((M.over U).over W).Presentation`; the iterated-slice
equivalence identifies that target with `(M.over W.left).Presentation`. -/
noncomputable def Presentation.over {M : SheafOfModules.{u} R} {U : C}
    (P : (M.over U).Presentation) (W : Over U) [HasBinaryProducts (Over U)] :
    (M.over W.left).Presentation := by
  haveI : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (𝟙 ((R.over U).over W))) :=
    preservesColimitsOfSize_shrink.{u, u, u, u} _
  let P' : ((M.over U).over W).Presentation :=
    P.map (SheafOfModules.pushforward (𝟙 _)) (.refl _)
  letI eW := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := (R.over U).over W) (R := R.over W.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  exact (P'.map eW.inverse (.refl _)).ofIsIso
    (eW.fullyFaithfulFunctor.preimageIso
      (by exact eW.counitIso.app ((M.over U).over W))).hom

set_option maxHeartbeats 1600000 in
/-- Restrict generating sections on `U` along an object `W ⟶ U` of the slice site. -/
noncomputable def GeneratingSections.over {M : SheafOfModules.{u} R} {U : C}
    (σ : (M.over U).GeneratingSections) (W : Over U) [HasBinaryProducts (Over U)] :
    (M.over W.left).GeneratingSections := by
  haveI : PreservesColimitsOfSize.{u, u}
      (pushforward.{u} (𝟙 ((R.over U).over W))) :=
    preservesColimitsOfSize_shrink.{u, u, u, u} _
  let σ' : ((M.over U).over W).GeneratingSections :=
    σ.map (pushforward (𝟙 _)) (.refl _)
  letI eW := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := (R.over U).over W) (R := R.over W.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  exact (σ'.map eW.inverse (.refl _)).ofEpi
    (eW.fullyFaithfulFunctor.preimageIso
      (by exact eW.counitIso.app ((M.over U).over W))).hom

set_option maxHeartbeats 1600000 in
/-- Restriction to a nested slice preserves finite generation. -/
instance GeneratingSections.isFiniteType_over {M : SheafOfModules.{u} R} {U : C}
    (σ : (M.over U).GeneratingSections) [σ.IsFiniteType]
    (W : Over U) [HasBinaryProducts (Over U)] : (σ.over W).IsFiniteType where
  finite := inferInstanceAs (Finite σ.I)

section QuasicoherentDataOver

variable [HasBinaryProducts C] [HasPullbacks C]

local instance (X : C) : HasBinaryProducts (Over X) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

set_option maxHeartbeats 1600000 in
/-- Restrict one of the presentations in `q` to the product with `U`. -/
noncomputable def QuasicoherentData.presentationOver {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) (i : q.I) :
    ((M.over U).over ((Over.star U).obj (q.X i))).Presentation := by
  let Y := (Over.star U).obj (q.X i)
  let W : Over (q.X i) := Over.mk (prod.snd : U ⨯ q.X i ⟶ q.X i)
  haveI : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (𝟙 ((R.over (q.X i)).over W))) :=
    preservesColimitsOfSize_shrink.{u, u, u, u} _
  let P : ((M.over (q.X i)).over W).Presentation :=
    (q.presentation i).map (SheafOfModules.pushforward (𝟙 _)) (.refl _)
  letI eW := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := (R.over (q.X i)).over W) (R := R.over W.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let P' : (M.over W.left).Presentation := (P.map eW.inverse (.refl _)).ofIsIso
    (eW.fullyFaithfulFunctor.preimageIso
      (by exact eW.counitIso.app ((M.over (q.X i)).over W))).hom
  letI eY := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over U).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  change (eY.functor.obj (M.over Y.left)).Presentation
  exact P'.map eY.functor (.refl _)

omit hasSheafComposeOver hasSheafComposeOverOver in
@[simp]
theorem QuasicoherentData.presentationOver_generators_I {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) (i : q.I) :
    (q.presentationOver U i).generators.I = (q.presentation i).generators.I := rfl

omit hasSheafComposeOver hasSheafComposeOverOver in
@[simp]
theorem QuasicoherentData.presentationOver_relations_I {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) (i : q.I) :
    (q.presentationOver U i).relations.I = (q.presentation i).relations.I := rfl

/-- Restrict local presentation data to an object of the site. The new cover consists of the
products of the old covering objects with the object of restriction. -/
noncomputable def QuasicoherentData.over {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) : (M.over U).QuasicoherentData where
  I := q.I
  X i := (Over.star U).obj (q.X i)
  coversTop V := by
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ (q.coversTop V.left)
    intro Z g hg
    rw [Sieve.overEquiv_iff]
    obtain ⟨i, ⟨k⟩⟩ := hg
    exact ⟨i, ⟨(Over.forgetAdjStar U).homEquiv _ _ k⟩⟩
  presentation i := q.presentationOver U i

end QuasicoherentDataOver

end SheafOfModules
