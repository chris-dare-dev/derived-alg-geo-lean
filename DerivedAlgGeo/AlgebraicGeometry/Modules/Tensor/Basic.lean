/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Picard
import DerivedAlgGeo.Algebra.Category.ModuleCat.StalkTensor
import DerivedAlgGeo.Topology.Sheaves.StalkW
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Tensor descent for invertible module sheaves

This file proves that tensoring a module-sheafification equivalence with a locally free
rank-one sheaf is again inverted by sheafification. It supplies both orientations, the
comparison between restriction and module sheafification, closure of invertible sheaves under
the sheafified tensor product, and the resulting associator.

Over a general site the rank-one hypothesis is essential for local injectivity: the proof
detects local injectivity on a `CoversTop` family and reduces there to tensoring with the unit
presheaf.

**Over a topological space it is not needed at all.** `W_whiskerLeft_of_isIso_stalk` and
`isIso_sheafification_map_whiskerLeft_unit` give the left comparison for an arbitrary
whiskering factor, by working stalkwise: `PresheafOfModules.stalkTensorEquiv` identifies the
stalk of a tensor with the tensor of the stalks, and tensoring with an isomorphism of stalks is
an isomorphism whether or not the other factor is flat. The rank-one lemmas are kept as the
general-site specialisation, which the stalkwise route cannot reach.
-/

open CategoryTheory Limits MonoidalCategory

universe u v u₁ v₁

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

lemma isLocallyInjective_of_coversTop {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    {ι : Type*} (X : ι → C) (hX : J.CoversTop X)
    (h : ∀ i, IsLocallyInjective (J.over (X i))
      (Functor.whiskerLeft (Over.forget (X i)).op f)) :
    IsLocallyInjective J f := by
  constructor
  intro U x y hxy
  apply J.transitive (hX U.unop) (equalizerSieve x y)
  intro V k hk
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hk
  let Y : Over (X i) := Over.mk b
  let f' := Functor.whiskerLeft (Over.forget (X i)).op f
  let x' : ToType (((Over.forget (X i)).op ⋙ P).obj (.op Y)) := P.map k.op x
  let y' : ToType (((Over.forget (X i)).op ⋙ P).obj (.op Y)) := P.map k.op y
  have hxy' : f'.app (.op Y) x' = f'.app (.op Y) y' := by
    change f.app (.op V) (P.map k.op x) = f.app (.op V) (P.map k.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  letI : IsLocallyInjective (J.over (X i)) f' := h i
  have hcover := equalizerSieve_mem (J.over (X i)) f' x' y' hxy'
  rw [GrothendieckTopology.mem_over_iff] at hcover
  change Sieve.overEquiv Y (equalizerSieve x' y') ∈ J Y.left at hcover
  have heqS : Sieve.overEquiv Y (equalizerSieve x' y') =
      equalizerSieve (P.map k.op x) (P.map k.op y) := by
    ext Z a
    rw [Sieve.overEquiv_iff]
    rfl
  rw [heqS] at hcover
  have hpull : Sieve.pullback k (equalizerSieve x y) =
      equalizerSieve (P.map k.op x) (P.map k.op y) := by
    ext Z a
    simp only [Sieve.pullback_apply, equalizerSieve_apply]
    rw [op_comp, P.map_comp]
    rfl
  rw [hpull]
  exact hcover

/-- Local surjectivity is detected on a covering family.

The companion of `isLocallyInjective_of_coversTop`, and stated over the same general site. It was
previously private in `Divisors/AssociatedSheaf/Construction.lean` and hardcoded to `Opens X`,
though its proof uses only `Sieve.ofObjects`, `J.transitive` and `Sieve.overEquiv` — all general. -/
lemma isLocallySurjective_of_coversTop {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    {ι : Type*} (X : ι → C) (hX : J.CoversTop X)
    (h : ∀ i, IsLocallySurjective (J.over (X i))
      (Functor.whiskerLeft (Over.forget (X i)).op f)) :
    IsLocallySurjective J f := by
  constructor
  intro U s
  apply J.transitive (hX U) (Presheaf.imageSieve f s)
  intro V k hk
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hk
  let Z : Over (X i) := Over.mk b
  let f' := Functor.whiskerLeft (Over.forget (X i)).op f
  let s' := Q.map k.op s
  change ToType (((Over.forget (X i)).op ⋙ Q).obj (.op Z)) at s'
  letI : IsLocallySurjective (J.over (X i)) f' := h i
  have hcover := Presheaf.imageSieve_mem (J.over (X i)) f' s'
  rw [GrothendieckTopology.mem_over_iff] at hcover
  change Sieve.overEquiv Z (Presheaf.imageSieve f' s') ∈ J V at hcover
  have heq : Sieve.overEquiv Z (Presheaf.imageSieve f' s') =
      Sieve.pullback k (Presheaf.imageSieve f s) := by
    ext W a
    rw [Sieve.overEquiv_iff]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change f.app (.op W) t = Q.map (a ≫ k).op s
      change f.app (.op W) t = Q.map a.op (Q.map k.op s) at ht
      simpa only [op_comp, Q.map_comp, ConcreteCategory.comp_apply]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change f.app (.op W) t = Q.map a.op (Q.map k.op s)
      rw [op_comp, Q.map_comp] at ht
      change f.app (.op W) t = Q.map a.op (Q.map k.op s) at ht
      exact ht
  rw [heq] at hcover
  exact hcover

/-- **A morphism that is a local weak equivalence on a covering family is one globally.**

This is the packaged form of the recipe `Divisors/AssociatedSheaf/Construction.lean` runs by hand:
local injectivity and local surjectivity each descend along a covering family, and together they
are membership in `J.W`. Sheafification inverts `J.W`, so this is the practical route to
"isomorphism on a cover implies isomorphism after sheafification" — for which no direct lemma
exists on `SheafOfModules` morphisms. -/
lemma W_of_coversTop [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    {ι : Type*} (X : ι → C) (hX : J.CoversTop X)
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (h : ∀ i, (J.over (X i)).W (Functor.whiskerLeft (Over.forget (X i)).op f)) :
    J.W f := by
  letI : IsLocallyInjective J f :=
    isLocallyInjective_of_coversTop f X hX (fun i => (h i).isLocallyInjective)
  letI : IsLocallySurjective J f :=
    isLocallySurjective_of_coversTop f X hX (fun i => (h i).isLocallySurjective)
  exact J.W_of_isLocallyBijective f

end CategoryTheory.Presheaf

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable section

namespace LocalGeneratorsData

noncomputable def rankOneTrivialization {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (i : q.I) : unit (R.over (q.X i)) ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := (hq i).1
  letI : Subsingleton (q.generators i).I := (hq i).2
  let i₀ : (q.generators i).I := Classical.choice (hq i).1
  letI : Unique (q.generators i).I := uniqueOfSubsingleton i₀
  let e := (q.generators i).π
  exact (freePUnitIsoUnit (R := R.over (q.X i))).symm ≪≫
    (freeFunctor (R := R.over (q.X i))).mapIso
      (Equiv.ofUnique PUnit (q.generators i).I).toIso ≪≫
    @asIso _ _ _ _ e (LocalGeneratorsData.IsLocallyFreeData.isIso i)

end LocalGeneratorsData

section CommRing

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}}

local instance : MonoidalCategory
    (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.monoidalCategory (R := S)

set_option pp.universes false in
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma isLocallySurjective_whiskerLeft
    (F : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    {G₁ G₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (g : G₁ ⟶ G₂)
    [Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (F ◁ g)) := by
  constructor
  intro U z
  induction z using TensorProduct.induction_on with
  | zero =>
      have h : Presheaf.imageSieve
          ((PresheafOfModules.toPresheaf _).map (F ◁ g))
          (((PresheafOfModules.toPresheaf _).map (F ◁ g)).app (.op U) 0) ∈ J U := by
        rw [Presheaf.imageSieve_app]
        exact J.top_mem _
      rw [map_zero] at h
      exact h
  | tmul x y =>
      apply J.superset_covering
        (S := Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map g) y)
      · intro V f hf
        let y' : ToType (((PresheafOfModules.toPresheaf _).obj G₂).obj (.op U)) := y
        let y₁' : ToType (((PresheafOfModules.toPresheaf _).obj G₁).obj (.op V)) :=
          Presheaf.localPreimage ((PresheafOfModules.toPresheaf _).map g) y' f hf
        let y₁ : G₁.obj (.op V) := y₁'
        let z₁ : (F ⊗ G₁).obj (.op V) := F.restrictₛₗ f.op x ⊗ₜ y₁
        refine ⟨z₁, ?_⟩
        change (F ◁ g).app (.op V) z₁ = (F ⊗ G₂).map f.op (x ⊗ₜ y)
        rw [PresheafOfModules.whiskerLeft_app]
        dsimp only [z₁]
        erw [ModuleCat.MonoidalCategory.whiskerLeft_apply,
          PresheafOfModules.Monoidal.tensorObj_map_tmul]
        change F.restrictₛₗ f.op x ⊗ₜ _ =
          F.restrictₛₗ f.op x ⊗ₜ G₂.restrictₛₗ f.op y
        congr 1
        exact Presheaf.app_localPreimage
          ((PresheafOfModules.toPresheaf _).map g) y' f hf
      · exact Presheaf.imageSieve_mem J
          ((PresheafOfModules.toPresheaf _).map g) y
  | add z₁ z₂ hz₁ hz₂ =>
      apply J.superset_covering
        (S := Presheaf.imageSieve
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₁ ⊓
          Presheaf.imageSieve
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₂)
      · intro V f hf
        refine ⟨Presheaf.localPreimage
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₁ f hf.1 +
          Presheaf.localPreimage
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₂ f hf.2, ?_⟩
        rw [map_add, Presheaf.app_localPreimage, Presheaf.app_localPreimage]
        exact (map_add _ _ _).symm
      · exact J.intersection_covering hz₁ hz₂

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma isLocallyInjective_whiskerLeft_of_isoUnit
    (F : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (e : 𝟙_ _ ≅ F)
    {G₁ G₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (g : G₁ ⟶ G₂)
    [Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (F ◁ g)) := by
  let e₁ : F ⊗ G₁ ≅ G₁ := MonoidalCategory.tensorIso e.symm (Iso.refl G₁) ≪≫ λ_ G₁
  let e₂ : F ⊗ G₂ ≅ G₂ := MonoidalCategory.tensorIso e.symm (Iso.refl G₂) ≪≫ λ_ G₂
  have hfg : F ◁ g = e₁.hom ≫ g ≫ e₂.inv := by
    rw [← cancel_mono e₂.hom]
    dsimp only [e₁, e₂]
    simp
    rw [← Category.assoc, MonoidalCategory.whisker_exchange]
    rw [Category.assoc, MonoidalCategory.leftUnitor_naturality]
  rw [hfg, Functor.map_comp, Functor.map_comp]
  infer_instance

end CommRing

section LocallyRankOne

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  {S : Sheaf K CommRingCat.{u}}
  [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

private abbrev ringSheaf (S : Sheaf K CommRingCat.{u}) : Sheaf K RingCat.{u} :=
  (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S

local instance : MonoidalCategory
    (PresheafOfModules.{u} (ringSheaf S).obj) :=
  PresheafOfModules.monoidalCategory (R := S.obj)

local instance : SymmetricCategory
    (PresheafOfModules.{u} (ringSheaf S).obj) :=
  PresheafOfModules.symmetricCategory (R := S.obj)

set_option maxHeartbeats 400000 in
omit [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma isLocallyInjective_whiskerLeft_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    [Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) := by
  apply Presheaf.isLocallyInjective_of_coversTop _ q.X q.coversTop
  intro i
  let F := PresheafOfModules.pushforward
    (𝟙 ((ringSheaf S).over (q.X i)).obj)
  let g' := F.map g
  letI : MonoidalCategory
      (PresheafOfModules.{u}
        ((ringSheaf S).over (q.X i)).obj) :=
    PresheafOfModules.monoidalCategory (R := (S.over (q.X i)).obj)
  haveI hg' : Presheaf.IsLocallyInjective (K.over (q.X i))
      ((PresheafOfModules.toPresheaf _).map g') := by
    haveI : Presheaf.IsLocallyInjective (K.over (q.X i))
        (Functor.whiskerLeft (Over.forget (q.X i)).op
          ((PresheafOfModules.toPresheaf _).map g)) :=
      Presheaf.isLocallyInjective_whisker (K.over (q.X i)) K
        (Over.forget (q.X i)) _
    change Presheaf.IsLocallyInjective (K.over (q.X i))
      (Functor.whiskerLeft (Over.forget (q.X i)).op
        ((PresheafOfModules.toPresheaf _).map g))
    infer_instance
  let e := q.rankOneTrivialization hq i
  let ep := (SheafOfModules.forget ((ringSheaf S).over (q.X i))).mapIso e
  haveI : Presheaf.IsLocallyInjective (K.over (q.X i))
      ((PresheafOfModules.toPresheaf
        ((S.over (q.X i)).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map g') := by
    change Presheaf.IsLocallyInjective (K.over (q.X i))
      ((PresheafOfModules.toPresheaf ((ringSheaf S).over (q.X i)).obj).map g')
    exact hg'
  have hlocal := isLocallyInjective_whiskerLeft_of_isoUnit
    (J := K.over (q.X i)) (S := (S.over (q.X i)).obj)
    ((M.over (q.X i)).val) ep g'
  exact hlocal

set_option maxHeartbeats 400000 in
omit [HasWeakSheafify K AddCommGrpCat.{u}] in
lemma W_whiskerLeft_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    (hg : K.W ((PresheafOfModules.toPresheaf _).map g)) :
    K.W ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) := by
  letI : Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map g) := hg.isLocallyInjective
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf _).map g) := hg.isLocallySurjective
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf
        (S.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map g) := by
    change Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf (ringSheaf S).obj).map g)
    infer_instance
  letI : Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) :=
    isLocallyInjective_whiskerLeft_of_rankOneData q hq g
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) :=
    isLocallySurjective_whiskerLeft (S := S.obj) M.val g
  exact K.W_of_isLocallyBijective _

set_option maxHeartbeats 400000 in
lemma isIso_sheafification_map_whiskerLeft_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    (hg : K.W ((PresheafOfModules.toPresheaf _).map g)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map (M.val ◁ g)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj))
    (K.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf S).obj))
  exact W_whiskerLeft_of_rankOneData q hq g hg

set_option maxHeartbeats 400000 in
lemma isIso_sheafification_map_whiskerRight_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    (hg : K.W ((PresheafOfModules.toPresheaf _).map g)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map (g ▷ M.val)) := by
  let a := PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)
  haveI : IsIso (a.map (M.val ◁ g)) :=
    isIso_sheafification_map_whiskerLeft_of_rankOneData q hq g hg
  have hgm : g ▷ M.val =
      (β_ G₁ M.val).hom ≫ (M.val ◁ g) ≫ (β_ M.val G₂).hom := by
    rw [← cancel_mono (β_ G₂ M.val).hom]
    simp
  rw [hgm, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option maxHeartbeats 400000 in
lemma isIso_sheafification_map_whiskerLeft_unit_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (P : PresheafOfModules.{u} (ringSheaf S).obj) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map
        (M.val ◁ (PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf S).obj)).unit.app P)) := by
  apply isIso_sheafification_map_whiskerLeft_of_rankOneData q hq
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact K.W_toSheafify P.presheaf

set_option maxHeartbeats 400000 in
lemma isIso_sheafification_map_whiskerRight_unit_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (P : PresheafOfModules.{u} (ringSheaf S).obj) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf S).obj)).unit.app P ▷ M.val)) := by
  apply isIso_sheafification_map_whiskerRight_of_rankOneData q hq
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact K.W_toSheafify P.presheaf

end LocallyRankOne

end

end SheafOfModules

namespace SheafOfModules

universe u₂ v₂

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {R : Sheaf K RingCat.{u}}
  [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable section

namespace LocalGeneratorsData

/-- Restrict a rank-one trivialization from a cover member to an object over it. -/
noncomputable def rankOneTrivializationOver {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (i : q.I) {Y : D} (f : Y ⟶ q.X i) :
    unit (R.over Y) ≅ M.over Y :=
  (overMapUnitIso f).symm ≪≫
    (overMap R f).mapIso (q.rankOneTrivialization hq i) ≪≫
    (overFunctorMap R f).app M

end LocalGeneratorsData

omit [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A sheaf locally isomorphic to the structure sheaf on a covering family is invertible. -/
lemma IsInvertible.of_trivializations {M : SheafOfModules.{u} R}
    {I : Type u₂} (Y : I → D) (hY : K.CoversTop Y)
    (e : ∀ i, unit (R.over (Y i)) ≅ M.over (Y i)) : M.IsInvertible := by
  let q : M.LocalGeneratorsData :=
    { I := I
      X := Y
      coversTop := hY
      generators i :=
        { I := PUnit
          s := (M.over (Y i)).freeHomEquiv
            ((freePUnitIsoUnit (R := R.over (Y i))) ≪≫ e i).hom
          epi := by
            rw [Equiv.symm_apply_apply]
            infer_instance } }
  have hfree : q.IsLocallyFreeData := by
    constructor
    intro i
    change IsIso ((M.over (Y i)).freeHomEquiv.symm
      ((M.over (Y i)).freeHomEquiv
        ((freePUnitIsoUnit (R := R.over (Y i))) ≪≫ e i).hom))
    rw [Equiv.symm_apply_apply]
    infer_instance
  have hrank : q.IsRankOne := by
    intro i
    exact ⟨inferInstance, inferInstance⟩
  exact ⟨q, hfree, hrank⟩

end

end SheafOfModules

namespace PresheafOfModules

section TopSpace

variable {Y : TopCat.{u}} {R : Y.Presheaf CommRingCat.{u}}

attribute [local instance] PresheafOfModules.monoidalCategory

/-- **Sheafification inverts `M ◁ g` whenever it inverts `g`, for an arbitrary `M`.**

On a topological space this is the general statement `#833` asks for: no flatness, no local
freeness, no rank-one trivialization on the whiskering factor. The route is stalkwise —
`PresheafOfModules.isIso_stalkMapAdd_whiskerLeft` carries a stalk isomorphism through the
whiskering, and `TopCat.Presheaf.W_of_isIso_stalkFunctor_map` converts a stalkwise isomorphism
back into a member of `J.W`. Note that `IsLocallyInjective` is never split off from
`IsLocallySurjective`, which is what makes the stalkwise route available at all: Mathlib has a
stalkwise criterion for `J.W` but none for the injective half on its own. -/
lemma W_whiskerLeft_of_isIso_stalk
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {G₁ G₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : G₁ ⟶ G₂)
    (hg : ∀ y : Y, IsIso (stalkMapAdd g y)) :
    (Opens.grothendieckTopology Y).W
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (M ◁ g)) := by
  haveI := hg
  haveI : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (M ◁ g))) :=
    fun y => isIso_stalkMapAdd_whiskerLeft M g y
  exact TopCat.Presheaf.W_of_isIso_stalkFunctor_map _

end TopSpace

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

local instance : MonoidalCategory
    (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance : SymmetricCategory
    (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private abbrev associatedSheaf' (X : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

private abbrev overPresheafFunctor (X : Scheme.{u}) (U : X.Opens) :=
  PresheafOfModules.pushforward
    (𝟙 (X.ringCatSheaf.over U).obj)

/-- Restriction of an associated module sheaf is the associated sheaf of the restriction. -/
noncomputable def overSheafificationComparison
    (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj
        ((overPresheafFunctor X U).obj P) ⟶
      ((associatedSheaf' X).obj P).over U :=
  (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).map
      ((overPresheafFunctor X U).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P)) ≫
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
        (((associatedSheaf' X).obj P).over U)

private lemma overSheafificationUnit_mem_W
    (P : X.PresheafOfModules) (U : X.Opens) :
    (_root_.Opens.grothendieckTopology X).over U |>.W
      ((PresheafOfModules.toPresheaf _).map
        ((overPresheafFunctor X U).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P))) := by
  let K := _root_.Opens.grothendieckTopology X
  let F := overPresheafFunctor X U
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  let g := F.map η
  have hη : K.W ((PresheafOfModules.toPresheaf _).map η) := by
    dsimp only [η]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact K.W_toSheafify P.presheaf
  letI : Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map η) := hη.isLocallyInjective
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf _).map η) := hη.isLocallySurjective
  haveI hi : Presheaf.IsLocallyInjective (K.over U)
      ((PresheafOfModules.toPresheaf _).map g) := by
    change Presheaf.IsLocallyInjective (K.over U)
      (Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf _).map η))
    exact Presheaf.isLocallyInjective_whisker (K.over U) K
      (Over.forget U) _
  haveI hs : Presheaf.IsLocallySurjective (K.over U)
      ((PresheafOfModules.toPresheaf _).map g) := by
    change Presheaf.IsLocallySurjective (K.over U)
      (Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf _).map η))
    exact Presheaf.isLocallySurjective_whisker (K.over U) K
      (Over.forget U) _
  exact (K.over U).W_of_isLocallyBijective _

private lemma isIso_overSheafificationUnit_map
    (P : X.PresheafOfModules) (U : X.Opens) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).map
        ((overPresheafFunctor X U).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P))) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj))
    (((_root_.Opens.grothendieckTopology X).over U).W.inverseImage
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj))
  exact overSheafificationUnit_mem_W P U

lemma isIso_overSheafificationComparison
    (P : X.PresheafOfModules) (U : X.Opens) :
    IsIso (overSheafificationComparison P U) := by
  haveI : IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit := by
    infer_instance
  dsimp only [overSheafificationComparison]
  apply IsIso.comp_isIso'
  · exact isIso_overSheafificationUnit_map P U
  · exact NatIso.isIso_app_of_isIso _ _

set_option maxHeartbeats 800000 in
private noncomputable def tensorPresheaf'
    (X : Scheme.{u}) (P Q : X.PresheafOfModules) : X.PresheafOfModules := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact P ⊗ Q

set_option maxHeartbeats 800000 in
/-- Restriction of the objectwise tensor presheaf is the tensor of the restrictions. -/
noncomputable def overTensorPresheafIso
    (P Q : X.PresheafOfModules) (U : X.Opens) :
    letI : MonoidalCategory
        (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
      PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
    (overPresheafFunctor X U).obj (tensorPresheaf' X P Q) ≅
      (overPresheafFunctor X U).obj P ⊗ (overPresheafFunctor X U).obj Q := by
  exact Iso.refl _

/-- The tensor product is trivial on an open where both factors are trivial. -/
noncomputable def tensorOverIsoOfTrivializations
    (L M : X.Modules) (U : X.Opens)
    (eL : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U)
    (eM : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    (tensorObj L M).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := by
  letI : MonoidalCategory
      (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let eLP := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eL
  let eMP := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eM
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let c := overSheafificationComparison
    ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) U
  exact (@asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)).symm ≪≫
    aU.mapIso (overTensorPresheafIso
      ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj M) U) ≪≫
    aU.mapIso (MonoidalCategory.tensorIso eLP.symm eMP.symm) ≪≫
    aU.mapIso (λ_ _) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit).app
        (SheafOfModules.unit (X.ringCatSheaf.over U))

set_option maxHeartbeats 1600000 in
/-- **Tensoring with a sheaf that is trivial on `U` does nothing to the restriction to `U`.**

The one-sided companion of `tensorOverIsoOfTrivializations`, which needs *both*
factors trivial and lands on the unit. Here only the right factor is trivialized
and the left one is arbitrary, so the right unitor replaces the left one and the
result is `L.over U` rather than the unit.

This is the shape a twist consumes: `F(n) = F ⊗ O(n)` restricted to a chart where
`O(n)` is trivial is just `F` restricted to that chart, with `F` arbitrary. -/
noncomputable def tensorOverIsoOfTrivializationRight
    (L M : X.Modules) (U : X.Opens)
    (eM : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    (tensorObj L M).over U ≅ L.over U := by
  letI : MonoidalCategory
      (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let eMP := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eM
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let c := overSheafificationComparison
    ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) U
  let cL := overSheafificationComparison ((toPresheafOfModules X).obj L) U
  exact (@asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)).symm ≪≫
    aU.mapIso (overTensorPresheafIso
      ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj M) U) ≪≫
    aU.mapIso (MonoidalCategory.tensorIso (Iso.refl _) eMP.symm) ≪≫
    aU.mapIso (ρ_ _) ≪≫
    (@asIso _ _ _ _ cL (isIso_overSheafificationComparison _ _)) ≪≫
    (SheafOfModules.overFunctor _ _).mapIso
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app L)

set_option maxHeartbeats 1600000 in
/-- The sheafified tensor product of invertible sheaves is invertible. -/
lemma isInvertible_tensorObj (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from tensorObj L M) := by
  obtain ⟨qL, hqL, hrankL⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from L)
  obtain ⟨qM, hqM, hrankM⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from M)
  letI : qL.IsLocallyFreeData := hqL
  letI : qM.IsLocallyFreeData := hqM
  let Y : qL.I × qM.I → X.Opens := fun k : qL.I × qM.I =>
    qL.X k.1 ⊓ qM.X k.2
  have hYL : ⨆ i, qL.X i = ⊤ :=
    (_root_.Opens.coversTop_iff (X : Type u) qL.X).mp qL.coversTop
  have hYM : ⨆ i, qM.X i = ⊤ :=
    (_root_.Opens.coversTop_iff (X : Type u) qM.X).mp qM.coversTop
  have hY : (_root_.Opens.grothendieckTopology X).CoversTop Y := by
    rw [_root_.Opens.coversTop_iff]
    change ⨆ k : qL.I × qM.I, qL.X k.1 ⊓ qM.X k.2 = ⊤
    rw [← iSup_inf_iSup, hYL, hYM, inf_top_eq]
  apply SheafOfModules.IsInvertible.of_trivializations Y hY
  intro k
  exact (tensorOverIsoOfTrivializations L M (Y k)
    (qL.rankOneTrivializationOver hrankL k.1
      (homOfLE inf_le_left))
    (qM.rankOneTrivializationOver hrankM k.2
      (homOfLE inf_le_right))).symm

attribute [instance] isInvertible_tensorObj

/-- **Sheafification inverts `M ◁ toSheafify` for an arbitrary `M`.**

The general form of `SheafOfModules.isIso_sheafification_map_whiskerLeft_unit_of_rankOneData`,
with the rank-one hypothesis on the whiskering factor gone. It is available here and not over a
general site because the proof is stalkwise; see
`PresheafOfModules.W_whiskerLeft_of_isIso_stalk`. -/
lemma isIso_sheafification_map_whiskerLeft_unit (M P : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (M ◁ (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    ((_root_.Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
  apply PresheafOfModules.W_whiskerLeft_of_isIso_stalk (R := X.presheaf)
  intro x
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.presheaf

/-- Comparison from tensoring before sheafification to tensoring with the associated sheaf. -/
noncomputable def tensorSheafificationComparisonLeft
    (L : X.Modules) (P : X.PresheafOfModules) :
    (associatedSheaf' X).obj ((toPresheafOfModules X).obj L ⊗ P) ⟶
      tensorObj L ((associatedSheaf' X).obj P) :=
  (associatedSheaf' X).map
    ((toPresheafOfModules X).obj L ◁
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P)

/-- Right-handed comparison from tensoring before sheafification. -/
noncomputable def tensorSheafificationComparisonRight
    (P : X.PresheafOfModules) (L : X.Modules) :
    (associatedSheaf' X).obj (P ⊗ (toPresheafOfModules X).obj L) ⟶
      tensorObj ((associatedSheaf' X).obj P) L :=
  (associatedSheaf' X).map
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ▷
        (toPresheafOfModules X).obj L)

/-- The left comparison is an isomorphism for **arbitrary** `L`.

The invertibility hypothesis this carried until #833 was an artifact of proving local
injectivity and local surjectivity separately: the injective half then needed `L` locally
trivial. Going through stalks avoids the split — see
`isIso_sheafification_map_whiskerLeft_unit`. -/
lemma isIso_tensorSheafificationComparisonLeft (L : X.Modules) (P : X.PresheafOfModules) :
    IsIso (tensorSheafificationComparisonLeft L P) :=
  isIso_sheafification_map_whiskerLeft_unit ((toPresheafOfModules X).obj L) P

set_option backward.isDefEq.respectTransparency false in
/-- The right comparison is an isomorphism for arbitrary `L`.

The left comparison is already invertible without a finiteness or flatness hypothesis. Symmetry of
the objectwise tensor conjugates the right comparison to that left comparison, so the same result
holds on the other side. This removes the last rank-one restriction from associativity of the
sheafified tensor product. -/
lemma isIso_tensorSheafificationComparisonRight (P : X.PresheafOfModules) (L : X.Modules) :
    IsIso (tensorSheafificationComparisonRight P L) := by
  let a := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let U := (toPresheafOfModules X).obj L
  let V := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
    SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  have hNat := BraidedCategory.braiding_naturality_right U eta
  have h : eta ▷ U =
      (β_ P U).hom ≫ (U ◁ eta) ≫ (β_ U V).hom := by
    symm
    dsimp only [V]
    calc
      (β_ P U).hom ≫ (U ◁ eta) ≫ (β_ U V).hom =
          (β_ P U).hom ≫
            (β_ U ((𝟭 X.PresheafOfModules).obj P)).hom ≫ (eta ▷ U) := by
              rw [hNat]
      _ = eta ▷ U := by
        change (β_ P U).hom ≫ (β_ U P).hom ≫ (eta ▷ U) = eta ▷ U
        simp
  haveI hMiddle : IsIso (a.map (U ◁ eta)) := by
    change IsIso (tensorSheafificationComparisonLeft L P)
    exact isIso_tensorSheafificationComparisonLeft L P
  change IsIso (a.map (eta ▷ U))
  rw [h, Functor.map_comp, Functor.map_comp]
  infer_instance

attribute [instance] isIso_tensorSheafificationComparisonLeft
  isIso_tensorSheafificationComparisonRight

/-- Associativity of the sheafified tensor product for arbitrary module sheaves. -/
noncomputable def tensorAssocIso (L M N : X.Modules) :
    tensorObj (tensorObj L M) N ≅ tensorObj L (tensorObj M N) := by
  let cR := tensorSheafificationComparisonRight
    ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) N
  let cL := tensorSheafificationComparisonLeft L
    ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)
  exact (@asIso _ _ _ _ cR
      (isIso_tensorSheafificationComparisonRight _ _)).symm ≪≫
    tensorTripleAssocIso L M N ≪≫
    @asIso _ _ _ _ cL (isIso_tensorSheafificationComparisonLeft _ _)

end


end AlgebraicGeometry.Scheme.Modules
