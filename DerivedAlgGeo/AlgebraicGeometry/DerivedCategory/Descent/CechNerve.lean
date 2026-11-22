/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicTopology.CechNerve
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KInjective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Augmentation
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.Cartesian

/-!
# Module sheaves on the Čech nerve of a morphism of schemes

For a morphism of schemes `π : Y' ⟶ Y`, let `Y'_•` be its Čech nerve, Mathlib's
`(Arrow.mk π).cechNerve`, so that `Y'_n = Y' ×_Y ⋯ ×_Y Y'` with `n + 1` factors.
This file specializes the total site of a simplicial scheme to `Y'_•`, in the
setting of Stacks, Situation 85.3.3 (Tag 09WE) with Zariski sites:

* the ringed site `Y'_{•,total}` (Stacks, Lemma 85.3.1, Tag 09WC) and its
  Grothendieck abelian category of module sheaves;
* the restrictions `g_n⁻¹` to the `Y'_n` (Stacks, Lemma 85.3.5, Tag 09WG);
* the augmentation `a : Y'_• ⟶ Y` with `a^* ⊣ a_*` (Stacks, Lemma 85.4.2,
  Tag 0D70), where `a_* F` has sections the equalizer of
  `F(0, a_0⁻¹ V) ⇉ F(1, a_1⁻¹ V)`, and `a^* G` restricts to `a_n^* G` on `Y'_n`;
* `a^*` is exact when `π` is flat, so it has the derived functor `La^*`;
* the right derived functor `Ra_*`, from K-injective resolutions;
* cartesian modules and cartesian objects of `D` (Stacks, Definition 85.12.1,
  Tag 0D7G).

## Main results

* `AlgebraicGeometry.CechNerve.flat_widePullback_base`: the structure map
  `Y'_n ⟶ Y` of the Čech nerve is flat when `π` is.
* `AlgebraicGeometry.CechNerve.augPullback_preservesFiniteLimits`: `a^*` is exact
  for flat `π`.
-/

attribute [local instance] HasDerivedCategory.standard

universe u

open CategoryTheory Opposite Limits Simplicial

namespace AlgebraicGeometry.CechNerve

variable {Y' Y : Scheme.{u}} (π : Y' ⟶ Y)

section WidePullback

/-- The projection `Y'_{n+1} ⟶ Y'_n` forgetting the last factor. -/
noncomputable def dropLast (n : ℕ) :
    widePullback Y (fun _ : Fin (n + 2) => Y') (fun _ => π) ⟶
      widePullback Y (fun _ : Fin (n + 1) => Y') (fun _ => π) :=
  WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.castSucc)
    (fun _ => WidePullback.π_arrow _ _)

/-- `Y'_{n+1}` is the fibre product of `Y'_n` and `Y'` over `Y`. -/
lemma isPullback_dropLast (n : ℕ) :
    IsPullback (dropLast π n) (WidePullback.π (fun _ => π) (Fin.last (n + 1)))
      (WidePullback.base (fun _ : Fin (n + 1) => π)) π := by
  have w : dropLast π n ≫ WidePullback.base (fun _ : Fin (n + 1) => π) =
      WidePullback.π (fun _ => π) (Fin.last (n + 1)) ≫ π := by
    simp [dropLast]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => WidePullback.lift (s.fst ≫ WidePullback.base _)
      (fun j => Fin.lastCases s.snd (fun i => s.fst ≫ WidePullback.π _ i) j) ?_) ?_ ?_ ?_)
  · intro j
    induction j using Fin.lastCases with
    | last => simp [s.condition]
    | cast i => simp
  · intro s
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp [dropLast]
    · simp [dropLast]
  · intro s
    simp
  · intro s m h₁ h₂
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · induction j using Fin.lastCases with
      | last => simpa using h₂
      | cast i =>
        simp only [WidePullback.lift_π, Fin.lastCases_castSucc, ← h₁, Category.assoc]
        simp [dropLast]
    · simp only [WidePullback.lift_base, ← h₁, Category.assoc]
      simp [dropLast]

/-- The structure map `Y'_n ⟶ Y` of the Čech nerve of a flat morphism is flat. -/
lemma flat_widePullback_base [Flat π] (n : ℕ) :
    Flat (WidePullback.base (fun _ : Fin (n + 1) => π)) := by
  induction n with
  | zero =>
    have : IsIso (WidePullback.π (fun _ : Fin 1 => π) 0) :=
      ⟨WidePullback.lift π (fun _ => 𝟙 Y') (by simp),
        WidePullback.hom_ext _ _ _ (fun j => by fin_cases j; simp) (by simp), by simp⟩
    rw [← WidePullback.π_arrow (fun _ : Fin 1 => π) 0]
    infer_instance
  | succ n ih =>
    have hp : Flat (dropLast π n) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_dropLast π n).flip
        ‹Flat π›
    have e : dropLast π n ≫ WidePullback.base (fun _ : Fin (n + 1) => π) =
        WidePullback.base (fun _ : Fin (n + 2) => π) :=
      WidePullback.lift_base _ _ _ _
    rw [← e]
    infer_instance

end WidePullback

/-- The total site of the Čech nerve of `π` (Stacks, Lemma 85.3.1, Tag 09WC). -/
noncomputable abbrev totalSite : Type u :=
  TotalSite (Arrow.mk π).cechNerve

/-- The topology of the total site of the Čech nerve (Stacks, Tag 09WC). -/
noncomputable abbrev topology : GrothendieckTopology (totalSite π) :=
  TotalSite.topology _

/-- The structure sheaf of rings of the total site of the Čech nerve. -/
noncomputable abbrev ringSheaf : Sheaf (topology π) RingCat.{u} :=
  TotalSite.ringSheaf _

/-- Module sheaves on the total site of the Čech nerve of `π`. -/
noncomputable abbrev Modules : Type (u + 1) :=
  SheafOfModules.{u} (ringSheaf π)

example : IsGrothendieckAbelian.{u} (Modules π) := inferInstance

/-- Restriction to the `n`-th scheme `Y'_n` of the Čech nerve: Stacks' `g_n⁻¹`. -/
noncomputable abbrev restrict (n : ℕ) :
    Modules π ⥤ ((Arrow.mk π).cechNerve.obj (op ⦋n⦌)).Modules :=
  TotalSite.restrict _ ⦋n⦌

/-- The augmentation `Y'_• ⟶ Y` of the Čech nerve, as a map to the constant
simplicial scheme. -/
noncomputable def aug : (Arrow.mk π).cechNerve ⟶ (SimplicialObject.const Scheme.{u}).obj Y :=
  (Arrow.mk π).augmentedCechNerve.hom

instance flat_aug_app [Flat π] (n : SimplexCategoryᵒᵖ) : Flat ((aug π).app n) :=
  flat_widePullback_base π n.unop.len

/-- The pullback `a^*` along the augmentation of the Čech nerve. -/
noncomputable abbrev augPullback : Y.Modules ⥤ Modules π :=
  TotalSite.augPullback (aug π)

/-- The pushforward `a_*` along the augmentation: on sections over `V`, the equalizer
of `F(0, a_0⁻¹ V) ⇉ F(1, a_1⁻¹ V)`. -/
noncomputable abbrev augPushforward : Modules π ⥤ Y.Modules :=
  TotalSite.augPushforward (aug π)

/-- `a^* ⊣ a_*`. -/
noncomputable abbrev augAdjunction : augPullback π ⊣ augPushforward π :=
  TotalSite.augAdjunction (aug π)

/-- Pullback along the augmentation of the Čech nerve of a flat morphism is exact. -/
instance augPullback_preservesFiniteLimits [Flat π] :
    PreservesFiniteLimits (augPullback π) :=
  TotalSite.augPullback_preservesFiniteLimits (aug π)

instance : (augPullback π).IsLeftAdjoint := (augAdjunction π).isLeftAdjoint

instance : (augPushforward π).IsRightAdjoint := (augAdjunction π).isRightAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts in
instance : (augPullback π).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
instance : (augPushforward π).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- The derived pullback `La^* : D(Y) ⥤ D(Y'_{•,total})` for flat `π`, where `a^*`
is exact. -/
noncomputable def derivedAugPullback [Flat π] :
    DerivedCategory Y.Modules ⥤ DerivedCategory (Modules π) :=
  (augPullback π).mapDerivedCategory

/-- The derived pushforward `Ra_* : D(Y'_{•,total}) ⥤ D(Y)`, the right derived functor
of `a_*` computed on K-injective resolutions (Stacks, Lemma 13.31.7, Tag 070K). -/
noncomputable def derivedAugPushforward :
    DerivedCategory (Modules π) ⥤ DerivedCategory Y.Modules :=
  kInjectiveDerivedFunctor (augPushforward π)

/-- Cartesian modules on the Čech nerve (Stacks, Definition 85.12.1, Tag 0D7G). -/
noncomputable abbrev IsCartesian : ObjectProperty (Modules π) :=
  TotalSite.IsCartesian _

/-- Cartesian objects of `D(Y'_{•,total})` (Stacks, Definition 85.12.1, Tag 0D7G):
the comparisons `L f_φ^* K_n ⟶ K_m` are isomorphisms for all `φ`. -/
noncomputable abbrev IsCartesianObj : ObjectProperty (DerivedCategory (Modules π)) :=
  TotalSite.IsCartesianObj _

end AlgebraicGeometry.CechNerve
