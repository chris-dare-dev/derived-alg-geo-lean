/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Over
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Locality of finite presentation on a ringed site

Finite presentation of a sheaf of modules on an arbitrary ringed site is preserved by restriction
to an object of the site and descends from a family of objects covering the terminal object.

## Main results

* `SheafOfModules.QuasicoherentData.isFinitePresentation_over` preserves finite local
  presentation data under restriction;
* `SheafOfModules.IsFinitePresentation.over` restricts finite presentation;
* `SheafOfModules.IsFinitePresentation.of_coversTop` glues finite presentation from a covering
  family.
-/

universe u v

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

section Restrict

variable [HasBinaryProducts C] [HasPullbacks C]

local instance (X : C) : HasBinaryProducts (Over X) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

instance QuasicoherentData.isFinitePresentation_over {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) [q.IsFinitePresentation] :
    (q.over U).IsFinitePresentation where
  isFinite_presentation i := by
    dsimp only [QuasicoherentData.over]
    let Y := (Over.star U).obj (q.X i)
    apply @Presentation.IsFinite.mk (Over Y) _ ((J.over U).over Y) ((R.over U).over Y)
      (hasWeakSheafifyOverOver U Y) (wEqualsLocallyBijectiveOverOver U Y)
    · apply @GeneratingSections.IsFiniteType.mk (Over Y) _ ((J.over U).over Y)
        ((R.over U).over Y) (hasWeakSheafifyOverOver U Y)
        (wEqualsLocallyBijectiveOverOver U Y)
      change Finite (q.presentationOver U i).generators.I
      rw [QuasicoherentData.presentationOver_generators_I]
      infer_instance
    · apply @GeneratingSections.IsFiniteType.mk (Over Y) _ ((J.over U).over Y)
        ((R.over U).over Y) (hasWeakSheafifyOverOver U Y)
        (wEqualsLocallyBijectiveOverOver U Y)
      change Finite (q.presentationOver U i).relations.I
      rw [QuasicoherentData.presentationOver_relations_I]
      infer_instance

omit hasSheafComposeOver hasSheafifyOver hasSheafComposeOverOver hasSheafifyOverOver in
/-- Finite presentation is preserved by restriction to an object of the site. -/
theorem IsFinitePresentation.over {M : SheafOfModules.{u} R}
    (hM : IsFinitePresentation M) (U : C) : IsFinitePresentation (M.over U) := by
  obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
  letI := hq
  exact ⟨q.over U, inferInstance⟩

end Restrict

omit hasSheafComposeOver hasSheafComposeOverOver in
/-- Finite presentation descends along a family of objects covering the terminal object. -/
theorem IsFinitePresentation.of_coversTop (M : SheafOfModules.{u} R) {I : Type v}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, IsFinitePresentation (M.over (X i))) : IsFinitePresentation M := by
  let I' := Set.range X
  let X' : I' → C := fun i ↦ X i.2.choose
  have hX' : J.CoversTop X' := by
    intro Y
    refine J.superset_covering ?_ (hX Y)
    intro Z f hf
    obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
    let i' : I' := ⟨X i, ⟨i, rfl⟩⟩
    apply (Sieve.mem_ofObjects_iff ..).mpr
    exact ⟨i', ⟨g ≫ eqToHom i'.2.choose_spec.symm⟩⟩
  choose D hD using fun i : I' ↦ (h i.2.choose).exists_quasicoherentData
  letI (i : I') : (D i).IsFinitePresentation := hD i
  let q := QuasicoherentData.bind M X' hX' D
  refine ⟨q, ?_⟩
  constructor
  rintro ⟨i, j⟩
  dsimp only [q, QuasicoherentData.bind]
  apply @Presentation.IsFinite.mk (Over ((D i).X j).left) _
    (J.over ((D i).X j).left) (R.over ((D i).X j).left)
    (hasWeakSheafifyOver _) (wEqualsLocallyBijectiveOver _)
  · apply @GeneratingSections.IsFiniteType.mk (Over ((D i).X j).left) _
      (J.over ((D i).X j).left) (R.over ((D i).X j).left)
      (hasWeakSheafifyOver _) (wEqualsLocallyBijectiveOver _)
    change Finite ((D i).presentation j).generators.I
    infer_instance
  · apply @GeneratingSections.IsFiniteType.mk (Over ((D i).X j).left) _
      (J.over ((D i).X j).left) (R.over ((D i).X j).left)
      (hasWeakSheafifyOver _) (wEqualsLocallyBijectiveOver _)
    change Finite ((D i).presentation j).relations.I
    infer_instance

end SheafOfModules
