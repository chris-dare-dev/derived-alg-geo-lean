/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Basic.Isomorphism
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Over
import DerivedAlgGeo.Topology.Opens.Limits
import DerivedAlgGeo.Topology.Opens.CoversTop
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.OpenImmersion
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Locality of finite presentation

This file proves the affine-local criterion for coherent sheaves. Finite presentation is preserved
by restriction to an object of the site, and finite presentations on the members of an affine open
cover glue to a finite presentation on the whole scheme.

The site-local arguments below are expressed using `M.over U`, the canonical restriction to the
slice site over an open `U`. The scheme-level restriction results use the equivalence with the
restriction functor along an open immersion constructed in
`AlgebraicGeometry.Modules.Restriction.OpenImmersion`.
-/

universe u v

open CategoryTheory Limits TopologicalSpace

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

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (M : X.Modules)
  (𝒰 : AlgebraicGeometry.Scheme.AffineOpenCover.{v, u} X)

/-- A coherent module restricts to a finitely presented module along an open immersion. -/
theorem Modules.IsCoherent.restrict_of_isOpenImmersion {Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (N : Y.Modules)
    (hN : Modules.IsCoherent Y N) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (N.restrict f) :=
  f.isFinitePresentation_restrict N
    (SheafOfModules.IsFinitePresentation.over hN f.opensRange)

/-- Coherence descends from finite presentation on the range slices of an affine open cover. -/
theorem Modules.IsCoherent.of_affineOpenCover
    (h : ∀ i, SheafOfModules.IsFinitePresentation.{u, u, u}
      (M.over ((𝒰.f i).opensRange))) :
    Modules.IsCoherent X M := by
  apply SheafOfModules.IsFinitePresentation.of_coversTop M
    (fun i ↦ (𝒰.f i).opensRange)
  · apply TopCat.Opens.grothendieckTopology_coversTop
    exact 𝒰.openCover.iSup_opensRange
  · exact h

/-- A sheaf of modules is coherent if and only if it is of finite presentation on the range slice
of every member of an affine open cover. -/
theorem Modules.isCoherent_iff_of_affineOpenCover :
    Modules.IsCoherent X M ↔
      ∀ i, SheafOfModules.IsFinitePresentation.{u, u, u}
        (M.over ((𝒰.f i).opensRange)) := by
  constructor
  · intro hM i
    exact SheafOfModules.IsFinitePresentation.over hM ((𝒰.f i).opensRange)
  · exact Modules.IsCoherent.of_affineOpenCover M 𝒰

/-- A coherent module restricts to a finitely presented module along each scheme-level open
immersion in an affine open cover. -/
theorem Modules.IsCoherent.restrict_affineOpenCover
    (hM : Modules.IsCoherent X M) (i) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (M.restrict (𝒰.f i)) :=
  Modules.IsCoherent.restrict_of_isOpenImmersion (𝒰.f i) M hM

/-- **The scheme-level affine-local criterion for coherence.**

A sheaf of modules is coherent exactly when it is of finite presentation after *scheme-level*
restriction along each member of an affine open cover.

This is `isCoherent_iff_of_affineOpenCover` carried across the open-immersion/slice
equivalence by `Scheme.Hom.isFinitePresentation_over_iff_restrict`, whose reverse half is what
makes the `↔` available rather than just the forward implication. The slice-level statement
remains the engine and is not reproved here; the point of this one is that downstream
arguments never have to mention `Over` or `M.over`. -/
theorem Modules.isCoherent_iff_restrict_affineOpenCover :
    Modules.IsCoherent X M ↔
      ∀ i, SheafOfModules.IsFinitePresentation.{u, u, u} (M.restrict (𝒰.f i)) := by
  rw [Modules.isCoherent_iff_of_affineOpenCover M 𝒰]
  exact forall_congr' fun i => (𝒰.f i).isFinitePresentation_over_iff_restrict M

end AlgebraicGeometry.Scheme
