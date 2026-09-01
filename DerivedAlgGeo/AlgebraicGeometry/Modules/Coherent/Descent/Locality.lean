/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Basic.Isomorphism
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Locality
import DerivedAlgGeo.Topology.Category.TopCat.Opens.Limits
import DerivedAlgGeo.Topology.Category.TopCat.Opens.CoversTop
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.OpenImmersion
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Affine locality of coherent sheaves

This file proves the scheme-level affine-local criterion for coherent sheaves. Preservation and
descent of finite presentation on an arbitrary ringed site are supplied by
`Algebra.Category.ModuleCat.Sheaf.Presentation.Locality`.

The site-local arguments below are expressed using `M.over U`, the canonical restriction to the
slice site over an open `U`. The scheme-level restriction results use the equivalence with the
restriction functor along an open immersion constructed in
`AlgebraicGeometry.Modules.Restriction.OpenImmersion`.
-/

universe u v

open CategoryTheory Limits TopologicalSpace

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
