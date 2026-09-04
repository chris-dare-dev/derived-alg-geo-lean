/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.EssentialImage

/-!
# Transferring preservation of coproducts

Two facts about functors and coproducts of a fixed shape `ι`.  A functor `G` out of the target of
an essentially surjective functor `L` preserves coproducts of shape `ι` as soon as `L` and the
composite `L ⋙ G` do (`preservesCoproductsOfShape_of_essSurj`): every family in the middle
category is isomorphic to the image of a family, whose coproduct the composite sends to a
coproduct.  And a functor preserving coproducts of shape `ι` sends `Sigma.map` of a family of
morphisms it inverts to an isomorphism (`isIso_map_sigma_map`).  The consumers are homology on
the homotopy and derived categories, which factor through the quotient and localization
functors, and the stability of quasi-isomorphisms under coproducts.

## Main results

* `CategoryTheory.Limits.preservesCoproductsOfShape_of_essSurj`
* `CategoryTheory.Limits.isIso_map_sigma_map`
-/

open CategoryTheory Category Limits

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {ι : Type w}

/-- A functor preserves coproducts of shape `ι` as soon as it does so after precomposition with
an essentially surjective functor preserving them. -/
theorem preservesCoproductsOfShape_of_essSurj (L : C ⥤ D) (G : D ⥤ E) [L.EssSurj]
    [HasCoproductsOfShape ι C] [PreservesColimitsOfShape (Discrete ι) L]
    [PreservesColimitsOfShape (Discrete ι) (L ⋙ G)] :
    PreservesColimitsOfShape (Discrete ι) G := by
  haveI : ∀ Y : ι → D, PreservesColimit (Discrete.functor Y) G := fun Y => by
    let X : ι → C := fun i => L.objPreimage (Y i)
    have e : Discrete.functor Y ≅ Discrete.functor X ⋙ L :=
      Discrete.natIso fun ⟨i⟩ => (L.objObjPreimageIso (Y i)).symm
    haveI : PreservesColimit (Discrete.functor X ⋙ L) G := by
      refine preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (coproductIsCoproduct X)) ?_
      exact isColimitOfPreserves (L ⋙ G) (coproductIsCoproduct X)
    exact preservesColimit_of_iso_diagram G e.symm
  exact preservesColimitsOfShape_of_discrete G

/-- A functor preserving coproducts of shape `ι` sends `Sigma.map` of a family of morphisms it
inverts to an isomorphism: the coproduct comparison squares identify its image with `Sigma.map`
of the images. -/
theorem isIso_map_sigma_map (G : D ⥤ E) [HasCoproductsOfShape ι D] [HasCoproductsOfShape ι E]
    [PreservesColimitsOfShape (Discrete ι) G]
    {X₁ X₂ : ι → D} (f : ∀ j, X₁ j ⟶ X₂ j) [∀ j, IsIso (G.map (f j))] :
    IsIso (G.map (Sigma.map f)) := by
  have hsq : Sigma.map (fun j => G.map (f j)) ≫ sigmaComparison G X₂ =
      sigmaComparison G X₁ ≫ G.map (Sigma.map f) := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_map_assoc, ι_comp_sigmaComparison, ← assoc, ι_comp_sigmaComparison,
      ← G.map_comp, ← G.map_comp, Sigma.ι_map]
  have : IsIso (sigmaComparison G X₁ ≫ G.map (Sigma.map f)) := by
    rw [← hsq]; infer_instance
  exact IsIso.of_isIso_comp_left (sigmaComparison G X₁) (G.map (Sigma.map f))

end CategoryTheory.Limits
