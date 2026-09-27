/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.ShortComplex.Limits
import DerivedAlgGeo.CategoryTheory.Limits.Preserves.Naturality
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Coproducts of homological complexes, degreewise; homology of colimits

A coproduct of homological complexes is computed degreewise: evaluation in each degree
preserves it.  This file names the degreewise identification (`sigmaXIso`), the two
summand-inclusion lemmas, extensionality for maps out of a degree of the coproduct
(`sigmaX_ext_from`), and the degreewise description of a family of maps out of the summands
(`sigmaXDesc`), in the shape of Mathlib's `biprodXIso` for binary biproducts.  The consumer is
`Homotopy.sigma`, which assembles homotopies on the summands into one on the coproduct.

The second section is about colimits of any shape `J` the underlying category has: the short
complex at a degree is a colimit-preserving functor of the complex, since its three components
are evaluations, so homology in a degree commutes with colimits of shape `J` as soon as homology
of short complexes does (which is the case when colimits of shape `J` are exact).

## Main definitions

* `HomologicalComplex.sigmaXIso`: `(∐ X).X i ≅ ∐ fun k => (X k).X i`.
* `HomologicalComplex.sigmaXDesc`: the degreewise map out of `(∐ X).X i` assembled from maps
  out of the summands.

## Main results

* `HomologicalComplex.ι_f_sigmaXIso_hom`, `ι_sigmaXIso_inv`: the summand inclusions on both
  sides of the identification.
* `HomologicalComplex.sigmaX_ext_from`: maps out of `(∐ X).X i` are determined by their
  restrictions to the summands.
* `HomologicalComplex.homologyFunctor_preservesColimitsOfShape`: homology in degree `i`
  preserves colimits of shape `J` when homology of short complexes does.
* `HomologicalComplex.quasiIso_colimMap_of_preservesHomology`: homology-preserving
  colimits preserve componentwise quasi-isomorphisms.
* `HomologicalComplex.quasiIso_colimMap`: the exact-colimit specialization.
* `HomologicalComplex.quasiIso_app_colimit_of_preserves`: a pointwise quasi-isomorphism
  between colimit-preserving functors is a quasi-isomorphism at a colimit.

## Implementation notes

`sigmaXIso` is `PreservesCoproduct.iso (eval C c i) X` rather than
`asIso (sigmaComparison (eval C c i) X)`: inside a definition, the `IsIso` search for the
comparison enters the coproduct instance on `HomologicalComplex C c` and does not terminate.
-/

open CategoryTheory Category Limits

universe w w' w'' v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  {κ : Type w} [HasColimitsOfShape (Discrete κ) C] (X : κ → HomologicalComplex C c)

/-- Evaluation at `i` preserves the coproduct; see the implementation notes for the choice of
spelling. -/
noncomputable def sigmaXIso (i : ι) : (∐ X).X i ≅ ∐ fun k => (X k).X i :=
  PreservesCoproduct.iso (eval C c i) X

@[reassoc (attr := simp)]
lemma ι_sigmaXIso_inv (k : κ) (i : ι) :
    Sigma.ι (fun k => (X k).X i) k ≫ (sigmaXIso X i).inv = (Sigma.ι X k).f i :=
  ι_comp_sigmaComparison (eval C c i) X k

@[reassoc (attr := simp)]
lemma ι_f_sigmaXIso_hom (k : κ) (i : ι) :
    (Sigma.ι X k).f i ≫ (sigmaXIso X i).hom = Sigma.ι (fun k => (X k).X i) k := by
  rw [← ι_sigmaXIso_inv X k i, assoc, Iso.inv_hom_id, comp_id]

variable {X}

/-- Maps out of `(∐ X).X i` are determined by their restrictions to the summands, since
evaluation preserves the coproduct. -/
lemma sigmaX_ext_from {i : ι} {A : C} {f g : (∐ X).X i ⟶ A}
    (h : ∀ k, (Sigma.ι X k).f i ≫ f = (Sigma.ι X k).f i ≫ g) : f = g := by
  rw [← cancel_epi (sigmaXIso X i).inv]
  ext k
  simp only [ι_sigmaXIso_inv_assoc, h k]

variable {Y : HomologicalComplex C c}

/-- The degreewise map out of `(∐ X).X i` assembled from maps out of the summands: the
degreewise identification followed by `Sigma.desc`. -/
noncomputable def sigmaXDesc (φ : ∀ k, ∀ i j, (X k).X i ⟶ Y.X j) (i j : ι) :
    (∐ X).X i ⟶ Y.X j :=
  (sigmaXIso X i).hom ≫ Sigma.desc fun k => φ k i j

@[reassoc (attr := simp)]
lemma ι_f_sigmaXDesc (φ : ∀ k, ∀ i j, (X k).X i ⟶ Y.X j) (k : κ) (i j : ι) :
    (Sigma.ι X k).f i ≫ sigmaXDesc φ i j = φ k i j := by
  simp only [sigmaXDesc, ι_f_sigmaXIso_hom_assoc, Sigma.ι_desc]

section Colimits

variable (C c) {J : Type w'} [Category.{w''} J] [HasColimitsOfShape J C]

/-- `shortComplexFunctor C c i` preserves colimits of every shape `C` has: its three components
are evaluations. -/
instance shortComplexFunctor_preservesColimitsOfShape (i : ι) :
    PreservesColimitsOfShape J (shortComplexFunctor C c i) := by
  constructor
  intro F
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) ?_
  refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
  · exact isColimitOfPreserves (eval C c (c.prev i)) (colimit.isColimit F)
  · exact isColimitOfPreserves (eval C c i) (colimit.isColimit F)
  · exact isColimitOfPreserves (eval C c (c.next i)) (colimit.isColimit F)

/-- Homology in degree `i` commutes with colimits of shape `J` when homology of short complexes
does, through the factorization `homologyFunctorIso` of homology of complexes. -/
instance homologyFunctor_preservesColimitsOfShape [CategoryWithHomology C] (i : ι)
    [PreservesColimitsOfShape J (ShortComplex.homologyFunctor C)] :
    PreservesColimitsOfShape J (homologyFunctor C c i) :=
  preservesColimitsOfShape_of_natIso (homologyFunctorIso C c i).symm

end Colimits

end HomologicalComplex

namespace HomologicalComplex

section HomologyPreservingColimits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]
  {J : Type w'} [Category.{w''} J]
  [HasColimitsOfShape J C]
  {ι : Type*} {c : ComplexShape ι}

/-- Commuting degreewise homology with this colimit identifies the homology map
of `colim.map α` with the colimit of the pointwise homology maps, which are
isomorphisms. -/
theorem quasiIso_colimMap_of_preservesHomology
    [∀ i, PreservesColimitsOfShape J (homologyFunctor C c i)]
    {F G : J ⥤ HomologicalComplex C c} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colim.map α) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor C c i
  haveI hαH (j : J) : IsIso ((Functor.whiskerRight α H).app j) := by
    change IsIso (homologyMap (α.app j) i)
    letI : QuasiIso (α.app j) := hα j
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  haveI : IsIso (Functor.whiskerRight α H) :=
    NatIso.isIso_of_isIso_app _
  haveI : IsIso (colim.map (Functor.whiskerRight α H)) := inferInstance
  let β := preservesColimitNatIso (J := J) H
  have h := β.hom.naturality α
  haveI : IsIso (β.hom.app F) := inferInstance
  haveI : IsIso (β.hom.app G) := inferInstance
  have hH : IsIso ((colim ⋙ H).map α ≫ β.hom.app G) := by
    rw [h]
    change IsIso (β.hom.app F ≫ colim.map (Functor.whiskerRight α H))
    exact IsIso.comp_isIso' (inferInstance : IsIso (β.hom.app F))
      (inferInstance : IsIso (colim.map (Functor.whiskerRight α H)))
  have hmap : IsIso ((colim ⋙ H).map α) :=
    IsIso.of_isIso_comp_right _ (β.hom.app G)
  exact hmap

end HomologyPreservingColimits

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w'} [Category.{w''} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
  {ι : Type*} {c : ComplexShape ι}

/-- Exact colimits commute with homology through the short-complex comparison, so the
homology-preserving criterion above applies. This includes filtered colimits in an
AB5 category. -/
theorem quasiIso_colimMap {F G : J ⥤ HomologicalComplex C c} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colim.map α) := by
  letI : ∀ i, PreservesColimitsOfShape J (homologyFunctor C c i) :=
    fun _ => inferInstance
  exact quasiIso_colimMap_of_preservesHomology α hα

end HomologicalComplex

namespace HomologicalComplex

universe w₁ w₂ v₁ u₁ v₂ u₂

variable {J : Type w₁} [Category.{w₂} J]
  {A : Type u₁} [Category.{v₁} A] [HasColimitsOfShape J A]
  {C : Type u₂} [Category.{v₂} C] [HasZeroMorphisms C] [CategoryWithHomology C]
  [HasColimitsOfShape J C]
  {ι : Type*} {c : ComplexShape ι}
  [∀ i, PreservesColimitsOfShape J (homologyFunctor C c i)]
  {H H' : A ⥤ HomologicalComplex C c}
  [PreservesColimitsOfShape J H] [PreservesColimitsOfShape J H']
  (F : J ⥤ A) (α : H ⟶ H')

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation between colimit-preserving functors to complexes is a
quasi-isomorphism at a colimit when it is one on every object of the diagram.
Preservation of the colimit by degreewise homology transfers the pointwise
quasi-isomorphisms through `colim.map`; naturality of the preserved-colimit
comparisons transfers the result back to the original transformation. -/
theorem quasiIso_app_colimit_of_preserves
    (hα : ∀ j, QuasiIso ((F.whiskerLeft α).app j)) :
    QuasiIso (α.app (colimit F)) := by
  have hcolim := quasiIso_colimMap_of_preservesHomology (F.whiskerLeft α) hα
  haveI : QuasiIso (colim.map (F.whiskerLeft α)) := hcolim
  have hnat := CategoryTheory.preservesColimitIso_naturality α F
  haveI : QuasiIso (α.app (colimit F) ≫
      (CategoryTheory.preservesColimitIso H' F).hom) := by
    rw [hnat]
    infer_instance
  exact quasiIso_of_comp_right (α.app (colimit F))
    (CategoryTheory.preservesColimitIso H' F).hom

end HomologicalComplex
