/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology of short complexes commutes with exact colimits

In an abelian category with exact colimits of shape `J` (`HasExactColimitsOfShape J C`, the
axiom AB4 when `J` is discrete and AB5 when it is filtered), the homology functor
`ShortComplex C ⥤ C` preserves colimits of shape `J`.  A diagram of short complexes is a short
complex `S` of diagrams; its colimit is `S.map colim` because colimits in `ShortComplex C` are
computed after each projection, and the homology of `S.map colim` is `colim` of the homology
of `S` by Mathlib's `mapHomologyIso`, since an exact `colim` preserves homology.

## Main results

* `ShortComplex.homologyFunctor_preservesColimitsOfShape`: the instance.

## Implementation notes

The colimit cocone of the diagram of short complexes is constructed by hand as `colimCocone S`,
with legs `S.mapNatTrans (colim.ι j)`, and shown to be a colimit through
`isColimitOfIsColimitπ`, so that its image under homology can be compared with the colimit
cocone of `S.homology` by `homologyMap_mapNatTrans` leg by leg.
-/

open CategoryTheory Category Limits

universe w w' v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {J : Type w} [Category.{w'} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

variable (S : ShortComplex (J ⥤ C))

/-- The cocone over the diagram of short complexes underlying `S`, with vertex `S.map colim`. -/
noncomputable def colimCocone : Cocone ((FunctorEquivalence.functor J C).obj S) where
  pt := S.map colim
  ι :=
    { app := fun j => S.mapNatTrans (colim.ι j)
      naturality := fun j j' f => by
        ext
        · exact (colimit.w S.X₁ f).trans (comp_id _).symm
        · exact (colimit.w S.X₂ f).trans (comp_id _).symm
        · exact (colimit.w S.X₃ f).trans (comp_id _).symm }

/-- `colimCocone S` is a colimit cocone: it is one after each projection. -/
noncomputable def isColimitColimCocone : IsColimit (colimCocone S) :=
  isColimitOfIsColimitπ _
    (IsColimit.ofIsoColimit (colimit.isColimit S.X₁) (Cocone.ext (Iso.refl _) (fun _ => comp_id _)))
    (IsColimit.ofIsoColimit (colimit.isColimit S.X₂) (Cocone.ext (Iso.refl _) (fun _ => comp_id _)))
    (IsColimit.ofIsoColimit (colimit.isColimit S.X₃) (Cocone.ext (Iso.refl _) (fun _ => comp_id _)))

/-- Homology in `J ⥤ C` is computed pointwise: the homology of the diagram of short complexes
underlying `S` is the homology of `S`, evaluated (`mapHomologyIso` at each evaluation
functor). -/
noncomputable def homologyPointwiseIso :
    (FunctorEquivalence.functor J C).obj S ⋙ homologyFunctor C ≅ S.homology :=
  NatIso.ofComponents (fun j => S.mapHomologyIso ((evaluation J C).obj j)) (fun {j j'} f => by
    change homologyMap (S.mapNatTrans ((evaluation J C).map f)) ≫ _ = _
    rw [S.homologyMap_mapNatTrans ((evaluation J C).map f)]
    simp only [evaluation_map_app, assoc]
    erw [Iso.inv_hom_id, comp_id]
    rfl)

/-- Homology sends `colimCocone S` to a colimit cocone: its vertex is the homology of
`S.map colim`, which `mapHomologyIso` identifies with `colim` of the homology of `S`, and its
legs are the evaluated legs by `homologyMap_mapNatTrans`. -/
noncomputable def isColimitMapCoconeColimCocone :
    IsColimit ((homologyFunctor C).mapCocone (colimCocone S)) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (homologyPointwiseIso S) _).symm
      (colimit.isColimit S.homology))
    (Cocone.ext (S.mapHomologyIso colim).symm (fun j => by
      change _ = homologyMap (S.mapNatTrans (colim.ι j))
      rw [S.homologyMap_mapNatTrans (colim.ι j)]
      simp [homologyPointwiseIso]
      exact assoc _ _ _))

/-- Homology preserves the colimit of the diagram of short complexes underlying `S`: the
colimit cocone `colimCocone S` is sent to a colimit cocone.  Only the `OfShape` instance below
is meant to be found by instance search. -/
lemma preservesColimit_homologyFunctor :
    PreservesColimit ((FunctorEquivalence.functor J C).obj S) (homologyFunctor C) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimCocone S)
    (isColimitMapCoconeColimCocone S)

/-- When colimits of shape `J` are exact, `colim : (J ⥤ C) ⥤ C` preserves homology
(`Functor.preservesHomologyOfExact`), so `mapHomologyIso` identifies the homology of
`S.map colim` with `colim` of the homology of `S`; every diagram of short complexes is such an
`S` by `functorEquivalence`.  Mathlib has the exactness of `colim` but not this consequence. -/
instance homologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J (homologyFunctor C) :=
  ⟨fun {F} => by
    haveI : PreservesColimit
        (((functorEquivalence J C).inverse ⋙ (functorEquivalence J C).functor).obj F)
        (homologyFunctor C) :=
      preservesColimit_homologyFunctor ((functorEquivalence J C).inverse.obj F)
    exact preservesColimit_of_iso_diagram _ ((functorEquivalence J C).counitIso.app F)⟩

end CategoryTheory.ShortComplex
