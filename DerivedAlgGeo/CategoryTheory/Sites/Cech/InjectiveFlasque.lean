/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.Comparison
import Mathlib.Topology.Sheaves.Flasque

/-!
# Injective abelian sheaves are flasque

For a topological space, every injective sheaf of abelian groups is flasque.  The proof uses the
free abelian sheaves represented by opens: a section over an open `V` is a map from the
corresponding free representable, and an inclusion `V ⊆ U` induces a monomorphism between those
representables.  Injectivity extends the map from `V` to `U`, which is exactly surjectivity of the
restriction map.

This is the first input to the injective-row half of the Cech-to-derived comparison.  It is kept
as a theorem rather than a global instance so that callers opt into the relatively expensive
injectivity argument explicitly.
-/

universe u

open CategoryTheory Category Limits Opposite
open TopCat TopologicalSpace

namespace CategoryTheory.Sheaf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

private lemma freeAbelianYonedaPresheafHomAddEquiv_precomp
    {C : Type u} [Category.{u} C] {X Y : C} (f : X ⟶ Y)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (g : yoneda.obj Y ⋙ AddCommGrpCat.free ⟶ G) :
    freeAbelianYonedaPresheafHomAddEquiv X G
        (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free ≫ g) =
      G.map f.op (freeAbelianYonedaPresheafHomAddEquiv Y G g) := by
  dsimp [freeAbelianYonedaPresheafHomAddEquiv]
  calc
    _ = g.app (op X) (FreeAbelianGroup.of f) := by
      congr 1
      change (AddCommGrpCat.free.map ((yoneda.map f).app (op X))).hom
        (FreeAbelianGroup.of (𝟙 X)) = FreeAbelianGroup.of f
      rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
      simp
    _ = G.map f.op (g.app (op Y) (FreeAbelianGroup.of (𝟙 Y))) := by
      have h := CategoryTheory.congr_fun (g.naturality f.op)
        (FreeAbelianGroup.of (𝟙 Y))
      simp only [Functor.comp_map, CategoryTheory.comp_apply] at h
      change g.app (op X)
          ((AddCommGrpCat.free.map ((yoneda.obj Y).map f.op)).hom
            (FreeAbelianGroup.of (𝟙 Y))) =
        G.map f.op (g.app (op Y) (FreeAbelianGroup.of (𝟙 Y))) at h
      rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of] at h
      simpa using h

private lemma freeAbelianYonedaSheafHomAddEquiv_precomp
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] {X Y : C} (f : X ⟶ Y)
    (G : Sheaf J AddCommGrpCat.{u})
    (g : freeAbelianYonedaSheaf J Y ⟶ G) :
    freeAbelianYonedaSheafHomAddEquiv X G
        ((presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫ g) =
      G.obj.map f.op (freeAbelianYonedaSheafHomAddEquiv Y G g) := by
  change freeAbelianYonedaPresheafHomAddEquiv X G.obj
      ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _
        ((presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeAbelianYonedaPresheafHomAddEquiv_precomp f G.obj _

/-- An injective sheaf of abelian groups on a topological space is flasque. -/
lemma isFlasque_of_injective {X : TopCat.{u}}
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [hI : Injective I] :
    I.IsFlasque := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let J := Opens.grothendieckTopology X
  let m : freeAbelianYonedaSheaf J V.unop ⟶
      freeAbelianYonedaSheaf J U.unop :=
    (presheafToSheaf J AddCommGrpCat.{u}).map
      (Functor.whiskerRight (yoneda.map i.unop) AddCommGrpCat.free)
  let g : freeAbelianYonedaSheaf J V.unop ⟶ I :=
    (freeAbelianYonedaSheafHomAddEquiv V.unop I).symm s
  letI hm : Mono m := by
    dsimp [m, freeAbelianYonedaSheaf]
    infer_instance
  let e : freeAbelianYonedaSheaf J U.unop ⟶ I :=
    @Injective.factorThru _ _ I _ _ hI g m hm
  refine ⟨freeAbelianYonedaSheafHomAddEquiv U.unop I e, ?_⟩
  have hme : m ≫ e = g := by
    dsimp [e]
    exact @Injective.comp_factorThru _ _ I _ _ hI g m hm
  calc
    _ = freeAbelianYonedaSheafHomAddEquiv V.unop I (m ≫ e) :=
      (freeAbelianYonedaSheafHomAddEquiv_precomp i.unop I e).symm
    _ = freeAbelianYonedaSheafHomAddEquiv V.unop I g :=
      congrArg (freeAbelianYonedaSheafHomAddEquiv V.unop I) hme
    _ = s := by
      dsimp [g]
      exact AddEquiv.apply_symm_apply _ s

end CategoryTheory.Sheaf
