/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.Comparison
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalk-locality of free abelian representable sheaves

If `U ⊆ V` are opens and `x ∈ U`, the induced map from the free abelian sheaf represented
by `U` to the one represented by `V` is an isomorphism on the stalk at `x`.

This is the local input for the injective-row half of the Cech-to-derived comparison.  It lets us
intersect a Cech cover with one chosen member without changing the resulting free representable
resolution on stalks inside that member.

The proof is deliberately made before sheafification.  The map is injective on every open.  For
surjectivity on the stalk, represent a germ over a neighborhood contained in `U`; on such a
neighborhood the two representable hom-types are both singletons, so the induced map of free
abelian groups is an isomorphism.  The units of sheafification are isomorphisms on stalks, which
then transports the result to sheaves.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.GrothendieckTopology Opposite TopologicalSpace

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}}

/-- The morphism of free abelian representable presheaves induced by an inclusion of opens. -/
noncomputable def freeAbelianYonedaPresheafMap {U V : Opens X} (i : U ⟶ V) :
    (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶
      (yoneda.obj V ⋙ AddCommGrpCat.free) :=
  Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free

private lemma freeAbelianYonedaPresheafMap_app_injective {U V : Opens X} (i : U ⟶ V)
    (W : Opens X) :
    Function.Injective ((freeAbelianYonedaPresheafMap i).app (op W)) := by
  rw [← AddCommGrpCat.mono_iff_injective]
  dsimp [freeAbelianYonedaPresheafMap]
  infer_instance

private lemma freeAbelianYonedaPresheafMap_app_surjective_of_le
    {U V W : Opens X} (i : U ⟶ V) (hWU : W ≤ U) :
    Function.Surjective ((freeAbelianYonedaPresheafMap i).app (op W)) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  dsimp [freeAbelianYonedaPresheafMap]
  let e := (yoneda.map i).app (op W)
  haveI : IsIso e := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro f g _
      cases f with
      | up f => cases f with
        | up _ => cases g with
          | up g => cases g with
            | up _ => rfl
    · intro f
      refine ⟨⟨⟨hWU⟩⟩, ?_⟩
      cases f with
      | up f => cases f with
        | up _ => rfl
  change Epi (AddCommGrpCat.free.map e)
  infer_instance

private lemma freeAbelianYonedaPresheafMap_stalk_isIso
    {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (freeAbelianYonedaPresheafMap i)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (freeAbelianYonedaPresheafMap_app_injective i) x
  · intro t
    obtain ⟨W, hWU, hxW, s, hs⟩ := TopCat.Presheaf.exists_le_germ_eq
      (yoneda.obj V ⋙ AddCommGrpCat.free) t hx
    obtain ⟨r, hr⟩ := freeAbelianYonedaPresheafMap_app_surjective_of_le i hWU s
    refine ⟨TopCat.Presheaf.germ
      (yoneda.obj U ⋙ AddCommGrpCat.free) W x hxW r, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hr]
    exact hs

private lemma freeAbelianYonedaPresheaf_stalk_isZero_of_not_mem
    (U : Opens X) (x : X) (hx : x ∉ U) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free)) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  constructor
  intro s t
  obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (yoneda.obj U ⋙ AddCommGrpCat.free) s
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (yoneda.obj U ⋙ AddCommGrpCat.free) t
  have hWU : ¬ W ≤ U := fun h ↦ hx (h hxW)
  have hVU : ¬ V ≤ U := fun h ↦ hx (h hxV)
  letI : IsEmpty ((yoneda.obj U).obj (op W)) :=
    ⟨fun f ↦ hWU f.down.down⟩
  letI : IsEmpty ((yoneda.obj U).obj (op V)) :=
    ⟨fun f ↦ hVU f.down.down⟩
  change FreeAbelianGroup ((yoneda.obj U).obj (op W)) at s
  change FreeAbelianGroup ((yoneda.obj U).obj (op V)) at t
  rw [Subsingleton.elim s 0, Subsingleton.elim t 0]
  exact (map_zero _).trans (map_zero _).symm

/-- The morphism of free abelian representable sheaves induced by an inclusion of opens. -/
noncomputable def freeAbelianYonedaSheafMap {U V : Opens X} (i : U ⟶ V) :
    freeAbelianYonedaSheaf (Opens.grothendieckTopology X) U ⟶
      freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (freeAbelianYonedaPresheafMap i)

/-- A map of free abelian sheaves represented by `U ⊆ V` is an isomorphism on every stalk
inside `U`. -/
lemma freeAbelianYonedaSheafMap_stalk_isIso {U V : Opens X} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (freeAbelianYonedaSheafMap i).hom) := by
  let J := Opens.grothendieckTopology X
  let P : X.Presheaf AddCommGrpCat.{u} := yoneda.obj U ⋙ AddCommGrpCat.free
  let Q : X.Presheaf AddCommGrpCat.{u} := yoneda.obj V ⋙ AddCommGrpCat.free
  let α : P ⟶ Q := freeAbelianYonedaPresheafMap i
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI hα : IsIso (S.map α) := freeAbelianYonedaPresheafMap_stalk_isIso i x hx
  haveI hU : IsIso (S.map (CategoryTheory.toSheafify J P)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  haveI hV : IsIso (S.map (CategoryTheory.toSheafify J Q)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat Q
  change IsIso (S.map (CategoryTheory.sheafifyMap J α))
  apply IsIso.of_isIso_fac_left (f := S.map (CategoryTheory.toSheafify J P))
    (h := S.map α ≫ S.map (CategoryTheory.toSheafify J Q))
  rw [← S.map_comp, ← S.map_comp]
  exact congrArg S.map (CategoryTheory.toSheafify_naturality J α).symm

/-- The stalk at `x` of the free abelian sheaf represented by an open not containing `x` is
zero. -/
lemma freeAbelianYonedaSheaf_stalk_isZero_of_not_mem
    (U : Opens X) (x : X) (hx : x ∉ U) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) U).obj) := by
  let J := Opens.grothendieckTopology X
  let P : X.Presheaf AddCommGrpCat.{u} := yoneda.obj U ⋙ AddCommGrpCat.free
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hP : IsZero (S.obj P) :=
    freeAbelianYonedaPresheaf_stalk_isZero_of_not_mem U x hx
  haveI : IsIso (S.map (CategoryTheory.toSheafify J P)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  exact IsZero.of_iso hP (asIso (S.map (CategoryTheory.toSheafify J P))).symm

end CategoryTheory.Sheaf
