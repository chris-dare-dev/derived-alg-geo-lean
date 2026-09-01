/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Topology.Sheaves.Stalks

/-!
# Detecting sheaf isomorphisms on a basis

A morphism of sheaves on a topological space is an isomorphism when its components are
isomorphisms on a basis of opens. The proof completes Mathlib's basiswise injectivity result with
the matching surjectivity statement, then detects the isomorphism on stalks.

These results are topological sheaf theory: their signatures require a topological space, its
opens, a basis, germs, and stalk functors, but no scheme.

## Main results

* `TopCat.Presheaf.stalkFunctor_map_surjective_of_isBasis` — surjectivity on a basis implies
  surjectivity on every stalk;
* `TopCat.Sheaf.isIso_of_isIso_app_of_isBasis` — a sheaf morphism that is an isomorphism on a
  basis is an isomorphism.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [Limits.HasColimits C] {X : TopCat.{v}}
  {FC : C → C → Type*} {CC : C → Type v} [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [Limits.PreservesFilteredColimits (CategoryTheory.forget C)]
  {B : Set (Opens X)}

/-- Surjectivity on stalks may be checked on a basis.

The mirror image of Mathlib's `stalkFunctor_map_injective_of_isBasis`: every germ is
represented by a section over a basic open (`germ_exist_of_isBasis`), and a surjection there
lifts it. -/
lemma stalkFunctor_map_surjective_of_isBasis (hB : Opens.IsBasis B)
    {F G : Presheaf C X} {α : F ⟶ G}
    (hα : ∀ U ∈ B, Function.Surjective (ConcreteCategory.hom (α.app (op U)))) (x : X) :
    Function.Surjective (ConcreteCategory.hom ((stalkFunctor C x).map α)) := by
  intro t
  obtain ⟨U, hxU, hU, s, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s', rfl⟩ := hα U hU s
  exact ⟨ConcreteCategory.hom (F.germ U x hxU) s', stalkFunctor_map_germ_apply U x hxU α s'⟩

end TopCat.Presheaf

namespace TopCat.Sheaf

/-- **A morphism of sheaves that is an isomorphism on a basis is an isomorphism.**

Checked on stalks: injectivity is Mathlib's `stalkFunctor_map_injective_of_isBasis` and
surjectivity is `stalkFunctor_map_surjective_of_isBasis` above.

The hypotheses are written out rather than taken from a `variable` block: `FC` and `CC` do
not appear in the statement, so `variable` auto-inclusion drops the `ConcreteCategory` and
`forget`-preservation binders along with them. -/
theorem isIso_of_isIso_app_of_isBasis
    {C : Type u} [Category.{v} C] [Limits.HasColimits C] {X : TopCat.{v}}
    {FC : C → C → Type*} {CC : C → Type v} [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [Limits.PreservesFilteredColimits (CategoryTheory.forget C)]
    [Limits.HasLimits C] [Limits.PreservesLimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {B : Set (Opens X)} (hB : Opens.IsBasis B) {F G : Sheaf C X} (α : F ⟶ G)
    (hα : ∀ U ∈ B, IsIso (α.hom.app (op U))) : IsIso α := by
  haveI : ∀ x : X, IsIso ((Presheaf.stalkFunctor C x).map α.hom) := fun x => by
    have hinj : Function.Injective
        (ConcreteCategory.hom ((Presheaf.stalkFunctor C x).map α.hom)) :=
      Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun U hU => by
        haveI := hα U hU
        exact ((ConcreteCategory.isIso_iff_bijective (α.hom.app (op U))).mp inferInstance).1) x
    have hsurj : Function.Surjective
        (ConcreteCategory.hom ((Presheaf.stalkFunctor C x).map α.hom)) :=
      Presheaf.stalkFunctor_map_surjective_of_isBasis hB (fun U hU => by
        haveI := hα U hU
        exact ((ConcreteCategory.isIso_iff_bijective (α.hom.app (op U))).mp inferInstance).2) x
    exact (ConcreteCategory.isIso_iff_bijective
      ((Presheaf.stalkFunctor C x).map α.hom)).mpr ⟨hinj, hsurj⟩
  exact Presheaf.isIso_of_stalkFunctor_map_iso α

end TopCat.Sheaf
