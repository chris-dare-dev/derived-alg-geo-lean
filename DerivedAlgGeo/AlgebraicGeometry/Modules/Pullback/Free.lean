/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import DerivedAlgGeo.AlgebraicGeometry.Modules.StructureSheaf

/-!
# Pullback of free module sheaves

Pullback of module sheaves along a morphism of schemes sends the free sheaf `free I` to the free
sheaf `free I`, by Mathlib's `SheafOfModules.pullbackObjFreeIso`. This file restates that
isomorphism for module sheaves on schemes and proves its coherence with the unitor and the
compositor of pullback, `pullbackId` and `pullbackComp`. Both coherences reduce, on the
generators `ιFree i`, to the corresponding statements for the structure sheaf,
`pullbackObjUnitToUnit_id` and `pullbackObjUnitToUnit_comp`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`: `f^* (free I) ≅ free I`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullback_free_hom_ext`: a morphism out of the pullback of a
  free sheaf is determined by its restrictions to the generators.
* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_id`: along the identity it is the unitor.
* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_comp`: along `f ≫ g` it is the composite of
  the compositor with the isomorphisms along `g` and `f`.
-/

open CategoryTheory Limits SheafOfModules

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (I : Type u)

/-- The pullback of the free module sheaf on `I` along a morphism of schemes is the free module
sheaf on `I`. -/
noncomputable def pullbackFreeIso (f : X ⟶ Y) :
    (pullback f).obj (free I : Y.Modules) ≅ (free I : X.Modules) :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- The `i`-th generator of `f^* (free I)` goes, under `pullbackFreeIso`, to the `i`-th generator
of `free I`, through the comparison of the structure sheaves. -/
@[reassoc]
lemma pullback_map_ιFree_pullbackFreeIso_hom (f : X ⟶ Y) (i : I) :
    (pullback f).map (ιFree i) ≫ (pullbackFreeIso I f).hom =
      pullbackObjUnitToUnit f.toRingCatSheafHom ≫ ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i

/-- Two morphisms out of the pullback of a free module sheaf are equal when they agree on the
pulled-back generators. -/
lemma pullback_free_hom_ext (f : X ⟶ Y) {N : X.Modules}
    {a b : (pullback f).obj (free I : Y.Modules) ⟶ N}
    (h : ∀ i : I, (pullback f).map (ιFree i) ≫ a = (pullback f).map (ιFree i) ≫ b) : a = b :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback f) _ _
    (isColimitFreeCofan (R := Y.ringCatSheaf) I)) _ _ h

/-- Along the identity, `pullbackFreeIso` is the unitor of pullback. -/
lemma pullbackFreeIso_id :
    (pullbackFreeIso I (𝟙 X)).hom = (pullbackId X).hom.app (free I : X.Modules) := by
  apply pullback_free_hom_ext
  intro i
  rw [pullback_map_ιFree_pullbackFreeIso_hom, pullbackObjUnitToUnit_id]
  exact ((pullbackId X).hom.naturality (ιFree i)).symm

/-- Along `f ≫ g`, `pullbackFreeIso` is the compositor of pullback followed by `f^*` of the
isomorphism along `g` and the isomorphism along `f`. -/
lemma pullbackFreeIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackComp f g).inv.app (free I : Z.Modules) ≫ (pullback f).map (pullbackFreeIso I g).hom ≫
      (pullbackFreeIso I f).hom = (pullbackFreeIso I (f ≫ g)).hom := by
  apply pullback_free_hom_ext
  intro i
  rw [pullback_map_ιFree_pullbackFreeIso_hom, pullbackObjUnitToUnit_comp]
  have h := (pullbackComp f g).inv.naturality (ιFree i)
  simp only [Functor.comp_map] at h
  rw [reassoc_of% h, ← Functor.map_comp_assoc, pullback_map_ιFree_pullbackFreeIso_hom]
  simp [pullback_map_ιFree_pullbackFreeIso_hom]

end AlgebraicGeometry.Scheme.Modules
