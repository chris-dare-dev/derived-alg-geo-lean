/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Basic

/-!
# Enhanced representatives and cones of ordinary morphisms

An enhancement `e : Enhancement W` presents an ordinary category `W` as the
homotopy category of a pretriangulated dg category.  Every ordinary morphism in
`W` therefore has a closed degree-zero representative between the chosen
inverse images of its endpoints, and that representative has a dg cone.

This file packages those two noncanonical choices once, independently of any
Fourier--Mukai, unit, or counit interpretation.  Conjugating the selected
representative by the counit of the comparison equivalence recovers the
original ordinary morphism.  No selected representative or cone is claimed
canonical, and no comparison between different selections is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace Enhancement

variable {W : Type u'} [Category.{v'} W]
  (e : Enhancement.{v, u} W)

/-- A noncanonical closed degree-zero representative of an ordinary morphism
between the chosen inverse images of its endpoints. -/
noncomputable def liftedCocycle {K L : W} (f : K ⟶ L) : cocycles
    (show e.dgCat from e.equiv.inverse.obj K)
    (show e.dgCat from e.equiv.inverse.obj L) :=
  (Z0.toH0 e.dgCat).preimage (e.equiv.inverse.map f)

/-- The selected cocycle represents the inverse image of the original
ordinary morphism in `H⁰` of the enhancement. -/
@[simp]
theorem homMk_liftedCocycle {K L : W} (f : K ⟶ L) :
    H0.homMk (C := e.dgCat) (e.liftedCocycle f) =
      e.equiv.inverse.map f :=
  (Z0.toH0 e.dgCat).map_preimage _

/-- Conjugating the selected representative by the counit of the enhancement
equivalence recovers the original ordinary morphism. -/
theorem counit_conjugate_liftedCocycle {K L : W} (f : K ⟶ L) :
    (e.equiv.counitIso.app K).inv ≫
        e.equiv.functor.map
          (H0.homMk (C := e.dgCat) (e.liftedCocycle f)) ≫
        (e.equiv.counitIso.app L).hom =
      f := by
  rw [e.homMk_liftedCocycle]
  rw [← cancel_epi (e.equiv.counitIso.app K).hom,
    Iso.hom_inv_id_assoc]
  exact e.equiv.counit_naturality f

/-- A noncanonically selected dg cone presentation of an ordinary morphism.

The source and target are the comparison equivalence's chosen inverse images,
the arrow is `liftedCocycle`, and pretriangulatedness supplies the cone. -/
noncomputable def conePresentation {K L : W} (f : K ⟶ L) :
    DGCategory.ConePresentation e.dgCat := by
  let hcone := IsPretriangulated.exists_cone
    (e.liftedCocycle f).1 (e.liftedCocycle f).2
  exact
    { source := H0.of e.dgCat (e.equiv.inverse.obj K)
      target := H0.of e.dgCat (e.equiv.inverse.obj L)
      arrow := e.liftedCocycle f
      cone := hcone.choose
      isCone := hcone.choose_spec.some }

@[simp]
theorem conePresentation_source {K L : W} (f : K ⟶ L) :
    (e.conePresentation f).source =
      H0.of e.dgCat (e.equiv.inverse.obj K) :=
  rfl

@[simp]
theorem conePresentation_target {K L : W} (f : K ⟶ L) :
    (e.conePresentation f).target =
      H0.of e.dgCat (e.equiv.inverse.obj L) :=
  rfl

@[simp]
theorem conePresentation_arrow {K L : W} (f : K ⟶ L) :
    (e.conePresentation f).arrow = e.liftedCocycle f :=
  rfl

/-- The arrow in the selected cone presentation represents the inverse image
of the original ordinary morphism. -/
@[simp]
theorem homMk_conePresentation_arrow {K L : W} (f : K ⟶ L) :
    H0.homMk (C := e.dgCat) (e.conePresentation f).arrow =
      e.equiv.inverse.map f :=
  e.homMk_liftedCocycle f

/-- Conjugating the arrow in the selected cone presentation recovers the
original ordinary morphism. -/
theorem counit_conjugate_conePresentation_arrow {K L : W} (f : K ⟶ L) :
    (e.equiv.counitIso.app K).inv ≫
        e.equiv.functor.map
          (H0.homMk (C := e.dgCat) (e.conePresentation f).arrow) ≫
        (e.equiv.counitIso.app L).hom =
      f :=
  e.counit_conjugate_liftedCocycle f

end Enhancement

end CategoryTheory
