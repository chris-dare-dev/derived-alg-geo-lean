/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model.Linear

/-!
# The scalar-linear Hom dg functor

For a fixed object `E` of a `k`-linear dg category, right composition assembles
the linear Hom-complexes `Hom(E, X)` into a `k`-linear dg functor to the
standard dg category of module-valued cochain complexes.

This is the right-adjoint-shaped half of the tensor--Hom interface.  The
adjunction itself belongs in `LinearCopowerAdjunction`, where scalar-linear
copowers are available.  No pretriangulated, cone, or finiteness assumptions
are needed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u w

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGLinear

variable (k : Type w) [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- For fixed `E`, the scalar-linear Hom-complex `Hom(E, -)` is a dg functor
to the standard dg category of `k`-module complexes. -/
def homFunctor (E : C) : DGFunctor C (Cdg (ModuleCat.{v} k)) where
  obj X := homComplex k E X
  map p := (postcompCochain k E p).toAddMonoidHom
  map_d p q f := by
    change postcompCochain k E q (((dgHom _ _).d p q).hom f) =
      CochainComplex.HomComplex.δ p q (postcompCochain k E p f)
    exact (postcompCochain_d k E p q f).symm
  map_id X := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    obtain rfl : j = i := by omega
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change (((postcompCochain k E 0) (dgId X)).v j j hij).hom g =
      ((CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (homComplex k E X))).v j j hij).hom g
    rw [postcompCochain_apply,
      CochainComplex.HomComplex.Cochain.ofHom_v, dgComp_id]
    rfl
  map_comp p q r hpq f g := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change dgComp i r j hij a (dgComp p q r hpq f g) =
      dgComp (i + p) q j (by omega)
        (dgComp i p (i + p) rfl a f) g
    exact (dgComp_assoc i p q (i + p) r j rfl hpq (by omega) a f g).symm

/-- Normalize object projections to the fixed-source Hom-complex.  This is a
simp lemma because objects have a canonical normal form; the map projection
below remains explicit so rewriting does not unfold abstract functor maps. -/
@[simp]
theorem homFunctor_obj (E X : C) : (homFunctor k E).obj X = homComplex k E X :=
  rfl

/-- The Hom dg functor acts on a homogeneous morphism by right
composition.  Kept out of the simp set to preserve the abstract functor-map
normal form. -/
theorem homFunctor_map (E : C) {X Y : C} (p : ℤ)
    (f : (dgHom X Y).X p) :
    (homFunctor k E).map p f = postcompCochain k E p f :=
  rfl

/-- The Hom dg functor preserves the scalar action. -/
instance homFunctor_linear (E : C) : (homFunctor k E).Linear k where
  map_smul p c f := (postcompCochain k E p).map_smul c f

end DGLinear

end CategoryTheory
