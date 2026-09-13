/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopowerFunctor
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.Seam

/-!
# Scalar-linear copowers and the homotopy-category enhancement

The scalar-linear copower dg functor sends a homotopy equivalence of
coefficient complexes to an isomorphism between the selected copowers in
`H⁰`.  This leaf owns the comparison because it uses the specialized
equivalence between `H⁰(C^dg)` and Mathlib's homotopy category.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

/-- Homotopy equivalent coefficient complexes give isomorphic selected
scalar-linear copowers in `H⁰ C`.  The construction uses the established seam
`H⁰(C^dg) ≃ K(k)` rather than another quotient-category implementation. -/
noncomputable def linearCopowerObjIsoOfHomotopyEquiv (X : C)
    {K L : Cdg (ModuleCat.{v} k)}
    (e : HomotopyEquiv (Cdg.of _ K) (Cdg.of _ L)) :
    (show H0 C from linearCopowerObj (C := C) (Cdg.of _ K) X) ≅
      (show H0 C from linearCopowerObj (C := C) (Cdg.of _ L) X) :=
  (linearCopowerFunctor k X).h0.mapIso
    ((Cdg.h0Functor (A := ModuleCat.{v} k)).preimageIso
      (HomotopyCategory.isoOfHomotopyEquiv e))

end CategoryTheory
