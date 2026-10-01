/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Natural transformations into strict bicategories

Mathlib promotes an ordinary functor into a strict bicategory to a pseudofunctor on the locally
discrete source. This module promotes its natural transformations as well.

## Main definitions and results

* `CategoryTheory.NatTrans.toStrongTrans` promotes a natural transformation to a strong one.
* `CategoryTheory.NatTrans.toStrongTrans_app` identifies its component with the original one.

## Implementation notes

Strictness turns the coherence maps into equality-induced isomorphisms. The ordinary
naturality equality supplies the naturality 2-isomorphism, while the components remain
definitionally unchanged.

## References

Mathlib's `CategoryTheory/Bicategory/Functor/LocallyDiscrete.lean` defines
`CategoryTheory.Functor.toPseudofunctor'`, the promotion extended here.

## Tags

bicategories, locally discrete, natural transformations
-/

namespace CategoryTheory.NatTrans

open Bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Promote a natural transformation between ordinary functors into any
strict bicategory to a strong transformation of their promoted pseudofunctors.
The component at `T : LocallyDiscrete I` is `φ.app T.as` by definition. -/
@[simps app]
def toStrongTrans {I B : Type*} [Category* I] [Bicategory B] [Strict B]
    {F G : I ⥤ B} (φ : F ⟶ G) :
    Pseudofunctor.StrongTrans F.toPseudofunctor' G.toPseudofunctor' where
  app T := φ.app T.as
  naturality f := eqToIso (φ.naturality f.as)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    simp [Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete]
  naturality_id a := by
    simp [Functor.toPseudofunctor', Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  naturality_comp f g := by
    simp [Functor.toPseudofunctor', Strict.associator_eqToIso]

end CategoryTheory.NatTrans
