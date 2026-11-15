/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat

/-!
# The module pseudofunctor with values in adjunctions

The pseudofunctor `CommRingCat.moduleCatAdjPseudofunctor` sends a commutative ring `R` to the
category `ModuleCat R` and a ring map `φ : A ⟶ B` to the adjunction
`extendScalars φ ⊣ restrictScalars φ`.

Its source is `LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ`: it is a pseudofunctor on the opposite of
the site `CommRingCatᵒᵖ` of affine schemes, the shape the descent theory of
`Mathlib.CategoryTheory.Sites.Descent` uses. A ring map `φ` enters as `φ.op.op.toLoc`. The
pullback along `φ.op` is extension of scalars and the pushforward is restriction of scalars.

## Main definitions

* `CommRingCat.moduleCatAdjPseudofunctor`: the pseudofunctor to `Adj Cat`.

## Main results

* `CommRingCat.moduleCatAdjPseudofunctor_obj_obj`, `CommRingCat.moduleCatAdjPseudofunctor_map_l`:
  on objects and on left adjoints it agrees with Mathlib's `Cat`-valued
  `CommRingCat.moduleCatExtendScalarsPseudofunctor`.

## Implementation notes

The pseudofunctor is built with `LocallyDiscrete.mkPseudofunctor`, as Mathlib builds
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`. Its unitors and compositors pair
`extendScalarsId` with `restrictScalarsId` and `extendScalarsComp` with `restrictScalarsComp`.
Mathlib defines each extension isomorphism as the conjugate of the restriction isomorphism, which
is the compatibility `Adj.iso₂Mk` requires. The coherence conditions are checked on left
adjoints, where they are Mathlib's `extendScalars_assoc'`, `extendScalars_id_comp` and
`extendScalars_comp_id`.

## References

No literature source is followed; the construction mirrors Mathlib's
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`.

## Tags

module, extension of scalars, restriction of scalars, pseudofunctor, adjunction
-/

universe u

open CategoryTheory Bicategory Opposite ModuleCat

namespace CommRingCat

/-- `extendScalarsId` is the conjugate of `restrictScalarsId`. -/
private lemma conjugateEquiv_extendScalarsId_hom (R : CommRingCat.{u}) :
    conjugateEquiv CategoryTheory.Adjunction.id (extendRestrictScalarsAdj (RingHom.id R))
      (extendScalarsId R).hom = (restrictScalarsId R).inv := by
  simp [extendScalarsId, CategoryTheory.conjugateIsoEquiv]

/-- `extendScalarsComp` is the conjugate of `restrictScalarsComp`. -/
private lemma conjugateEquiv_extendScalarsComp_hom {R₁ R₂ R₃ : CommRingCat.{u}}
    (f₁₂ : R₁ ⟶ R₂) (f₂₃ : R₂ ⟶ R₃) :
    conjugateEquiv ((extendRestrictScalarsAdj f₁₂.hom).comp (extendRestrictScalarsAdj f₂₃.hom))
      (extendRestrictScalarsAdj (f₂₃.hom.comp f₁₂.hom)) (extendScalarsComp f₁₂.hom f₂₃.hom).hom =
      (restrictScalarsComp f₁₂.hom f₂₃.hom).inv := by
  simp [extendScalarsComp, CategoryTheory.conjugateIsoEquiv]

/-- The pseudofunctor from `LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ` to adjunctions which sends a
commutative ring `R` to `ModuleCat R` and a ring map `φ` to the adjunction
`extendScalars φ ⊣ restrictScalars φ`. It contains both the covariant (extension) and the
contravariant (restriction) functoriality of module categories. -/
noncomputable def moduleCatAdjPseudofunctor :
    LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ ⥤ᵖ Adj Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Adj.mk ↧(ModuleCat.{u} R.unop.unop))
    (fun f ↦ .mk (extendRestrictScalarsAdj f.unop.unop.hom).toCat)
    (fun R ↦ Adj.iso₂Mk (Cat.Hom.isoMk (extendScalarsId R.unop.unop))
      (Cat.Hom.isoMk (restrictScalarsId R.unop.unop).symm) (by
        ext1
        rw [toNatTrans_conjugateEquiv]
        exact conjugateEquiv_extendScalarsId_hom R.unop.unop))
    (fun f g ↦ Adj.iso₂Mk (Cat.Hom.isoMk (extendScalarsComp f.unop.unop.hom g.unop.unop.hom))
      (Cat.Hom.isoMk (restrictScalarsComp f.unop.unop.hom g.unop.unop.hom).symm) (by
        ext1
        rw [toNatTrans_conjugateEquiv, Adj.comp_adj, Adjunction.ofCat_comp]
        exact conjugateEquiv_extendScalarsComp_hom f.unop.unop g.unop.unop))
    (fun f g h ↦ by
      ext1
      ext1
      exact extendScalars_assoc' f.unop.unop.hom g.unop.unop.hom h.unop.unop.hom)
    (fun f ↦ by
      ext1
      ext1
      exact extendScalars_id_comp f.unop.unop.hom)
    (fun f ↦ by
      ext1
      ext1
      exact extendScalars_comp_id f.unop.unop.hom)

/-- On objects, `moduleCatAdjPseudofunctor` agrees with `moduleCatExtendScalarsPseudofunctor`. -/
@[simp]
lemma moduleCatAdjPseudofunctor_obj_obj (R : CommRingCat.{u}) :
    (moduleCatAdjPseudofunctor.obj (.mk (op (op R)))).obj =
      moduleCatExtendScalarsPseudofunctor.obj (.mk R) :=
  rfl

/-- On left adjoints, `moduleCatAdjPseudofunctor` agrees with
`moduleCatExtendScalarsPseudofunctor`. -/
@[simp]
theorem moduleCatAdjPseudofunctor_map_l {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (moduleCatAdjPseudofunctor.map φ.op.op.toLoc).l =
      moduleCatExtendScalarsPseudofunctor.map φ.toLoc :=
  rfl

end CommRingCat
