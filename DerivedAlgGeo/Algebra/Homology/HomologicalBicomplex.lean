/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalBicomplex
import DerivedAlgGeo.Algebra.Homology.Embedding.Extend

/-!
# Single complexes, arbitrary embeddings, and bicomplex symmetry

For any source and target complex shapes, source degree, embedding, and image
degree `j`, extending a single and mapping it degreewise along an independent
complex shape gives a bicomplex naturally isomorphic to the flipped single at
`j`. The comparison requires only zero morphisms and a zero object, and factors
through the arbitrary-shape mapped-single/flip isomorphism rather than a
definitional equality.

## Main results

* `HomologicalComplex₂.singleMapHomologicalComplexFlipIso` identifies the
  mapped-single and flipped-bicomplex functors for arbitrary complex shapes.
* `HomologicalComplex₂.singleExtendMapFlipIso` identifies an extended single
  at an arbitrary source degree with the flipped bicomplex at its image degree,
  for arbitrary source, target, and mapped complex shapes.

## Implementation notes

At each outer degree, the component is the inverse of Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` for the evaluation functor.
Differential compatibility splits the supported inner degree from the zero
ones. Naturality follows from that existing comparison. The arbitrary-image
embedding theorem composes the natural single-extension and flip isomorphisms.

## References

The proof uses Mathlib's `HomologicalComplex.singleMapHomologicalComplex`,
`HomologicalComplex.Hom.isoOfComponents`, `HomologicalComplex₂.flipFunctor`,
and the repository's `HomologicalComplex.singleCompExtendIso`.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {I J : Type*} (c₁ : ComplexShape I) (c₂ : ComplexShape J) [DecidableEq J]
variable (j₀ : J)

private noncomputable def singleMapHomologicalComplexFlipXIso
    (K : HomologicalComplex C c₁) (i : I) :
    (((HomologicalComplex.single C c₂ j₀).mapHomologicalComplex c₁).obj K).X i ≅
      (flip ((HomologicalComplex.single (HomologicalComplex C c₁) c₂ j₀).obj K)).X i :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (HomologicalComplex.eval C c₁ i) c₂ j₀).app K).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def singleMapHomologicalComplexFlipObjIso
    (K : HomologicalComplex C c₁) :
    ((HomologicalComplex.single C c₂ j₀).mapHomologicalComplex c₁).obj K ≅
      flip ((HomologicalComplex.single (HomologicalComplex C c₁) c₂ j₀).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (singleMapHomologicalComplexFlipXIso c₁ c₂ j₀ K) (by
      intro i i' hii'
      ext j
      by_cases hj : j = j₀
      · subst j
        simp [singleMapHomologicalComplexFlipXIso,
          HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
          HomologicalComplex.single_map_f_self, Category.assoc,
          HomologicalComplex.Hom.comm]
      · simp [singleMapHomologicalComplexFlipXIso,
          HomologicalComplex.singleMapHomologicalComplex_inv_app_ne _ _ hj])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The two functors package the complex indices differently, so this comparison
is not definitional. Its components use the inverse of
`HomologicalComplex.singleMapHomologicalComplex`; differential compatibility
reduces to the supported inner degree and its zero complement. -/
noncomputable def singleMapHomologicalComplexFlipIso :
    (HomologicalComplex.single C c₂ j₀).mapHomologicalComplex c₁ ≅
      HomologicalComplex.single (HomologicalComplex C c₁) c₂ j₀ ⋙
        flipFunctor C c₂ c₁ :=
  NatIso.ofComponents (singleMapHomologicalComplexFlipObjIso c₁ c₂ j₀) (by
    intro K L f
    apply HomologicalComplex.hom_ext
    intro i
    exact (HomologicalComplex.singleMapHomologicalComplex
      (HomologicalComplex.eval C c₁ i) c₂ j₀).inv.naturality f)

/-- Extending a single at source index `i` along `e` with `e.f i = j`, then
mapping along any independent complex shape `d`, is the flipped single at the
image index `j`. This composes the existing single-extension and flip
comparisons, without an additive or total-complex assumption. -/
noncomputable def singleExtendMapFlipIso
    {ι ι' κ : Type*} [DecidableEq ι] [DecidableEq ι']
    {c : ComplexShape ι} {c' : ComplexShape ι'} (d : ComplexShape κ)
    (e : c.Embedding c') (i : ι) (j : ι') (h : e.f i = j) :
    ((HomologicalComplex.single C c i ⋙ e.extendFunctor C).mapHomologicalComplex d) ≅
      HomologicalComplex.single (HomologicalComplex C d) c' j ⋙
        flipFunctor C c' d :=
  (CategoryTheory.NatIso.mapHomologicalComplex
    (HomologicalComplex.singleCompExtendIso (C := C) e i j h) d).trans
  (singleMapHomologicalComplexFlipIso (C := C) d c' j)

end HomologicalComplex₂
