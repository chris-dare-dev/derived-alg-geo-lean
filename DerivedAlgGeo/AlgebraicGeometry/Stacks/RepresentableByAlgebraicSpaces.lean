/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.Basic
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representability

/-!
# Morphisms of stacks representable by algebraic spaces

A morphism `f : 𝒳 ⟶ 𝒴` of stacks in groupoids on `(Over S, fppf)` is representable by algebraic
spaces when its fibre functors are faithful and, for every object `y` of `𝒴` over `T : Over S`,
the presheaf of isomorphism classes of the fibre of `f` over `y` is an algebraic space over
`T.left` (Stacks 02ZW).

## Main definitions

* `AlgebraicGeometry.StackMorphism.fiberSpace`: the class presheaf
  `CategoryTheory.StackMorphism.fiberIsoClasses` of the fibre over `y`, read on `Over T.left`
  through `Over.iteratedSliceEquiv T`.
* `AlgebraicGeometry.StackMorphism.IsRepresentableByAlgebraicSpaces`: Stacks 02ZW.
* `AlgebraicGeometry.StackMorphism.IsRepresentableByAlgebraicSpacesWith`: Stacks 03YJ, a
  property of scheme morphisms measured on an étale surjective atlas of each fibre.

## Main results

* `AlgebraicGeometry.StackMorphism.IsRepresentable.isRepresentableByAlgebraicSpaces`: a morphism
  representable by schemes is representable by algebraic spaces.
* `AlgebraicGeometry.StackMorphism.HasRepresentableProperty.isRepresentableByAlgebraicSpacesWith`:
  a morphism representable by schemes with `P.over` is representable by algebraic spaces with `P`.

## Implementation notes

`fiberIsoClasses y` is a presheaf on `Over T` for `T : Over S`, while
`AlgebraicGeometry.isAlgebraicSpace` is defined on `Over T.left`. The two sites are identified by
`Over.iteratedSliceEquiv T`. The class presheaf lands in `Type (max u' v')`, the universe of the
objects of the fibre, which need not contain `Type u`; it is lifted to `Type (max u u' v')` and
compared with `AlgebraicGeometry.isULiftAlgebraicSpace`.

`CategoryTheory.StackMorphism` is an abbreviation for `Pseudofunctor.StrongTrans`, so dot notation
on a stack morphism does not reach the `AlgebraicGeometry.StackMorphism` namespace. The
predicates here are applied with explicit names, as is
`AlgebraicGeometry.StackMorphism.HasPointwiseRepresentableProperty`.

The agreement with the presheaf notion on discrete stacks
(`representableByAlgebraicSpaces S φ`, Stacks 02YQ) is not proved here. It needs the change of
base for algebraic spaces: an algebraic space over `S` with a map to `T` is the same as an
algebraic space over `T.left`.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW), Definition 94.9.1
* [Stacks Project, Tag 03YJ](https://stacks.math.columbia.edu/tag/03YJ), Section 94.10

## Tags

algebraic stack, algebraic space, representable morphism
-/

universe v' u' u

open CategoryTheory Opposite MorphismProperty

namespace AlgebraicGeometry

namespace StackMorphism

variable {S : Scheme.{u}}
  {𝒳 𝒴 : StackInGroupoids.{v', u, u', u + 1} (Over S) (Scheme.fppfTopology.over S)}
  (f : StackMorphism 𝒳 𝒴)

/-- The presheaf of isomorphism classes of the fibre of `f` over `y`, read on `Over T.left`
through `Over.iteratedSliceEquiv T` and lifted to `Type (max u u' v')`. -/
noncomputable abbrev fiberSpace {T : Over S} (y : 𝒴.presheaf.obj (.mk (op T))) :
    (Over T.left)ᵒᵖ ⥤ Type (max u u' v') :=
  (Over.iteratedSliceEquiv T).inverse.op ⋙ f.fiberIsoClasses y ⋙ uliftFunctor.{u}

/-- A morphism of stacks in groupoids on `(Over S, fppf)` is **representable by algebraic
spaces** (Stacks 02ZW) when its fibre functors are faithful and, for every object `y` of `𝒴`
over `T : Over S`, the presheaf of isomorphism classes of the fibre over `y`, read on
`Over T.left`, is an algebraic space over `T.left`.

Stacks 02ZW asks that the 2-fibre product `(Sch/T) ×_{y, 𝒴} 𝒳` be representable by an
algebraic space over `T`. As for `CategoryTheory.StackMorphism.IsRepresentable`, this is stated
through the fibre categories: the faithfulness of the fibre functors makes the fibres of the
2-fibre product setoids, and the algebraic space is its presheaf of isomorphism classes. The
equivalence with the form of Stacks 02ZW is not proved here. -/
def IsRepresentableByAlgebraicSpaces : Prop :=
  (∀ T, (f.app T).Faithful) ∧ ∀ ⦃T : Over S⦄ (y : 𝒴.presheaf.obj (.mk (op T))),
    isULiftAlgebraicSpace.{u, max u' v'} T.left (fiberSpace f y)

/-- A morphism of stacks is **representable by algebraic spaces with `P`** (Stacks 03YJ) when it
is representable by algebraic spaces and the fibre over every `y` admits an étale surjective
atlas `v : yoneda.obj V ⟶ F` from a scheme `V` over `T.left` whose structure morphism
`V.hom : V.left ⟶ T.left` has `P`.

Here `F` is an algebraic space over `T.left` whose lift to `Type (max u u' v')` is isomorphic to
`fiberSpace f y`. As in `AlgebraicGeometry.representableByAlgebraicSpacesWith`, the property is
measured on one atlas of each fibre, which is how Stacks 04RD induces properties of morphisms
of algebraic spaces from properties étale local on the source. -/
def IsRepresentableByAlgebraicSpacesWith (P : MorphismProperty Scheme.{u}) : Prop :=
  IsRepresentableByAlgebraicSpaces f ∧ ∀ ⦃T : Over S⦄ (y : 𝒴.presheaf.obj (.mk (op T))),
    ∃ (F : (Over T.left)ᵒᵖ ⥤ Type u) (_ : Nonempty (F ⋙ uliftFunctor.{max u' v'} ≅ fiberSpace f y))
      (V : Over T.left) (v : yoneda.obj V ⟶ F),
      (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf v ∧ P V.hom

variable {f}

theorem IsRepresentableByAlgebraicSpacesWith.isRepresentableByAlgebraicSpaces
    {P : MorphismProperty Scheme.{u}} (h : IsRepresentableByAlgebraicSpacesWith f P) :
    IsRepresentableByAlgebraicSpaces f :=
  h.1

/-- Weakening the property in `IsRepresentableByAlgebraicSpacesWith`. -/
theorem IsRepresentableByAlgebraicSpacesWith.mono {P Q : MorphismProperty Scheme.{u}}
    (h : IsRepresentableByAlgebraicSpacesWith f P) (hPQ : P ≤ Q) :
    IsRepresentableByAlgebraicSpacesWith f Q := by
  refine ⟨h.1, fun T y ↦ ?_⟩
  obtain ⟨F, e, V, v, hv, hP⟩ := h.2 y
  exact ⟨F, e, V, v, hv, hPQ _ hP⟩

variable {T : Over S} {y : 𝒴.presheaf.obj (.mk (op T))} {R : Over T}

/-- A representation of the class presheaf on `Over T` by `R` represents `fiberSpace f y` by
the image of `R` in `Over T.left`. -/
noncomputable def fiberSpaceRepresentableBy (e : (f.fiberIsoClasses y).RepresentableBy R) :
    (fiberSpace f y).RepresentableBy ((Over.iteratedSliceEquiv T).functor.obj R) where
  homEquiv {W} := ((Over.iteratedSliceEquiv T).symm.toAdjunction.homEquiv W R).symm.trans
    (e.homEquiv.trans Equiv.ulift.symm)
  homEquiv_comp {W W'} g k := by
    apply Equiv.ulift.injective
    simp only [Equiv.trans_apply, Functor.comp_map, Functor.op_map, uliftFunctor_map]
    erw [Adjunction.homEquiv_naturality_left_symm]
    exact e.homEquiv_comp _ _

/-- The fibre over `y` of a morphism represented at `y` by `R` is the scheme
`(Over.iteratedSliceEquiv T).functor.obj R`, up to universe lifting. -/
noncomputable def fiberSpaceIso (e : (f.fiberIsoClasses y).RepresentableBy R) :
    yoneda.obj ((Over.iteratedSliceEquiv T).functor.obj R) ⋙ uliftFunctor.{max u' v'} ≅
      fiberSpace f y :=
  Functor.RepresentableBy.equivUliftYonedaIso.{max u' v'} _ _ (fiberSpaceRepresentableBy e)

variable (f) in
/-- A morphism of stacks representable by schemes is representable by algebraic spaces: each
representing scheme is an algebraic space (Stacks 025Z). -/
theorem IsRepresentable.isRepresentableByAlgebraicSpaces [hf : f.IsRepresentable] :
    IsRepresentableByAlgebraicSpaces f := by
  refine ⟨hf.faithful, fun T y ↦ ?_⟩
  have := hf.representable y
  let e := (f.fiberIsoClasses y).representableBy
  exact ⟨_, isAlgebraicSpace_yoneda _ _, ⟨fiberSpaceIso e⟩⟩

/-- The identity of a represented presheaf is an étale surjective atlas. -/
private theorem presheaf_etale_surjective_id {X : Scheme.{u}} (V : Over X) :
    (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf (𝟙 (yoneda.obj V)) := by
  let P : MorphismProperty Scheme.{u} := @Etale ⊓ @Surjective
  have : P.IsMultiplicative := IsMultiplicative.inf (P := @Etale) (Q := @Surjective)
  have : RespectsIso (@Etale : MorphismProperty Scheme.{u}) := IsStableUnderBaseChange.respectsIso
  have : P.RespectsIso := RespectsIso.inf _ _
  have : (P.over (X := X)).IsMultiplicative :=
    inferInstanceAs (P.inverseImage (Over.forget X)).IsMultiplicative
  have : (P.over (X := X)).RespectsIso :=
    inferInstanceAs (P.inverseImage (Over.forget X)).RespectsIso
  exact MorphismProperty.id_mem _ _

variable (f) in
/-- A morphism of stacks representable by schemes whose representing morphisms have `P` is
representable by algebraic spaces with `P`: each representing scheme is its own atlas. -/
theorem HasRepresentableProperty.isRepresentableByAlgebraicSpacesWith
    (P : MorphismProperty Scheme.{u}) [hf : f.HasRepresentableProperty P.over] :
    IsRepresentableByAlgebraicSpacesWith f P := by
  refine ⟨IsRepresentable.isRepresentableByAlgebraicSpaces f, fun T y ↦ ?_⟩
  have := hf.isRepresentable.representable y
  let e := (f.fiberIsoClasses y).representableBy
  exact ⟨_, ⟨fiberSpaceIso e⟩, _, 𝟙 _, presheaf_etale_surjective_id _, hf.property y e⟩

end StackMorphism

end AlgebraicGeometry
