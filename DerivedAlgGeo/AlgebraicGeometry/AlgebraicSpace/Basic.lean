/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete

/-!
# Algebraic spaces over a scheme

An algebraic space over a scheme `S` (Stacks 025Y) is a presheaf of sets `F` on `Over S` such
that
1. `F` is a sheaf for the fppf topology;
2. the diagonal `F ⟶ F ⨯ F` is representable by schemes over `S`;
3. some scheme `U` over `S` admits a map `yoneda.obj U ⟶ F` whose base changes to schemes are
   étale and surjective.

Representability is Mathlib's `Functor.relativelyRepresentable yoneda`, and condition 3 is
Mathlib's `MorphismProperty.presheaf` for `(@Etale ⊓ @Surjective).over`. Algebraic spaces form
the full subcategory of presheaves cut out by these conditions, so their morphisms are natural
transformations (Stacks 0260).

## Main definitions

* `AlgebraicGeometry.isAlgebraicSpace S`: the property of presheaves on `Over S` of being an
  algebraic space.
* `AlgebraicGeometry.AlgebraicSpace S`: the category of algebraic spaces over `S`.
* `AlgebraicGeometry.AlgebraicSpace.ofScheme S`: schemes over `S` as algebraic spaces.
* `AlgebraicGeometry.AlgebraicSpace.toSheaf`, `AlgebraicGeometry.AlgebraicSpace.toStack`: the
  underlying fppf sheaf, and the discrete stack in groupoids it determines.
* `AlgebraicGeometry.isULiftAlgebraicSpace S`: presheaves in a larger universe that are
  algebraic spaces up to `ULift`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_yoneda`, `AlgebraicSpace.fullyFaithfulOfScheme`: every
  scheme over `S` is an algebraic space (Stacks 025Z), fully faithfully.
* `AlgebraicGeometry.relativelyRepresentable_of_isAlgebraicSpace`: every map from a scheme to an
  algebraic space is representable.

## Implementation notes

**Universes.** Algebraic spaces over `S : Scheme.{u}` are `Type u`-valued presheaves on
`Over S`. This is the universe in which `yoneda : Over S ⥤ (Over S)ᵒᵖ ⥤ Type u` lands, so Mathlib's
`Functor.relativelyRepresentable`, `MorphismProperty.presheaf` and
`Scheme.LocalRepresentability` apply verbatim. The consequences:
1. **No sheafification in `Type u`.** Mathlib supplies sheafification on a site
   `C : Type u₁` with morphisms in `Type v₁` for `Type (max u₁ v₁)`-valued presheaves
   (`HasSheafify J (Type (max u v))`, `Mathlib/CategoryTheory/Sites/LeftExact.lean:313`). For
   `Over S` that universe is `Type (u+1)`. Quotients `U/R` by étale equivalence relations
   (Stacks 02WW) and the étale-topology definition (Stacks 076L) are therefore not constructed
   here: algebraic spaces enter as targets.
2. **Larger universes enter by `ULift`.** A presheaf valued in `Type (max u w)`, such as an
   `Isom` sheaf of a stack with large fibres or a `Type (u+1)` sheafification, is an algebraic
   space when it is isomorphic to `F ⋙ uliftFunctor.{w}` for an algebraic space `F`. This is
   `AlgebraicGeometry.isULiftAlgebraicSpace`.
3. **Stacks.** The discrete stack of an algebraic space has fibres in `Cat.{u, u}`, the
   universe of representable stacks. It reaches larger fibre universes by the same universe lift
   as representable stacks.
4. **Base.** Stacks and spaces over `S` live on `Over S`. Absolute algebraic spaces take for `S`
   the terminal scheme `Spec ℤ` (`AlgebraicGeometry.specZIsTerminal`). The comparison with
   presheaves on `Scheme` over `yoneda.obj S` is the discrete case of the comparison between
   stacks on `Over S` and stacks on `Scheme` over `yoneda.obj S`, and is not made here.

## References

* [Stacks, Section 65.6 (Tag 025X)](https://stacks.math.columbia.edu/tag/025X)

## Tags

algebraic space, representable morphism, étale atlas, fppf sheaf
-/

universe u w

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- A presheaf of sets on `Over S` is an **algebraic space** over `S` (Stacks 025Y) when it is an
fppf sheaf, its diagonal is representable by schemes over `S`, and some scheme over `S` maps to it
by a morphism whose base changes to schemes over `S` are étale and surjective. -/
def isAlgebraicSpace : ObjectProperty ((Over S)ᵒᵖ ⥤ Type u) := fun F ↦
  Presieve.IsSheaf (Scheme.fppfTopology.over S) F ∧
  yoneda.relativelyRepresentable (Limits.diag F) ∧
  ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
    (@Etale ⊓ @Surjective : MorphismProperty Scheme).over.presheaf p

instance : (isAlgebraicSpace S).IsClosedUnderIsomorphisms where
  of_iso {F G} e := by
    rintro ⟨hs, hd, U, p, hp⟩
    refine ⟨Presieve.isSheaf_iso _ e hs, ?_, U, p ≫ e.hom, RespectsIso.postcomp _ e.hom p hp⟩
    rw [Functor.relativelyRepresentable.diag_iff] at hd ⊢
    intro a g
    rw [← Category.comp_id g, ← e.inv_hom_id, ← Category.assoc]
    exact comp_mem _ _ _ (hd _) (Functor.relativelyRepresentable.of_isIso _ _)

/-- The category of algebraic spaces over `S`: the full subcategory of presheaves on `Over S`
cut out by `AlgebraicGeometry.isAlgebraicSpace`, so morphisms are natural transformations
(Stacks 0260). -/
abbrev AlgebraicSpace := (isAlgebraicSpace S).FullSubcategory

/-- Every scheme over `S` is an algebraic space over `S` (Stacks 025Z). -/
theorem isAlgebraicSpace_yoneda (X : Over S) : isAlgebraicSpace S (yoneda.obj X) := by
  refine ⟨GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _, ?_, X, 𝟙 _, ?_⟩
  · rw [Functor.relativelyRepresentable.diag_iff]
    intro a g
    obtain ⟨f, rfl⟩ := yoneda.map_surjective g
    exact Functor.relativelyRepresentable.map yoneda f
  · let P : MorphismProperty Scheme.{u} := @Etale ⊓ @Surjective
    have : P.IsMultiplicative := IsMultiplicative.inf (P := @Etale) (Q := @Surjective)
    have : RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      IsStableUnderBaseChange.respectsIso
    have : P.RespectsIso := RespectsIso.inf _ _
    have : (P.over (X := S)).IsMultiplicative :=
      inferInstanceAs (P.inverseImage (Over.forget S)).IsMultiplicative
    have : (P.over (X := S)).RespectsIso :=
      inferInstanceAs (P.inverseImage (Over.forget S)).RespectsIso
    exact MorphismProperty.id_mem _ _

/-- Schemes over `S` as algebraic spaces over `S` (Stacks 025Z). -/
@[simps! obj_obj]
def AlgebraicSpace.ofScheme : Over S ⥤ AlgebraicSpace S :=
  (isAlgebraicSpace S).lift yoneda (isAlgebraicSpace_yoneda S)

/-- Schemes over `S` form a full subcategory of algebraic spaces over `S`. -/
def AlgebraicSpace.fullyFaithfulOfScheme : (AlgebraicSpace.ofScheme S).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (isAlgebraicSpace S).ι) Yoneda.fullyFaithful

instance : (AlgebraicSpace.ofScheme S).Full :=
  (AlgebraicSpace.fullyFaithfulOfScheme S).full

instance : (AlgebraicSpace.ofScheme S).Faithful :=
  (AlgebraicSpace.fullyFaithfulOfScheme S).faithful

variable {S}

/-- Every map from a scheme to an algebraic space is representable.

Only the diagonal condition of `AlgebraicGeometry.isAlgebraicSpace` is used: by
`Functor.relativelyRepresentable.diag_iff`, the conclusion for all `U` and `g` is equivalent to
it. -/
theorem relativelyRepresentable_of_isAlgebraicSpace {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : isAlgebraicSpace S F) {U : Over S} (g : yoneda.obj U ⟶ F) :
    yoneda.relativelyRepresentable g :=
  Functor.relativelyRepresentable.of_diag hF.2.1 g

/-- The fppf sheaf underlying an algebraic space. -/
def AlgebraicSpace.toSheaf (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨X.obj, (isSheaf_iff_isSheaf_of_type _ _).2 X.property.1⟩

/-- The stack in discrete groupoids on `(Over S, fppf)` determined by an algebraic space. -/
def AlgebraicSpace.toStack (X : AlgebraicSpace S) :
    StackInGroupoids.{u, u} (Over S) (Scheme.fppfTopology.over S) :=
  stackInGroupoidsOfSheaf _ X.obj X.property.1

variable (S)

/-- A presheaf on `Over S` valued in `Type (max u w)` is an algebraic space up to `ULift` when it
is isomorphic to `F ⋙ uliftFunctor.{w}` for an algebraic space `F` over `S`. -/
def isULiftAlgebraicSpace : ObjectProperty ((Over S)ᵒᵖ ⥤ Type (max u w)) := fun G ↦
  ∃ F : (Over S)ᵒᵖ ⥤ Type u, isAlgebraicSpace S F ∧ Nonempty (F ⋙ uliftFunctor.{w} ≅ G)

instance : (isULiftAlgebraicSpace.{u, w} S).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨F, hF, ⟨e'⟩⟩ ↦ ⟨F, hF, ⟨e' ≪≫ e⟩⟩

variable {S} in
/-- The `ULift` of an algebraic space is an algebraic space up to `ULift`. -/
theorem isULiftAlgebraicSpace_comp_uliftFunctor {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : isAlgebraicSpace S F) : isULiftAlgebraicSpace.{u, w} S (F ⋙ uliftFunctor.{w}) :=
  ⟨F, hF, ⟨Iso.refl _⟩⟩

/-- In the universe of `S`, an algebraic space up to `ULift` is an algebraic space. -/
theorem isULiftAlgebraicSpace_zero_iff (G : (Over S)ᵒᵖ ⥤ Type u) :
    isULiftAlgebraicSpace.{u, 0} S G ↔ isAlgebraicSpace S G := by
  let e (F : (Over S)ᵒᵖ ⥤ Type u) : F ⋙ uliftFunctor.{0} ≅ F :=
    NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso)
  refine ⟨fun ⟨F, hF, ⟨e'⟩⟩ ↦ (isAlgebraicSpace S).prop_of_iso ((e F).symm ≪≫ e') hF,
    fun hG ↦ ⟨G, hG, ⟨e G⟩⟩⟩

end AlgebraicGeometry
