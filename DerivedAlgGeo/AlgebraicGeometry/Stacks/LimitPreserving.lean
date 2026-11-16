/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable

/-!
# Limit-preserving stacks

A pseudofunctor `F` on `Over S`, for a scheme `S`, is limit preserving if for every cofiltered
diagram `D` of affine `S`-schemes with an affine limit `T`, the functor
`colim F(D i) ⥤ F(T)` is an equivalence (Stacks 07XL). A representable stack of a scheme
locally of finite presentation over `S` is limit preserving (Stacks 01ZC).

## Main definitions

* `CategoryTheory.Pseudofunctor.IsLimitPreservingAt`: the three conditions that make
  `colim F(D i) ⥤ F(c.pt)` an equivalence for one diagram `D` and one cone `c`.
* `CategoryTheory.Pseudofunctor.IsLimitPreserving`: the conditions for every cofiltered diagram
  of affine `S`-schemes and limit cone with an affine apex.
* `CategoryTheory.StackInGroupoids.IsLimitPreserving`: the property for a stack in groupoids.

## Main results

* `CategoryTheory.StackInGroupoids.isLimitPreserving_representable`: the stack represented by
  `T : Over S` with `T.hom` locally of finite presentation is limit preserving.

## Implementation notes

No colimit in `Cat` is built. The conditions of `IsLimitPreservingAt` say elementwise that the
functor from the 2-colimit is essentially surjective, full and faithful: every object over the
limit comes from a finite stage, and morphisms over the limit come from, and are equal at, a
finite stage. Morphisms are read in `Pseudofunctor.presheafHom`, whose restriction maps carry
the compositors of `F`.

Stacks indexes the systems by directed sets. Here they are indexed by any small cofiltered
category, as in Mathlib's `AlgebraicGeometry.Scheme.preservesColimit_yoneda`. So
`IsLimitPreserving` quantifies over at least the diagrams of Stacks 07XL, and asks no less.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)

## Tags

limit preserving, locally of finite presentation, cofiltered limit, stack
-/

universe w₁ w₂ w w' v' u' u

namespace CategoryTheory.Pseudofunctor

open AlgebraicGeometry Bicategory Limits Opposite

variable {S : Scheme.{u}} (F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The conditions of Stacks 07XL for one diagram `D : I ⥤ Over S` and one cone `c` over it:
the functor `colim F(D i) ⥤ F(c.pt)` is essentially surjective (`exists_obj`), full
(`exists_hom`) and faithful (`hom_ext`). The structure is stated for any cone; it is meaningful
when `I` is cofiltered and `c` is a limit. -/
structure IsLimitPreservingAt {I : Type w} [Category.{w'} I] (D : I ⥤ Over S) (c : Cone D) :
    Prop where
  /-- Essentially surjective: every object over `c.pt` is the pullback of an object over a
  finite stage. -/
  exists_obj (x : F.obj (.mk (op c.pt))) : ∃ (i : I) (xᵢ : F.obj (.mk (op (D.obj i)))),
    Nonempty ((F.map (c.π.app i).op.toLoc).toFunctor.obj xᵢ ≅ x)
  /-- Full: a morphism over `c.pt` between pullbacks of objects over `D.obj i` is the pullback of
  a morphism over a later stage. -/
  exists_hom (i : I) (x y : F.obj (.mk (op (D.obj i))))
    (φ : (F.presheafHom x y).obj (op (Over.mk (c.π.app i)))) :
    ∃ (j : I) (a : j ⟶ i) (ψ : (F.presheafHom x y).obj (op (Over.mk (D.map a)))),
      (F.presheafHom x y).map
        (Over.homMk (c.π.app j) (c.w a) : Over.mk (c.π.app i) ⟶ Over.mk (D.map a)).op ψ = φ
  /-- Faithful: two morphisms over a stage that agree over `c.pt` agree over a later stage. -/
  hom_ext (i : I) (x y : F.obj (.mk (op (D.obj i)))) {j : I} (a : j ⟶ i)
    (ψ₁ ψ₂ : (F.presheafHom x y).obj (op (Over.mk (D.map a))))
    (h : (F.presheafHom x y).map
        (Over.homMk (c.π.app j) (c.w a) : Over.mk (c.π.app i) ⟶ Over.mk (D.map a)).op ψ₁ =
      (F.presheafHom x y).map
        (Over.homMk (c.π.app j) (c.w a) : Over.mk (c.π.app i) ⟶ Over.mk (D.map a)).op ψ₂) :
    ∃ (k : I) (b : k ⟶ j),
      (F.presheafHom x y).map (Over.homMk (D.map b) (D.map_comp b a).symm :
          Over.mk (D.map (b ≫ a)) ⟶ Over.mk (D.map a)).op ψ₁ =
        (F.presheafHom x y).map (Over.homMk (D.map b) (D.map_comp b a).symm :
          Over.mk (D.map (b ≫ a)) ⟶ Over.mk (D.map a)).op ψ₂

/-- A pseudofunctor on `Over S` is limit preserving (Stacks 07XL) if, for every small cofiltered
diagram `D` of affine `S`-schemes and every limit cone `c` over it with an affine apex, the
functor `colim F(D i) ⥤ F(c.pt)` is an equivalence in the elementwise sense of
`Pseudofunctor.IsLimitPreservingAt`.

Stacks asks this for directed inverse systems, and these are among the cofiltered diagrams
quantified over here. The affineness hypotheses are Stacks'. -/
@[stacks 07XL]
def IsLimitPreserving : Prop :=
  ∀ ⦃I : Type u⦄ [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S) (c : Cone D),
    IsLimit c → (∀ i, IsAffine (D.obj i).left) → IsAffine c.pt.left → F.IsLimitPreservingAt D c

end CategoryTheory.Pseudofunctor

namespace CategoryTheory.StackInGroupoids

open AlgebraicGeometry Bicategory Limits Opposite

/-- A stack in groupoids on `Over S` is limit preserving (Stacks 07XL) if its pseudofunctor is,
in the sense of `Pseudofunctor.IsLimitPreserving`. -/
abbrev IsLimitPreserving {S : Scheme.{u}} {J : GrothendieckTopology (Over S)}
    (X : StackInGroupoids.{v', u, u', u + 1} (Over S) J) : Prop :=
  X.presheaf.IsLimitPreserving

/-- Two morphisms between pullbacks agree when the fibres are discrete. -/
private lemma presheafHom_obj_ext {C : Type*} [Category* C]
    {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [∀ X, IsDiscrete (F.obj X)] {X : C}
    {M N : F.obj (.mk (op X))} {W : (Over X)ᵒᵖ} (φ ψ : (F.presheafHom M N).obj W) : φ = ψ :=
  (IsDiscrete.subsingleton _ _).elim φ ψ

/-- The stack represented by `T : Over S`, with `T.hom` locally of finite presentation, is limit
preserving. This is the direction (1) ⇒ (2) of Stacks 01ZC, through Mathlib's
`AlgebraicGeometry.Scheme.preservesColimit_yoneda`.

The hypothesis `LocallyOfFinitePresentation T.hom` cannot be dropped. Let `S = Spec k`, let
`T = Spec k[x₁, x₂, …]`, and let `D` be the tower of the `Spec k[x₁, …, xₙ]`, whose limit is `T`.
The identity of `T` does not factor through any `Spec k[x₁, …, xₙ]`, so `exists_obj` fails for
the object `𝟙 T` over `T`. -/
@[stacks 01ZC]
theorem isLimitPreserving_representable {S : Scheme.{u}} (J : GrothendieckTopology (Over S))
    [J.Subcanonical] (T : Over S) [LocallyOfFinitePresentation T.hom] :
    (representable.{w₁, w₂} J T).IsLimitPreserving := by
  intro I _ _ D c hc hD _
  have (i : I) : CompactSpace (D.obj i).left := by
    have := hD i
    infer_instance
  have (i : I) : QuasiSeparatedSpace (D.obj i).left := by
    have := hD i
    infer_instance
  have {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f).left := by
    have := hD i
    have := hD j
    infer_instance
  have hcol := isColimitOfPreserves (yoneda.obj T) hc.op
  refine ⟨fun x ↦ ?_, fun i x y φ ↦ ?_, fun i x y j a ψ₁ ψ₂ _ ↦ ⟨j, 𝟙 j, presheafHom_obj_ext _ _⟩⟩
  · obtain ⟨g, rfl⟩ := (representableObjEquiv J).surjective x
    obtain ⟨⟨i⟩, gᵢ, hgᵢ⟩ := Types.jointly_surjective_of_isColimit hcol g
    exact ⟨i, representableObj J gᵢ, ⟨eqToIso (congrArg (representableObj J) hgᵢ)⟩⟩
  · obtain ⟨gx, rfl⟩ := (representableObjEquiv J).surjective x
    obtain ⟨gy, rfl⟩ := (representableObjEquiv J).surjective y
    have hφ : c.π.app i ≫ gx = c.π.app i ≫ gy :=
      representableObj_injective J (IsDiscrete.eq_of_hom φ)
    obtain ⟨⟨j⟩, ⟨a⟩, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcol (i := op i) gx gy).1 hφ
    exact ⟨j, a, eqToHom (congrArg (representableObj J) ha), presheafHom_obj_ext _ _⟩

end CategoryTheory.StackInGroupoids
