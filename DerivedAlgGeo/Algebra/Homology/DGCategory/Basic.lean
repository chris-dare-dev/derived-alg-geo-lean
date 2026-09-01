/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# DG categories

A dg category is a category whose hom-objects are cochain complexes of abelian
groups, with a composition that is biadditive, associative, unital, and
satisfies the Leibniz rule. `k`-linearity is a refinement, `DGLinear`, rather
than part of the definition.

## The encoding, and why it is this one

`ADR-0010` decides against `EnrichedOrdinaryCategory` over
`CochainComplex (ModuleCat k) ℤ`: at the pinned Mathlib revision
`HomologicalComplex.HasTensor` does not synthesize for the `ℤ`-indexed shape,
so there is no monoidal category available to enrich over. See
`.claude/notes/2026-08-13-dg-surface-reconnaissance.md`.

`ADR-0011` decides the remaining question — what the Hom-complexes are
complexes *of*. They are complexes of abelian groups, matching
`CochainComplex.HomComplex`, with `k`-linearity layered on top. The first draft
of this file used `ModuleCat k` and collided with that choice three times; the
ADR records all three.

Composition is a family of biadditive maps on the graded pieces rather than a
chain map out of a tensor product, because the tensor product of `ℤ`-indexed
complexes is exactly what the pin does not have.

## Sign convention

Composition is **diagrammatic**: `dgComp p q r h f g` is `f` then `g`, matching
`CochainComplex.HomComplex.Cochain.comp`. The Leibniz rule is

`δ (f · g) = f · (δ g) + (-1) ^ q • (δ f) · g`  for `g` of degree `q`,

which is `CochainComplex.HomComplex.δ_comp` at the pin, verbatim.

**There is a second, equally consistent convention** — `(δf) · g + (-1)^p · f · (δg)`,
the textbook graded anti-derivation — and it is *not* the one used here. The two
differ whenever `p` and `q` have different parities; at `p = q = 0` they agree,
which is exactly why the disagreement can hide. An earlier draft of this file
stated the textbook form while claiming to match Mathlib, and the claim survived
review until `dg-enhancements-e4` tried to build `C^dg` on it and could not.

Mathlib's form is adopted so that `HomComplex` instantiates this class directly,
which is the whole point of the `AddCommGrpCat`-valued `dgHom` (ADR-0011). A
divergence from it must be documented as a divergence rather than absorbed
silently.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u w


namespace CategoryTheory

/-- The data of a dg category on a type of objects `C`: a cochain complex of
abelian groups for each pair of objects, a degree-zero identity, and a
biadditive graded composition. -/
class DGCategoryStruct (C : Type u) where
  /-- The hom-complex between two objects. -/
  dgHom : C → C → CochainComplex AddCommGrpCat.{v} ℤ
  /-- The identity, a degree-zero element of the endomorphism complex. -/
  dgId (X : C) : (dgHom X X).X 0
  /-- Graded composition, additive in each variable. -/
  dgComp {X Y Z : C} (p q r : ℤ) (h : p + q = r) :
    (dgHom X Y).X p →+ (dgHom Y Z).X q →+ (dgHom X Z).X r

/-- A dg category: the data of `DGCategoryStruct` subject to associativity,
unitality, the identity being a cocycle, and the Leibniz rule. -/
class DGCategory (C : Type u) extends DGCategoryStruct.{v} C where
  dgComp_assoc {W X Y Z : C} (p q r pq qr pqr : ℤ)
      (hpq : p + q = pq) (hqr : q + r = qr) (hpqr : pq + r = pqr)
      (f : (dgHom W X).X p) (g : (dgHom X Y).X q) (h : (dgHom Y Z).X r) :
    dgComp pq r pqr (by omega) (dgComp p q pq hpq f g) h =
      dgComp p qr pqr (by omega) f (dgComp q r qr hqr g h)
  dgId_comp {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    dgComp 0 p p (zero_add p) (dgId X) f = f
  dgComp_id {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    dgComp p 0 p (add_zero p) f (dgId Y) = f
  dgId_cocycle (X : C) : ((dgHom X X).d 0 1).hom (dgId X) = 0
  dgComp_leibniz {X Y Z : C} (p q r r' : ℤ) (h : p + q = r) (hr : r + 1 = r')
      (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    ((dgHom X Z).d r r').hom (dgComp p q r h f g) =
      dgComp p (q + 1) r' (by omega) f (((dgHom Y Z).d q (q + 1)).hom g) +
        q.negOnePow • dgComp (p + 1) q r' (by omega)
          (((dgHom X Y).d p (p + 1)).hom f) g

end CategoryTheory
