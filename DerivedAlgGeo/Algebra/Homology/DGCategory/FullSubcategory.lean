/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Linear

/-!
# Full dg subcategories

`dg-enhancements-e8`, part one. Given a dg category `C` and a predicate `P` on
its objects, the objects satisfying `P` form a dg category whose Hom-complexes
are the ambient ones, unchanged.

## Why this is a root rather than a one-off

The derived dg enhancement is the full dg subcategory of `C^dg A` on the
K-injective complexes, and its dual is the one on the K-projective complexes.
Neither is a new dg category: both are `C^dg A` with its objects cut down, and
writing either one directly would duplicate five axiom proofs that have nothing
to do with resolutions. `HomotopyCategory/DGEnhancement/KInjective.lean` and
`HomotopyCategory/DGEnhancement/KProjective.lean` are the two consumers, and
they supply only the predicate.

## The construction is definitional, and that is the point

`dgHom X Y` is `dgHom X.obj Y.obj` **by definition**, not up to an isomorphism
that later files would have to transport along. So is `dgId`, and so is
`dgComp`. Every field of `DGCategory` is therefore the ambient field applied,
and every axiom is the ambient axiom applied -- there is no sign, no
re-association, and no `AddMonoidHom` to rebuild. Contrast `Product.lean`,
where the Hom-complex is a genuinely new complex and the file is four times
this length.

Two consequences worth stating, because later files rely on both:

* the inclusion `iota` has `AddMonoidHom.id` for its action on Hom-complexes,
  so it is faithful and full in every degree on the nose (`iota_map_apply`,
  which is deliberately not `@[simp]` -- see its docstring);
* `DGLinear` transfers with no new module structure, because the graded pieces
  are literally the same abelian groups (`homModule`, `linear`, and
  `iota_map_smul` as the test).

## Why there are no `@[simp]` lemmas for the identifications

The obvious candidates -- `dgHom X Y = dgHom X.obj Y.obj` and its siblings --
have the same head symbol on both sides and differ only in the
`DGCategoryStruct` instance. `simp`'s discrimination tree does not separate
those reliably, so tagging them invites a loop for no gain: every one of them
is `rfl`, and a goal that needs one is discharged by `rfl`, `exact`, or `show`.
The lemmas are stated anyway, named, so that a reader can see the
identification and cite it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u w

namespace CategoryTheory

open DGCategoryStruct

/-- The objects of a dg category satisfying a predicate `P`.

A `def` on `Subtype P` rather than an abbreviation, so that the `DGCategory`
instance below attaches here and not to `Subtype` generally. -/
def DGFullSubcategory {C : Type u} (P : C → Prop) : Type u := {X : C // P X}

namespace DGFullSubcategory

variable {C : Type u} {P : C → Prop}

/-! ### The objects

These five need no dg structure at all, so they are stated before `C` acquires
one. Keeping them outside the `[DGCategory C]` scope is not cosmetic: the
`unusedSectionVars` linter runs library-wide in CI and fails on an
automatically included instance a declaration does not use. -/

/-- The underlying ambient object. -/
def obj (X : DGFullSubcategory P) : C := X.1

/-- The underlying object satisfies the defining predicate. -/
lemma prop (X : DGFullSubcategory P) : P X.obj := X.2

/-- An ambient object satisfying `P`, as an object of the full dg
subcategory. -/
def mk (X : C) (hX : P X) : DGFullSubcategory P := ⟨X, hX⟩

/-- `mk` and `obj` are inverse on objects. -/
@[simp]
lemma obj_mk (X : C) (hX : P X) : (mk X hX).obj = X := rfl

/-- Two objects of the full dg subcategory agree as soon as their ambient
objects do; `P` is a `Prop`, so there is nothing else to check. -/
@[ext]
lemma ext {X Y : DGFullSubcategory P} (h : X.obj = Y.obj) : X = Y := Subtype.ext h

variable [DGCategory.{v} C]

/-- The Hom-complexes, identity and composition are the ambient ones. -/
instance struct : DGCategoryStruct.{v} (DGFullSubcategory P) where
  dgHom X Y := dgHom X.obj Y.obj
  dgId X := dgId X.obj
  dgComp p q r h := dgComp p q r h

/-! ### The identifications

All three are `rfl`. See the module docstring on why none is `@[simp]`. -/

/-- The Hom-complex is the ambient one. -/
lemma dgHom_eq (X Y : DGFullSubcategory P) :
    dgHom X Y = dgHom X.obj Y.obj := rfl

/-- The identity is the ambient one. -/
lemma dgId_eq (X : DGFullSubcategory P) :
    dgId X = dgId X.obj := rfl

/-- Graded composition is the ambient one. -/
lemma dgComp_eq {X Y Z : DGFullSubcategory P} (p q r : ℤ) (h : p + q = r)
    (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h f g =
      dgComp (X := X.obj) (Y := Y.obj) (Z := Z.obj) p q r h f g := rfl

/-- The full dg subcategory is a dg category. Every axiom is the ambient axiom
applied to the ambient objects; nothing is reproved. -/
instance dgCategory : DGCategory.{v} (DGFullSubcategory P) where
  dgComp_assoc p q r pq qr pqr hpq hqr hpqr f g h :=
    DGCategory.dgComp_assoc p q r pq qr pqr hpq hqr hpqr f g h
  dgId_comp p f := DGCategory.dgId_comp p f
  dgComp_id p f := DGCategory.dgComp_id p f
  dgId_cocycle X := DGCategory.dgId_cocycle X.obj
  dgComp_leibniz p q r r' h hr f g := DGCategory.dgComp_leibniz p q r r' h hr f g

/-! ### The identity and composition tests

The two laws that would be wrong if the instance above had transported
anything rather than reusing it. Both are `rfl`, and that they are `rfl` is the
claim. -/

/-- **The identity test.** `dgId` is a left unit for `dgComp`, by the ambient
unit law rather than a transported one. -/
lemma dgId_comp_eq {X Y : DGFullSubcategory P} (p : ℤ) (f : (dgHom X Y).X p) :
    dgComp 0 p p (zero_add p) (dgId X) f = f :=
  DGCategory.dgId_comp p f

/-- **The composition test.** `dgId` is a right unit for `dgComp`, likewise. -/
lemma dgComp_id_eq {X Y : DGFullSubcategory P} (p : ℤ) (f : (dgHom X Y).X p) :
    dgComp p 0 p (add_zero p) f (dgId Y) = f :=
  DGCategory.dgComp_id p f

/-! ### The inclusion -/

/-- The inclusion of a full dg subcategory into its ambient dg category. Its
action on Hom-complexes is the identity. -/
def iota (P : C → Prop) : DGFunctor (DGFullSubcategory P) C where
  obj X := X.obj
  map _ := AddMonoidHom.id _
  map_d _ _ _ := rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- The inclusion sends an object to its ambient object. -/
@[simp]
lemma iota_obj (X : DGFullSubcategory P) : (iota P).obj X = X.obj := rfl

/-- The inclusion acts as the identity on every graded piece of every
Hom-complex. This is the precise form of "full and faithful" available here:
`DGFunctor` has no fullness or faithfulness class, and for this functor the
statement is stronger than either would be.

Not `@[simp]`, and the reason is `iota_obj` above. That lemma rewrites
`(iota P).obj X` to `X.obj` -- including inside the *type* of this one's
left-hand side, which mentions `dgHom ((iota P).obj X) ((iota P).obj Y)`. The
left-hand side is therefore never in simp-normal form and `simpNF` rejects the
attribute. Keep the attribute on the `obj` lemma, drop it on the `map` one,
and name this lemma explicitly in the `simp only` sets that need it. -/
lemma iota_map_apply {X Y : DGFullSubcategory P} (p : ℤ) (f : (dgHom X Y).X p) :
    (iota P).map p f = f := rfl

/-! ### Linearity

No module structure is introduced. The graded pieces of the Hom-complexes are
the ambient ones, so the ambient `Module k` instances are the instances, and
each `DGLinear` axiom is the ambient axiom applied. -/

section Linear

variable (k : Type w) [CommRing k]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]

/-- The ambient module structure, seen through the subtype. -/
instance homModule (X Y : DGFullSubcategory P) (p : ℤ) :
    Module k ((dgHom X Y).X p) :=
  inferInstanceAs (Module k ((dgHom X.obj Y.obj).X p))

/-! **The scalar-compatibility test, and why it is not a lemma.**

The statement one reaches for first -- that the subcategory's action on
`(dgHom X Y).X p` is the ambient action on `(dgHom X.obj Y.obj).X p` -- cannot
be written down usefully. Both sides elaborate to the *same term*, so the
`simpNF` linter rejects it with "LHS equals RHS syntactically", and it is
right to: a lemma that is `rfl` with no change of spelling records nothing.

That there is nothing to record is the claim. A transported module structure
would need such a lemma; this one does not, because it is the ambient
structure. What does carry content is that the inclusion preserves scalars,
and that is `iota_linear` below with `iota_map_smul` reading it back. -/

variable [DGLinear k C]

/-- A full dg subcategory of a `k`-linear dg category is `k`-linear.

Each field names the ambient dg category explicitly with `(C := C)`. Without
it, Lean reads the dg category off the type of `f`, which is the subcategory,
and then tries to synthesize the very instance being defined. -/
instance linear : DGLinear k (DGFullSubcategory P) where
  d_smul p q c f := DGLinear.d_smul (C := C) (k := k) p q c f
  comp_smul_left p q r h c f g :=
    DGLinear.comp_smul_left (C := C) (k := k) p q r h c f g
  comp_smul_right p q r h c f g :=
    DGLinear.comp_smul_right (C := C) (k := k) p q r h c f g

/-- The inclusion is `k`-linear. -/
instance iota_linear : (iota P).Linear k where
  map_smul _ _ _ := rfl

/-- **The scalar-compatibility test.** The inclusion preserves scalar
multiplication in every degree. Unlike the identity that the section comment
above declines to state, this one is not `rfl` on the nose: the two sides
differ by where the identity `AddMonoidHom` sits. -/
lemma iota_map_smul {X Y : DGFullSubcategory P} (p : ℤ) (c : k)
    (f : (dgHom X Y).X p) :
    (iota P).map p (c • f) = c • (iota P).map p f :=
  DGFunctor.map_smul (F := iota P) p c f

end Linear

end DGFullSubcategory

end CategoryTheory
