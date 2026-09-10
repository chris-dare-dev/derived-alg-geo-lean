/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Whiskering

/-!
# Horizontal composition of homogeneous dg natural transformations

The Godement product of `α : F ⟶ F'` of degree `n` and `β : G ⟶ G'` of degree
`m` is a transformation `F ⋙ G ⟶ F' ⋙ G'` of degree `n + m`.  Whiskering
supplies the two halves and `HomogeneousNatTrans.interchange` says the two
possible readings differ by `(-1)^(m * n)`, so a choice has to be made.

## The choice, and what it costs

`hcomp` is the reading that whiskers `α` first:

`α ⋆ β := (α ◁ G) ≫ (F' ▷ β)`.

Nothing forces this over the other order, and `hcomp_eq_smul_swap` records
the price of swapping.  What the choice buys is that the two unit laws come
out as the two whiskerings with no sign at all (`id_hcomp`, `hcomp_id`), and
that the Leibniz rule below has its sign on the term where the repository's
`dgComp` convention already puts it.

## The Leibniz rule is the point

`hcomp` is vertical composition in the dg category of dg functors, applied to
two whiskerings, and whiskering commutes with the differential.  So the
differential of a Godement product obeys the graded Leibniz rule of that dg
category:

`δ (α ⋆ β) = α ⋆ δβ + (-1)^m • (δα ⋆ β)`.

That is `differential_hcomp`, and it is what makes horizontal composition a
dg-level operation rather than a bookkeeping convenience: it says the product
of two closed transformations is closed (`IsClosed.hcomp`) and that a
homotopy in either argument produces a homotopy of the product.

## Strictness

Dg functors compose strictly (`DGFunctor.comp_assoc`, `DGFunctor.id_comp`,
`DGFunctor.comp_id`, all `rfl`), so `hcomp_assoc` is an equation between
transformations of the same type rather than a coherence isomorphism, and the
unit laws need no comparison either.  Only the degrees have to be threaded,
which is why every statement below carries its result degree explicitly, as
`HomogeneousNatTrans.composition` does.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u'' u'''

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor.HomogeneousNatTrans

variable {C : Type u} {D : Type u'} {E : Type u''} {B : Type u'''}
  [DGCategory.{v} C] [DGCategory.{v} D] [DGCategory.{v} E] [DGCategory.{v} B]

section Hcomp

variable {F F' : DGFunctor C D} {G G' : DGFunctor D E} {n m : ℤ}

/-- **The Godement product.**

`α` is whiskered on the right by `G`, `β` on the left by `F'`, and the two are
composed vertically in the result degree `r`.  See `hcomp_eq_smul_swap` for
the other reading. -/
def hcomp (α : HomogeneousNatTrans F F' n) (β : HomogeneousNatTrans G G' m)
    (r : ℤ) (h : n + m = r) : HomogeneousNatTrans (F.comp G) (F'.comp G') r :=
  composition (F.comp G) (F'.comp G) (F'.comp G') n m r h
    (whiskerRight α G) (whiskerLeft F' β)

@[simp]
theorem hcomp_app (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) (X : C) :
    app (hcomp α β r h) X =
      dgComp n m r h (G.map n (app α X)) (app β (F'.obj X)) := by
  rw [hcomp, composition_apply_app, whiskerRight_app, whiskerLeft_app]
  rfl

/-- **Swapping the order of the product costs `(-1)^(m * n)`.**

This is `interchange`, read as a statement about `hcomp`.  The sign is graded
naturality of `β` evaluated at the degree-`n` component of `α`, so it is not a
convention: whichever reading is taken as the definition, the other one
carries that factor. -/
theorem hcomp_eq_smul_swap (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) (h' : m + n = r) :
    hcomp α β r h =
      (m * n).negOnePow •
        composition (F.comp G) (F.comp G') (F'.comp G') m n r h'
          (whiskerLeft F β) (whiskerRight α G') :=
  interchange α β r h h'

/-- The componentwise form of `hcomp_eq_smul_swap`. -/
theorem hcomp_app_swap (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) (h' : m + n = r)
    (X : C) :
    app (hcomp α β r h) X =
      (m * n).negOnePow •
        dgComp m n r h' (app β (F.obj X)) (G'.map n (app α X)) := by
  rw [hcomp_app, interchange_app α β r h h']

/-! ### Additivity in each argument -/

@[simp]
theorem hcomp_zero_left (β : HomogeneousNatTrans G G' m) (r : ℤ)
    (h : n + m = r) :
    hcomp (0 : HomogeneousNatTrans F F' n) β r h = 0 := by
  rw [hcomp, whiskerRight_zero, map_zero, AddMonoidHom.zero_apply]

@[simp]
theorem hcomp_zero_right (α : HomogeneousNatTrans F F' n) (r : ℤ)
    (h : n + m = r) :
    hcomp α (0 : HomogeneousNatTrans G G' m) r h = 0 := by
  rw [hcomp, whiskerLeft_zero, map_zero]

theorem hcomp_add_left (α α' : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) :
    hcomp (α + α') β r h = hcomp α β r h + hcomp α' β r h := by
  rw [hcomp, hcomp, hcomp, whiskerRight_add, map_add, AddMonoidHom.add_apply]

theorem hcomp_add_right (α : HomogeneousNatTrans F F' n)
    (β β' : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) :
    hcomp α (β + β') r h = hcomp α β r h + hcomp α β' r h := by
  rw [hcomp, hcomp, hcomp, whiskerLeft_add, map_add]

/-- Horizontal composition as a biadditive map, in a fixed result degree. -/
def horizontalComposition (F F' : DGFunctor C D) (G G' : DGFunctor D E)
    (n m r : ℤ) (h : n + m = r) :
    HomogeneousNatTrans F F' n →+
      HomogeneousNatTrans G G' m →+
        HomogeneousNatTrans (F.comp G) (F'.comp G') r :=
  AddMonoidHom.mk'
    (fun α => AddMonoidHom.mk' (fun β => hcomp α β r h) (hcomp_add_right α · · r h))
    (fun α α' => by
      apply AddMonoidHom.ext
      intro β
      exact hcomp_add_left α α' β r h)

@[simp]
theorem horizontalComposition_apply (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) :
    horizontalComposition F F' G G' n m r h α β = hcomp α β r h :=
  rfl

/-! ### Units -/

/-- Horizontally composing with an identity on the left is left whiskering.
No sign appears, which is one reason to take this order as the definition. -/
@[simp]
theorem id_hcomp (F : DGFunctor C D) (β : HomogeneousNatTrans G G' m) :
    hcomp (id F) β m (zero_add m) = whiskerLeft F β := by
  -- `whiskerRight (id F) G` is the identity, and what is left is the unit law
  -- of the dg category of dg functors, whose `dgId` and `dgComp` are `id` and
  -- `composition`.  Working there rather than componentwise avoids a goal that
  -- mixes `(F.comp G).obj X` with `G.obj (F.obj X)`.
  rw [hcomp, whiskerRight_id]
  exact dgId_comp (C := DGFunctor C E) m (whiskerLeft F β)

/-- Horizontally composing with an identity on the right is right
whiskering. -/
@[simp]
theorem hcomp_id (α : HomogeneousNatTrans F F' n) (G : DGFunctor D E) :
    hcomp α (id G) n (add_zero n) = whiskerRight α G := by
  rw [hcomp, whiskerLeft_id]
  exact dgComp_id (C := DGFunctor C E) n (whiskerRight α G)

theorem id_hcomp_id (F : DGFunctor C D) (G : DGFunctor D E) :
    hcomp (id F) (id G) 0 (add_zero 0) = id (F.comp G) := by
  rw [hcomp_id, whiskerRight_id]

/-! ### The differential -/

/-- **The graded Leibniz rule for the Godement product.**

`δ (α ⋆ β) = α ⋆ δβ + (-1)^m • (δα ⋆ β)`, with `m` the degree of `β`.  Both
whiskerings commute with the differential, so this is the Leibniz rule of the
dg category of dg functors applied to the vertical composite that defines
`hcomp`; the sign is the repository's `dgComp` convention and nothing more. -/
theorem differential_hcomp (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (h : n + m = r) :
    differential (hcomp α β r h) =
      hcomp α (differential β) (r + 1) (by omega) +
        m.negOnePow • hcomp (differential α) β (r + 1) (by omega) := by
  ext X
  simp only [differential_app, hcomp_app, add_app, units_smul_app]
  rw [G.map_d n (n + 1)]
  -- `exact` rather than a final `rw`: the outer differential is spelled at
  -- `(F.comp G).obj X` in the goal and at `G.obj (F.obj X)` in the Leibniz
  -- rule, which are definitionally equal but not syntactically.
  exact dgComp_leibniz n m r (r + 1) h rfl (G.map n (app α X))
    (app β (F'.obj X))

/-- The Godement product of two closed transformations is closed. -/
theorem IsClosed.hcomp {α : HomogeneousNatTrans F F' n}
    {β : HomogeneousNatTrans G G' m} (hα : IsClosed α) (hβ : IsClosed β)
    (r : ℤ) (h : n + m = r) :
    IsClosed (HomogeneousNatTrans.hcomp α β r h) := by
  have hd := differential_hcomp α β r h
  rw [IsClosed] at hα hβ ⊢
  rw [hd, hα, hβ, hcomp_zero_left, hcomp_zero_right, smul_zero, add_zero]

end Hcomp

/-! ### Associativity -/

section Assoc

variable {F F' : DGFunctor C D} {G G' : DGFunctor D E} {H H' : DGFunctor E B}
  {n m k : ℤ}

/-- **The Godement product is strictly associative.**

Dg functors compose strictly, so both sides are transformations
`F ⋙ G ⋙ H ⟶ F' ⋙ G' ⋙ H'` of the same degree and the statement needs no
comparison isomorphism.  The proof is `DGFunctor.map_comp` for `H`, then
associativity of the graded composition. -/
theorem hcomp_assoc (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (γ : HomogeneousNatTrans H H' k)
    (nm mk s : ℤ) (hnm : n + m = nm) (hmk : m + k = mk) (hs : nm + k = s)
    (hs' : n + mk = s) :
    hcomp (hcomp α β nm hnm) γ s hs = hcomp α (hcomp β γ mk hmk) s hs' := by
  -- Not componentwise.  Unfold both sides into whiskerings, normalise the
  -- repeated whiskerings, and the statement becomes associativity of the
  -- graded composition in the dg category of dg functors `C ⟶ B`.  A
  -- componentwise proof runs into a goal mixing `(F.comp G).obj X` with
  -- `G.obj (F.obj X)`, which `rw` will not build a motive over.
  rw [hcomp, hcomp, hcomp, hcomp, whiskerRight_composition,
    whiskerLeft_composition, whiskerRight_whiskerRight,
    whiskerRight_whiskerLeft, whiskerLeft_whiskerLeft]
  exact dgComp_assoc (C := DGFunctor C B) n m k nm mk s hnm hmk (by omega) _ _ _

end Assoc

end DGFunctor.HomogeneousNatTrans

end CategoryTheory
