/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Functor

/-!
# Cocycles, coboundaries, and `Z⁰` of a dg category

The degree-zero cocycles of a dg category form an ordinary category on the same
objects, and the coboundaries sit inside them as an additive subgroup. `H⁰` is
the quotient; this file builds everything the quotient needs.

Both halves rest on the Leibniz rule, at three different pairs of degrees:

* `(0, 0)` — composition of cocycles is a cocycle, so `Z⁰` is a category;
* `(0, -1)` — a cocycle composed with a coboundary is a coboundary;
* `(-1, 0)` — a coboundary composed with a cocycle is a coboundary.

The last two are what make composition descend to `H⁰`. They are the reason the
Leibniz rule is an axiom of `DGCategory` rather than a lemma about a special
case, and the `Const` example in `DerivedAlgGeo/CategoryTheory/Enriched/DGCategory/Instances.lean` — whose
differential is zero — tests none of them.

## A wrinkle in the degrees

`dgComp_leibniz` states the shifted degrees as `p + 1`, and those are dependent
arguments: `simp only [zero_add]` cannot normalise `0 + 1` to `1` in a goal
without breaking the motive. Hypotheses are therefore restated at the shifted
degree — they typecheck directly, the degrees being definitionally equal —
rather than rewriting the goal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u''

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- The degree-zero cocycles from `X` to `Y`. -/
def cocycles (X Y : C) : AddSubgroup ((dgHom X Y).X 0) :=
  ((dgHom X Y).d 0 1).hom.ker

/-- The degree-zero coboundaries from `X` to `Y`. -/
def coboundaries (X Y : C) : AddSubgroup ((dgHom X Y).X 0) :=
  ((dgHom X Y).d (-1) 0).hom.range

lemma mem_cocycles_iff {X Y : C} (f : (dgHom X Y).X 0) :
    f ∈ cocycles X Y ↔ ((dgHom X Y).d 0 1).hom f = 0 := Iff.rfl

lemma mem_coboundaries_iff {X Y : C} (f : (dgHom X Y).X 0) :
    f ∈ coboundaries X Y ↔ ∃ h, ((dgHom X Y).d (-1) 0).hom h = f := Iff.rfl

/-- Every coboundary is a cocycle: this is `d ∘ d = 0`. -/
lemma coboundaries_le_cocycles (X Y : C) : coboundaries X Y ≤ cocycles X Y := by
  rintro _ ⟨h, rfl⟩
  rw [mem_cocycles_iff, ← AddCommGrpCat.comp_apply, (dgHom X Y).d_comp_d]
  simp

/-- A cocycle composed with a coboundary is a coboundary. Leibniz at `(0, -1)`:
the `δf` term vanishes because `f` is closed, and the sign is `+1`. -/
lemma comp_coboundary_mem {X Y Z : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    {b : (dgHom Y Z).X 0} (hb : b ∈ coboundaries Y Z) :
    dgComp 0 0 0 (by omega) f b ∈ coboundaries X Z := by
  obtain ⟨h, rfl⟩ := hb
  refine ⟨dgComp 0 (-1) (-1) (by omega) f h, ?_⟩
  have hf' : ((dgHom X Y).d 0 (0 + 1)).hom f = 0 := hf
  have key := dgComp_leibniz (C := C) 0 (-1) (-1) 0 (by omega) (by omega) f h
  rw [key]
  simp only [hf', map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero]
  -- only `-1 + 1` versus `0` in dependent positions remains; they are defeq
  rfl

/-- A coboundary composed with a cocycle is a coboundary. Leibniz at `(-1, 0)`:
the `δg` term vanishes because `g` is closed, so the sign never matters. -/
lemma coboundary_comp_mem {X Y Z : C} {b : (dgHom X Y).X 0} (hb : b ∈ coboundaries X Y)
    {g : (dgHom Y Z).X 0} (hg : g ∈ cocycles Y Z) :
    dgComp 0 0 0 (by omega) b g ∈ coboundaries X Z := by
  obtain ⟨h, rfl⟩ := hb
  refine ⟨dgComp (-1) 0 (-1) (by omega) h g, ?_⟩
  have hg' : ((dgHom Y Z).d 0 (0 + 1)).hom g = 0 := hg
  have key := dgComp_leibniz (C := C) (-1) 0 (-1) 0 (by omega) (by omega) h g
  rw [key]
  simp only [hg', map_zero, zero_add, Int.negOnePow_zero, one_smul]
  rfl

variable (C)

/-- Objects of `Z⁰`. A type synonym, so the ordinary category structure does not
attach itself to `C`. -/
def Z0 : Type u := C

namespace Z0

/-- The underlying object of `C`. -/
def of (X : Z0 C) : C := X

variable {C}

/-- Composition of cocycles is a cocycle: Leibniz at `(0, 0)`, with both
differential terms vanishing. -/
lemma comp_mem {X Y Z : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    {g : (dgHom Y Z).X 0} (hg : g ∈ cocycles Y Z) :
    dgComp 0 0 0 (by omega) f g ∈ cocycles X Z := by
  have hf' : ((dgHom X Y).d 0 (0 + 1)).hom f = 0 := hf
  have hg' : ((dgHom Y Z).d 0 (0 + 1)).hom g = 0 := hg
  have key := dgComp_leibniz (C := C) 0 0 0 1 (by omega) (by omega) f g
  -- No `simp` before the rewrites: it normalises `0 + 1` to `1` in the goal, and
  -- the hypotheses are stated at `0 + 1` because that is the shape the axiom has.
  rw [mem_cocycles_iff, key, hf', hg', map_zero, map_zero, AddMonoidHom.zero_apply,
    smul_zero, add_zero]

instance category : Category.{v} (Z0 C) where
  Hom X Y := cocycles (of C X) (of C Y)
  id X := ⟨dgId (of C X), dgId_cocycle _⟩
  comp f g := ⟨dgComp 0 0 0 (by omega) f.1 g.1, comp_mem f.2 g.2⟩
  id_comp f := Subtype.ext (dgId_comp 0 f.1)
  comp_id f := Subtype.ext (dgComp_id 0 f.1)
  assoc f g h := Subtype.ext (dgComp_assoc 0 0 0 0 0 0 rfl rfl rfl f.1 g.1 h.1)

/-! The two computation rules below are stated through `Subtype.val` on the
ascribed subgroup type: `X ⟶ Y` in `Z0 C` *is* `cocycles _ _`, but only
definitionally, so the anonymous coercion does not fire on the `⟶` form. -/

@[simp]
lemma id_val (X : Z0 C) :
    ((𝟙 X : X ⟶ X) : cocycles (of C X) (of C X)).val = dgId (of C X) := rfl

@[simp]
lemma comp_val {X Y Z : Z0 C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g : X ⟶ Z) : cocycles (of C X) (of C Z)).val =
      dgComp 0 0 0 (by omega)
        ((f : cocycles (of C X) (of C Y)).val) ((g : cocycles (of C Y) (of C Z)).val) := rfl

end Z0

variable {C}

/-- Composition respects cohomology classes. Writing
`f₁ ∘ g₁ - f₂ ∘ g₂ = (f₁ - f₂) ∘ g₁ + f₂ ∘ (g₁ - g₂)` reduces this to the two
descent lemmas, one for each summand.

Only `f₂` and `g₁` are required to be closed — the split above touches the other
two only through the differences, which are already assumed to be coboundaries. -/
lemma comp_sub_mem {X Y Z : C} {f₁ f₂ : (dgHom X Y).X 0} {g₁ g₂ : (dgHom Y Z).X 0}
    (hf₂ : f₂ ∈ cocycles X Y) (hg₁ : g₁ ∈ cocycles Y Z)
    (hf : f₁ - f₂ ∈ coboundaries X Y) (hg : g₁ - g₂ ∈ coboundaries Y Z) :
    dgComp 0 0 0 (by omega) f₁ g₁ - dgComp 0 0 0 (by omega) f₂ g₂ ∈ coboundaries X Z := by
  have expand :
      dgComp 0 0 0 (by omega) f₁ g₁ - dgComp 0 0 0 (by omega) f₂ g₂ =
        dgComp 0 0 0 (by omega) (f₁ - f₂) g₁ + dgComp 0 0 0 (by omega) f₂ (g₁ - g₂) := by
    simp [map_sub, AddMonoidHom.sub_apply]
  rw [expand]
  exact AddSubgroup.add_mem _ (coboundary_comp_mem hf hg₁)
    (comp_coboundary_mem hf₂ hg)

/-- Objects of `H⁰`. -/
def H0 (C : Type u) : Type u := C

namespace H0

/-- The underlying object of `C`. -/
def of (C : Type u) (X : H0 C) : C := X

omit [DGCategory C] in
/-- `of` is the identity. **Not** a `simp` lemma: making it one changes how the
quotient's membership goals normalise and breaks the descent proofs above. Pass
it explicitly where objects need to be unfolded. -/
lemma of_self (X : H0 C) : of C X = X := rfl

/-- The coboundaries, viewed inside the cocycles. -/
def coboundariesIn (X Y : C) : AddSubgroup (cocycles X Y) :=
  (coboundaries X Y).addSubgroupOf (cocycles X Y)

instance category : Category.{v} (H0 C) where
  Hom X Y := cocycles (of C X) (of C Y) ⧸ coboundariesIn (of C X) (of C Y)
  id X := QuotientAddGroup.mk ⟨dgId (of C X), dgId_cocycle _⟩
  comp {X Y Z} f g := by
    refine Quotient.map₂ (fun f g => ⟨dgComp 0 0 0 (by omega) f.1 g.1,
      Z0.comp_mem f.2 g.2⟩) ?_ f g
    rintro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ hfr ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ hgr
    -- `≈` here is `QuotientAddGroup.leftRel`; `leftRel_apply` turns each side
    -- into a membership, but only through `.mp`/`.mpr`, since the goal is stated
    -- with the setoid's notation rather than the relation's name.
    have hf : f₂ - f₁ ∈ coboundaries (of C X) (of C Y) := by
      simpa [coboundariesIn, AddSubgroup.mem_addSubgroupOf, sub_eq_neg_add] using
        QuotientAddGroup.leftRel_apply.mp hfr
    have hg : g₂ - g₁ ∈ coboundaries (of C Y) (of C Z) := by
      simpa [coboundariesIn, AddSubgroup.mem_addSubgroupOf, sub_eq_neg_add] using
        QuotientAddGroup.leftRel_apply.mp hgr
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    simpa [coboundariesIn, AddSubgroup.mem_addSubgroupOf, sub_eq_neg_add] using
      comp_sub_mem hf₁ hg₂ hf hg
  id_comp := by
    rintro X Y f
    induction f using Quotient.ind with
    | _ f => exact congrArg _ (Subtype.ext (dgId_comp 0 f.1))
  comp_id := by
    rintro X Y f
    induction f using Quotient.ind with
    | _ f => exact congrArg _ (Subtype.ext (dgComp_id 0 f.1))
  assoc := by
    rintro W X Y Z f g h
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g =>
        induction h using Quotient.ind with
        | _ h =>
          exact congrArg _ (Subtype.ext
            (dgComp_assoc 0 0 0 0 0 0 rfl rfl rfl f.1 g.1 h.1))

/-- `H⁰` is preadditive: its Hom-sets are quotients of abelian groups, and
composition is biadditive because `dgComp` is. -/
instance preadditive : Preadditive (H0 C) where
  homGroup X Y := by
    -- `X ⟶ Y` is the quotient only definitionally, so instance search needs the
    -- type spelled out before it will look.
    show AddCommGroup (cocycles (of C X) (of C Y) ⧸ coboundariesIn (of C X) (of C Y))
    infer_instance
  add_comp P Q R f f' g := by
    induction f using Quotient.ind with
    | _ f =>
      induction f' using Quotient.ind with
      | _ f' =>
        induction g using Quotient.ind with
        | _ g => exact congrArg _ (Subtype.ext (by
            simp [AddSubgroup.coe_add, map_add, AddMonoidHom.add_apply]))
  comp_add P Q R f g g' := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g =>
        induction g' using Quotient.ind with
        | _ g' => exact congrArg _ (Subtype.ext (by
            simp [AddSubgroup.coe_add, map_add]))

end H0

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]

/-- A dg functor sends cocycles to cocycles: it commutes with the differential,
and an additive map sends `0` to `0`. -/
lemma map_mem_cocycles (F : DGFunctor C D) {X Y : C} {f : (dgHom X Y).X 0}
    (hf : f ∈ cocycles X Y) : F.map 0 f ∈ cocycles (F.obj X) (F.obj Y) := by
  have hf' : ((dgHom X Y).d 0 1).hom f = 0 := hf
  rw [mem_cocycles_iff, ← F.map_d 0 1 f, hf', map_zero]

/-- A dg functor sends coboundaries to coboundaries, for the same reason and
with no closedness hypothesis: `map_d` already exhibits the primitive. -/
lemma map_mem_coboundaries (F : DGFunctor C D) {X Y : C} {f : (dgHom X Y).X 0}
    (hf : f ∈ coboundaries X Y) : F.map 0 f ∈ coboundaries (F.obj X) (F.obj Y) := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨F.map (-1) h, (F.map_d (-1) 0 h).symm⟩

/-- The functor `H⁰(F)` induced by a dg functor. -/
def h0 (F : DGFunctor C D) : H0 C ⥤ H0 D where
  obj X := F.obj (H0.of C X)
  map {X Y} := Quotient.map (fun f => ⟨F.map 0 f.1, F.map_mem_cocycles f.2⟩) (by
    rintro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ hr
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    have := QuotientAddGroup.leftRel_apply.mp hr
    simp only [H0.coboundariesIn, AddSubgroup.mem_addSubgroupOf] at this ⊢
    -- Additivity of `F.map` first, then `exact`: the subgroup coercion of a sum
    -- is the sum of the coercions definitionally, which `exact` accepts and the
    -- `coe_add` simp lemmas do not fire on.
    have key : F.map 0 (-f₁ + f₂) ∈ coboundaries (F.obj X) (F.obj Y) :=
      F.map_mem_coboundaries this
    rw [map_add, map_neg] at key
    exact key)
  map_id X := congrArg _ (Subtype.ext (F.map_id _))
  map_comp {X Y Z} f g := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g => exact congrArg _ (Subtype.ext (F.map_comp 0 0 0 (by omega) f.1 g.1))


/-- A dg functor's action on a single Hom-complex, packaged as a morphism of
cochain complexes. `map_d` is exactly the commutation square. -/
def mapComplex (F : DGFunctor C D) (X Y : C) :
    dgHom X Y ⟶ dgHom (F.obj X) (F.obj Y) where
  f p := AddCommGrpCat.ofHom (F.map p)
  comm' p q _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simpa using (F.map_d p q x).symm

/-- A quasi-equivalence of dg categories: the action on every Hom-complex is a
quasi-isomorphism, and `H⁰` of it is essentially surjective.

This is a definition and nothing more. No theorem in this repository relates it
to anything — in particular there is no claim here that a quasi-equivalence
induces an equivalence on `H⁰`, which is `dg-enhancements-e10`. -/
structure IsQuasiEquivalence (F : DGFunctor C D) : Prop where
  /-- Every Hom-complex map is a quasi-isomorphism. -/
  quasiIso : ∀ X Y : C, QuasiIso (F.mapComplex X Y)
  /-- `H⁰ F` hits every object up to isomorphism. -/
  essSurj : F.h0.EssSurj

end DGFunctor

/-- The quotient functor from cocycles to cohomology classes. -/
def Z0.toH0 (C : Type u) [DGCategory.{v} C] : Z0 C ⥤ H0 C where
  obj X := X
  map f := QuotientAddGroup.mk f
  map_id _ := rfl
  map_comp _ _ := rfl

namespace DGFunctor

variable {C : Type u} {D : Type u'} {E : Type u''} [DGCategory.{v} C] [DGCategory.{v} D]
  [DGCategory.{v} E]

/-- The object part of `H⁰ F`. A `simp` lemma because otherwise the objects in
a naturality square stay in the `h0.obj` form and `Category.comp_id` — whose
statement mentions the codomain — cannot match. -/
@[simp]
lemma h0_obj (F : DGFunctor C D) (X : H0 C) : F.h0.obj X = F.obj (H0.of C X) := rfl

/-- How `H⁰ F` acts on a class: this is the computation rule `simp` needs
before any naturality square involving `h0` will close. -/
@[simp]
lemma h0_map_mk (F : DGFunctor C D) {X Y : H0 C} (f : cocycles (H0.of C X) (H0.of C Y)) :
    F.h0.map (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨F.map 0 f.1, F.map_mem_cocycles f.2⟩ := rfl

/-- `H⁰` of the identity dg functor is the identity. -/
def h0IdIso : (DGFunctor.id C).h0 ≅ 𝟭 (H0 C) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    induction f using Quotient.ind with
    | _ f =>
      simp [DGFunctor.id, H0.of_self]
      rfl)

/-- `H⁰` takes composition of dg functors to composition of functors. -/
def h0CompIso (F : DGFunctor C D) (G : DGFunctor D E) :
    (F.comp G).h0 ≅ F.h0 ⋙ G.h0 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    induction f using Quotient.ind with
    | _ f =>
      show _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      rfl)


end DGFunctor

end CategoryTheory
