/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Shift.Basic
import DerivedAlgGeo.CategoryTheory.DGCategory.Pretriangulated

/-!
# The shift functor on `H⁰`

`dg-enhancements-e6`. `IsPretriangulated.exists_shift` says every object has a
shift in every degree, as an existential. This file makes a choice, and shows
the choice assembles into a functor `H⁰ C ⥤ H⁰ C` for each `n`.

## The choice does not matter, and that is a theorem rather than a hope

`shiftObj` and `shiftWitness` are `Classical.choice` applied to
`exists_shift`, so nothing about them is canonical on the nose. What makes them
usable is `IsShiftBy.compare_comp_compare`: any two shifts of `X` by `n` are
canonically isomorphic in `Z⁰`. So a different choice gives a naturally
isomorphic functor, and `IsShiftBy.mapShift_compare` says the comparison is
natural without a diagram to chase.

## Descent to `H⁰`

The action on morphisms is `IsShiftBy.mapShift`, and it descends because it is
additive (`mapShift_add`), preserves cocycles (`mapShift_mem_cocycles`) and
preserves coboundaries (`mapShift_mem_coboundaries`). The descent argument is
the one `DGFunctor.h0` already uses, down to the `leftRel_apply` idiom.

## Free degrees, and why

`shiftFunctorAddIso'` carries its target degree `nm` as a variable with
`n + m = nm` as a hypothesis, rather than fixing it at `n + m`. Every coherence
identity for a shift functor compares an object indexed by `n + 0`, `0 + n` or
`(a + b) + c` against one indexed by `n`, `n` or `a + (b + c)`. Those indices
are propositionally but not definitionally equal, so `ShiftMkCore` bridges them
with `eqToHom` -- and with the degree fixed there is no way to normalise that
`eqToHom` away. With the degree free, `obtain rfl : nm = n` eliminates a
*variable*, the `eqToHom` acquires equal endpoints, and `eqToHom_refl` finishes
it. Mathlib carries `CochainComplex.shiftFunctorAdd'` for exactly this reason.

## What is proved, and what is not

All three of `ShiftMkCore`'s coherence identities are proved here, in that
general form: `shiftFunctorAddIso'_hom_app_zero_right`, `..._zero_left`, and
`shiftFunctorAddIso'_assoc`. The last one reduces, by `compare_trans` and
`mapShift_compare_comp'`, to `compare` from the chosen shift by `m₁ + m₂ + m₃`
to a threefold composite, and the two threefold composites have equal `hom`
fields by `comp'_assoc_hom`.

So `HasShift (H0 C) ℤ` is an instance, not an aspiration: `hasShift` at the
foot of this file. What `dg-enhancements-e6` still owes after it is the
transport theorem itself, `IsPretriangulated C → Pretriangulated (H0 C)`, whose
remaining clauses are the six fields of `Pretriangulated` rather than anything
about the shift.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory IsShiftBy

variable (C : Type u) [DGCategory.{v} C] [IsPretriangulated C]

namespace IsPretriangulated

/-- A chosen shift of `X` by `n`. -/
noncomputable def shiftObj (X : C) (n : ℤ) : C :=
  (IsPretriangulated.exists_shift X n).choose

/-- The witness that the chosen object really is a shift. -/
noncomputable def shiftWitness (X : C) (n : ℤ) : IsShiftBy X n (shiftObj C X n) :=
  (IsPretriangulated.exists_shift X n).choose_spec.some

end IsPretriangulated

namespace H0

open IsPretriangulated

/-- The shift functor on `H⁰`, at a fixed degree.

`Quotient.map`'s well-definedness obligation is discharged exactly as in
`DGFunctor.h0`: the relation is `QuotientAddGroup.leftRel`, so the hypothesis
arrives as `-f₁ + f₂ ∈ coboundaries` and `mapShiftHom`'s additivity turns
`mapShift_mem_coboundaries` into what is needed. -/
noncomputable def shiftFunctor (n : ℤ) : H0 C ⥤ H0 C where
  obj X := shiftObj C (H0.of C X) n
  map {X Y} := Quotient.map
    (fun f => ⟨mapShift (shiftWitness C (H0.of C X) n) (shiftWitness C (H0.of C Y) n) f.1,
      mapShift_mem_cocycles _ _ f.2⟩) (by
    rintro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ hr
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    have hcob := QuotientAddGroup.leftRel_apply.mp hr
    simp only [H0.coboundariesIn, AddSubgroup.mem_addSubgroupOf] at hcob ⊢
    have key : mapShiftHom (shiftWitness C (H0.of C X) n) (shiftWitness C (H0.of C Y) n)
        (-f₁ + f₂) ∈ coboundaries _ _ :=
      mapShift_mem_coboundaries _ _ hcob
    rw [map_add, map_neg] at key
    exact key)
  map_id X := congrArg _ (Subtype.ext (mapShift_id _))
  map_comp {X Y Z} f g := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g => exact congrArg _ (Subtype.ext (mapShift_comp _ _ _ f.1 g.1).symm)

/-- How the shift functor acts on a class. The computation rule `simp` needs
before any square involving `shiftFunctor` will close. -/
@[simp]
lemma shiftFunctor_map_mk (n : ℤ) {X Y : H0 C}
    (f : cocycles (H0.of C X) (H0.of C Y)) :
    (shiftFunctor C n).map (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨mapShift (shiftWitness C (H0.of C X) n)
        (shiftWitness C (H0.of C Y) n) f.1, mapShift_mem_cocycles _ _ f.2⟩ := rfl

/-- The shift functor is additive: `mapShift` is additive on representatives,
and the quotient map is a group homomorphism. -/
instance shiftFunctor_additive (n : ℤ) : (shiftFunctor C n).Additive where
  map_add {X Y} f g := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g => exact congrArg _ (Subtype.ext (mapShift_add _ _ f.1 g.1))

variable {C}

/-- Two shifts of the same object by the same degree, compared as an
isomorphism in `H⁰`. The inverse is the comparison the other way, and
`compare_comp_compare` is both triangle identities. -/
noncomputable def compareIso {X Y Y' : C} {n : ℤ}
    (s : IsShiftBy X n Y) (t : IsShiftBy X n Y') :
    (show H0 C from Y) ≅ (show H0 C from Y') where
  hom := QuotientAddGroup.mk ⟨compare s t, compare_mem_cocycles s t⟩
  inv := QuotientAddGroup.mk ⟨compare t s, compare_mem_cocycles t s⟩
  hom_inv_id := congrArg _ (Subtype.ext (compare_comp_compare s t))
  inv_hom_id := congrArg _ (Subtype.ext (compare_comp_compare t s))

variable (C)

/-- `shiftFunctor C 0` is the identity, up to natural isomorphism.

Naturality is `IsShiftBy.mapShift_compare` together with
`IsShiftBy.mapShift_self`: shifting by zero does nothing to a morphism, and the
comparison of two shifts is natural for free. -/
noncomputable def shiftFunctorZeroIso : shiftFunctor C 0 ≅ 𝟭 (H0 C) :=
  NatIso.ofComponents
    (fun X => compareIso (C := C) (shiftWitness C (H0.of C X) 0)
      (IsShiftBy.self (H0.of C X)))
    (by
      intro X Y f
      induction f using Quotient.ind with
      | _ f =>
        -- The goal is already the naturality square on representatives; no
        -- unfolding of `compareIso` is needed.
        refine congrArg _ (Subtype.ext ?_)
        exact (mapShift_compare (shiftWitness C (H0.of C X) 0)
          (IsShiftBy.self (H0.of C X)) (shiftWitness C (H0.of C Y) 0)
          (IsShiftBy.self (H0.of C Y)) f.1).trans
          (congrArg (fun z => dgComp 0 0 0 (by omega)
            (compare (shiftWitness C (H0.of C X) 0) (IsShiftBy.self (H0.of C X))) z)
            (mapShift_self _ _ f.1)))

/-- The chosen shift by `n` followed by the chosen shift by `m`, as a shift by
`nm`. The degree is a free variable for the reason `IsShiftBy.comp'` records:
the coherence identities compare `n + 0`, `0 + n` and `(a + b) + c` against
`n`, `n` and `a + (b + c)`, and only a free degree can be `subst`ed. -/
noncomputable def shiftCompWitness' (X : C) (n m nm : ℤ) (hnm : n + m = nm) :
    IsShiftBy X nm (shiftObj C (shiftObj C X n) m) :=
  IsShiftBy.comp' (shiftWitness C X n) (shiftWitness C (shiftObj C X n) m) nm hnm

/-- `shiftFunctor C nm` is `shiftFunctor C n ⋙ shiftFunctor C m` whenever
`n + m = nm`, up to natural isomorphism.

Naturality is `IsShiftBy.mapShift_compare` followed by
`IsShiftBy.mapShift_comp'_shift`, in the same shape as the degree-zero case:
`mapShift` along a composite shift is `mapShift` twice, so the square is two
rewrites and no diagram. -/
noncomputable def shiftFunctorAddIso' (n m nm : ℤ) (hnm : n + m = nm) :
    shiftFunctor C nm ≅ shiftFunctor C n ⋙ shiftFunctor C m :=
  NatIso.ofComponents
    (fun X => compareIso (C := C) (shiftWitness C (H0.of C X) nm)
      (shiftCompWitness' C (H0.of C X) n m nm hnm))
    (by
      intro X Y f
      induction f using Quotient.ind with
      | _ f =>
        refine congrArg _ (Subtype.ext ?_)
        exact (mapShift_compare (shiftWitness C (H0.of C X) nm)
          (shiftCompWitness' C (H0.of C X) n m nm hnm) (shiftWitness C (H0.of C Y) nm)
          (shiftCompWitness' C (H0.of C Y) n m nm hnm) f.1).trans
          (congrArg (fun z => dgComp 0 0 0 (by omega)
            (compare (shiftWitness C (H0.of C X) nm) (shiftCompWitness' C (H0.of C X) n m nm hnm)) z)
            (mapShift_comp'_shift _ _ _ _ nm hnm f.1)))

/-- The chosen shift by `n` followed by the chosen shift by `m`, at the
definitional degree. -/
noncomputable def shiftCompWitness (X : C) (n m : ℤ) :
    IsShiftBy X (n + m) (shiftObj C (shiftObj C X n) m) :=
  shiftCompWitness' C X n m (n + m) rfl

/-- `shiftFunctorAddIso'` at the definitional degree. -/
noncomputable def shiftFunctorAddIso (n m : ℤ) :
    shiftFunctor C (n + m) ≅ shiftFunctor C n ⋙ shiftFunctor C m :=
  shiftFunctorAddIso' C n m (n + m) rfl

/-- `ShiftMkCore.add_zero_hom_app`, in the general form where the target degree
is free.

The free degree is the whole point: `obtain rfl : nm = n` eliminates a
*variable*, which is exactly what `n + 0 = n` does not allow. Once it is gone
the `eqToHom` has equal endpoints and collapses to the identity, and both sides
reduce to `(shiftWitness C (shiftObj C X n) 0).hom` -- the left by
`inv_hom` on the outer shift, the right by `self_inv`. -/
lemma shiftFunctorAddIso'_hom_app_zero_right (n nm : ℤ) (hnm : n + 0 = nm) (X : H0 C) :
    (shiftFunctorAddIso' C n 0 nm hnm).hom.app X =
      eqToHom (congrArg (fun k => (shiftFunctor C k).obj X) (show nm = n by omega)) ≫
        (shiftFunctorZeroIso C).inv.app ((shiftFunctor C n).obj X) := by
  obtain rfl : nm = n := by omega
  rw [eqToHom_refl, Category.id_comp]
  refine congrArg _ (Subtype.ext ?_)
  -- `obtain rfl` above eliminated `n` in favour of `nm`, so the rest is
  -- written at `nm`.
  show IsShiftBy.compare (shiftWitness C (H0.of C X) nm)
      (shiftCompWitness' C (H0.of C X) nm 0 nm hnm) =
    IsShiftBy.compare (IsShiftBy.self (shiftObj C (H0.of C X) nm))
      (shiftWitness C (shiftObj C (H0.of C X) nm) 0)
  rw [IsShiftBy.compare, IsShiftBy.compare, shiftCompWitness', comp'_hom, self_inv,
    ← dgComp_assoc nm (-nm) (-0) 0 (-nm) 0 (by omega) (by omega) (by omega), inv_hom]

/-- `ShiftMkCore.zero_add_hom_app`, in the general form where the target degree
is free.

Same shape as the right-handed case, with one extra step: the right-hand side
applies `shiftFunctor` to a comparison, and `mapShift_compare_comp'` turns that
into a comparison of composites. What is left is that prefixing a shift with
the zero shift does not change its inverse, which is `comp'_self_left_inv`. -/
lemma shiftFunctorAddIso'_hom_app_zero_left (n nm : ℤ) (hnm : 0 + n = nm) (X : H0 C) :
    (shiftFunctorAddIso' C 0 n nm hnm).hom.app X =
      eqToHom (congrArg (fun k => (shiftFunctor C k).obj X) (show nm = n by omega)) ≫
        (shiftFunctor C n).map ((shiftFunctorZeroIso C).inv.app X) := by
  obtain rfl : nm = n := by omega
  rw [eqToHom_refl, Category.id_comp]
  refine congrArg _ (Subtype.ext ?_)
  show IsShiftBy.compare (shiftWitness C (H0.of C X) nm)
      (shiftCompWitness' C (H0.of C X) 0 nm nm hnm) =
    mapShift (shiftWitness C (H0.of C X) nm)
      (shiftWitness C (shiftObj C (H0.of C X) 0) nm)
      (IsShiftBy.compare (IsShiftBy.self (H0.of C X))
        (shiftWitness C (H0.of C X) 0))
  rw [mapShift_compare_comp' _ _ _ _ nm hnm, shiftCompWitness', IsShiftBy.compare,
    IsShiftBy.compare, comp'_self_left_inv]

/-- Two `shiftFunctorAddIso'` at propositionally equal target degrees differ by
the `eqToHom` between them. This is the bridge from the free-degree lemmas to
`ShiftMkCore`'s fields, whose degrees are fixed. -/
lemma shiftFunctorAddIso'_hom_app_congr (n m nm nm' : ℤ) (h : n + m = nm) (h' : n + m = nm')
    (X : H0 C) :
    (shiftFunctorAddIso' C n m nm h).hom.app X =
      eqToHom (congrArg (fun k => (shiftFunctor C k).obj X) (show nm = nm' by omega)) ≫
        (shiftFunctorAddIso' C n m nm' h').hom.app X := by
  obtain rfl : nm = nm' := by omega
  rw [eqToHom_refl, Category.id_comp]

/-- `ShiftMkCore.assoc_hom_app`, in the general form where every degree is free.

With the degrees free there is no `eqToHom` at all -- both sides are indexed by
`m₁₂₃` -- and the identity reduces to three moves with no diagram chase:
`mapShift_compare_comp'` turns the functor applied to a comparison into a
comparison of composites, `compare_trans` and `compare_comp'_right` collapse
each side to a single comparison out of the chosen shift, and `comp'_assoc_hom`
observes that the two threefold composites carry the same element. -/
lemma shiftFunctorAddIso'_assoc (m₁ m₂ m₃ m₁₂ m₂₃ m₁₂₃ : ℤ)
    (h₁₂ : m₁ + m₂ = m₁₂) (h₂₃ : m₂ + m₃ = m₂₃) (h : m₁₂ + m₃ = m₁₂₃) (X : H0 C) :
    (shiftFunctorAddIso' C m₁₂ m₃ m₁₂₃ h).hom.app X ≫
        (shiftFunctor C m₃).map ((shiftFunctorAddIso' C m₁ m₂ m₁₂ h₁₂).hom.app X) =
      (shiftFunctorAddIso' C m₁ m₂₃ m₁₂₃ (by omega)).hom.app X ≫
        (shiftFunctorAddIso' C m₂ m₃ m₂₃ h₂₃).hom.app ((shiftFunctor C m₁).obj X) := by
  refine congrArg _ (Subtype.ext ?_)
  show dgComp 0 0 0 (by omega)
      (IsShiftBy.compare (shiftWitness C (H0.of C X) m₁₂₃)
        (shiftCompWitness' C (H0.of C X) m₁₂ m₃ m₁₂₃ h))
      (mapShift (shiftWitness C (shiftObj C (H0.of C X) m₁₂) m₃)
        (shiftWitness C (shiftObj C (shiftObj C (H0.of C X) m₁) m₂) m₃)
        (IsShiftBy.compare (shiftWitness C (H0.of C X) m₁₂)
          (shiftCompWitness' C (H0.of C X) m₁ m₂ m₁₂ h₁₂))) =
    dgComp 0 0 0 (by omega)
      (IsShiftBy.compare (shiftWitness C (H0.of C X) m₁₂₃)
        (shiftCompWitness' C (H0.of C X) m₁ m₂₃ m₁₂₃ (by omega)))
      (IsShiftBy.compare (shiftWitness C (shiftObj C (H0.of C X) m₁) m₂₃)
        (shiftCompWitness' C (shiftObj C (H0.of C X) m₁) m₂ m₃ m₂₃ h₂₃))
  rw [mapShift_compare_comp' _ _ _ _ m₁₂₃ h, shiftCompWitness',
    compare_trans, shiftCompWitness', shiftCompWitness',
    compare_comp'_right _ _ _ _ (by omega)]
  exact compare_congr _ _ _
    (comp'_assoc_hom (shiftWitness C (H0.of C X) m₁)
      (shiftWitness C (shiftObj C (H0.of C X) m₁) m₂)
      (shiftWitness C (shiftObj C (shiftObj C (H0.of C X) m₁) m₂) m₃)
      m₁₂ m₂₃ m₁₂₃ h₁₂ h₂₃ h)

/-- Everything `HasShift` needs, assembled. -/
noncomputable def shiftMkCore : ShiftMkCore (H0 C) ℤ where
  F := shiftFunctor C
  zero := shiftFunctorZeroIso C
  add n m := shiftFunctorAddIso C n m
  assoc_hom_app m₁ m₂ m₃ X := by
    rw [shiftFunctorAddIso, shiftFunctorAddIso, shiftFunctorAddIso, shiftFunctorAddIso,
      shiftFunctorAddIso'_assoc C m₁ m₂ m₃ (m₁ + m₂) (m₂ + m₃) (m₁ + m₂ + m₃) rfl rfl rfl X,
      shiftFunctorAddIso'_hom_app_congr C m₁ (m₂ + m₃) (m₁ + m₂ + m₃) (m₁ + (m₂ + m₃))
        (by omega) (by omega) X, Category.assoc]
  zero_add_hom_app n X := shiftFunctorAddIso'_hom_app_zero_left C n (0 + n) rfl X
  add_zero_hom_app n X := shiftFunctorAddIso'_hom_app_zero_right C n (n + 0) rfl X



/-- `H⁰` of a pretriangulated dg category has a shift by `ℤ`.

This is the second clause of a `Pretriangulated` structure, and the one
`dg-enhancements-e6` was sized around. -/
noncomputable instance hasShift : HasShift (H0 C) ℤ :=
  hasShiftMk _ _ (shiftMkCore C)

/-- The ambient `shiftFunctorZero` is the comparison this file built. `hasShiftMk`
records `ShiftMkCore.zero` as the `shiftFunctorZero` of the resulting `HasShift`,
so this is `ShiftMkCore.shiftFunctorZero_eq` read back through `shiftMkCore`. -/
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (H0 C) ℤ = shiftFunctorZeroIso C := by
  rw [ShiftMkCore.shiftFunctorZero_eq]; rfl

/-- The ambient `shiftFunctorAdd` is the comparison this file built. -/
lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (H0 C) a b = shiftFunctorAddIso C a b := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]; rfl


end H0

end CategoryTheory
