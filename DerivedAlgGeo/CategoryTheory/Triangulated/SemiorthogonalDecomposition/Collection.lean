/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Exceptional
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Orientation

/-!
# Exceptional collections and the semiorthogonal sequence they generate

An **exceptional collection** is a family of exceptional objects, indexed by
a preorder, whose cross-member maps vanish in the CLASSICAL direction: maps
from a LATER member into any shift of an EARLIER one are zero. The theorem
this lane exists for is proved here: the triangulated envelopes of the
shift-closures of the members form a semiorthogonal sequence.

## The classical direction, deliberately

The field `hom_shift_eq_zero` is the definition of the literature (this
structure is an upstream candidate), and it is the OPPOSITE of the repository
root's convention — the root vanishes Hom(earlier, later). The two are NOT
definitionally aligned; the bridge to the root is `Orientation.lean`'s
order-reversing adapter, applied in `toSemiorthogonalSequence`. No file
should restate the flip.

## One meaning of generation

`component i` is the triangulated envelope of the shift closure of the
singleton at `obj i`, and that is the ONLY component convention: Mathlib's
`shiftClosure` already closes under isomorphism, and defining a second
generator-level component would create two meanings of generation. The
repository's `Triangulated.ExtensionClosure` is not used, for the reason the
projective-families reconnaissance rejected it: it proves neither shift
stability nor retract closure.

## What is deliberately out of scope

Admissibility of `component i` needs finite-dimensional Hom-spaces
(`AlgebraicGeometry/Modules/Coherent/Linear.lean`, issue #332) and is not
claimed. Mutation is not filed in this milestone. Beilinson's collection
`O, O(1), …, O(n)` on `P^n`, its fullness, and the decomposition of
`D^b(P^n)` land in `AlgebraicGeometry/ProjectiveSpectrum/**` (issues #570, #586, #571,
#332, #806, #833, #824–#828) and are deliberately NOT touched here; the
concrete inhabitant of this structure is the `D^b(field)` example of the next
issue in this lane.

## Main definitions

* `ExceptionalCollection` — the structure, classical direction.
* `ExceptionalCollection.IsStrong` — an independent predicate, not a field.
* `ExceptionalCollection.component` — the envelope of the shift closure.
* `ExceptionalCollection.toSemiorthogonalSequence` — the image in the root,
  through `Orientation.lean`'s adapter; `toSemiorthogonalSequenceFin` lands
  the finite case back on `Fin n`.
* `ExceptionalCollection.ofExceptional` and
  `ExceptionalCollection.reindex` — the two honest producers of the
  structure.

## Main results

* `ExceptionalCollection.semiorthogonal_component` — the envelopes are
  semiorthogonal in the classical direction; the proof peels both envelopes
  with `triangEnvelope_le_iff` against the orthogonals' triangulated and
  retract-stability instances.
* `ObjectProperty.rightOrthogonal_isStableUnderRetracts` and its left
  dual — two short lemmas absent from the pinned Mathlib (the only files
  mentioning `rightOrthogonal` there prove no retract stability); flagged
  as upstream candidates.

## References

* Bondal, *Representations of associative algebras and coherent sheaves*,
  Izv. Akad. Nauk SSSR (1989).
* Huybrechts, *Fourier–Mukai Transforms in Algebraic Geometry*, §1.4.

## Tags

exceptional collection, semiorthogonal decomposition, triangulated envelope
-/

universe w u v

namespace CategoryTheory.ObjectProperty

open Limits

section Retracts

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- The right orthogonal of any property is stable under retracts: a map from
a `P`-object into a retract extends to the ambient object, where it vanishes.
Upstream candidate — the pinned Mathlib has no retract-stability instance for
either orthogonal. -/
instance rightOrthogonal_isStableUnderRetracts (P : ObjectProperty C) :
    P.rightOrthogonal.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    intro A f hA
    rw [← Category.comp_id f, ← h.retract, ← Category.assoc,
      hY (f ≫ h.i) hA, zero_comp]

/-- The left orthogonal of any property is stable under retracts — the dual.
Upstream candidate. -/
instance leftOrthogonal_isStableUnderRetracts (P : ObjectProperty C) :
    P.leftOrthogonal.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    intro A f hA
    rw [← Category.id_comp f, ← h.retract, Category.assoc,
      hY (h.r ≫ f) hA, comp_zero]

end Retracts

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated

open Limits Pretriangulated

variable (k : Type*) [Field k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (ι : Type w) [Preorder ι]

/-- An **exceptional collection**: exceptional objects indexed by a preorder,
with cross-member vanishing in the CLASSICAL direction — maps from a later
member into any shift of an earlier one are zero. This is the reverse of the
repository root's convention; `toSemiorthogonalSequence` bridges through
`Orientation.lean`'s adapter, and the two conventions are not definitionally
aligned. -/
structure ExceptionalCollection where
  /-- The members of the collection. -/
  obj : ι → C
  /-- Each member is exceptional. -/
  exceptional : ∀ i, IsExceptional k (obj i)
  /-- Maps from a later member into any shift of an earlier one vanish. -/
  hom_shift_eq_zero :
    ∀ ⦃i j : ι⦄, i < j → ∀ (n : ℤ) (f : obj j ⟶ (obj i)⟦n⟧), f = 0

namespace ExceptionalCollection

variable {k C ι} (E : ExceptionalCollection k C ι)

/-- A collection is **strong** when maps between any two members into nonzero
shifts vanish, in both index directions. An independent predicate, not a
field, matching the root's discipline for `IsFull`. Its content beyond the
structure's fields is the `i < j` case alone: `j < i` already follows from
`hom_shift_eq_zero` and `i = j` from `exceptional`. -/
def IsStrong : Prop :=
  ∀ i j, ∀ n : ℤ, n ≠ 0 → ∀ f : E.obj i ⟶ (E.obj j)⟦n⟧, f = 0

/-- The component generated by a member: the triangulated envelope of the
shift closure of the singleton. `shiftClosure` already closes under
isomorphism, so no `isoClosure` wrapper appears; shift stability of the
component is Mathlib's global envelope instance. Deliberately an `abbrev`:
instance search must see through to `triangEnvelope` to find
`IsStableUnderShift ℤ`, hence `IsTriangulated` of the orthogonals, which
`triangEnvelope_le_iff` demands in `semiorthogonal_component`. -/
abbrev component (i : ι) : ObjectProperty C :=
  (ObjectProperty.shiftClosure (fun X => X = E.obj i) ℤ).triangEnvelope

/-- The generating member lies in its own component: it is in the shift
closure at shift `0`, hence in the envelope. -/
theorem obj_mem_component (i : ι) : E.component i (E.obj i) :=
  ObjectProperty.le_triangEnvelope _ _
    (ObjectProperty.le_shiftClosure _ _ rfl)

/-- The envelope-level nonemptiness of a component. Note that Mathlib's
`instance [P.Nonempty] [IsTriangulated C] : P.triangEnvelope.IsTriangulated`
consumes nonemptiness of the *generator*, not of the envelope — which is why
`hasTriangulatedComponents` supplies its own generator-level witness — so
this is the exported form for downstream consumers, not that instance's
input. -/
theorem component_nonempty (i : ι) : (E.component i).Nonempty :=
  ⟨E.obj i, E.obj_mem_component i⟩

omit [Limits.HasZeroObject C] [Pretriangulated C] in
/-- Cross-member vanishing between arbitrary shifts, transported from the
collection's field by conjugating with the shift by `-b` — the two-object
form of `IsExceptional.hom_shift_shift_eq_zero`'s argument. -/
theorem hom_shift_shift_eq_zero ⦃i j : ι⦄ (hij : i < j) (a b : ℤ)
    (f : (E.obj j)⟦a⟧ ⟶ (E.obj i)⟦b⟧) : f = 0 := by
  have h0 :
      (shiftFunctorZero C ℤ).inv.app (E.obj j) ≫
        (shiftFunctorAdd' C a (-a) 0 (add_neg_cancel a)).hom.app (E.obj j) ≫
          (shiftFunctor C (-a)).map f ≫
            (shiftFunctorAdd' C b (-a) (b - a)
              (sub_eq_add_neg b a).symm).inv.app (E.obj i)
        = 0 :=
    E.hom_shift_eq_zero hij (b - a) _
  have h1 := (cancel_epi ((shiftFunctorZero C ℤ).inv.app (E.obj j))).1
    (h0.trans comp_zero.symm)
  have h2 := (cancel_epi
      ((shiftFunctorAdd' C a (-a) 0 (add_neg_cancel a)).hom.app (E.obj j))).1
    (h1.trans comp_zero.symm)
  have h3 := (cancel_mono
      ((shiftFunctorAdd' C b (-a) (b - a)
        (sub_eq_add_neg b a).symm).inv.app (E.obj i))).1
    (h2.trans zero_comp.symm)
  exact (shiftFunctor C (-a)).map_injective
    (h3.trans ((shiftFunctor C (-a)).map_zero _ _).symm)

/-- **The envelopes are semiorthogonal** in the classical direction. The
proof peels the two triangulated envelopes in turn with
`triangEnvelope_le_iff` — first against `(component j).rightOrthogonal`,
then against the left orthogonal of the earlier member's shift closure —
using the orthogonals' triangulated instances and the retract-stability
instances above; what remains is the transported cross-member vanishing. -/
theorem semiorthogonal_component ⦃i j : ι⦄ (hij : i < j) :
    E.component i ≤ (E.component j).rightOrthogonal := by
  have key : E.component j ≤
      (ObjectProperty.shiftClosure (fun X => X = E.obj i) ℤ).leftOrthogonal := by
    rw [component]
    rw [ObjectProperty.triangEnvelope_le_iff]
    rintro X ⟨Y, b, e, rfl⟩
    refine ((ObjectProperty.shiftClosure
      (fun X => X = E.obj i) ℤ).leftOrthogonal).prop_of_iso e.symm ?_
    rintro W f ⟨V, a, e', rfl⟩
    have h0 : f ≫ e'.hom = 0 := E.hom_shift_shift_eq_zero hij b a (f ≫ e'.hom)
    rw [← Category.comp_id f, ← e'.hom_inv_id, ← Category.assoc, h0, zero_comp]
  rw [component]
  rw [ObjectProperty.triangEnvelope_le_iff]
  rintro X hX B f hB
  exact key B hB f hX

/-- The collection's image in the repository root, through `Orientation.lean`'s
order-reversing adapter. -/
def toSemiorthogonalSequence : SemiorthogonalSequence C ιᵒᵈ :=
  SemiorthogonalSequence.ofReverse E.component E.semiorthogonal_component

@[simp]
theorem toSemiorthogonalSequence_component (i : ιᵒᵈ) :
    E.toSemiorthogonalSequence.component i = E.component (OrderDual.ofDual i) :=
  rfl

/-- The root's classical fullness, on the collection's image. A definition by
reuse: no second fullness notion appears. -/
def IsFull : Prop := E.toSemiorthogonalSequence.IsFull

/-- The root's strong fullness, on the collection's image. -/
def IsStronglyFull : Prop := E.toSemiorthogonalSequence.IsStronglyFull

theorem IsStronglyFull.isFull {E : ExceptionalCollection k C ι}
    (h : E.IsStronglyFull) : E.IsFull :=
  SemiorthogonalSequence.IsStronglyFull.isFull _ h

/-- Every component is triangulated, from Mathlib's envelope instance — which
demands nonemptiness, supplied by `component_nonempty`, and
`[IsTriangulated C]`. -/
theorem hasTriangulatedComponents [IsTriangulated C] :
    E.toSemiorthogonalSequence.HasTriangulatedComponents := by
  intro i
  rw [toSemiorthogonalSequence_component]
  haveI : (ObjectProperty.shiftClosure
      (fun X => X = E.obj (OrderDual.ofDual i)) ℤ).Nonempty :=
    ⟨E.obj (OrderDual.ofDual i), ObjectProperty.le_shiftClosure _ _ rfl⟩
  infer_instance

/-- A single exceptional object is a collection over `PUnit`: the cross-member
condition is vacuous because `PUnit` has no strict inequality. One of the two
honest producers of this structure. -/
def ofExceptional {E : C} (h : IsExceptional k E) :
    ExceptionalCollection k C PUnit where
  obj _ := E
  exceptional _ := h
  hom_shift_eq_zero := fun i j hij =>
    absurd (Subsingleton.elim i j ▸ hij) (lt_irrefl j)

/-- Restrict a collection along a strictly monotone map of index types — the
second producer. The unfolded strict-monotonicity binder matches the shape
the root's `reindex` established rather than `StrictMono`. -/
def reindex {κ : Type*} [Preorder κ] (f : κ → ι)
    (hf : ∀ ⦃a b : κ⦄, a < b → f a < f b) : ExceptionalCollection k C κ where
  obj := E.obj ∘ f
  exceptional i := E.exceptional (f i)
  hom_shift_eq_zero := fun _ _ hij n g => E.hom_shift_eq_zero (hf hij) n g

/-- Reindexing commutes with passage to the root, as an equality of
semiorthogonal sequences — through the root's own `reindex`, not a second
one. -/
theorem reindex_toSemiorthogonalSequence {κ : Type*} [Preorder κ] (f : κ → ι)
    (hf : ∀ ⦃a b : κ⦄, a < b → f a < f b) :
    (E.reindex f hf).toSemiorthogonalSequence
      = E.toSemiorthogonalSequence.reindex
          (fun i => OrderDual.toDual (f (OrderDual.ofDual i)))
          (fun _ _ h => hf h) :=
  rfl

section Fin

variable {n : ℕ} (F : ExceptionalCollection k C (Fin n))

/-- The finite case, landed back on `Fin n` through `Orientation.lean`'s
`ofReverseFin`: component `i` of the result is the collection's component
`i.rev`. -/
def toSemiorthogonalSequenceFin : SemiorthogonalSequence C (Fin n) :=
  SemiorthogonalSequence.ofReverseFin n F.component F.semiorthogonal_component

@[simp]
theorem toSemiorthogonalSequenceFin_component (i : Fin n) :
    F.toSemiorthogonalSequenceFin.component i = F.component i.rev :=
  rfl

/-- Every component of the finite sequence is triangulated. This is the
`Fin n` counterpart of `hasTriangulatedComponents`; it is stated separately
because `toSemiorthogonalSequenceFin` lands back in the original finite order
rather than in `OrderDual (Fin n)`. -/
theorem hasTriangulatedComponentsFin [IsTriangulated C] :
    F.toSemiorthogonalSequenceFin.HasTriangulatedComponents := by
  intro i
  rw [toSemiorthogonalSequenceFin_component]
  haveI : (ObjectProperty.shiftClosure
      (fun X => X = F.obj i.rev) ℤ).Nonempty :=
    ⟨F.obj i.rev, ObjectProperty.le_shiftClosure _ _ rfl⟩
  infer_instance

end Fin

end ExceptionalCollection

end CategoryTheory.Triangulated
