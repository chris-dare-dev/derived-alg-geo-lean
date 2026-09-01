/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Order.Fin.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Basic

/-!
# Orientation of the semiorthogonal root

This file pins, once, the direction convention of `SemiorthogonalSequence`,
and supplies the adapter from the classical convention. No downstream file
should re-derive the flip when *constructing* a sequence; it calls
`ofReverse` or `ofReverseFin`.

## The two conventions, side by side

Mathlib's definition, written out so the argument order can be checked:

`ObjectProperty.rightOrthogonal P Y := ∀ ⦃X : C⦄ (f : X ⟶ Y), P X → f = 0`

— every map *from* a `P` object *into* `Y` vanishes. The root's field

`semiorthogonal : i < j → component j ≤ (component i).rightOrthogonal`

therefore unfolds to: for `i < j`, `hX : component i X`, `hY : component j Y`
and `f : X ⟶ Y`, `f = 0` — the root vanishes **Hom(earlier, later)**, as its
own `SemiorthogonalSequence.hom_eq_zero` witnesses.

The classical convention `⟨A₀, …, Aₙ⟩` of the literature instead requires
`Hom(A_j, A_i) = 0` for `i < j` — maps from **later** to **earlier** vanish.
The two differ by reversing the index order, not by swapping an orthogonal:
`ofReverse` reindexes along `OrderDual` and forgets nothing, and
`ofReverseFin` lands the finite case back on `Fin n` through the root's own
`reindex` along `OrderDual.toDual ∘ Fin.rev`.

## Main definitions

* `SemiorthogonalSequence.ofReverse` — a classically-ordered family, as a
  sequence indexed by the order dual.
* `SemiorthogonalSequence.ofReverseFin` — the finite case, landed back on
  `Fin n` by reversal.

## Main results

* `SemiorthogonalSequence.ofReverse_hom_eq_zero` — the vanishing read in the
  classical direction; the lemma consumers cite.

## References

* Huybrechts, *Fourier–Mukai Transforms in Algebraic Geometry*, §1.4, for the
  classical `⟨A₀, …, Aₙ⟩` convention with `Hom(A_j, A_i) = 0` for `i < j`;
  Bondal–Orlov, *Semiorthogonal decompositions for algebraic varieties*, for
  its origin.

## Tags

semiorthogonal decomposition, orientation, order dual
-/

universe u v w

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type w} [Preorder ι]

namespace SemiorthogonalSequence

/-- A classically-ordered semiorthogonal family — `Hom(component j,
component i) = 0` for `i < j` — as a `SemiorthogonalSequence` indexed by the
order dual. The `semiorthogonal` field is the hypothesis applied to the dual
order relation and nothing else: reversing the index order *is* the whole
difference between the conventions. -/
def ofReverse (component : ι → ObjectProperty C)
    (h : ∀ ⦃i j : ι⦄, i < j → component i ≤ (component j).rightOrthogonal) :
    SemiorthogonalSequence C ιᵒᵈ where
  component i := component (OrderDual.ofDual i)
  semiorthogonal := fun _ _ hij => h hij

@[simp]
lemma ofReverse_component (component : ι → ObjectProperty C)
    (h : ∀ ⦃i j : ι⦄, i < j → component i ≤ (component j).rightOrthogonal)
    (i : ιᵒᵈ) :
    (ofReverse component h).component i = component (OrderDual.ofDual i) :=
  rfl

/-- The vanishing of `ofReverse`, read in the classical direction: for
`i < j`, maps from the *later* component into the *earlier* one vanish. This
is the form consumers cite, so the classical index order appears here and the
`OrderDual` bookkeeping does not. -/
lemma ofReverse_hom_eq_zero (component : ι → ObjectProperty C)
    (h : ∀ ⦃i j : ι⦄, i < j → component i ≤ (component j).rightOrthogonal)
    ⦃i j : ι⦄ (hij : i < j) ⦃X Y : C⦄
    (hX : component j X) (hY : component i Y) (f : X ⟶ Y) : f = 0 :=
  (ofReverse component h).hom_eq_zero
    (show OrderDual.toDual j < OrderDual.toDual i from hij) hX hY f

/-- The finite classical case, landed back on `Fin n`: component `i` of the
result is the classical component `i.rev`. Built through the root's own
`reindex` along `OrderDual.toDual ∘ Fin.rev` — strict monotonicity into the
dual is exactly strict antitonicity of `Fin.rev`, the core lemma
`Fin.rev_lt_rev` (bundled in Mathlib as `Fin.rev_strictAnti`) — so no second
reindexing construction exists. -/
def ofReverseFin (n : ℕ) (component : Fin n → ObjectProperty C)
    (h : ∀ ⦃i j : Fin n⦄, i < j → component i ≤ (component j).rightOrthogonal) :
    SemiorthogonalSequence C (Fin n) :=
  (ofReverse component h).reindex (fun i => OrderDual.toDual i.rev)
    (fun _ _ hij => Fin.rev_lt_rev.mpr hij)

@[simp]
lemma ofReverseFin_component (n : ℕ) (component : Fin n → ObjectProperty C)
    (h : ∀ ⦃i j : Fin n⦄, i < j → component i ≤ (component j).rightOrthogonal)
    (i : Fin n) :
    (ofReverseFin n component h).component i = component i.rev :=
  rfl

end SemiorthogonalSequence

end CategoryTheory.Triangulated
