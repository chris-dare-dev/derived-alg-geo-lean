/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.FullSubcategory
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic

/-!
# When a full dg subcategory is pretriangulated

`dg-enhancements-e8`, part two. `IsPretriangulated` asks for a zero object, a
shift of every object, and a cone on every closed degree-zero morphism. This
file says exactly what a predicate `P` must satisfy for the full dg
subcategory on `P` to inherit all three.

## The restriction direction, and why only that one

`IsShiftBy X n Y` and `IsConeOf f Z` are not data attached to `Y` and `Z`: they
are *representability* conditions, each of the form "right composition with one
fixed closed element is bijective **from every object** `W`". That universal
quantifier is what makes this file short, and it is also what makes it
one-directional.

In `DGFullSubcategory P` the quantifier ranges over the objects satisfying `P`,
which are fewer. So an ambient witness is already a witness downstairs, with
the same element and the same closedness proof and the bijectivity instantiated
at `W.obj` — that is all `isShiftByRestrict` and `isConeOfRestrict` do, and
neither needs a single rewrite, because `dgHom X Y` is `dgHom X.obj Y.obj` by
definition.

**The converse is false in general**, and it is worth being plain about why: a
map `compRight W hom p q h` can be bijective for every `W` satisfying `P` and
fail to be bijective for some ambient `W`. Nothing below asserts that
direction, and no later file should reach for it.

## Why the hypotheses are closure conditions rather than a supplied conclusion

The three fields of `IsPretriangulated (DGFullSubcategory P)` could have been
taken as inputs. They are not. Each is *derived* from a statement about `P`
alone:

* `ContainsZeroObject P` — `P` holds of some object with vanishing identity;
* `ClosedUnderShift P` — a shift of a `P`-object can be chosen in `P`;
* `ClosedUnderCone P` — a cone on a closed degree-zero map between
  `P`-objects can be chosen in `P`.

Each of the three is a property of the *predicate*, checkable where the
predicate is defined, and for the K-injective model each is a theorem of
Mathlib rather than an assumption this repository makes. That is the point of
stating them this way: `HomotopyCategory/DGEnhancement/KInjective.lean`
discharges all three, so nothing about resolutions arrives here as a
caller-supplied conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct

namespace DGFullSubcategory

variable {C : Type u} [DGCategory.{v} C] {P : C → Prop}

/-! ### Ambient witnesses restrict -/

/-- An ambient shift witness is a shift witness in the full dg subcategory:
same element, same closedness, bijectivity read at fewer objects. -/
def isShiftByRestrict {X Y : DGFullSubcategory P} {n : ℤ}
    (h : IsShiftBy X.obj n Y.obj) : IsShiftBy X n Y where
  hom := h.hom
  hom_closed := h.hom_closed
  bijective W p q hpq := h.bijective W.obj p q hpq

/-- An ambient cone witness is a cone witness in the full dg subcategory. Both
inclusions and both of their defining identities are the ambient ones. -/
def isConeOfRestrict {X Y Z : DGFullSubcategory P} {f : (dgHom X Y).X 0}
    (h : IsConeOf (X := X.obj) (Y := Y.obj) f Z.obj) : IsConeOf f Z where
  inr := h.inr
  inr_closed := h.inr_closed
  inl := h.inl
  δ_inl := h.δ_inl
  bijective W p q hq := h.bijective W.obj p q hq

/-! ### The closure conditions -/

/-- `P` holds of an object whose identity vanishes, so the full dg subcategory
has the zero object `H⁰` needs. -/
def ContainsZeroObject (P : C → Prop) : Prop := ∃ Z : C, P Z ∧ dgId Z = 0

/-- `P` is closed under shifts: for every `P`-object and every degree, some
shift of it in that degree again satisfies `P`. The shift is chosen, not
constructed, because `IsShiftBy` is a representability condition and a dg
category has no shift functor. -/
def ClosedUnderShift (P : C → Prop) : Prop :=
  ∀ X : C, P X → ∀ n : ℤ, ∃ Y : C, P Y ∧ Nonempty (IsShiftBy X n Y)

/-- `P` is closed under cones: a cone on a closed degree-zero morphism between
`P`-objects can be chosen to satisfy `P`. -/
def ClosedUnderCone (P : C → Prop) : Prop :=
  ∀ {X Y : C}, P X → P Y → ∀ f : (dgHom X Y).X 0, f ∈ cocycles X Y →
    ∃ Z : C, P Z ∧ Nonempty (IsConeOf f Z)

/-! ### The inheritance theorem -/

/-- **A full dg subcategory closed under zero, shifts and cones is
pretriangulated.** Each field is the corresponding closure condition followed
by the matching restriction lemma; no representability is reproved. -/
theorem isPretriangulated (hz : ContainsZeroObject P) (hs : ClosedUnderShift P)
    (hc : ClosedUnderCone P) :
    IsPretriangulated (DGFullSubcategory P) where
  exists_zero := by
    obtain ⟨Z, hZ, hid⟩ := hz
    exact ⟨mk Z hZ, hid⟩
  exists_shift X n := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := hs X.obj X.prop n
    exact ⟨mk Y hY, ⟨isShiftByRestrict e⟩⟩
  exists_cone {X Y} f hf := by
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hc X.prop Y.prop f hf
    exact ⟨mk Z hZ, ⟨isConeOfRestrict e⟩⟩

/-- The whole dg category is the full dg subcategory on `fun _ => True`, and
the three closure conditions there are exactly the three fields of
`IsPretriangulated C`. Recorded as a sanity check on the shape of the
conditions: if any of them had been stated too strongly, this would fail. -/
lemma closedUnderShift_true [IsPretriangulated.{v} C] :
    ClosedUnderShift (fun _ : C => True) := by
  intro X _ n
  obtain ⟨Y, hY⟩ := IsPretriangulated.exists_shift X n
  exact ⟨Y, trivial, hY⟩

/-- The cone half of the same sanity check. -/
lemma closedUnderCone_true [IsPretriangulated.{v} C] :
    ClosedUnderCone (fun _ : C => True) := by
  intro X Y _ _ f hf
  obtain ⟨Z, hZ⟩ := IsPretriangulated.exists_cone f hf
  exact ⟨Z, trivial, hZ⟩

/-- The zero-object half of the same sanity check. -/
lemma containsZeroObject_true [IsPretriangulated.{v} C] :
    ContainsZeroObject (fun _ : C => True) := by
  obtain ⟨Z, hZ⟩ := IsPretriangulated.exists_zero (C := C)
  exact ⟨Z, trivial, hZ⟩

end DGFullSubcategory

end CategoryTheory
