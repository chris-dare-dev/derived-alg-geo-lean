/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory.H0

/-!
# Shifts and cones inside a dg category

`dg-enhancements-e5`. A dg category has no shift functor and no cone
construction the way a triangulated category has: it has *representability
conditions*, and this file states them.

## Why these are predicates rather than constructions

`X[n]` and `Cone f` are not built from `X` and `f`. They are objects of `C`
whose dg module of maps *in* is prescribed:

* `Y` is a shift of `X` by `n` when `dgHom W Y ≅ (dgHom W X)⟦n⟧`, naturally in
  `W`;
* `Z` is a cone on a closed degree-zero `f : X ⟶ Y` when `dgHom W Z` is the
  mapping cone of `dgHom W X → dgHom W Y`, naturally in `W`.

Both are conditions a dg category may or may not satisfy, so `IsPretriangulated`
is a class asserting that it does.

## Naturality is not an axiom here

Each condition is stated as *right composition with one fixed element is
bijective*, and that is what buys the naturality clause for free: composition
with a fixed element commutes with composition on the other side by
`dgComp_assoc`, so there is no square left to impose. Stating the iso of dg
modules directly would put a graded naturality axiom in the structure and then
oblige every witness to prove it.

## The degree conventions

`Hom^d(K, L) = ∏ₚ Hom(Kᵖ, L^{p+d})`, so with `L = X[n]` the identity-like
element of `Hom(X, X[n])` sits in degree `-n`, not `n`. That is why
`IsShiftBy.hom` has degree `-n`, and it matches Mathlib: `mappingCone.inl` is a
`Cochain F (mappingCone φ) (-1)`, the inclusion of `F[1]`.

The cone conditions are transcribed from Mathlib's `mappingCone` API rather than
rederived. `IsConeOf.δ_inl` is `mappingCone.δ_inl`, and the bijectivity clause
is the pair `mappingCone.id` (surjectivity) and `inl_fst`/`inl_snd`/`inr_fst`/
`inr_snd` (injectivity).

## The zero clause is dg-level, and stronger than it needs to be

`IsPretriangulated.exists_zero` asks for an object with `dgId Z = 0`. In a
preadditive category that is exactly "`Z` is a zero object", so the clause says
`Z⁰ C` and `H⁰ C` have a zero object on the nose.

The literature does not axiomatize this: `Cone (𝟙 X)` is contractible, so `H⁰`
gets its zero object from the cone clause alone. Contractibility is a homotopy
statement about `H⁰`, which is `dg-enhancements-e6`'s subject, and deriving the
zero object there rather than assuming it here would invert the dependency. The
clause is kept, and it costs nothing: every model in this repository has a
strict dg zero object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- Right composition with a fixed `ε : (dgHom X Y).X n`, as an additive map on
the Hom-complex from any `W`. This is the map every representability condition
below asks to be bijective. -/
def compRight (W : C) {X Y : C} {n : ℤ} (ε : (dgHom X Y).X n) (p q : ℤ) (h : p + n = q) :
    (dgHom W X).X p →+ (dgHom W Y).X q :=
  (dgComp p n q h).flip ε

@[simp]
lemma compRight_apply (W : C) {X Y : C} {n : ℤ} (ε : (dgHom X Y).X n) (p q : ℤ)
    (h : p + n = q) (f : (dgHom W X).X p) :
    compRight W ε p q h f = dgComp p n q h f ε := rfl

/-- `ε` exhibits `Y` as a shift of `X` by `n`: it is closed of degree `-n`, and
right composition with it identifies `dgHom W X` with `dgHom W Y` in every
degree, for every `W`. -/
structure IsShiftBy (X : C) (n : ℤ) (Y : C) where
  /-- The identity-like element, of degree `-n`. -/
  hom : (dgHom X Y).X (-n)
  /-- It is closed. -/
  hom_closed : ((dgHom X Y).d (-n) (-n + 1)).hom hom = 0
  /-- Right composition with it is bijective in every degree, from every object. -/
  bijective (W : C) (p q : ℤ) (h : p + -n = q) :
    Function.Bijective (compRight W hom p q h)

/-- `Z` is a cone on the closed degree-zero morphism `f : X ⟶ Y`: it carries an
inclusion `inr` of `Y` and a degree `-1` inclusion `inl` of `X` whose
differential is `f ≫ inr`, and every map into `Z` splits uniquely along the
two. -/
structure IsConeOf {X Y : C} (f : (dgHom X Y).X 0) (Z : C) where
  /-- The inclusion of `Y`. -/
  inr : (dgHom Y Z).X 0
  /-- It is closed. -/
  inr_closed : ((dgHom Y Z).d 0 1).hom inr = 0
  /-- The inclusion of `X`, of degree `-1`. -/
  inl : (dgHom X Z).X (-1)
  /-- Its differential is `f` followed by `inr`. This is `mappingCone.δ_inl`. -/
  δ_inl : ((dgHom X Z).d (-1) 0).hom inl = dgComp 0 0 0 (by omega) f inr
  /-- Every map into `Z` splits uniquely as `a ≫ inl + b ≫ inr`. -/
  bijective (W : C) (p q : ℤ) (hq : p + 1 = q) :
    Function.Bijective (fun ab : (dgHom W X).X q × (dgHom W Y).X p =>
      dgComp q (-1) p (by omega) ab.1 inl + dgComp p 0 p (by omega) ab.2 inr)

/-- A composite of closed elements is closed. Both Leibniz terms carry a factor
that vanishes, so the sign never has to be computed. Stated once here because
every construction below composes two or three closed elements. -/
lemma dgComp_closed {X Y Z : C} {p q r r' : ℤ} (h : p + q = r) (hr : r + 1 = r')
    {f : (dgHom X Y).X p} {g : (dgHom Y Z).X q}
    (hf : ((dgHom X Y).d p (p + 1)).hom f = 0)
    (hg : ((dgHom Y Z).d q (q + 1)).hom g = 0) :
    ((dgHom X Z).d r r').hom (dgComp p q r h f g) = 0 := by
  rw [dgComp_leibniz p q r r' h hr f g, hf, hg]
  simp

namespace IsShiftBy

/-- Every object is its own shift by zero, witnessed by the identity. The
degree-`-0` and degree-`0` Hom-groups are the same group, so no transport is
needed. -/
def self (X : C) : IsShiftBy X 0 X where
  hom := dgId X
  hom_closed := dgId_cocycle X
  bijective W p q h := by
    have hq : q = p := by omega
    subst hq
    -- `-0` and `0` are the same integer definitionally but not syntactically:
    -- the field's degree is `-n`, so `compRight` here carries `n := -0` while
    -- `dgComp_id` is stated at `0`. `exact` closes the gap and `simp` does not,
    -- so the two directions are term proofs rather than rewrites.
    refine ⟨fun a b hab => ?_, fun c => ⟨c, ?_⟩⟩
    · exact (dgComp_id q a).symm.trans (hab.trans (dgComp_id q b))
    · exact dgComp_id q c

section Inverse

variable {X Y Y' : C} {n : ℤ}

/-- The element inverse to `s.hom`. It exists because right composition with
`s.hom` is surjective onto `(dgHom Y Y).X 0`, which contains `dgId Y`. -/
noncomputable def inv (s : IsShiftBy X n Y) : (dgHom Y X).X n :=
  ((s.bijective Y n 0 (by omega)).surjective (dgId Y)).choose

/-- The defining property of `s.inv`: composing it with `s.hom` is the identity
of `Y`. -/
lemma inv_hom (s : IsShiftBy X n Y) :
    dgComp n (-n) 0 (by omega) s.inv s.hom = dgId Y :=
  ((s.bijective Y n 0 (by omega)).surjective (dgId Y)).choose_spec

/-- And the other way round. `s.hom` is not assumed invertible; this is forced,
because right composition with it is injective on `(dgHom X X).X 0` and both
sides go to `s.hom`. -/
lemma hom_inv (s : IsShiftBy X n Y) :
    dgComp (-n) n 0 (by omega) s.hom s.inv = dgId X := by
  refine (s.bijective X 0 (-n) (by omega)).injective ?_
  show dgComp 0 (-n) (-n) _ (dgComp (-n) n 0 (by omega) s.hom s.inv) s.hom =
    dgComp 0 (-n) (-n) _ (dgId X) s.hom
  rw [dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    inv_hom, dgComp_id, dgId_comp]

/-- `s.inv` is closed. The Leibniz rule at `(n, -n)` has its first term killed
by `s.hom` being closed and its second scaled by a unit, so the differential of
`s.inv` composes to zero with `s.hom` -- and right composition with `s.hom` is
injective. -/
lemma inv_closed (s : IsShiftBy X n Y) :
    ((dgHom Y X).d n (n + 1)).hom s.inv = 0 := by
  have key := dgComp_leibniz (C := C) n (-n) 0 1 (by omega) (by omega) s.inv s.hom
  rw [inv_hom, dgId_cocycle, s.hom_closed] at key
  -- `key` is now `0 = 0 + (-n).negOnePow • ((δ s.inv) ∘ s.hom)`. The sign is a
  -- unit, so the composite itself vanishes.
  have key2 : dgComp (n + 1) (-n) 1 (by omega)
      (((dgHom Y X).d n (n + 1)).hom s.inv) s.hom = 0 := by
    simpa [smul_eq_zero_iff_eq] using key.symm
  refine (s.bijective Y (n + 1) 1 (by omega)).injective ?_
  show dgComp (n + 1) (-n) 1 _ (((dgHom Y X).d n (n + 1)).hom s.inv) s.hom =
    dgComp (n + 1) (-n) 1 _ 0 s.hom
  rw [key2, map_zero, AddMonoidHom.zero_apply]

end Inverse

section Uniqueness

variable {X Y Y' Y'' : C} {n : ℤ}

/-- The comparison between two shifts of `X` by `n`: go back along one and out
along the other. -/
noncomputable def compare (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    (dgHom Y Y').X 0 :=
  dgComp n (-n) 0 (by omega) s.inv s'.hom

/-- The comparison is closed, so it is a morphism of `Z⁰`. Both factors are
closed, so both Leibniz terms vanish. -/
lemma compare_mem_cocycles (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    compare s s' ∈ cocycles Y Y' := by
  have key := dgComp_leibniz (C := C) n (-n) 0 1 (by omega) (by omega) s.inv s'.hom
  rw [mem_cocycles_iff, compare, key, s'.hom_closed, s.inv_closed]
  simp

/-- The two comparisons are mutually inverse, so any two shifts of `X` by `n`
are isomorphic in `Z⁰` -- and therefore in `H⁰`. This is what lets a shift
*functor* be built from the existential `IsPretriangulated.exists_shift`
without the choice mattering. -/
lemma compare_comp_compare (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    dgComp 0 0 0 (by omega) (compare s s') (compare s' s) = dgId Y := by
  rw [compare, compare,
    dgComp_assoc n (-n) 0 0 (-n) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    hom_inv, dgId_comp, inv_hom]

/-- Comparing a shift with itself gives the identity. -/
lemma compare_self (s : IsShiftBy X n Y) : compare s s = dgId Y := by
  rw [compare, inv_hom]

/-- Comparisons compose. Together with `compare_self` and
`compare_comp_compare` this makes the shifts of `X` by `n` into a contractible
groupoid inside `Z⁰`, which is what every coherence statement about the shift
functor ultimately reduces to. -/
lemma compare_trans (s : IsShiftBy X n Y) (t : IsShiftBy X n Y')
    (w : IsShiftBy X n Y'') :
    dgComp 0 0 0 (by omega) (compare s t) (compare t w) = compare s w := by
  rw [compare, compare, compare,
    dgComp_assoc n (-n) 0 0 (-n) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    hom_inv, dgId_comp]

end Uniqueness

section Comp

variable {X Y Z : C} {n m : ℤ}

/-- Shifts compose, with the resulting degree carried as a free variable.

The free `nm` is not decoration. Every coherence statement about a shift
functor compares objects indexed by `n + 0`, `0 + n` or `(a + b) + c` against
ones indexed by `n`, `n` and `a + (b + c)`, and those are propositionally but
not definitionally equal. With the degree fixed as `n + m` the mismatch can
only be crossed by an `eqToHom` that no rewrite normalises; with it free, the
equation `n + m = nm` is a hypothesis about a *variable*, and `subst` removes
the problem outright. Mathlib carries `CochainComplex.shiftFunctorAdd'` for the
same reason.

The degree of the composite element is handed to `dgComp` as `-nm` directly,
rather than asking it to normalise `-n + -m` in a dependent position. -/
noncomputable def comp' (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) (nm : ℤ)
    (hnm : n + m = nm) : IsShiftBy X nm Z where
  hom := dgComp (-n) (-m) (-nm) (by omega) s.hom u.hom
  hom_closed :=
    dgComp_closed (by omega) (by omega) s.hom_closed u.hom_closed
  bijective W p q h := by
    -- Right composition with the composite is the composite of the two right
    -- compositions, by associativity.
    have factor : ∀ f : (dgHom W X).X p,
        compRight W (dgComp (-n) (-m) (-nm) (by omega) s.hom u.hom) p q h f =
          compRight W u.hom (p + -n) q (by omega)
            (compRight W s.hom p (p + -n) (by omega) f) := fun f => by
      simpa using
        (dgComp_assoc p (-n) (-m) (p + -n) (-nm) q (by omega) (by omega) (by omega)
          f s.hom u.hom).symm
    have : ⇑(compRight W (dgComp (-n) (-m) (-nm) (by omega) s.hom u.hom) p q h) =
        ⇑(compRight W u.hom (p + -n) q (by omega)) ∘
          ⇑(compRight W s.hom p (p + -n) (by omega)) := funext factor
    rw [this]
    exact (u.bijective W (p + -n) q (by omega)).comp (s.bijective W p (p + -n) (by omega))

/-- Shifts compose, at the definitional degree `n + m`. -/
noncomputable def comp (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) :
    IsShiftBy X (n + m) Z :=
  comp' s u (n + m) rfl

/-- `comp` is `comp'` at the definitional degree: the primed form carries the
target degree as a free variable, this one fixes it at `n + m`. -/
lemma comp_eq_comp' (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) :
    comp s u = comp' s u (n + m) rfl := rfl

@[simp]
lemma comp'_hom (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) (nm : ℤ) (hnm : n + m = nm) :
    (comp' s u nm hnm).hom = dgComp (-n) (-m) (-nm) (by omega) s.hom u.hom := rfl

@[simp]
lemma comp_hom (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) :
    (comp s u).hom = dgComp (-n) (-m) (-(n + m)) (by omega) s.hom u.hom := rfl

/-- The inverse is determined by its defining equation, because right
composition with `s.hom` is injective. -/
lemma inv_unique (s : IsShiftBy X n Y) {a : (dgHom Y X).X n}
    (ha : dgComp n (-n) 0 (by omega) a s.hom = dgId Y) : a = s.inv := by
  refine (s.bijective Y n 0 (by omega)).injective ?_
  show dgComp n (-n) 0 _ a s.hom = dgComp n (-n) 0 _ s.inv s.hom
  rw [ha, inv_hom]

/-- The inverse of a composite shift is the composite of the inverses, in the
other order. Proved by `inv_unique` rather than by unfolding: both `inv`s are
`Classical.choice`, so the only handle on them is their defining equation. -/
lemma comp'_inv (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) (nm : ℤ) (hnm : n + m = nm) :
    dgComp m n nm (by omega) u.inv s.inv = (comp' s u nm hnm).inv := by
  refine inv_unique _ ?_
  show dgComp nm (-nm) 0 _ (dgComp m n nm (by omega) u.inv s.inv)
    (dgComp (-n) (-m) (-nm) (by omega) s.hom u.hom) = dgId Z
  rw [dgComp_assoc m n (-nm) nm (-m) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc n (-n) (-m) 0 (-nm) (-m) (by omega) (by omega) (by omega),
    inv_hom, dgId_comp, inv_hom]

/-- The unprimed form, at the definitional degree. -/
lemma comp_inv (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z) :
    dgComp m n (n + m) (by omega) u.inv s.inv = (comp s u).inv :=
  comp'_inv s u (n + m) rfl

/-- Prefixing with the zero shift changes nothing: the composite's element is
`dgId ≫ u.hom`, so its inverse is `u`'s. Stated on `inv` rather than as an
equality of `IsShiftBy` structures because the `bijective` field depends on
`hom`, which would make a structure `ext` produce a `HEq` goal for no gain. -/
lemma comp'_self_left_inv (u : IsShiftBy X m Z) (h : 0 + m = m) :
    (comp' (self X) u m h).inv = u.inv := by
  refine (inv_unique _ ?_).symm
  -- `-0` is definitionally `0`, so `show` may state the composite at `0`, where
  -- `dgId_comp` matches syntactically. `rw` alone cannot cross that gap.
  show dgComp m (-m) 0 _ u.inv (dgComp 0 (-m) (-m) (by omega) (dgId X) u.hom) = dgId Z
  rw [dgId_comp, inv_hom]

/-- And suffixing with it: the composite's element is `s.hom ≫ dgId`. -/
lemma comp'_self_right_inv (s : IsShiftBy X n Y) (h : n + 0 = n) :
    (comp' s (self Y) n h).inv = s.inv := by
  refine (inv_unique _ ?_).symm
  show dgComp n (-n) 0 _ s.inv (dgComp (-n) 0 (-n) (by omega) s.hom (dgId Y)) = dgId Y
  rw [dgComp_id, inv_hom]


end Comp

section Map

variable {X X' X'' Y Y' Y'' Y''' : C} {n : ℤ}

/-- The map induced on shifts: go back along the source's shift, across, and out
along the target's. `compare` is the case `f = dgId`.

This is the action on morphisms that a shift *functor* on `H⁰` would have, and
the three lemmas below are its functoriality. The functor itself is not built
here: `IsPretriangulated.exists_shift` gives an existential rather than a
choice, and `HasShift` additionally wants `shiftFunctorZero` and
`shiftFunctorAdd` coherence. -/
noncomputable def mapShift (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (f : (dgHom X X').X 0) : (dgHom Y Y').X 0 :=
  dgComp n (-n) 0 (by omega) (dgComp n 0 n (by omega) s.inv f) s'.hom

/-- `mapShift` sends closed elements to closed elements, so it descends to `Z⁰`.
All three factors are closed. -/
lemma mapShift_mem_cocycles (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    {f : (dgHom X X').X 0} (hf : f ∈ cocycles X X') :
    mapShift s s' f ∈ cocycles Y Y' :=
  dgComp_closed (by omega) (by omega)
    (dgComp_closed (by omega) (by omega) s.inv_closed hf) s'.hom_closed

/-- The identity is sent to the identity. -/
lemma mapShift_id (s : IsShiftBy X n Y) : mapShift s s (dgId X) = dgId Y := by
  rw [mapShift, dgComp_id, inv_hom]

/-- `mapShift` is compatible with composition. The middle `s'.hom` and `s'.inv`
annihilate by `hom_inv`, which is the only place the shift's invertibility is
used. -/
lemma mapShift_comp (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (s'' : IsShiftBy X'' n Y'') (f : (dgHom X X').X 0) (g : (dgHom X' X'').X 0) :
    dgComp 0 0 0 (by omega) (mapShift s s' f) (mapShift s' s'' g) =
      mapShift s s'' (dgComp 0 0 0 (by omega) f g) := by
  rw [mapShift, mapShift, mapShift,
    dgComp_assoc n (-n) 0 0 (-n) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n 0 0 n 0 (by omega) (by omega) (by omega),
    hom_inv, dgId_comp,
    ← dgComp_assoc n 0 (-n) n (-n) 0 (by omega) (by omega) (by omega),
    dgComp_assoc n 0 0 n 0 n (by omega) (by omega) (by omega)]

/-- `compare` is `mapShift` at the identity. Recorded so the two names cannot
drift apart. -/
lemma compare_eq_mapShift (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    compare s s' = mapShift s s' (dgId X) := by
  rw [compare, mapShift, dgComp_id]

/-- `mapShift` is additive in the morphism, because `dgComp` is biadditive.
Needed before it can descend to `H⁰`, where morphisms are cosets. -/
lemma mapShift_add (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (f g : (dgHom X X').X 0) :
    mapShift s s' (f + g) = mapShift s s' f + mapShift s s' g := by
  simp [mapShift, map_add]

/-- `mapShift` of a coboundary is a coboundary, so it descends to `H⁰`.

The primitive is the obvious one, `s.inv ≫ h ≫ s'.hom`, and its differential
picks up a single sign: `s'.hom` and `s.inv` are both closed, so of the four
Leibniz terms only one survives.

## Why `n` is replaced by `m + 1` first

`dgComp_leibniz` states the shifted degrees as `p + 1` and `q + 1`, and those
are not free parameters. Writing the primitive's inner factor at degree `n - 1`
makes the rule produce `n - 1 + 1`, which is propositionally but not
definitionally `n`, and the two then sit in different `dgHom` fibres with no
rewrite available that keeps the motive type-correct.

Substituting `n = m + 1` fixes it at the source: the inner factor is written at
degree `m`, the rule produces `m + 1`, and that *is* `n` syntactically. The only
remaining shift, `-1 + 1` against `0`, is definitional for integer literals and
`rfl` closes it. -/
lemma mapShift_mem_coboundaries (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    {f : (dgHom X X').X 0} (hf : f ∈ coboundaries X X') :
    mapShift s s' f ∈ coboundaries Y Y' := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(-(m + 1)).negOnePow • dgComp m (-(m + 1)) (-1) (by omega)
    (dgComp (m + 1) (-1) m (by omega) s.inv h) s'.hom, ?_⟩
  rw [Units.smul_def, map_zsmul]
  -- The outer Leibniz step: `s'.hom` is closed, so only the second term lives.
  rw [dgComp_leibniz m (-(m + 1)) (-1) 0 (by omega) (by omega)
    (dgComp (m + 1) (-1) m (by omega) s.inv h) s'.hom, s'.hom_closed]
  -- The inner one: `s.inv` is closed, so only the first term lives.
  rw [dgComp_leibniz (m + 1) (-1) m (m + 1) (by omega) (by omega) s.inv h,
    s.inv_closed]
  simp only [map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero, zero_add]
  rw [mapShift, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  -- only `-1 + 1` against `0` is left, and for integer literals that is `rfl`
  rfl

/-- `mapShift` bundled as an additive map, so that `map_neg` and `map_sub` are
available when it descends to the quotient defining `H⁰`. -/
noncomputable def mapShiftHom (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y') :
    (dgHom X X').X 0 →+ (dgHom Y Y').X 0 :=
  AddMonoidHom.mk' (mapShift s s') (mapShift_add s s')

@[simp]
lemma mapShiftHom_apply (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (f : (dgHom X X').X 0) : mapShiftHom s s' f = mapShift s s' f := rfl

/-- Naturality of `compare`, and it costs nothing: both sides are `mapShift`
of the same morphism, by `mapShift_comp` and a unit law.

This is the payoff of stating `IsShiftBy` as representability. A shift functor
on `H⁰` needs its comparison isomorphisms to be natural, and here that is not a
diagram to chase -- it is `f ≫ 𝟙 = 𝟙 ≫ f` transported through one lemma. -/
lemma mapShift_compare (s : IsShiftBy X n Y) (t : IsShiftBy X n Y'')
    (s' : IsShiftBy X' n Y') (t' : IsShiftBy X' n Y''') (f : (dgHom X X').X 0) :
    dgComp 0 0 0 (by omega) (mapShift s s' f) (compare s' t') =
      dgComp 0 0 0 (by omega) (compare s t) (mapShift t t' f) := by
  rw [compare_eq_mapShift, compare_eq_mapShift, mapShift_comp, mapShift_comp,
    dgComp_id, dgId_comp]

/-- The zero shift's inverse is the identity. Forced, not chosen: `inv` is
`Classical.choice` on a surjectivity, but `inv_hom` pins it down. -/
lemma self_inv (X : C) : (self X).inv = dgId X :=
  (dgComp_id 0 (self X).inv).symm.trans (self X).inv_hom

/-- `mapShift` along the zero shift is the identity on morphisms. This is what
makes `shiftFunctor 0` naturally isomorphic to the identity functor. -/
lemma mapShift_self (X X' : C) (f : (dgHom X X').X 0) :
    mapShift (self X) (self X') f = f := by
  rw [mapShift, self_inv]
  exact (congrArg (fun z => dgComp 0 (-0) 0 (by omega) z (dgId X')) (dgId_comp 0 f)).trans
    (dgComp_id 0 f)

/-- **`mapShift` is determined by the square it makes commute.** An element `c`
of degree zero with `s.hom ≫ c = f ≫ s'.hom` is `mapShift s s' f`.

`mapShift` is built from `s.inv`, which is `Classical.choice`, so nothing about
it can be unfolded. What can be used is that left composition with `s.hom` is
injective -- `s.inv` is a left inverse for it by `inv_hom` -- and the defining
square is exactly what that injectivity reads off. Every identification of
`mapShift` with a concretely given morphism goes through here. -/
lemma mapShift_unique (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (f : (dgHom X X').X 0) (c : (dgHom Y Y').X 0)
    (h : dgComp (-n) 0 (-n) (by omega) s.hom c =
      dgComp 0 (-n) (-n) (by omega) f s'.hom) :
    mapShift s s' f = c := by
  have hc : dgComp n (-n) 0 (by omega) s.inv (dgComp (-n) 0 (-n) (by omega) s.hom c) = c := by
    rw [← dgComp_assoc n (-n) 0 0 (-n) 0 (by omega) (by omega) (by omega), inv_hom, dgId_comp]
  have hm : mapShift s s' f =
      dgComp n (-n) 0 (by omega) s.inv (dgComp 0 (-n) (-n) (by omega) f s'.hom) :=
    dgComp_assoc n 0 (-n) n (-n) 0 (by omega) (by omega) (by omega) s.inv f s'.hom
  rw [hm, ← h, hc]

/-- `compare` is `mapShift` at the identity, so it too is determined by its
defining square. -/
lemma compare_unique {Y' : C} (s : IsShiftBy X n Y) (t : IsShiftBy X n Y')
    (c : (dgHom Y Y').X 0)
    (h : dgComp (-n) 0 (-n) (by omega) s.hom c = t.hom) : compare s t = c := by
  rw [compare_eq_mapShift]
  refine mapShift_unique s t _ c ?_
  rw [h, dgId_comp]

end Map

section CompMap

variable {X X' Y Y' Z Z' : C} {n m : ℤ}

/-- `mapShift` along a composite shift is `mapShift` twice. Everything in sight
is a composite of the same five factors; the proof is four applications of
`dgComp_assoc` moving the brackets from one side's shape to the other's.

This is the naturality obligation of `shiftFunctorAdd` in disguise, and it is
where `comp_inv` is needed: the composite shift's inverse has to be recognised
as the composite of the inverses before either side can be reassociated. -/
lemma mapShift_comp'_shift (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z)
    (s' : IsShiftBy X' n Y') (u' : IsShiftBy Y' m Z') (nm : ℤ) (hnm : n + m = nm)
    (f : (dgHom X X').X 0) :
    mapShift (comp' s u nm hnm) (comp' s' u' nm hnm) f = mapShift u u' (mapShift s s' f) := by
  simp only [mapShift, comp'_hom]
  rw [← comp'_inv s u nm hnm,
    dgComp_assoc m n 0 nm n nm (by omega) (by omega) (by omega),
    dgComp_assoc m n (-nm) nm (-m) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc n (-n) (-m) 0 (-nm) (-m) (by omega) (by omega) (by omega),
    ← dgComp_assoc m 0 (-m) m (-m) 0 (by omega) (by omega) (by omega)]

/-- The unprimed form, at the definitional degree. -/
lemma mapShift_comp_shift (s : IsShiftBy X n Y) (u : IsShiftBy Y m Z)
    (s' : IsShiftBy X' n Y') (u' : IsShiftBy Y' m Z') (f : (dgHom X X').X 0) :
    mapShift (comp s u) (comp s' u') f = mapShift u u' (mapShift s s' f) :=
  mapShift_comp'_shift s u s' u' (n + m) rfl f

/-- Shifting a comparison is the comparison of the composites. This is
`mapShift_comp_shift` at the identity, and it is what lets the coherence
statements for the shift functor be read entirely in terms of `compare`. -/
lemma mapShift_compare_comp' (s : IsShiftBy X n Y) (t : IsShiftBy X n Y')
    (u : IsShiftBy Y m Z) (u' : IsShiftBy Y' m Z') (nm : ℤ) (hnm : n + m = nm) :
    mapShift u u' (compare s t) = compare (comp' s u nm hnm) (comp' t u' nm hnm) := by
  rw [compare_eq_mapShift s t,
    compare_eq_mapShift (comp' s u nm hnm) (comp' t u' nm hnm),
    mapShift_comp'_shift]

/-- The unprimed form, at the definitional degree. -/
lemma mapShift_compare_comp (s : IsShiftBy X n Y) (t : IsShiftBy X n Y')
    (u : IsShiftBy Y m Z) (u' : IsShiftBy Y' m Z') :
    mapShift u u' (compare s t) = compare (comp s u) (comp t u') :=
  mapShift_compare_comp' s t u u' (n + m) rfl

section Assoc

variable {W X Y Z Y' Z' : C} {a b d : ℤ}

/-- `compare s t` reads `t` only through `t.hom`, so two witnesses with the same
element compare the same way. This is the whole of what the associativity
coherence needs, once both sides are reduced to a single comparison. -/
lemma compare_congr {n : ℤ} (s : IsShiftBy X n Y) (t t' : IsShiftBy X n Y')
    (h : t.hom = t'.hom) : compare s t = compare s t' := by
  rw [compare, compare, h]

/-- The two bracketings of a threefold composite shift carry the same element.
This is `dgComp_assoc` on the three `hom`s, and nothing more -- which is why
the associativity coherence is not a diagram chase either. -/
lemma comp'_assoc_hom (s : IsShiftBy X a Y) (u : IsShiftBy Y b Z) (w : IsShiftBy Z d W)
    (ab bd abd : ℤ) (hab : a + b = ab) (hbd : b + d = bd) (habd : ab + d = abd) :
    (comp' (comp' s u ab hab) w abd habd).hom =
      (comp' s (comp' u w bd hbd) abd (by omega)).hom := by
  simp only [comp'_hom]
  exact dgComp_assoc (-a) (-b) (-d) (-ab) (-bd) (-abd) (by omega) (by omega) (by omega)
    s.hom u.hom w.hom

/-- Composing a comparison-into-a-composite with a comparison of the composite's
second factor replaces that factor. The middle `v.hom ≫ v.inv` collapses by
`hom_inv`, which is the only step with content. -/
lemma compare_comp'_right {k : ℤ} (s : IsShiftBy X k Y') (t : IsShiftBy X a Y)
    (v : IsShiftBy Y b Z) (v' : IsShiftBy Y b Z') (hk : a + b = k) :
    dgComp 0 0 0 (by omega) (compare s (comp' t v k hk)) (compare v v') =
      compare s (comp' t v' k hk) := by
  simp only [compare, comp'_hom]
  rw [dgComp_assoc k (-k) 0 0 (-k) 0 (by omega) (by omega) (by omega),
    dgComp_assoc (-a) (-b) 0 (-k) (-b) (-k) (by omega) (by omega) (by omega),
    ← dgComp_assoc (-b) b (-b) 0 0 (-b) (by omega) (by omega) (by omega),
    hom_inv, dgId_comp]

end Assoc

end CompMap

end IsShiftBy

namespace IsConeOf

variable {X Y Z : C} {f : (dgHom X Y).X 0}

/-- The composite `X ⟶ Y ⟶ Cone f` is a coboundary: `inl` is its primitive.
This is the whole content of `δ_inl`, restated so that `H⁰` can read it, and it
is what makes the cone sequence a triangle in `dg-enhancements-e6`. -/
lemma comp_inr_mem_coboundaries (hc : IsConeOf f Z) :
    dgComp 0 0 0 (by omega) f hc.inr ∈ coboundaries X Z :=
  ⟨hc.inl, hc.δ_inl⟩

/-- `inr` is a cocycle, so it is a morphism of `Z⁰`. -/
lemma inr_mem_cocycles (hc : IsConeOf f Z) : hc.inr ∈ cocycles Y Z :=
  hc.inr_closed

end IsConeOf

/-- A pretriangulated dg category: it has a zero object, a shift in every
degree, and a cone on every closed degree-zero morphism. -/
class IsPretriangulated (C : Type u) [DGCategory.{v} C] : Prop where
  /-- Some object has zero identity, so `Z⁰ C` and `H⁰ C` have a zero object. -/
  exists_zero : ∃ Z : C, dgId Z = 0
  /-- Every object has a shift in every degree. -/
  exists_shift (X : C) (n : ℤ) : ∃ Y : C, Nonempty (IsShiftBy X n Y)
  /-- Every closed degree-zero morphism has a cone. -/
  exists_cone {X Y : C} (f : (dgHom X Y).X 0) (hf : f ∈ cocycles X Y) :
    ∃ Z : C, Nonempty (IsConeOf f Z)

end CategoryTheory
