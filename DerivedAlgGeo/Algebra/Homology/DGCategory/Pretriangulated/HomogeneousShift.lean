/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic

/-!
# Transporting homogeneous morphisms across chosen shifts

`IsShiftBy.mapShift` moves a *closed degree-zero* morphism across two chosen
shifts.  A shift functor has to move morphisms of every degree, and this file
does that.

## One characterising square, and everything else follows

`shiftMap` is written down as `s.inv ≫ f ≫ s'.hom`, but nothing below unfolds
that formula.  What is used is that it is the unique degree-`p` morphism `c`
with

`s.hom ≫ c = f ≫ s'.hom`,

uniqueness holding because `s.inv ≫ s.hom = 𝟙` makes left composition with
`s.hom` injective.  Identity, composition and the differential are then three
short verifications of that square rather than three associativity chains.

## The differential is where the sign appears

`s.hom` and `s'.hom` are closed, so differentiating the square leaves one
Leibniz term, and with the repository's convention
`δ(a ≫ b) = a ≫ δb + (-1)^|b| δa ≫ b` and `|s'.hom| = -n` that term carries
`(-1)^n`.  So

`δ (shiftMap p f) = (-1)^n • shiftMap (p+1) (δ f)`,

and *not* `shiftMap (p+1) (δ f)`.  A shift functor must therefore multiply
`shiftMap` by a sign depending on the degree; `(-1)^(n * p)` is the unique
solution, and `Pretriangulated/FunctorCategory.lean` uses it.  This is the
reason the naive formula does not define a dg functor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- `dgComp` commutes with the sign action in its first argument. -/
lemma dgComp_units_smul_left {W X Y : C} (p q r : ℤ) (h : p + q = r)
    (c : ℤˣ) (f : (dgHom W X).X p) (g : (dgHom X Y).X q) :
    dgComp p q r h (c • f) g = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- `dgComp` commutes with the sign action in its second argument. -/
lemma dgComp_units_smul_right {W X Y : C} (p q r : ℤ) (h : p + q = r)
    (c : ℤˣ) (f : (dgHom W X).X p) (g : (dgHom X Y).X q) :
    dgComp p q r h f (c • g) = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

namespace IsShiftBy

variable {A A' B B' E E' : C} {n : ℤ}

/-- Transport a homogeneous morphism across chosen shifts of its source and
target: go back along the source's shift, across, and out along the target's.

`mapShift` is this at degree zero.  The sign that makes the construction a dg
functor is *not* included here; see the module docstring. -/
noncomputable def shiftMap (s : IsShiftBy A n A') (s' : IsShiftBy B n B')
    (p : ℤ) (f : (dgHom A B).X p) : (dgHom A' B').X p :=
  dgComp (n + p) (-n) p (by omega)
    (dgComp n p (n + p) (by omega) s.inv f) s'.hom

/-- **The characterising square.**  `s.hom` followed by the transported
morphism is the morphism followed by `s'.hom`. -/
lemma hom_comp_shiftMap (s : IsShiftBy A n A') (s' : IsShiftBy B n B')
    (p m : ℤ) (hm : -n + p = m) (hm' : p + -n = m)
    (f : (dgHom A B).X p) :
    dgComp (-n) p m hm s.hom (s.shiftMap s' p f) =
      dgComp p (-n) m hm' f s'.hom := by
  rw [shiftMap,
    ← dgComp_assoc (-n) (n + p) (-n) p p m (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n p 0 (n + p) p (by omega) (by omega) (by omega),
    s.hom_inv, dgId_comp]

/-- **The transported morphism is the only one making that square commute.**

Left composition with `s.hom` is injective because `s.inv` is a left inverse
for it, so the square determines `c`.  Every property of `shiftMap` below is
proved by checking the square for a candidate. -/
lemma shiftMap_unique (s : IsShiftBy A n A') (s' : IsShiftBy B n B')
    (p m : ℤ) (hm : -n + p = m) (hm' : p + -n = m)
    (f : (dgHom A B).X p) (c : (dgHom A' B').X p)
    (h : dgComp (-n) p m hm s.hom c = dgComp p (-n) m hm' f s'.hom) :
    s.shiftMap s' p f = c := by
  have hcancel : ∀ d : (dgHom A' B').X p,
      dgComp n m p (by omega) s.inv (dgComp (-n) p m hm s.hom d) = d := by
    intro d
    rw [← dgComp_assoc n (-n) p 0 m p (by omega) (by omega) (by omega),
      s.inv_hom, dgId_comp]
  rw [← hcancel (s.shiftMap s' p f), ← hcancel c,
    s.hom_comp_shiftMap s' p m hm hm' f, h]

/-- Transport is additive in the morphism. -/
lemma shiftMap_add (s : IsShiftBy A n A') (s' : IsShiftBy B n B') (p : ℤ)
    (f g : (dgHom A B).X p) :
    s.shiftMap s' p (f + g) = s.shiftMap s' p f + s.shiftMap s' p g := by
  simp [shiftMap, map_add]

@[simp]
lemma shiftMap_zero (s : IsShiftBy A n A') (s' : IsShiftBy B n B') (p : ℤ) :
    s.shiftMap s' p 0 = 0 := by
  simp [shiftMap]

/-- Transport commutes with the sign action. -/
lemma shiftMap_units_smul (s : IsShiftBy A n A') (s' : IsShiftBy B n B') (p : ℤ)
    (c : ℤˣ) (f : (dgHom A B).X p) :
    s.shiftMap s' p (c • f) = c • s.shiftMap s' p f := by
  simp [shiftMap, Units.smul_def, map_zsmul]

/-- Transport takes the identity to the identity. -/
lemma shiftMap_id (s : IsShiftBy A n A') :
    s.shiftMap s 0 (dgId A) = dgId A' := by
  refine s.shiftMap_unique s 0 (-n) (by omega) (by omega) (dgId A) (dgId A') ?_
  rw [dgComp_id, dgId_comp]

/-- Transport preserves the graded composition. -/
lemma shiftMap_comp (s : IsShiftBy A n A') (s' : IsShiftBy B n B')
    (s'' : IsShiftBy E n E') (p q r : ℤ) (h : p + q = r)
    (f : (dgHom A B).X p) (g : (dgHom B E).X q) :
    s.shiftMap s'' r (dgComp p q r h f g) =
      dgComp p q r h (s.shiftMap s' p f) (s'.shiftMap s'' q g) := by
  refine s.shiftMap_unique s'' r (-n + r) (by omega) (by omega) _ _ ?_
  rw [← dgComp_assoc (-n) p q (-n + p) r (-n + r)
      (by omega) (by omega) (by omega),
    s.hom_comp_shiftMap s' p (-n + p) (by omega) (by omega) f,
    dgComp_assoc p (-n) q (-n + p) (-n + q) (-n + r)
      (by omega) (by omega) (by omega),
    s'.hom_comp_shiftMap s'' q (-n + q) (by omega) (by omega) g,
    ← dgComp_assoc p q (-n) r (-n + q) (-n + r)
      (by omega) (by omega) (by omega)]

/-- Transport followed by the target's inverse is the source's inverse
followed by the morphism.  The two `hom`/`inv` factors in the middle cancel,
and this is the form the shift witness's surjectivity argument needs. -/
lemma shiftMap_comp_inv (s : IsShiftBy A n A') (s' : IsShiftBy B n B')
    (p m : ℤ) (hm : p + n = m) (hm' : n + p = m)
    (f : (dgHom A B).X p) :
    dgComp p n m hm (s.shiftMap s' p f) s'.inv =
      dgComp n p m hm' s.inv f := by
  -- Normalise the result index first: `dgComp_id` is stated at the index it
  -- already carries, and `m` is only propositionally `n + p`.
  have hmn : m = n + p := by omega
  cases hmn
  rw [shiftMap,
    dgComp_assoc (n + p) (-n) n p 0 (n + p) (by omega) (by omega) (by omega),
    s'.hom_inv, dgComp_id]


/-- **Transport does not commute with the differential; it anticommutes by
`(-1)^n`.**

Both `s.hom` and `s'.hom` are closed, so differentiating the characterising
square leaves the single Leibniz term carrying `(-1)^{-n} = (-1)^n`.  This is
the identity that forces a shift functor's sign, and it is why the naive
formula does not define a dg functor. -/
lemma shiftMap_d (s : IsShiftBy A n A') (s' : IsShiftBy B n B') (p : ℤ)
    (f : (dgHom A B).X p) :
    ((dgHom A' B').d p (p + 1)).hom (s.shiftMap s' p f) =
      n.negOnePow •
        s.shiftMap s' (p + 1) (((dgHom A B).d p (p + 1)).hom f) := by
  -- Differentiate the characterising square.  One Leibniz term survives on
  -- each side, and the surviving one on the right carries `(-1)^(-n)`.
  have hleft := dgComp_leibniz (C := C) (-n) p (-n + p) (-n + p + 1)
    (by omega) (by omega) s.hom (s.shiftMap s' p f)
  have hright := dgComp_leibniz (C := C) p (-n) (-n + p) (-n + p + 1)
    (by omega) (by omega) f s'.hom
  have hsq : ((dgHom A B').d (-n + p) (-n + p + 1)).hom
        (dgComp (-n) p (-n + p) (by omega) s.hom (s.shiftMap s' p f)) =
      ((dgHom A B').d (-n + p) (-n + p + 1)).hom
        (dgComp p (-n) (-n + p) (by omega) f s'.hom) := by
    rw [s.hom_comp_shiftMap s' p (-n + p) (by omega) (by omega) f]
  rw [hleft, hright, s.hom_closed, s'.hom_closed] at hsq
  simp only [map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero,
    zero_add] at hsq
  rw [Int.negOnePow_neg] at hsq
  -- The square identifies `(-1)^n • δ (shiftMap p f)` as the transport of `δ f`.
  have huniq : s.shiftMap s' (p + 1) (((dgHom A B).d p (p + 1)).hom f) =
      n.negOnePow • ((dgHom A' B').d p (p + 1)).hom (s.shiftMap s' p f) := by
    refine s.shiftMap_unique s' (p + 1) (-n + p + 1) (by omega) (by omega) _ _ ?_
    rw [dgComp_units_smul_right, hsq, smul_smul, Int.units_mul_self, one_smul]
  rw [huniq, smul_smul, Int.units_mul_self, one_smul]

/-- **Naturality transports back along the inverses.**

Suppose a degree-`q` family is natural for the transported morphism
`s.shiftMap t r g` (with the shift functor's sign `(-1)^(n r)` in place).  Then
the family composed with the inverses is natural for `g` itself, at degree
`p = q + n`, and the sign becomes `(-1)^(p r)`.

This is the step that makes right composition with a shift element surjective
on natural transformations, and it is stated here, with every object a
variable, on purpose: in the dg category of dg functors the same identity has
`(F.shiftedFunctor n).obj X` and `F.shiftObj n X` in the two arguments, which
are definitionally but not syntactically equal, and `rw` cannot build a motive
over such a goal. -/
lemma comp_inv_naturality (s : IsShiftBy A n A') (t : IsShiftBy B n B')
    {V V' : C} (q p r m rq : ℤ) (hp : q + n = p) (hrq : r + q = rq)
    (hm : r + p = m) (hm' : p + r = m)
    (w : (dgHom V V').X r) (α : (dgHom V A').X q) (β : (dgHom V' B').X q)
    (g : (dgHom A B).X r)
    (hnat : dgComp r q rq hrq w β =
      (q * r).negOnePow • dgComp q r rq (by omega) α
        ((n * r).negOnePow • s.shiftMap t r g)) :
    dgComp r p m hm w (dgComp q n p hp β t.inv) =
      (p * r).negOnePow • dgComp p r m hm' (dgComp q n p hp α s.inv) g := by
  rw [← dgComp_assoc r q n rq p m (by omega) (by omega) (by omega), hnat]
  simp only [dgComp_units_smul_left, dgComp_units_smul_right, smul_smul,
    ← Int.negOnePow_add]
  rw [dgComp_assoc q r n rq (r + n) m (by omega) (by omega) (by omega),
    s.shiftMap_comp_inv t r (r + n) (by omega) (by omega) g,
    ← dgComp_assoc q n r p (r + n) m (by omega) (by omega) (by omega),
    show q * r + n * r = p * r by rw [← hp]; ring]

/-- Composing with the inverse and then with the shift element again is the
identity.  Stated with the ambient object a variable for the same reason as
`comp_inv_naturality`. -/
lemma comp_inv_comp_hom (s : IsShiftBy A n A') {V : C} (q p : ℤ)
    (hp : q + n = p) (hq : p + -n = q) (α : (dgHom V A').X q) :
    dgComp p (-n) q hq (dgComp q n p hp α s.inv) s.hom = α := by
  rw [dgComp_assoc q n (-n) p 0 q (by omega) (by omega) (by omega),
    s.inv_hom, dgComp_id]

/-! ### Comparing two chosen shifts, and composing shifts

Everything above fixes one shift of the source and one of the target.  A shift
*functor* needs two more things: that the shifts of one object by `n` form a
contractible groupoid, which `IsShiftBy.compare` already says, and that
shifting by `n` and then by `m` agrees with shifting by `n + m`.  The lemmas
here make both statements natural in the morphism rather than true only at
each object. -/

/-- **The characterising property of `compare`.**  Composing the first shift
element with the comparison gives the second; this is `s.hom ≫ s.inv = 𝟙` and
nothing else.  Every use of `compare` below reduces to it. -/
lemma hom_comp_compare {A'' : C} (s : IsShiftBy A n A') (t : IsShiftBy A n A'') :
    dgComp (-n) 0 (-n) (by omega) s.hom (compare s t) = t.hom := by
  rw [compare,
    ← dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    s.hom_inv, dgId_comp]

/-- **Transport commutes with the comparison of chosen shifts.**

Both sides are the transport of `f` from `s` to `t'`, because both satisfy that
one characterising square; `shiftMap_unique` is applied twice and the two
results are compared.  This is what lets a shift functor be built from chosen
witnesses without the choice mattering, in every degree and not only in degree
zero. -/
lemma shiftMap_compare {A'' B'' : C} (s : IsShiftBy A n A')
    (t : IsShiftBy A n A'') (s' : IsShiftBy B n B') (t' : IsShiftBy B n B'')
    (p : ℤ) (f : (dgHom A B).X p) :
    dgComp p 0 p (by omega) (s.shiftMap s' p f) (compare s' t') =
      dgComp 0 p p (by omega) (compare s t) (t.shiftMap t' p f) := by
  have hleft : s.shiftMap t' p f =
      dgComp p 0 p (by omega) (s.shiftMap s' p f) (compare s' t') := by
    refine s.shiftMap_unique t' p (-n + p) (by omega) (by omega) f _ ?_
    rw [← dgComp_assoc (-n) p 0 (-n + p) p (-n + p)
        (by omega) (by omega) (by omega),
      s.hom_comp_shiftMap s' p (-n + p) (by omega) (by omega) f,
      dgComp_assoc p (-n) 0 (-n + p) (-n) (-n + p)
        (by omega) (by omega) (by omega),
      s'.hom_comp_compare t']
  have hright : s.shiftMap t' p f =
      dgComp 0 p p (by omega) (compare s t) (t.shiftMap t' p f) := by
    refine s.shiftMap_unique t' p (-n + p) (by omega) (by omega) f _ ?_
    rw [← dgComp_assoc (-n) 0 p (-n) p (-n + p)
        (by omega) (by omega) (by omega),
      s.hom_comp_compare t,
      t.hom_comp_shiftMap t' p (-n + p) (by omega) (by omega) f]
  rw [← hleft, ← hright]

/-- **Transport across a composite shift is the two transports in turn.**

`IsShiftBy.comp'` composes two shift witnesses; this says its `shiftMap` is the
composite of the two `shiftMap`s.  Together with `shiftMap_compare` it is the
whole content of a shift functor being additive in the degree. -/
lemma comp'_shiftMap {E E'' : C} {m : ℤ} (s : IsShiftBy A n A')
    (u : IsShiftBy A' m E) (s' : IsShiftBy B n B') (u' : IsShiftBy B' m E'')
    (nm : ℤ) (hnm : n + m = nm) (p : ℤ) (f : (dgHom A B).X p) :
    (s.comp' u nm hnm).shiftMap (s'.comp' u' nm hnm) p f =
      u.shiftMap u' p (s.shiftMap s' p f) := by
  refine (s.comp' u nm hnm).shiftMap_unique (s'.comp' u' nm hnm) p (-nm + p)
    (by omega) (by omega) f _ ?_
  rw [comp'_hom, comp'_hom,
    dgComp_assoc (-n) (-m) p (-nm) (-m + p) (-nm + p)
      (by omega) (by omega) (by omega),
    u.hom_comp_shiftMap u' p (-m + p) (by omega) (by omega) (s.shiftMap s' p f),
    ← dgComp_assoc (-n) p (-m) (-n + p) (-m + p) (-nm + p)
      (by omega) (by omega) (by omega),
    s.hom_comp_shiftMap s' p (-n + p) (by omega) (by omega) f,
    dgComp_assoc p (-n) (-m) (-n + p) (-nm) (-nm + p)
      (by omega) (by omega) (by omega)]

/-- **The two transports and their two signs, merged.**

This is `comp'_shiftMap` with the shift functor's Koszul signs already in
place: shifting by `n` contributes `(-1)^(n p)` and then shifting by `m`
contributes `(-1)^(m p)`, and the product is the `(-1)^(nm p)` of the single
shift because `n p + m p = nm p`.  Stated here, with every object a variable,
so that the functor-category proof can apply it instead of rewriting across
two spellings of the same shifted object. -/
lemma comp'_shiftMap_smul {E E'' : C} {m : ℤ} (s : IsShiftBy A n A')
    (u : IsShiftBy A' m E) (s' : IsShiftBy B n B') (u' : IsShiftBy B' m E'')
    (nm : ℤ) (hnm : n + m = nm) (p : ℤ) (f : (dgHom A B).X p) :
    (m * p).negOnePow • u.shiftMap u' p ((n * p).negOnePow • s.shiftMap s' p f) =
      (nm * p).negOnePow • (s.comp' u nm hnm).shiftMap (s'.comp' u' nm hnm) p f := by
  rw [shiftMap_units_smul, smul_smul, ← Int.negOnePow_add,
    show m * p + n * p = nm * p by rw [← hnm]; ring,
    comp'_shiftMap s u s' u' nm hnm p f]

/-! ### Coherence for three composed shifts

The binary comparison for shifted dg functors is canonical only if its two
threefold composites agree.  The two lemmas below isolate the remaining
pointwise content of that coherence.  They are stated for arbitrary shift
witnesses so the functor-category proof does not have to unfold the chosen
shifted objects.
-/

/-- The degree-zero transport of a comparison is the comparison of the
composite witnesses.

The total degree `nm` is explicit because the associativity proof compares
the propositionally equal indices `(n + m) + k` and `n + (m + k)`.  The proof
uses the characterising square of `shiftMap`; this is the all-degree
counterpart of `mapShift_compare_comp'`. -/
lemma shiftMap_compare_compOfDegree {A'' E'' : C} {m nm : ℤ}
    (s : IsShiftBy A n A') (t : IsShiftBy A n A'')
    (u : IsShiftBy A' m E) (v : IsShiftBy A'' m E'')
    (hnm : n + m = nm) :
    u.shiftMap v 0 (compare s t) =
      compare (s.comp' u nm hnm) (t.comp' v nm hnm) := by
  symm
  refine (s.comp' u nm hnm).compare_unique (t.comp' v nm hnm) _ ?_
  rw [comp'_hom, comp'_hom,
    dgComp_assoc (-n) (-m) 0 (-nm) (-m) (-nm)
      (by omega) (by omega) (by omega),
    u.hom_comp_shiftMap v 0 (-m) (by omega) (by omega) (compare s t),
    ← dgComp_assoc (-n) 0 (-m) (-n) (-m) (-nm)
      (by omega) (by omega) (by omega),
    s.hom_comp_compare t]

/-- Prefixing two witnesses by the same shift does not change their
comparison: the common shift element and its inverse cancel.  The explicit
total degree keeps the statement usable under either bracketing of three
integer shifts. -/
lemma compare_compLeftOfDegree {Z Z' : C} {m nm : ℤ}
    (s : IsShiftBy A n A') (u : IsShiftBy A' m Z)
    (v : IsShiftBy A' m Z') (hnm : n + m = nm) :
    compare (s.comp' u nm hnm) (s.comp' v nm hnm) = compare u v := by
  refine (s.comp' u nm hnm).compare_unique (s.comp' v nm hnm) _ ?_
  rw [comp'_hom, comp'_hom,
    dgComp_assoc (-n) (-m) 0 (-nm) (-m) (-nm)
      (by omega) (by omega) (by omega),
    u.hom_comp_compare v]

/-- **In degree zero, transport is `IsShiftBy.mapShift`.**

`mapShift` is the degree-zero transport that `Pretriangulated/Basic.lean`
already had, and `shiftMap` is the all-degree one.  They are the same map, but
not definitionally: `shiftMap` indexes its middle composite by `n + p`, which
at `p = 0` is `n + 0` and is only propositionally `n`.  `shiftMap_unique`
crosses that gap, because its result index is a free variable. -/
lemma shiftMap_zero_eq_mapShift (s : IsShiftBy A n A') (s' : IsShiftBy B n B')
    (f : (dgHom A B).X 0) :
    s.shiftMap s' 0 f = mapShift s s' f := by
  refine s.shiftMap_unique s' 0 (-n) (by omega) (by omega) f _ ?_
  rw [mapShift,
    ← dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n 0 0 n 0 (by omega) (by omega) (by omega),
    s.hom_inv, dgId_comp]

/-- Transport across the identity shift is the identity. -/
lemma shiftMap_self (p : ℤ) (f : (dgHom A B).X p) :
    (IsShiftBy.self A).shiftMap (IsShiftBy.self B) p f = f := by
  refine (IsShiftBy.self A).shiftMap_unique (IsShiftBy.self B) p p
    (by omega) (by omega) f f ?_
  -- `self.hom` is `dgId` at degree `-0`, which is `0` definitionally but not
  -- syntactically, so the two unit laws are applied as terms.
  exact (dgId_comp p f).trans (dgComp_id p f).symm

end IsShiftBy

end CategoryTheory
