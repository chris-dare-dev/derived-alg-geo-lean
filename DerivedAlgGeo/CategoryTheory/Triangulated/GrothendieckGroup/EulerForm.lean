/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.LinearAlgebra.AlternatingFinsum

/-!
# The Hom-built Euler form

`χ(X, Y) = Σᵢ (-1)ⁱ · dimₖ Hom(X, Y⟦i⟧)`, built from the long exact Hom
sequences of `LinearYoneda` and `LinearCoyoneda` and the `ℤ`-indexed
alternating-sum arithmetic of `LinearAlgebra/AlternatingFinsum`.

The additive pairing itself is the generic `K₀.EulerForm` abbreviation in this
file. `K₀.EulerForm.ofLinear` constructs it from the Hom-built form; geometric
Riemann--Roch comparisons consume that root separately.

## Restrictions, stated up front

**`k` is a division ring, not a field and not an arbitrary ring.** That is
exactly what the arithmetic needs and no more: rank--nullity
(`LinearMap.finrank_range_add_finrank_ker`) lives in a `section DivisionRing`,
and the support bounds go through `LinearMap.finrank_range_le`, which needs
`StrongRankCondition`. Commutativity is used nowhere, which is why `Field` is
not assumed — Mathlib states the same alternating-sum corollary at
`DivisionRing` (`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`). The
generality is deliberate and currently **unexercised**: nothing in this
repository instantiates `k` at a noncommutative division ring, and
`IsRiemannRoch` lands in a `ℚ`-algebra, so every intended instantiation is a
field. Mathlib's weaker `HasRankNullity` is declined — it does not supply
`StrongRankCondition`, its universe parameter would have to be threaded against
the category's morphism universe, and over a domain `finrank` is torsion-blind,
so the resulting pairing would be additive but not the `χ` that
Hirzebruch--Riemann--Roch compares against.

**The two variables carry different hypotheses, deliberately.** Additivity in
the second variable needs no linearity of the shift; additivity in the first
does. This is not an oversight: `linearCoyoneda` is covariant with source `C`
and its shift sequence is `Functor.ShiftSequence.tautological`, whereas
`linearYoneda` is contravariant and its shift sequence has to cross `op`, which
is what requires `[∀ n, (shiftFunctor C n).Linear k]`. `chiHom` itself carries
neither hypothesis; `chiK₀` carries the shift-linearity one.

## `chiHom` is junk-total, and that is deliberate

`Module.finrank` is `0` on a module that is not finite, and `finsum` is `0` on a
family with infinite support. So `chiHom` is a plain function defined for
*every* pair of objects in *any* `k`-linear pretriangulated category, carrying
no data and no well-definedness obligation — and returning a meaningless number
when `HomFiniteBounded` fails. Only the additivity theorems and everything
downstream of them require that hypothesis. A reader must not take availability
of `chiHom` as evidence that a category has an Euler form.

## What this file does not assert

* Nothing *in this file* constructs a `HomFiniteBounded` instance; at this
  generality it is unprovable, see its docstring. A concrete model lives in
  `GrothendieckGroup/HomFiniteWitness.lean` (#543).
* No relation to any geometric Euler characteristic, to `chi₂`, or to
  Riemann--Roch. Those comparisons remain supplied in the numerical track.
* Nothing about Serre duality, or about `χ` being symmetric, or non-degenerate.
-/

universe w u v u' v'

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Module DerivedAlgGeo.LinearAlgebra

/-- A biadditive integer-valued form on the triangulated Grothendieck group.
This is an abbreviation for the canonical nested additive-homomorphism type,
not a parallel one-field structure. -/
abbrev K₀.EulerForm (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :=
  K₀ C →+ K₀ C →+ ℤ

namespace K₀.EulerForm

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A triangulated functor preserves two Euler forms when its `K₀` map
preserves their values. -/
def Preserves (E : K₀.EulerForm C) (E' : K₀.EulerForm D)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] : Prop :=
  ∀ x y : K₀ C, E' (K₀.map F x) (K₀.map F y) = E x y

end K₀.EulerForm

variable (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Hom-finiteness and finite Ext-amplitude.**

Every `Hom(X, Y⟦i⟧)` is a finite-dimensional `k`-module, and for each pair only
finitely many `i` contribute. This is the "properness" input: there is no Euler
form without it.

Genuinely supplied, and unprovable at this generality. In an arbitrary
`k`-linear pretriangulated category the Hom-spaces are arbitrary `k`-modules and
nothing in `Pretriangulated` bounds them; nor need `Hom(X, Y⟦i⟧)` vanish for
large `|i|`, and it does not in an unbounded derived category. It is not
vacuous either: `GrothendieckGroup/HomFiniteWitness.lean` proves it for the
bounded homotopy category of any Hom-finite `k`-linear category, with
`Kᵇ(FGModuleCat k)` the named concrete model (#543).

The two fields are independent: `finrank` returns `0` for a non-finite module,
so finiteness of the *rank support* says nothing about the modules themselves
without `finite`.

**On the spelling of `support_finite`.** Given `finite`, this is *equivalent* to
a vanishing bound `∃ N, ∀ |i| > N, Subsingleton (X ⟶ Y⟦i⟧)` — over a division
ring `finrank = 0 ↔ Subsingleton` for a finite module, and a finite subset of
`ℤ` is bounded. Finite support is chosen for ergonomics, not generality: it is
the form `finsum_add_distrib` consumes directly, and it avoids the
`max`-of-three-bounds bookkeeping a common window forces at every triangle. It
is not a weaker hypothesis and is not claimed to be. -/
class HomFiniteBounded : Prop where
  /-- Each shifted Hom-space is a finite-dimensional `k`-module. -/
  finite : ∀ (X Y : C) (i : ℤ), Module.Finite k (X ⟶ Y⟦i⟧)
  /-- For each pair, only finitely many shifts contribute. -/
  support_finite : ∀ X Y : C,
    (Function.support fun i : ℤ => (finrank k (X ⟶ Y⟦i⟧) : ℤ)).Finite

attribute [instance] HomFiniteBounded.finite

/-- **The Euler form on objects**, `Σᵢ (-1)ⁱ dimₖ Hom(X, Y⟦i⟧)`.

Junk-total: see the module docstring. Carries no hypothesis beyond the ambient
`k`-linear pretriangulated structure. -/
noncomputable def chiHom (X Y : C) : ℤ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * finrank k (X ⟶ Y⟦i⟧)

variable {k C}

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
theorem chiHom_eq_finsum_altDim (X Y : C) :
    chiHom k C X Y = ∑ᶠ i : ℤ, altDim (k := k) (fun i => X ⟶ Y⟦i⟧) i :=
  rfl

/-- A `ShortComplex` exact in `ModuleCat k` gives `Function.Exact` of the
underlying linear maps.  The bridge from the categorical homology sequence to
the arithmetic of `AlternatingFinsum`. -/
theorem exact_hom_of_shortComplex_exact {S : ShortComplex (ModuleCat k)}
    (hS : S.Exact) : Function.Exact S.f.hom S.g.hom :=
  LinearMap.exact_iff.mpr hS.moduleCat_range_eq_ker.symm

section Additivity

variable [HomFiniteBounded k C]

/-- **The Euler form is additive in its second variable.**

No linearity of the shift is required: `linearCoyoneda` is covariant with source
`C`, so its shift sequence is tautological. See the module docstring on the
deliberate asymmetry with `chiHom_additive_left`. -/
theorem chiHom_additive_right (X : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    chiHom k C X T.obj₂ = chiHom k C X T.obj₁ + chiHom k C X T.obj₃ := by
  set F := (linearCoyoneda k C).obj (op X) with hF
  refine finsum_altDim_middle (k := k)
    (A := fun i => X ⟶ T.obj₁⟦i⟧) (B := fun i => X ⟶ T.obj₂⟦i⟧)
    (C := fun i => X ⟶ T.obj₃⟦i⟧)
    (fun i => ((F.shift i).map T.mor₁).hom)
    (fun i => ((F.shift i).map T.mor₂).hom)
    (fun i => (F.homologySequenceδ T i (i + 1) rfl).hom)
    (fun i => exact_hom_of_shortComplex_exact
      (linearCoyoneda_homologySequence_exact₂ (op X) T hT i))
    (fun i => exact_hom_of_shortComplex_exact
      (linearCoyoneda_homologySequence_exact₃ (op X) T hT i (i + 1) rfl))
    (fun i => exact_hom_of_shortComplex_exact
      (linearCoyoneda_homologySequence_exact₁ (op X) T hT i (i + 1) rfl))
    (HomFiniteBounded.support_finite X T.obj₁)
    (HomFiniteBounded.support_finite X T.obj₂)
    (HomFiniteBounded.support_finite X T.obj₃)

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The Euler form is additive in its first variable.**

Unlike `chiHom_additive_right` this needs `[∀ n, (shiftFunctor C n).Linear k]`,
because `linearYoneda` is contravariant and its shift sequence has to cross
`op`. See the module docstring.

Note the wiring: `triangleOpEquivalence` sends `X ⟶ Y ⟶ Z` to
`op Z ⟶ op Y ⟶ op X`, so the arithmetic's `A` family is `Hom(T.obj₃, −)` and
its `C` family is `Hom(T.obj₁, −)` — reversed relative to the statement. The
closing `add_comm` is that reversal and nothing else; a swapped wiring would
still typecheck against the symmetric-looking goal, so it is worth saying. -/
theorem chiHom_additive_left (Y : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    chiHom k C T.obj₂ Y = chiHom k C T.obj₁ Y + chiHom k C T.obj₃ Y := by
  set F := (linearYoneda k C).obj Y with hF
  set T' := (triangleOpEquivalence C).functor.obj (op T) with hT'
  have hT'd : T' ∈ distTriang Cᵒᵖ := op_distinguished T hT
  have key : chiHom k C T.obj₂ Y = chiHom k C T.obj₃ Y + chiHom k C T.obj₁ Y :=
    finsum_altDim_middle (k := k)
      (A := fun i => T.obj₃ ⟶ Y⟦i⟧) (B := fun i => T.obj₂ ⟶ Y⟦i⟧)
      (C := fun i => T.obj₁ ⟶ Y⟦i⟧)
      (fun i => ((F.shift i).map T'.mor₁).hom)
      (fun i => ((F.shift i).map T'.mor₂).hom)
      (fun i => (F.homologySequenceδ T' i (i + 1) rfl).hom)
      (fun i => exact_hom_of_shortComplex_exact
        (linearYoneda_homologySequence_exact₂ Y T' hT'd i))
      (fun i => exact_hom_of_shortComplex_exact
        (linearYoneda_homologySequence_exact₃ Y T' hT'd i (i + 1) rfl))
      (fun i => exact_hom_of_shortComplex_exact
        (linearYoneda_homologySequence_exact₁ Y T' hT'd i (i + 1) rfl))
      (HomFiniteBounded.support_finite T.obj₃ Y)
      (HomFiniteBounded.support_finite T.obj₂ Y)
      (HomFiniteBounded.support_finite T.obj₁ Y)
  rw [key, add_comm]

end Additivity

section Descent

variable (k C)
variable [HomFiniteBounded k C]

/-- Additivity in the second variable, as the class `K₀.lift` consumes. -/
instance isTriangleAdditive_chiHom (X : C) :
    IsTriangleAdditive (chiHom k C X) :=
  ⟨fun T hT => chiHom_additive_right X T hT⟩

/-- **`χ(X, −)` on the Grothendieck group.**

The second variable descends with no linearity-of-shift hypothesis; see the
module docstring. -/
noncomputable def chiRight (X : C) : K₀ C →+ ℤ :=
  K₀.lift C (chiHom k C X)

@[simp]
theorem chiRight_of (X Y : C) : chiRight k C X (K₀.of C Y) = chiHom k C X Y :=
  K₀.lift_of C _ Y

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- Additivity in the first variable, now valued in `K₀ C →+ ℤ`.  This is the
step that needs the shift to be `k`-linear. -/
instance isTriangleAdditive_chiRight :
    IsTriangleAdditive (chiRight k C) :=
  ⟨fun T hT => K₀.hom_ext C fun Y => by
    simpa using chiHom_additive_left Y T hT⟩

/-- **The Euler form on `K₀`.**

`χ : K₀ C →+ K₀ C →+ ℤ`, biadditive by construction: the second variable
descended in `chiRight`, the first descends here. -/
noncomputable def chiK₀ : K₀ C →+ K₀ C →+ ℤ :=
  K₀.lift C (chiRight k C)

@[simp]
theorem chiK₀_of (X : C) : chiK₀ k C (K₀.of C X) = chiRight k C X :=
  K₀.lift_of C _ X

/-- Not `@[simp]`: `chiK₀_of` and `chiRight_of` already rewrite the left-hand
side, so marking this fails `simpNF`.  Kept as the readable two-object
statement, which is the form every consumer reasons with. -/
theorem chiK₀_of_of (X Y : C) :
    chiK₀ k C (K₀.of C X) (K₀.of C Y) = chiHom k C X Y := by
  rw [chiK₀_of, chiRight_of]

/-- Package the Hom-built Euler pairing as the generic Euler-form alias. -/
noncomputable def K₀.EulerForm.ofLinear : K₀.EulerForm C :=
  chiK₀ k C

theorem K₀.EulerForm.ofLinear_eq_chiK₀ :
    K₀.EulerForm.ofLinear k C = chiK₀ k C :=
  rfl

end Descent

section Preservation

/-! ### A fully faithful `k`-linear functor preserves `χ`

The classical argument, and the reason `k`-linearity is the hypothesis rather
than additivity: a fully faithful functor matches the summands
`Hom(X, Y⟦i⟧) ≅ Hom(ΦX, ΦY⟦i⟧)` one by one, and it is `k`-linearity that makes
the matched summands equal as `k`-*dimensions*. An additive fully faithful
functor gives a bijection of Hom-groups, which fixes `finrank ℤ` but not
`finrank k`.

For the Hom-built form, full faithfulness and linearity prove the generic
`K₀.EulerForm.Preserves` predicate below. -/

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- The Hom-bijection of a fully faithful `k`-linear functor, as a `k`-linear
equivalence.

Mathlib has `Functor.FullyFaithful.homEquiv` (a bare `Equiv`) and
`Functor.Linear.map_smul`, but not the two combined. Written here in the
`ForMathlib` pattern: nothing about it is specific to this development. -/
noncomputable def homLinearEquivOfFullyFaithful (Φ : C ⥤ D) [Φ.Additive]
    [Φ.Linear k] (hΦ : Φ.FullyFaithful) (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (Φ.obj X ⟶ Φ.obj Y) where
  toFun := Φ.map
  map_add' _ _ := Φ.map_add
  map_smul' r f := Φ.map_smul r f
  invFun := hΦ.preimage
  left_inv f := hΦ.preimage_map f
  right_inv f := hΦ.map_preimage f

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- **The shifted Hom-spaces are `k`-linearly equivalent** under a fully
faithful `k`-linear functor commuting with the shift.

Two linear equivalences composed: full faithfulness moves `Hom(X, Y⟦i⟧)` to
`Hom(ΦX, Φ(Y⟦i⟧))`, and the `CommShift` isomorphism moves that to
`Hom(ΦX, (ΦY)⟦i⟧)`.

This was inline inside `finrank_hom_shift_map`. It is named because equality of
dimensions is not enough to transport `HomFiniteBounded` — finite-dimensionality
has to travel too, and for that the equivalence itself is needed. -/
noncomputable def homShiftLinearEquiv (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k]
    [Φ.CommShift ℤ] (hΦ : Φ.FullyFaithful) (X Y : C) (i : ℤ) :
    (X ⟶ Y⟦i⟧) ≃ₗ[k] (Φ.obj X ⟶ (Φ.obj Y)⟦i⟧) :=
  (homLinearEquivOfFullyFaithful Φ hΦ X (Y⟦i⟧)).trans
    (Linear.homCongr k (Iso.refl (Φ.obj X)) ((Φ.commShiftIso i).app Y))

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- **The shifted Hom-spaces have the same `k`-dimension.** The dimension
shadow of `homShiftLinearEquiv`. -/
theorem finrank_hom_shift_map (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k]
    [Φ.CommShift ℤ] (hΦ : Φ.FullyFaithful) (X Y : C) (i : ℤ) :
    finrank k (Φ.obj X ⟶ (Φ.obj Y)⟦i⟧) = finrank k (X ⟶ Y⟦i⟧) :=
  ((homShiftLinearEquiv Φ hΦ X Y i).finrank_eq).symm

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- **`χ` is preserved on objects.**

Term by term: `finrank_hom_shift_map` under the `finsum`. No finiteness
hypothesis is needed — the two families are equal pointwise, so their `finsum`s
agree whether or not either is finitely supported. -/
theorem chiHom_map (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k] [Φ.CommShift ℤ]
    (hΦ : Φ.FullyFaithful) (X Y : C) :
    chiHom k D (Φ.obj X) (Φ.obj Y) = chiHom k C X Y :=
  finsum_congr fun i => by rw [finrank_hom_shift_map Φ hΦ X Y i]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- The shifted Hom-spaces of `D`, carried back to `C` along a comparison that
is also essentially surjective.

`homShiftLinearEquiv` only reaches objects of the form `Φ.obj X`. Essential
surjectivity supplies, for an arbitrary `Y : D`, a preimage and an isomorphism
`Φ.obj (Φ.objPreimage Y) ≅ Y`; conjugating by it — and by its shift in the
second variable — extends the equivalence to every pair of objects of `D`. -/
noncomputable def homShiftLinearEquivOfEssSurj (Φ : C ⥤ D) [Φ.Additive]
    [Φ.Linear k] [Φ.CommShift ℤ] (hΦ : Φ.FullyFaithful) [Φ.EssSurj]
    (Y Y' : D) (i : ℤ) :
    (Y ⟶ Y'⟦i⟧) ≃ₗ[k] (Φ.objPreimage Y ⟶ (Φ.objPreimage Y')⟦i⟧) :=
  (Linear.homCongr k (Φ.objObjPreimageIso Y).symm
      ((shiftFunctor D i).mapIso (Φ.objObjPreimageIso Y').symm)).trans
    (homShiftLinearEquiv Φ hΦ (Φ.objPreimage Y) (Φ.objPreimage Y') i).symm

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- **`HomFiniteBounded` transports along a `k`-linear triangulated equivalence.**

If `Φ` is fully faithful, `k`-linear, commutes with the shift and is essentially
surjective — an equivalence, presented by the data an equivalence gives — then
`D` inherits the property from `C`. Both fields move across
`homShiftLinearEquivOfEssSurj`: finite-dimensionality by `Module.Finite.equiv`,
and the support because the two dimension functions are *equal*, not merely
both finite.

This is what `finrank_hom_shift_map` alone could not do. Equality of dimensions
says nothing about finiteness — `finrank` is junk-valued at `0` on an infinite-
dimensional space, so two infinite-dimensional Hom-spaces have equal `finrank`
and neither is finite. The equivalence itself has to travel, which is why
`homShiftLinearEquiv` was factored out of that proof.

## The intended use

A concrete `HomFiniteBounded` category is built where the statement is
elementary — `Kᵇ` of a Hom-finite linear category, in
`GrothendieckGroup/HomFiniteWitness.lean` — and then moved to a category where
proving it directly would be a theorem about a localization. Supplying the
equivalence is the caller's problem and is not made easier here. -/
theorem HomFiniteBounded.of_essSurj (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k]
    [Φ.CommShift ℤ] (hΦ : Φ.FullyFaithful) [Φ.EssSurj] [HomFiniteBounded k C] :
    HomFiniteBounded k D where
  finite Y Y' i :=
    Module.Finite.equiv (homShiftLinearEquivOfEssSurj Φ hΦ Y Y' i).symm
  support_finite Y Y' := by
    have h : (fun i : ℤ => (finrank k (Y ⟶ Y'⟦i⟧) : ℤ))
        = fun i : ℤ => (finrank k (Φ.objPreimage Y ⟶ (Φ.objPreimage Y')⟦i⟧) : ℤ) := by
      funext i
      exact_mod_cast (homShiftLinearEquivOfEssSurj Φ hΦ Y Y' i).finrank_eq
    rw [h]
    exact HomFiniteBounded.support_finite _ _

variable [HomFiniteBounded k C] [HomFiniteBounded k D]
  [∀ n : ℤ, (shiftFunctor C n).Linear k] [∀ n : ℤ, (shiftFunctor D n).Linear k]

/-- **`χ` is preserved on `K₀`.**

The object-level statement descended in both variables. `AddMonoidHom.compHom'`
is precomposition-as-a-homomorphism, which is what lets the outer variable be
handled by `K₀.hom_ext` rather than by hand. -/
theorem chiK₀_map (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (D : Type u') [Category.{v'} D] [Preadditive D] [Linear k D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HomFiniteBounded k C] [HomFiniteBounded k D]
    [∀ n : ℤ, (shiftFunctor C n).Linear k] [∀ n : ℤ, (shiftFunctor D n).Linear k]
    (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k] [Φ.CommShift ℤ]
    [Φ.IsTriangulated] (hΦ : Φ.FullyFaithful) (x y : K₀ C) :
    chiK₀ k D (K₀.map Φ x) (K₀.map Φ y) = chiK₀ k C x y := by
  have outer :
      (AddMonoidHom.compHom' (K₀.map Φ)).comp ((chiK₀ k D).comp (K₀.map Φ))
        = chiK₀ k C := by
    refine K₀.hom_ext C fun X => K₀.hom_ext C fun Y => ?_
    simp [K₀.map_of, chiHom_map Φ hΦ X Y]
  exact DFunLike.congr_fun (DFunLike.congr_fun outer x) y

/-- A fully faithful linear triangulated functor preserves the Hom-built Euler
forms on its source and target. -/
theorem K₀.EulerForm.ofLinear_preserves (k : Type w) [DivisionRing k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (D : Type u') [Category.{v'} D] [Preadditive D] [Linear k D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [HomFiniteBounded k C] [HomFiniteBounded k D]
    [∀ n : ℤ, (shiftFunctor C n).Linear k]
    [∀ n : ℤ, (shiftFunctor D n).Linear k]
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.CommShift ℤ]
    [F.IsTriangulated] (hF : F.FullyFaithful) :
    (K₀.EulerForm.ofLinear k C).Preserves
      (K₀.EulerForm.ofLinear k D) F :=
  fun x y => chiK₀_map k C D F hF x y

end Preservation

end CategoryTheory.Triangulated
