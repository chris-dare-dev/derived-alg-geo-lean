/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Cartier divisors on an integral scheme

This file defines Cartier divisors without inventing a meromorphic-function sheaf that Mathlib
does not yet have. For an integral scheme `X`, the function field `K(X)` is upstream. At a point
`x`, the local Cartier group is

`K(X)ˣ / 𝒪_{X,x}ˣ`,

where local units enter `K(X)ˣ` through the canonical map from the stalk. A Cartier divisor is a
section of these stalkwise quotients that is locally represented by one nonzero rational
function. This is the usual local-equations definition of a Cartier divisor on an integral
scheme, expressed without a sheaf quotient.

The construction provides:

* the abelian group `Scheme.CartierDivisor X`;
* principal divisors and the explicit quotient `CartierDivisor.ClassGroup X`;
* codimension-one coefficients through Mathlib's `Scheme.ord`;
* pullback from explicit function-field data that carries local units to local units.

## Deliberate boundaries

Mathlib v4.32.1 does not construct a function-field map for an arbitrary morphism of integral
schemes, so this file does not claim an unconditional pullback. `CartierPullbackHypotheses` states the
exact missing hypotheses. Likewise, `coefficient` is not packaged as an `AlgebraicCycle`: the
upstream order-of-vanishing API does not yet prove local finiteness of its support. No cycle
infrastructure is duplicated here.
-/

open Additive CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

section LocalClasses

variable (X : Scheme.{u}) [IsIntegral X]

/-- Units in the local ring at `x`, viewed as units of the function field. -/
def localUnitHom (x : X) : (X.presheaf.stalk x)ˣ →* X.functionFieldˣ :=
  Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom

/-- Rational functions that are units in the local ring at `x`, in additive notation. -/
def localUnits (x : X) : AddSubgroup (Additive X.functionFieldˣ) :=
  (localUnitHom X x).range.toAddSubgroup

/-- A germ of a Cartier divisor at `x`: a rational function modulo local units. -/
abbrev LocalCartierClass (x : X) := Additive X.functionFieldˣ ⧸ localUnits X x

/-- The local Cartier class of a nonzero rational function. -/
def localCartierClass (x : X) : Additive X.functionFieldˣ →+ LocalCartierClass X x :=
  QuotientAddGroup.mk' (localUnits X x)

@[simp]
lemma localCartierClass_zero (x : X) : localCartierClass X x 0 = 0 :=
  map_zero _

@[simp]
lemma localCartierClass_add (x : X) (f g : Additive X.functionFieldˣ) :
    localCartierClass X x (f + g) =
      localCartierClass X x f + localCartierClass X x g :=
  map_add _ _ _

/-- Two local equations give the same germ precisely when their quotient is a local unit. -/
lemma localCartierClass_eq_iff (x : X) (f g : Additive X.functionFieldˣ) :
    localCartierClass X x f = localCartierClass X x g ↔ f - g ∈ localUnits X x :=
  QuotientAddGroup.eq_iff_sub_mem

end LocalClasses

section Divisors

variable (X : Scheme.{u}) [IsIntegral X]

/-- A family of local Cartier classes is Cartier when it is locally represented by a single
nonzero rational function. -/
def IsCartier (D : ∀ x : X, LocalCartierClass X x) : Prop :=
  ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∃ f : Additive X.functionFieldˣ,
    ∀ y, y ∈ U → D y = localCartierClass X y f

lemma isCartier_zero : IsCartier X 0 := by
  intro x
  refine ⟨⊤, Set.mem_univ x, 0, ?_⟩
  intro y hy
  simp

lemma IsCartier.add {D E : ∀ x : X, LocalCartierClass X x}
    (hD : IsCartier X D) (hE : IsCartier X E) : IsCartier X (D + E) := by
  intro x
  obtain ⟨U, hxU, f, hf⟩ := hD x
  obtain ⟨V, hxV, g, hg⟩ := hE x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, f + g, ?_⟩
  intro y hy
  rw [Pi.add_apply, hf y hy.1, hg y hy.2, localCartierClass_add]

lemma IsCartier.neg {D : ∀ x : X, LocalCartierClass X x}
    (hD : IsCartier X D) : IsCartier X (-D) := by
  intro x
  obtain ⟨U, hxU, f, hf⟩ := hD x
  refine ⟨U, hxU, -f, ?_⟩
  intro y hy
  rw [Pi.neg_apply, hf y hy, map_neg]

/-- The additive subgroup of locally representable families: Cartier divisors on `X`. -/
def cartierDivisor : AddSubgroup (∀ x : X, LocalCartierClass X x) where
  carrier := IsCartier X
  zero_mem' := isCartier_zero X
  add_mem' := IsCartier.add X
  neg_mem' := IsCartier.neg X

/-- Cartier divisors on an integral scheme. -/
abbrev CartierDivisor := cartierDivisor X

namespace CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- Cartier divisors are equal when all of their local classes are equal. -/
@[ext]
lemma ext {D E : CartierDivisor X} (h : ∀ x, D.1 x = E.1 x) : D = E :=
  Subtype.ext (funext h)

@[simp]
lemma zero_apply (x : X) : (0 : CartierDivisor X).1 x = 0 :=
  rfl

@[simp]
lemma add_apply (D E : CartierDivisor X) (x : X) : (D + E).1 x = D.1 x + E.1 x :=
  rfl

@[simp]
lemma neg_apply (D : CartierDivisor X) (x : X) : (-D).1 x = -D.1 x :=
  rfl

/-- Every Cartier divisor admits a rational local equation around every point. -/
lemma exists_localEquation (D : CartierDivisor X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : Additive X.functionFieldˣ,
      ∀ y, y ∈ U → D.1 y = localCartierClass X y f :=
  D.2 x

/-- Principal Cartier divisors, as an additive homomorphism from the multiplicative function
field written additively. -/
def principal (X : Scheme.{u}) [IsIntegral X] :
    Additive X.functionFieldˣ →+ CartierDivisor X where
  toFun f := ⟨fun x ↦ localCartierClass X x f, by
    intro x
    exact ⟨⊤, Set.mem_univ x, f, fun y _ ↦ rfl⟩⟩
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

/-- The principal divisor attached to a nonzero rational function. -/
def ofRationalFunction (X : Scheme.{u}) [IsIntegral X] (f : X.functionFieldˣ) :
    CartierDivisor X :=
  principal X (.ofMul f)

/-- The subgroup of principal Cartier divisors. -/
def principalDivisors (X : Scheme.{u}) [IsIntegral X] : AddSubgroup (CartierDivisor X) :=
  (principal X).range

instance principalDivisors_normal (X : Scheme.{u}) [IsIntegral X] :
    (principalDivisors X).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [add_comm g n, add_assoc, add_neg_cancel, add_zero]
  exact hn

/-- Cartier divisor classes: Cartier divisors modulo principal equivalence. -/
abbrev ClassGroup (X : Scheme.{u}) [IsIntegral X] :=
  CartierDivisor X ⧸ principalDivisors X

/-- The quotient map from Cartier divisors to Cartier divisor classes. -/
def toClass (X : Scheme.{u}) [IsIntegral X] : CartierDivisor X →+ ClassGroup X :=
  QuotientAddGroup.mk' (principalDivisors X)

/-- The quotient relation defining Cartier divisor classes. -/
theorem toClass_eq_iff (D E : CartierDivisor X) :
    toClass X D = toClass X E ↔ D - E ∈ principalDivisors X :=
  QuotientAddGroup.eq_iff_sub_mem

/-- Explicit principal-equivalence form of the quotient relation. -/
theorem toClass_eq_iff_exists (D E : CartierDivisor X) :
    toClass X D = toClass X E ↔
      ∃ f : Additive X.functionFieldˣ, principal X f = D - E := by
  rw [toClass_eq_iff]
  exact AddMonoidHom.mem_range

@[simp]
theorem toClass_principal (f : Additive X.functionFieldˣ) :
    toClass X (principal X f) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨f, rfl⟩

section Order

variable [IsLocallyNoetherian X]

/-- Order of vanishing of nonzero rational functions, as an additive homomorphism. -/
def ordUnitHom (x : X) : Additive X.functionFieldˣ →+ ℤ where
  toFun f := X.ord (f.toMul : X.functionField) x
  map_zero' := by
    change X.ord (1 : X.functionField) x = 0
    by_cases hx : coheight x = 1
    · rw [Scheme.ord_eq_iff hx one_ne_zero]
      simp
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hx 1
  map_add' f g := by
    change X.ord ((f.toMul * g.toMul : X.functionFieldˣ) : X.functionField) x = _
    exact Scheme.ord_mul f.toMul.ne_zero g.toMul.ne_zero

lemma ordUnitHom_eq_zero_of_mem_localUnits (x : X) (f : Additive X.functionFieldˣ)
    (hf : f ∈ localUnits X x) : ordUnitHom x f = 0 := by
  obtain ⟨u, rfl⟩ := hf
  change X.ord
    ((Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u :
      X.functionFieldˣ) : X.functionField) x = 0
  by_cases hx : coheight x = 1
  · rw [Scheme.ord_eq_iff hx]
    · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
        krullDimLE_of_coheight_le hx.le
      change Ring.ordFrac (X.presheaf.stalk x)
        (algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x)) = 1
      exact Ring.ordFrac_of_isUnit u.isUnit
    · simp
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- Order of vanishing descends to a local Cartier class because local units have order zero. -/
def localOrder (x : X) : LocalCartierClass X x →+ ℤ :=
  QuotientAddGroup.lift (localUnits X x) (ordUnitHom x)
    (ordUnitHom_eq_zero_of_mem_localUnits x)

@[simp]
lemma localOrder_localCartierClass (x : X) (f : Additive X.functionFieldˣ) :
    localOrder x (localCartierClass X x f) = X.ord (f.toMul : X.functionField) x :=
  rfl

/-- The codimension-one coefficient of a Cartier divisor. At other points this uses the upstream
junk value `0` of `Scheme.ord`. -/
def coefficient (D : CartierDivisor X) (x : X) : ℤ :=
  localOrder x (D.1 x)

@[simp]
lemma coefficient_add (D E : CartierDivisor X) (x : X) :
    coefficient (D + E) x = coefficient D x + coefficient E x :=
  map_add (localOrder x) (D.1 x) (E.1 x)

@[simp]
lemma coefficient_principal (f : Additive X.functionFieldˣ) (x : X) :
    coefficient (principal X f) x = X.ord (f.toMul : X.functionField) x :=
  rfl

lemma coefficient_eq_zero_of_coheight_ne_one (D : CartierDivisor X) (x : X)
    (hx : coheight x ≠ 1) : coefficient D x = 0 := by
  obtain ⟨U, hxU, f, hf⟩ := exists_localEquation D x
  change localOrder x (D.1 x) = 0
  rw [hf x hxU, localOrder_localCartierClass,
    Scheme.ord_eq_zero_of_coheight_neq_one hx]

end Order

end CartierDivisor

end Divisors

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)

/-- Data sufficient to pull Cartier divisors back along a scheme morphism.

The field map and the condition that it carries local units to local units are explicit because
Mathlib v4.32.1 provides no such map for an arbitrary scheme morphism. -/
structure CartierPullbackHypotheses where
  fieldMap : Additive Y.functionFieldˣ →+ Additive X.functionFieldˣ
  map_localUnits : ∀ x, localUnits Y (f x) ≤ (localUnits X x).comap fieldMap

namespace CartierPullbackHypotheses

variable (p : CartierPullbackHypotheses f)

/-- The induced map on local Cartier classes. -/
def localMap (x : X) : LocalCartierClass Y (f x) →+ LocalCartierClass X x :=
  QuotientAddGroup.map (localUnits Y (f x)) (localUnits X x)
    p.fieldMap (p.map_localUnits x)

@[simp]
lemma localMap_localCartierClass (x : X) (g : Additive Y.functionFieldˣ) :
    localMap f p x (localCartierClass Y (f x) g) =
      localCartierClass X x (p.fieldMap g) :=
  rfl

/-- Pullback of Cartier divisors from explicit compatible function-field data. -/
def pullback : CartierDivisor Y →+ CartierDivisor X where
  toFun D := ⟨fun x ↦ localMap f p x (D.1 (f x)), by
    intro x
    obtain ⟨U, hxU, g, hg⟩ := D.2 (f x)
    refine ⟨f ⁻¹ᵁ U, hxU, p.fieldMap g, ?_⟩
    intro y hy
    change localMap f p y (D.1 (f y)) = localCartierClass X y (p.fieldMap g)
    rw [hg (f y) hy, localMap_localCartierClass f p]⟩
  map_zero' := by ext; simp
  map_add' D E := by ext; simp

@[simp]
lemma pullback_principal (g : Additive Y.functionFieldˣ) :
    pullback f p (CartierDivisor.principal Y g) =
      CartierDivisor.principal X (p.fieldMap g) := by
  ext
  rfl

end CartierPullbackHypotheses

end Pullback

end

end AlgebraicGeometry.Scheme
