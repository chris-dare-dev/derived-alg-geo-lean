/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.RelativeNumerical.Basic
import Mathlib.GroupTheory.Index

/-!
# Images and finite-index overlattices of additive-group maps

This file models an image by the canonical `AddMonoidHom.range`, records the
finite-index-overlattice predicate for two additive subgroups, and factors
family values through chosen image inclusions.  The terminology is motivated
by relative numerical K-theory, but the public API uses only additive groups
and homomorphisms; geometric base-change maps are consumers of this root.
-/

namespace DerivedAlgGeo.Algebra.RelativeNumerical

universe u v w

/-! ## Images and finite-index overlattices -/

variable {A B V : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

/-- The image group determined by an additive map `η`.

This is an abbreviation for the existing additive-subgroup range, so all
subgroup, quotient, and finite-index API remains available without a parallel
lattice hierarchy. -/
abbrev EtaImage (eta : A →+ V) := eta.range

/-- A numerical class regarded as an element of the image of `ηᵛ`. -/
def etaClass (eta : A →+ V) : A →+ EtaImage eta :=
  eta.rangeRestrict

@[simp]
theorem etaClass_coe (eta : A →+ V) (x : A) :
    (etaClass eta x : V) = eta x :=
  rfl

/-- `larger` is a finite-index overlattice of `base` inside their common
ambient additive group.  Containment and finite relative index are properties,
not fields on a new carrier. -/
def IsFiniteIndexOverlattice (base larger : AddSubgroup V) : Prop :=
  base ≤ larger ∧ base.IsFiniteRelIndex larger

/-- Transport a class through an additive map whose range lies in a chosen
second range. -/
def specializationMap (eta : A →+ V) (geometricEta : B →+ V)
    (h : eta.range ≤ geometricEta.range) : A →+ EtaImage geometricEta :=
  eta.codRestrict geometricEta.range fun x ↦ h ⟨x, rfl⟩

@[simp]
theorem specializationMap_coe (eta : A →+ V) (geometricEta : B →+ V)
    (h : eta.range ≤ geometricEta.range) (x : A) :
    (specializationMap eta geometricEta h x : V) = eta x :=
  rfl

theorem specializationMap_self (eta : A →+ V) :
    specializationMap eta eta le_rfl = etaClass eta := by
  ext x
  rfl

/-! ## Admissible families -/

namespace FamilyRelationSystem

variable {I : Type u} {K V₀ : I → Type v}
  [∀ i, AddCommGroup (K i)] [∀ i, AddCommGroup (V₀ i)]

/-- Construct a family relation system from indexed additive maps.

For each index `i`, `geometricEta i` presents the target group as an image in
`V₀ i`. At a point `t` of an admissible family, `eta F t` maps a source into
the same ambient group; `hEta` is precisely its factorization through the
chosen image. The resulting system is consumed by the saturated quotient in
`Basic`. Geometric applications may instantiate these parameters with
base-change maps, but no geometric vocabulary occurs in this root. -/
def ofEta
    (geometricEta : ∀ i, K i →+ V₀ i)
    (Family : Type w) (Point : Family → Type w)
    (index : ∀ F, Point F → I)
    (Source : ∀ F, Point F → Type v)
    [∀ F t, AddCommGroup (Source F t)]
    (eta : ∀ F t, Source F t →+ V₀ (index F t))
    (hEta : ∀ F t, (eta F t).range ≤ (geometricEta (index F t)).range)
    (classValue : ∀ F t, Source F t) :
    FamilyRelationSystem fun i ↦ EtaImage (geometricEta i) where
  Family := Family
  Point := Point
  index := index
  classValue := fun F t ↦
    specializationMap (eta F t) (geometricEta (index F t)) (hEta F t)
      (classValue F t)

@[simp]
theorem ofEta_classValue_coe
    (geometricEta : ∀ i, K i →+ V₀ i)
    (Family : Type w) (Point : Family → Type w)
    (index : ∀ F, Point F → I)
    (Source : ∀ F, Point F → Type v)
    [∀ F t, AddCommGroup (Source F t)]
    (eta : ∀ F t, Source F t →+ V₀ (index F t))
    (hEta : ∀ F t, (eta F t).range ≤ (geometricEta (index F t)).range)
    (classValue : ∀ F t, Source F t) (F : Family) (t : Point F) :
    ((ofEta geometricEta Family Point index Source eta hEta classValue).classValue F t).1 =
      eta F t (classValue F t) :=
  rfl

end FamilyRelationSystem

/-! ## Boundary tests -/

/-- For the identity base-change map, the image construction recovers the
original additive group. -/
def etaImageIdEquiv (A : Type*) [AddCommGroup A] :
    EtaImage (AddMonoidHom.id A) ≃+ A where
  toFun x := x.1
  invFun := etaClass (AddMonoidHom.id A)
  left_inv x := by
    ext
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem etaImageIdEquiv_etaClass (A : Type*) [AddCommGroup A] (x : A) :
    etaImageIdEquiv A (etaClass (AddMonoidHom.id A) x) = x :=
  rfl

end DerivedAlgGeo.Algebra.RelativeNumerical
