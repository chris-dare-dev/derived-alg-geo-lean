/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Relative
import Mathlib.GroupTheory.Index

/-!
# Geometric fibre groups for relative numerical K-theory

Definition 8.7 of Li--Liu--Liu--Macrì--Perry--Stellari--Zhao uses the image of
the base-change map `ηᵛ` as the numerical group of a geometric fibre.  This
file models that group by the canonical `AddMonoidHom.range`; it does not add a
second lattice carrier or Grothendieck-group presentation.

The finite-index assertion proved by the geometric base-change theory is kept
as a predicate on two additive subgroups.  It is provenance for the fibre
overlattice, not extra data needed by the relative quotient.  Finally,
`FamilyRelationSystem.ofEta` transports the fibre class of every admissible
family through `ηᵛ` and feeds it to the algebraic quotient in `Relative`.
-/

namespace AlgebraicGeometry.Numerical.Relative

universe u v w

/-! ## Images and finite-index overlattices -/

variable {A B V : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

/-- The geometric numerical group determined by a base-change map `ηᵛ`.

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

/-- `geometric` is a finite-index overlattice of `base` inside their common
ambient additive group.  Containment and finite relative index are properties,
not fields on a new carrier. -/
def IsFiniteIndexOverlattice (base geometric : AddSubgroup V) : Prop :=
  base ≤ geometric ∧ base.IsFiniteRelIndex geometric

/-- Transport a class through a base-change map whose image lies in the chosen
geometric-fibre image.  This is the formal factorization used in map (8.2) of
arXiv:2607.28411v1. -/
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

/-- Construct the connected-family relation system from fibrewise `ηᵛ` maps.

For each base index `i`, `geometricEta i` presents the numerical group of the
geometric fibre as its image in `V₀ i`.  At a point `t` of an admissible family,
`eta F t` is the corresponding specialization map into the same ambient group;
`hEta` is precisely the factorization through the chosen geometric fibre.
The resulting system is consumed by the saturated quotient already defined in
`Relative`, so the geometric layer cannot accidentally create another relative
Grothendieck group. -/
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

end AlgebraicGeometry.Numerical.Relative
