/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Duality.Serre.Bilinear
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedHeart
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomFinite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Euler

/-!
# Geometric comparison for Serre duality

This file relates abstract Serre duality on the bounded coherent derived category
of a smooth proper scheme to the existing sheaf-level bilinear duality data.

## Main definitions

* `GeometricSerreData` holds the abstract Serre datum, a derived canonical
  twist, their natural isomorphism after shifting, and sheaf-range comparison
  data.
* `GeometricSerreData.toSerreFunctorData` transports the abstract datum to the
  specified twist-then-shift functor.

## Main results

* `GeometricSerreData.finrank_eq_from_abstract` recovers the sheaf-range
  numerical duality in one direction.
* `GeometricSerreData.hom_finite_bounded` derives finite-dimensional Hom spaces
  with bounded shift support for the bounded coherent derived category.
* `AlgebraicGeometry.Duality.Serre.GeometricSerreData.chiHom_boundedSingleFunctor_obj_eq_eulerChar`
  identifies the Hom-built Euler form on
  embedded sheaves with the sheaf-level Euler characteristic.
* `AlgebraicGeometry.Duality.Serre.GeometricSerreData.selfHomShiftTwoDual` and
  `AlgebraicGeometry.Duality.Serre.GeometricSerreData.chiHom_symm_of_trivialTwist`
  give conditional dimension-two
  consequences of a functor-level trivialization of the derived twist.
* A one-dimensional endomorphism condition transfers to degree-two self-Hom
  under derived twist triviality.
* `AlgebraicGeometry.Duality.Serre.GeometricSerreData.chiHom_self_eq_of_trivialCanonical`
  transfers the
  sheaf-level self-Euler calculation without that functor-level trivialization.

## Implementation notes

`GeometricSerreData.serre` reuses the canonical abstract Serre root. The scalar
compatibility of the additive Ext comparison and the derived twist's restriction
to sheaves are supplied; the resulting derived duality and its naturality are
transported along the specified functor isomorphism. Hom-finiteness follows
from sheaf Ext-finiteness, that transport, and the standard t-structure. No
geometric inhabitant or derived tensor functor is constructed here.
`CategoryTheory.SerreFunctor.SerreFunctorData` is the abstract API, and
`AlgebraicGeometry.Duality.Serre.BilinearData` is the sheaf presentation.

A sheaf-level `AlgebraicGeometry.Duality.Serre.BilinearData.TrivialCanonical`
does not identify the derived
twist functor with identity; the dimension-two consequences below state that
functor-level natural isomorphism explicitly.

## References

* A. I. Bondal and M. M. Kapranov, *Representable functors, Serre functors,
  and mutations*, Math. USSR-Izv. 35:3 (1990), 519-541.
  DOI: https://doi.org/10.1070/IM1990v035n03ABEH000716.

## Tags

Serre duality, bounded derived category, coherent sheaves, Ext comparison.
-/

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.DerivedCategory
open CategoryTheory.Triangulated
attribute [local instance] HasDerivedCategory.standard

universe w v
namespace AlgebraicGeometry.Duality.Serre
variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C]

private noncomputable def transportSerreAlongIso
    (D : CategoryTheory.SerreFunctor.SerreFunctorData k C)
    (T : C ⥤ C) (e : D.S ≅ T) : CategoryTheory.SerreFunctor.SerreFunctorData k C where
  S := T
  eta A B := (D.eta A B).trans (Linear.homCongr k (Iso.refl B) (e.app A))
  naturality_left := by
    intro A A' B f phi
    simp only [LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
      Category.id_comp]
    rw [D.naturality_left]
    simpa only [Category.assoc, Iso.app_hom] using
      congrArg (fun h => (D.eta A B phi) ≫ h) (e.hom.naturality f)
  naturality_right := by
    intro A B B' g phi
    simp only [LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
      Category.id_comp]
    rw [D.naturality_right]
    simp only [Category.assoc]
end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]

private local instance hasExtCohCategorical : HasExt.{u + 1} (Coh X) := HasExt.standard _

private noncomputable def boundedHomLinearEquiv (E F : Coh X) (i : ℕ) :
    (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
      ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧) ≃ₗ[k]
    ShiftedHom ((DerivedCategory.singleFunctor (Coh X) 0).obj E)
      ((DerivedCategory.singleFunctor (Coh X) 0).obj F) (i : ℤ) := by
  let J := DerivedCategory.Bounded.ι (C := Coh X)
  let hJ : J.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful J
  let A := (DerivedCategory.boundedSingleFunctor (Coh X)).obj E
  let B := (DerivedCategory.boundedSingleFunctor (Coh X)).obj F
  let e := CategoryTheory.Triangulated.homShiftLinearEquiv (k := k)
    J hJ A B (i : ℤ)
  exact e

private noncomputable def extToBounded (E F : Coh X) (i : ℕ) :
    Abelian.Ext.{u + 1} E F i ≃ₗ[k]
    (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
      ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧) :=
  (Abelian.Ext.homLinearEquiv (R := k) (X := E) (Y := F) (n := i)).trans
    (boundedHomLinearEquiv (k := k) E F i).symm
end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
private local instance hasExtCohCategorical2 : HasExt.{u + 1} (Coh X) := HasExt.standard _

/-- Convert the supplied additive-group isomorphism to an additive equivalence.
Its scalar compatibility is separately supplied by
`GeometricSerreData.extComparison_scalar`. -/
noncomputable def extSpaceAddEquiv
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (S : AlgebraicGeometry.Duality.Serre.BilinearData K)
    (E F : Coh X) (i : ℕ) :
    S.extSpace E F i ≃+ Abelian.Ext.{u + 1} E F i :=
  (S.extComparison E F i).addCommGroupIsoToAddEquiv

private noncomputable def extSpaceAddEquivToBounded
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (S : AlgebraicGeometry.Duality.Serre.BilinearData K)
    (E F : Coh X) (i : ℕ) :
    S.extSpace E F i ≃+
    (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
      ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧) :=
  (extSpaceAddEquiv S E F i).trans
    (extToBounded (k := k) E F i).toAddEquiv
end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
private local instance hasExtCohCategorical3 : HasExt.{u + 1} (Coh X) := HasExt.standard _

private noncomputable def extSpaceLinearEquivWithScalar
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (S : AlgebraicGeometry.Duality.Serre.BilinearData K)
    (E F : Coh X) (i : ℕ)
    (hscalar : ∀ (r : k) (x : S.extSpace E F i),
      extSpaceAddEquiv S E F i (r • x) =
        r • extSpaceAddEquiv S E F i x) :
    S.extSpace E F i ≃ₗ[k]
    (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
      ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧) := by
  let e : S.extSpace E F i ≃ₗ[k] Abelian.Ext.{u + 1} E F i :=
    { toAddEquiv := extSpaceAddEquiv S E F i
      map_smul' := hscalar }
  exact e.trans (extToBounded (k := k) E F i)
end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
private local instance hasExtCohCategorical4 : HasExt.{u + 1} (Coh X) := HasExt.standard _

private local instance boundedShiftLinear (i : ℤ) :
    (shiftFunctor (SchemeBoundedCoherentDerivedCategory X) i).Linear k := by
  let J := DerivedCategory.Bounded.ι (C := Coh X)
  have hcomp : ((shiftFunctor (SchemeBoundedCoherentDerivedCategory X) i) ⋙ J).Linear k :=
    Functor.linear_of_iso k (J.commShiftIso i).symm
  refine ⟨fun {A B} f r => ?_⟩
  apply J.map_injective
  exact hcomp.map_smul f r

private noncomputable def shiftCancel
    (A B' : SchemeBoundedCoherentDerivedCategory X) (i m : ℤ) :
    (A⟦i⟧ ⟶ B'⟦m⟧) ≃ₗ[k] (A ⟶ B'⟦m - i⟧) := by
  let Q := shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (-i)
  let hQ : Q.FullyFaithful :=
    (shiftEquiv (SchemeBoundedCoherentDerivedCategory X) (-i)).fullyFaithfulFunctor
  let e := CategoryTheory.Triangulated.homLinearEquivOfFullyFaithful
    (k := k) Q hQ (A⟦i⟧) (B'⟦m⟧)
  let sourceIso : (A⟦i⟧)⟦-i⟧ ≅ A :=
    (shiftFunctorCompIsoId (SchemeBoundedCoherentDerivedCategory X) i (-i) (by omega)).app A
  let targetIso : (B'⟦m⟧)⟦-i⟧ ≅ B'⟦m - i⟧ :=
    ((shiftFunctorAdd' (SchemeBoundedCoherentDerivedCategory X) m (-i) (m - i)
      (by omega)).app B').symm
  exact e.trans (Linear.homCongr k sourceIso targetIso)

private noncomputable def rightComparison
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (S : AlgebraicGeometry.Duality.Serre.BilinearData K)
    (T : (SchemeBoundedCoherentDerivedCategory X) ⥤ (SchemeBoundedCoherentDerivedCategory X))
    (hscalar : ∀ (E F : Coh X) (j : ℕ) (r : k) (x : S.extSpace E F j),
      extSpaceAddEquiv S E F j (r • x) =
        r • extSpaceAddEquiv S E F j x)
    (hTwist : ∀ E : Coh X, T.obj ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ≅
      (DerivedCategory.boundedSingleFunctor (Coh X)).obj (S.canonicalTwist E))
    (E F : Coh X) (i : ℕ) (hi : i ≤ n) :
    (((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧ ⟶
      (T ⋙ shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)).obj
        ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E)) ≃ₗ[k]
      S.extSpace F (S.canonicalTwist E) (n - i) := by
  let e1 := Linear.homCongr k
    (Iso.refl (((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧))
    ((shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)).mapIso (hTwist E))
  let e2 := shiftCancel (k := k) ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)
    ((DerivedCategory.boundedSingleFunctor (Coh X)).obj (S.canonicalTwist E)) (i : ℤ) (n : ℤ)
  have hIndex : (n : ℤ) - (i : ℤ) = ((n - i : ℕ) : ℤ) := by
    exact (Nat.cast_sub hi).symm
  let e3 := (extSpaceLinearEquivWithScalar S F (S.canonicalTwist E) (n - i)
    (hscalar F (S.canonicalTwist E) (n - i))).symm
  exact e1.trans (e2.trans (hIndex ▸ e3))

end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
private local instance hasExtCohCategorical5 : HasExt.{u + 1} (Coh X) := HasExt.standard _

/-- Transport a derived Serre pairing into the realized Ext coordinates.
Agreement with the sheaf duality pairing is the separate
`GeometricSerreData.compat` field. -/
noncomputable def sheafComparison
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (S : AlgebraicGeometry.Duality.Serre.BilinearData K)
    (T : (SchemeBoundedCoherentDerivedCategory X) ⥤ (SchemeBoundedCoherentDerivedCategory X))
    (hscalar : ∀ (E F : Coh X) (j : ℕ) (r : k) (x : S.extSpace E F j),
      extSpaceAddEquiv S E F j (r • x) =
        r • extSpaceAddEquiv S E F j x)
    (hTwist : ∀ E : Coh X, T.obj ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ≅
      (DerivedCategory.boundedSingleFunctor (Coh X)).obj (S.canonicalTwist E))
    (eta : ∀ A B' : (SchemeBoundedCoherentDerivedCategory X), Module.Dual k (A ⟶ B') ≃ₗ[k]
      (B' ⟶ (T ⋙ shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)).obj A))
    (E F : Coh X) (i : ℕ) (hi : i ≤ n) :
    Module.Dual k (S.extSpace E F i) ≃ₗ[k]
      S.extSpace F (S.canonicalTwist E) (n - i) :=
  ((extSpaceLinearEquivWithScalar S E F i (hscalar E F i)).dualMap.symm).trans
    ((eta ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E)
      (((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧)).trans
      (rightComparison S T hscalar hTwist E F i hi))

end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
private local instance hasExtCohCategorical6 : HasExt.{u + 1} (Coh X) := HasExt.standard _

/-- Abstract Serre duality on the bounded coherent derived category, together
with its geometric twist and sheaf-level comparison in degrees `i ≤ n`.

No inhabitant is constructed here. The specified twist's Serre duality and
bounded Hom-finiteness are derived from these fields below. -/
structure GeometricSerreData
    (K : SmoothProperVariety.CanonicalSheafData k X n) where
  /-- The supplied derived canonical-twist functor. -/
  canonicalTwistFunctor :
    (SchemeBoundedCoherentDerivedCategory X) ⥤ (SchemeBoundedCoherentDerivedCategory X)
  /-- The existing sheaf-level bilinear duality data. -/
  bilinear : AlgebraicGeometry.Duality.Serre.BilinearData K
  /-- Reuse the canonical abstract Serre functor package. -/
  serre : CategoryTheory.SerreFunctor.SerreFunctorData k (SchemeBoundedCoherentDerivedCategory X)
  /-- Identify the abstract Serre functor with the geometric twist and shift. -/
  serreTwistIso :
    serre.S ≅ canonicalTwistFunctor ⋙
      shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)
  /-- The additive Ext comparison also respects scalar multiplication. -/
  extComparison_scalar :
    ∀ (E F : Coh X) (j : ℕ) (r : k) (x : bilinear.extSpace E F j),
      extSpaceAddEquiv bilinear E F j (r • x) =
        r • extSpaceAddEquiv bilinear E F j x
  /-- The derived twist restricts to the supplied sheaf-level twist. -/
  twistOnSheaves :
    ∀ E : Coh X,
      canonicalTwistFunctor.obj ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ≅
      (DerivedCategory.boundedSingleFunctor (Coh X)).obj (bilinear.canonicalTwist E)
  /-- The transported derived pairing agrees with sheaf duality for `i ≤ n`. -/
  compat :
    ∀ (E F : Coh X) (i : ℕ) (hi : i ≤ n),
      sheafComparison bilinear canonicalTwistFunctor extComparison_scalar
        twistOnSheaves
        (fun A B => (serre.eta A B).trans
          (Linear.homCongr k (Iso.refl B) (serreTwistIso.app A)))
        E F i hi = bilinear.duality E F i hi

namespace GeometricSerreData

/-- Transport the abstract Serre functor to the specified geometric twist. -/
noncomputable def toSerreFunctorData
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (G : GeometricSerreData K) :
    CategoryTheory.SerreFunctor.SerreFunctorData k (SchemeBoundedCoherentDerivedCategory X) :=
  transportSerreAlongIso G.serre
    (G.canonicalTwistFunctor ⋙ shiftFunctor
      (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)) G.serreTwistIso

/-- Derived Serre duality for the specified twist, obtained from `G.serre`. -/
noncomputable def serreDuality
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (G : GeometricSerreData K)
    (A B : SchemeBoundedCoherentDerivedCategory X) :
    Module.Dual k (A ⟶ B) ≃ₗ[k]
      (B ⟶ (G.canonicalTwistFunctor ⋙
        shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)).obj A) :=
  G.toSerreFunctorData.eta A B
end GeometricSerreData
end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.DerivedCategory
open CategoryTheory.Triangulated
attribute [local instance] HasDerivedCategory.standard
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
private local instance hasExtCohNoFinite : HasExt.{u + 1} (Coh X) := HasExt.standard _

/-- Recover the sheaf-level finrank identity from the abstract Serre pairing
and the explicit Ext, twist, and sheaf comparison maps. No global Hom-finiteness
input is needed. -/
theorem GeometricSerreData.finrank_eq_from_abstract
    {K : SmoothProperVariety.CanonicalSheafData k X n}
    (G : GeometricSerreData K) (E F : Coh X) (i : ℕ) (hi : i ≤ n) :
    Module.finrank k (G.bilinear.extSpace E F i) =
      Module.finrank k
        (G.bilinear.extSpace F (G.bilinear.canonicalTwist E) (n - i)) := by
  let eL := extSpaceLinearEquivWithScalar G.bilinear E F i
    (G.extComparison_scalar E F i)
  let eR := rightComparison G.bilinear G.canonicalTwistFunctor
    G.extComparison_scalar G.twistOnSheaves E F i hi
  letI : Module.Finite k (G.bilinear.extSpace E F i) := G.bilinear.extFinite E F i
  letI : Module.Finite k
      (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
        ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧) :=
    Module.Finite.equiv eL
  calc
    Module.finrank k (G.bilinear.extSpace E F i) =
        Module.finrank k (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
          ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧) := eL.finrank_eq
    _ = Module.finrank k (Module.Dual k
          (((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) ⟶
            ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧)) :=
      Subspace.dual_finrank_eq.symm
    _ = Module.finrank k
          (((DerivedCategory.boundedSingleFunctor (Coh X)).obj F)⟦(i : ℤ)⟧ ⟶
            (G.canonicalTwistFunctor ⋙ shiftFunctor
              (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)).obj
              ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E)) :=
      (G.serreDuality _ _).finrank_eq
    _ = Module.finrank k
          (G.bilinear.extSpace F (G.bilinear.canonicalTwist E) (n - i)) :=
      eR.finrank_eq
end AlgebraicGeometry.Duality.Serre

namespace AlgebraicGeometry.Duality.Serre.GeometricSerreData

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.DerivedCategory
open CategoryTheory.Triangulated
open scoped BigOperators
attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
  {K : SmoothProperVariety.CanonicalSheafData k X n}

private abbrev D := SchemeBoundedCoherentDerivedCategory X
private noncomputable abbrev B : Coh X ⥤ D (X := X) :=
  DerivedCategory.boundedSingleFunctor (Coh X)
private local instance hasExtCohRecovery : HasExt.{u + 1} (Coh X) := HasExt.standard _

private theorem finrank_shifted_hom_eq_zero_of_neg (E F : Coh X) (j : ℤ) (hj : j < 0) :
    Module.finrank k (((B (X := X)).obj E) ⟶ ((B (X := X)).obj F)⟦j⟧) = 0 := by
  let J := DerivedCategory.Bounded.ι (C := Coh X)
  have hJ : J.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful J
  let e := CategoryTheory.Triangulated.homShiftLinearEquiv (k := k)
    J hJ ((B (X := X)).obj E) ((B (X := X)).obj F) j
  have hle : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.singleFunctor (Coh X) 0).obj E) 0 :=
    inferInstance
  have hge : DerivedCategory.TStructure.t.IsGE
      (((DerivedCategory.singleFunctor (Coh X) 0).obj F)⟦j⟧) (-j) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 j (-j) (by omega)
  haveI : Subsingleton
      (ShiftedHom ((DerivedCategory.singleFunctor (Coh X) 0).obj E)
        ((DerivedCategory.singleFunctor (Coh X) 0).obj F) j) :=
    ⟨fun f g => by
      rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f 0 (-j) (by omega) hle hge,
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g 0 (-j) (by omega) hle hge]⟩
  haveI : Subsingleton (J.obj ((B (X := X)).obj E) ⟶
      (J.obj ((B (X := X)).obj F))⟦j⟧) := by
    change Subsingleton (ShiftedHom ((DerivedCategory.singleFunctor (Coh X) 0).obj E)
      ((DerivedCategory.singleFunctor (Coh X) 0).obj F) j)
    infer_instance
  exact e.finrank_eq.trans Module.finrank_zero_of_subsingleton

private theorem finrank_shifted_hom_eq_zero_of_dim_lt (G : GeometricSerreData K)
    (E F : Coh X) (j : ℤ) (hj : (n : ℤ) < j) :
    Module.finrank k (((B (X := X)).obj E) ⟶ ((B (X := X)).obj F)⟦j⟧) = 0 := by
  let A := (B (X := X)).obj E
  let C := (B (X := X)).obj F
  let W := (B (X := X)).obj (G.bilinear.canonicalTwist E)
  let eDual := G.serreDuality A (C⟦j⟧)
  let eTwist : (C⟦j⟧ ⟶ (G.canonicalTwistFunctor ⋙
      shiftFunctor (D (X := X)) (n : ℤ)).obj A) ≃ₗ[k]
      (C⟦j⟧ ⟶ W⟦(n : ℤ)⟧) :=
    Linear.homCongr k (Iso.refl _) ((shiftFunctor (D (X := X)) (n : ℤ)).mapIso
      (G.twistOnSheaves E))
  let eShift := AlgebraicGeometry.Duality.Serre.shiftCancel (k := k) C W j (n : ℤ)
  have hneg : Module.finrank k (C ⟶ W⟦(n : ℤ) - j⟧) = 0 :=
    finrank_shifted_hom_eq_zero_of_neg (k := k)
      F (G.bilinear.canonicalTwist E) ((n : ℤ) - j) (by omega)
  have hDual : Module.finrank k
      (Module.Dual k (A ⟶ C⟦j⟧)) = 0 :=
    eDual.finrank_eq.trans (eTwist.finrank_eq.trans (eShift.finrank_eq.trans hneg))
  have hj0 : 0 ≤ j := by omega
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
  letI : Module.Finite k (G.bilinear.extSpace E F m) := G.bilinear.extFinite E F m
  letI : Module.Finite k (A ⟶ C⟦(m : ℤ)⟧) := Module.Finite.equiv
    (extSpaceLinearEquivWithScalar G.bilinear E F m (G.extComparison_scalar E F m))
  simpa only [Subspace.dual_finrank_eq] using hDual

end AlgebraicGeometry.Duality.Serre.GeometricSerreData

namespace AlgebraicGeometry.Duality.Serre.GeometricSerreData
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.DerivedCategory
open CategoryTheory.Triangulated
attribute [local instance] HasDerivedCategory.standard
variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
  {K : SmoothProperVariety.CanonicalSheafData k X n}
private local instance hasExtCohFiniteness : HasExt.{u + 1} (Coh X) := HasExt.standard _

/-- The sheaf Ext comparison and Serre duality bound the derived Hom support,
so the bounded coherent derived category has finite-dimensional Hom spaces
with finite shift support. -/
theorem hom_finite_bounded (G : GeometricSerreData K) :
    CategoryTheory.Triangulated.HomFiniteBounded k
      (SchemeBoundedCoherentDerivedCategory X) := by
  letI : DerivedCategory.ExtFiniteBounded (k := k) (A := Coh X) :=
    DerivedCategory.ExtFiniteBounded.of_ext (k := k) (A := Coh X)
      (fun E F j => by
        letI : Module.Finite k (G.bilinear.extSpace E F j) := G.bilinear.extFinite E F j
        exact Module.Finite.equiv
          ((extSpaceLinearEquivWithScalar G.bilinear E F j
            (G.extComparison_scalar E F j)).trans
            (extToBounded (k := k) E F j).symm))
      (fun E F => by
        refine (Finset.finite_toSet (Finset.range (n + 1))).subset ?_
        intro j hj
        by_contra hnot
        have hhigh : (n : ℤ) < (j : ℤ) := by
          simp only [Finset.mem_coe, Finset.mem_range] at hnot
          omega
        have hzero := finrank_shifted_hom_eq_zero_of_dim_lt G E F (j : ℤ) hhigh
        have he := (extToBounded (k := k) E F j).finrank_eq
        rw [Function.mem_support] at hj
        exact hj (by exact_mod_cast he.trans hzero))
  exact DerivedCategory.homFiniteBounded_boundedDerived (k := k) (A := Coh X)
end AlgebraicGeometry.Duality.Serre.GeometricSerreData

namespace AlgebraicGeometry.Duality.Serre.GeometricSerreData

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.DerivedCategory
open CategoryTheory.Triangulated
attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
  {K : SmoothProperVariety.CanonicalSheafData k X n}

/-- Whisker the twist trivialization by the dimension shift, then remove the
identity functor with the left unitor. The sheaf-level
`AlgebraicGeometry.Duality.Serre.BilinearData.TrivialCanonical` does not supply
this natural isomorphism. -/
noncomputable def serreIsoShift (G : GeometricSerreData K)
    (hT : G.canonicalTwistFunctor ≅ 𝟭 (SchemeBoundedCoherentDerivedCategory X)) :
    G.toSerreFunctorData.S ≅ shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ) :=
  Functor.isoWhiskerRight hT
    (shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ)) ≪≫
    Functor.leftUnitor (shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ))

/-- Specialize the Serre pairing to an object paired with itself and transport
along the twist trivialization. Reverse the resulting equivalence so that the
degree-two self-Hom can be computed from the endomorphism space. -/
noncomputable def selfHomShiftTwoDual (G : GeometricSerreData K)
    (hn : n = 2) (hT : G.canonicalTwistFunctor ≅ 𝟭 (SchemeBoundedCoherentDerivedCategory X))
    (E : SchemeBoundedCoherentDerivedCategory X) :
    (E ⟶ E⟦(2 : ℤ)⟧) ≃ₗ[k] Module.Dual k (E ⟶ E) := by
  let hS := G.serreIsoShift hT
  subst hn
  exact ((G.toSerreFunctorData.eta E E).trans
    (Linear.homCongr k (Iso.refl E) (hS.app E))).symm

/-- Compose the degree-two Serre equivalence with the dual of the endomorphism
equivalence and the self-duality of the base field. This supplies the degree-two
clause of `AlgebraicGeometry.K3Surface.SphericalExtProfile` under a derived
twist trivialization; the profile itself keeps its independent fields. -/
theorem nonempty_hom_shift_two_linearEquiv_of_nonempty_end_linearEquiv
    (G : GeometricSerreData K)
    (hn : n = 2) (hT : G.canonicalTwistFunctor ≅ 𝟭 (SchemeBoundedCoherentDerivedCategory X))
    (E : SchemeBoundedCoherentDerivedCategory X) (hEnd : Nonempty ((E ⟶ E) ≃ₗ[k] k)) :
    Nonempty ((E ⟶ E⟦(2 : ℤ)⟧) ≃ₗ[k] k) := by
  obtain ⟨e⟩ := hEnd
  exact ⟨(G.selfHomShiftTwoDual hn hT E).trans
    (e.dualMap.symm.trans (LinearMap.ringLmapEquivSelf k k k))⟩

/-- In dimension two a naturally trivial derived canonical twist makes the
Hom-built Euler form symmetric. Bounded Hom support comes from the supplied
geometric data. -/
theorem chiHom_symm_of_trivialTwist (G : GeometricSerreData K)
    (hn : n = 2) (hT : G.canonicalTwistFunctor ≅ 𝟭 (SchemeBoundedCoherentDerivedCategory X))
    (A B : SchemeBoundedCoherentDerivedCategory X) :
    chiHom k (SchemeBoundedCoherentDerivedCategory X) A B =
      chiHom k (SchemeBoundedCoherentDerivedCategory X) B A := by
  letI := G.hom_finite_bounded
  letI : ∀ j : ℤ, (shiftFunctor (SchemeBoundedCoherentDerivedCategory X) j).Linear k :=
    fun j => AlgebraicGeometry.Duality.Serre.boundedShiftLinear j
  let hS : G.toSerreFunctorData.S ≅
      (𝟭 (SchemeBoundedCoherentDerivedCategory X)) ⋙
        shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ) :=
    Functor.isoWhiskerRight hT (shiftFunctor (SchemeBoundedCoherentDerivedCategory X) (n : ℤ))
  have h := G.toSerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist_of_natIso
    k (SchemeBoundedCoherentDerivedCategory X)
      (𝟭 (SchemeBoundedCoherentDerivedCategory X)) A B (n : ℤ) hS
  subst hn
  have hsign : (2 : ℤ).negOnePow = 1 := by
    simpa using Int.negOnePow_two_mul (1 : ℤ)
  simpa [hsign] using h

end AlgebraicGeometry.Duality.Serre.GeometricSerreData

namespace AlgebraicGeometry.Duality.Serre.GeometricSerreData

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.DerivedCategory
open CategoryTheory.Triangulated
open scoped BigOperators
attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}
  {K : SmoothProperVariety.CanonicalSheafData k X n}

private theorem chiHom_eq_eulerChar_of_finrank_vanishing_of_finrank_eq
    (G : GeometricSerreData K) (E F : Coh X)
    (hwindow : ∀ j : ℤ, j < 0 ∨ (n : ℤ) < j →
      Module.finrank k (((B (X := X)).obj E) ⟶ ((B (X := X)).obj F)⟦j⟧) = 0)
    (hrank : ∀ i : ℕ,
      Module.finrank k (G.bilinear.extSpace E F i) =
        Module.finrank k (((B (X := X)).obj E) ⟶
          ((B (X := X)).obj F)⟦(i : ℤ)⟧)) :
    chiHom k (D (X := X)) ((B (X := X)).obj E) ((B (X := X)).obj F) =
      G.bilinear.eulerChar E F := by
  unfold chiHom BilinearData.eulerChar
  let f : ℤ → ℤ := fun j => (j.negOnePow : ℤ) *
    Module.finrank k (((B (X := X)).obj E) ⟶ ((B (X := X)).obj F)⟦j⟧)
  have hsupport : Function.support f ⊆
      (Finset.range (n + 1)).image (fun i : ℕ => (i : ℤ)) := by
    intro j hj
    by_contra hnot
    have hlow : 0 ≤ j := by
      by_contra hh
      have hz := hwindow j (Or.inl (lt_of_not_ge hh))
      exact hj (by simp [f, hz])
    have hhigh : j ≤ (n : ℤ) := by
      by_contra hh
      have hz := hwindow j (Or.inr (lt_of_not_ge hh))
      exact hj (by simp [f, hz])
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hlow
    simp at hnot
    omega
  rw [show (∑ᶠ j : ℤ, (j.negOnePow : ℤ) *
      Module.finrank k (((B (X := X)).obj E) ⟶ ((B (X := X)).obj F)⟦j⟧)) =
      ∑ᶠ j : ℤ, f j from rfl]
  rw [finsum_eq_sum_of_support_subset f hsupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [f, Int.coe_negOnePow_natCast, hrank i]
  · intro a ha b hb hab
    exact Int.ofNat_injective hab

private theorem finrank_extSpace_eq_finrank_boundedSingleFunctor_shifted_hom
    (G : GeometricSerreData K)
    (E F : Coh X) (i : ℕ) :
    Module.finrank k (G.bilinear.extSpace E F i) =
      Module.finrank k (((B (X := X)).obj E) ⟶
        ((B (X := X)).obj F)⟦(i : ℤ)⟧) := by
  exact (extSpaceLinearEquivWithScalar G.bilinear E F i
    (G.extComparison_scalar E F i)).finrank_eq

/-- The Hom-built Euler form on embedded coherent sheaves equals the
sheaf-level Euler characteristic supplied by the bilinear data. The derived
Serre pairing and the sheaf restriction kill shifts above the dimension. -/
theorem chiHom_boundedSingleFunctor_obj_eq_eulerChar
    (G : GeometricSerreData K) (E F : Coh X) :
    chiHom k (SchemeBoundedCoherentDerivedCategory X)
        ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E)
        ((DerivedCategory.boundedSingleFunctor (Coh X)).obj F) =
      G.bilinear.eulerChar E F := by
  apply chiHom_eq_eulerChar_of_finrank_vanishing_of_finrank_eq G E F
  · intro j hj
    rcases hj with hneg | hhigh
    · exact finrank_shifted_hom_eq_zero_of_neg (k := k) E F j hneg
    · exact finrank_shifted_hom_eq_zero_of_dim_lt G E F j hhigh
  · exact finrank_extSpace_eq_finrank_boundedSingleFunctor_shifted_hom G E F

/-- Transfer the existing sheaf-level
`AlgebraicGeometry.Duality.Serre.BilinearData.surface_selfEuler_eq` calculation to
the Hom-built Euler form on the bounded derived category. The sheaf-level
trivial-canonical datum suffices for this numerical statement. -/
theorem chiHom_self_eq_of_trivialCanonical (G : GeometricSerreData K)
    (hn : n = 2) (T : G.bilinear.TrivialCanonical) (E : Coh X) :
    chiHom k (SchemeBoundedCoherentDerivedCategory X)
        ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E)
        ((DerivedCategory.boundedSingleFunctor (Coh X)).obj E) =
      2 * (Module.finrank k (G.bilinear.extSpace E E 0) : ℤ) -
        (Module.finrank k (G.bilinear.extSpace E E 1) : ℤ) := by
  rw [G.chiHom_boundedSingleFunctor_obj_eq_eulerChar]
  exact G.bilinear.surface_selfEuler_eq hn T E

end AlgebraicGeometry.Duality.Serre.GeometricSerreData
