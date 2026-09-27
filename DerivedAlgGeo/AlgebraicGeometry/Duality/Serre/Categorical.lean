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

/-!
# Geometric Serre data on a smooth proper scheme

`GeometricSerreData` packages an abstract right Serre functor, an explicit
isomorphism to the derived canonical twist followed by shift, and the supplied
sheaf comparison. The derived duality and its naturality are transported along
the isomorphism; bounded Hom-finiteness follows from the scalar Ext comparison,
sheaf Ext-finiteness, and derived duality. No geometric inhabitant is built here.
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

/-- Forget the scalar action in `BilinearData.extComparison` to obtain the
underlying additive Ext comparison. -/
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

/-- Compare the supplied derived Serre pairing with the sheaf-level
bilinear pairing on coherent sheaves in degrees `i ≤ n`, using explicit scalar
compatibility and the restriction of the canonical twist to sheaves. -/
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

private theorem negativeHomZero (E F : Coh X) (j : ℤ) (hj : j < 0) :
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

private theorem highHomZeroNoBounded (G : GeometricSerreData K)
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
    negativeHomZero (k := k) F (G.bilinear.canonicalTwist E) ((n : ℤ) - j) (by omega)
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
theorem homFiniteBoundedFromRest (G : GeometricSerreData K) :
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
        have hzero := highHomZeroNoBounded G E F (j : ℤ) hhigh
        have he := (extToBounded (k := k) E F j).finrank_eq
        rw [Function.mem_support] at hj
        exact hj (by exact_mod_cast he.trans hzero))
  exact DerivedCategory.homFiniteBounded_boundedDerived (k := k) (A := Coh X)
end AlgebraicGeometry.Duality.Serre.GeometricSerreData
