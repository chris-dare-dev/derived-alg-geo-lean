/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Additivity
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.AlgebraicGeometry.Duality.Canonical.Derived
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.LinearDual
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.Surface.Number
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Serre duality: explicit derived and cohomological interfaces

For a smooth proper variety of pure dimension `n`, Serre duality should identify

`H^i(X, F)ᵛ ≃ Ext^(n-i)(F, ω_X)`.

The pinned Mathlib has derived categories and `Ext`, but no derived global-sections functor into
`D(k)`, coherent `RHom`, or Grothendieck-duality theorem. Accordingly this file packages the
exact remaining realization data and derives the finite-dimensional pairing and
Euler-characteristic consequences.

`CanonicalSheafData.dualizingComplex` constructs the object `ω_X[n]` rather than accepting it as
a field. `DerivedStatement` records the functors and duality isomorphism still missing upstream.
`Data` records the cohomology-level realization against Mathlib's actual `Abelian.Ext` groups.
`LocallyFreeSpecialization` identifies those Ext groups with the cohomology of `Fᵛ ⊗ ω_X`; from
these inputs this file proves the usual dimension and Euler symmetries.
-/

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.Duality.Serre

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.DerivedCategory

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}

noncomputable section

/-- The derived-category form of the missing Serre-duality construction.

The functor `linearDualShift` is the exact derived lift of algebraic linear duality followed by
the shift `[-n]`.  It is now constructed rather than supplied as an arbitrary field.  The only
remaining categorical input on this side is the explicit comparison
`(DerivedCategory C)ᵒᵖ ≃ DerivedCategory (Cᵒᵖ)`, which the pinned Mathlib does not yet bundle.
The dualizing object itself is the constructed `K.dualizingComplex = ω_X[n]`. -/
structure DerivedStatement (K : SmoothProperVariety.CanonicalSheafData k X n) where
  /-- Derived global sections with its base-field-linear target. -/
  rGlobalSections :
    SchemeCoherentDerivedCategory X ⥤
      DerivedCategory (ModuleCat.{u + 1} k)
  /-- Derived Hom into the chosen dualizing object. -/
  rHomDualizing :
    (SchemeCoherentDerivedCategory X)ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} k)
  /-- Comparison between the opposite derived category and the derived category of the opposite
  module category. -/
  oppositeDerived : CategoryTheory.DerivedCategory.OppositeComparison
    (ModuleCat.{u + 1} k)
  /-- The derived Serre-duality isomorphism. -/
  dualityIso :
    rHomDualizing ≅ rGlobalSections.op ⋙
      ModuleCat.derivedLinearDualShift k oppositeDerived (-(n : ℤ))

namespace DerivedStatement

variable {K : SmoothProperVariety.CanonicalSheafData k X n}

/-- The constructed derived linear-dual functor followed by the dimension shift. -/
noncomputable def linearDualShift (S : DerivedStatement K) :
    (DerivedCategory (ModuleCat.{u + 1} k))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  ModuleCat.derivedLinearDualShift k S.oppositeDerived (-(n : ℤ))

/-- The dualizing object associated to a derived Serre statement is the constructed
canonical complex `ω_X[n]`. -/
noncomputable abbrev dualizingObject (_ : DerivedStatement K) := K.dualizingComplex

/-- The canonical shift identification attached to every derived Serre statement. -/
noncomputable def canonicalShiftIso (_ : DerivedStatement K) :
    K.dualizingComplex ≅
      (DerivedCategory.singleFunctor (Coh X) (n : ℤ)).obj
        K.canonicalCohObject :=
  K.dualizingComplexIso

end DerivedStatement

section Ext

local instance : HasExt.{u + 1} (Coh X) :=
  HasExt.standard _

/-- Explicit coherent Serre-duality data relative to a finite-cohomology realization.

`extSpace` is a linear lift of Mathlib's additive `Abelian.Ext` group, just as
`FiniteCohomology.moduleH` is a linear lift of `Sheaf.H`.  The comparison prevents the field
structure from being an unrelated replacement.  Perfection is carried by the linear
equivalence `duality`; it is not asserted as a proposition with no map.
-/
structure Data (K : SmoothProperVariety.CanonicalSheafData k X n) (D : FiniteCohomology k X) where
  /-- The derived-category statement from which this realization is intended to be extracted. -/
  derived : DerivedStatement K
  /-- A base-field-linear realization of `Ext^j(F, ω_X)`. -/
  extSpace : Coh X → ℕ → ModuleCat.{u + 1} k
  /-- Forgetting scalars recovers Mathlib's actual Ext group. -/
  extComparison : ∀ (F : Coh X) (j : ℕ),
    (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).obj (extSpace F j) ≅
      AddCommGrpCat.of (Abelian.Ext.{u + 1} F K.canonicalCohObject j)
  /-- The Ext spaces are finite-dimensional. -/
  extFinite : ∀ (F : Coh X) (j : ℕ),
    Module.Finite k (extSpace F j)
  /-- Perfect coherent Serre duality in every degree in the geometric range. -/
  duality : ∀ (F : Coh X) (i : ℕ) (_hi : i ≤ n),
    Module.Dual k ((D.moduleH i).obj F) ≃ₗ[k] extSpace F (n - i)
  /-- Cohomology above the relative dimension vanishes. -/
  vanishesAboveDimension : ∀ (F : Coh X) (i : ℕ), n < i →
    Subsingleton ((D.moduleH i).obj F)

namespace Data

variable {K : SmoothProperVariety.CanonicalSheafData k X n}
variable {D : FiniteCohomology k X} (S : Data K D)

/-- The coherent cohomology-level Serre-duality equivalence in the geometric range. -/
noncomputable def coherentDualityEquiv (F : Coh X)
    (i : ℕ) (hi : i ≤ n) :
    Module.Dual k ((D.moduleH i).obj F) ≃ₗ[k] S.extSpace F (n - i) :=
  S.duality F i hi

/-- The perfect pairing `H^i(X,F) × Ext^(n-i)(F,ω_X) → k` extracted from duality. -/
def pairing (F : Coh X) (i : ℕ) (hi : i ≤ n) :
    (D.moduleH i).obj F →ₗ[k] S.extSpace F (n - i) →ₗ[k] k where
  toFun x :=
    { toFun := fun y ↦ (S.duality F i hi).symm y x
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by
    intro x y
    ext z
    exact map_add ((S.duality F i hi).symm z) x y
  map_smul' := by
    intro r x
    ext z
    exact map_smul ((S.duality F i hi).symm z) r x

@[simp]
theorem pairing_apply (F : Coh X) (i : ℕ) (hi : i ≤ n)
    (x : (D.moduleH i).obj F) (y : S.extSpace F (n - i)) :
    S.pairing F i hi x y = (S.duality F i hi).symm y x :=
  rfl

/-- The displayed coherent Serre pairing is perfect in Mathlib's standard sense: both induced
maps to the opposite dual space are bijective. -/
noncomputable instance pairing_isPerfPair (F : Coh X)
    (i : ℕ) (hi : i ≤ n) :
    (S.pairing F i hi).IsPerfPair := by
  letI := D.finite i F
  letI : Module.Free k ((D.moduleH i).obj F) :=
    Module.Free.of_divisionRing k _
  let e := (S.duality F i hi).symm
  have he : e.toLinearMap.IsPerfPair := by infer_instance
  change e.toLinearMap.flip.IsPerfPair
  exact he.flip

/-- Perfection gives equality of the cohomology and complementary Ext dimensions. -/
theorem dimension_eq_ext (F : Coh X) (i : ℕ) (hi : i ≤ n) :
    D.dimension F i = Module.finrank k (S.extSpace F (n - i)) := by
  letI := D.finite i F
  letI := S.extFinite F (n - i)
  rw [← (S.duality F i hi).finrank_eq, Subspace.dual_finrank_eq]

/-- A locally free specialization identifies Ext with the cohomology of
`Fᵛ ⊗ ω_X`.  The dual twist is explicit because the present sheaf API does not yet construct
internal Hom or prove its coherence automatically. -/
structure LocallyFreeSpecialization (F : Coh X) where
  /-- A fixed finite locally free certificate for `F`. -/
  rank : ℕ
  locallyFree : Scheme.Modules.FiniteLocallyFreeData F.1 rank
  /-- The coherent sheaf representing `Fᵛ ⊗ ω_X`. -/
  dualCanonicalTwist : Coh X
  /-- `Ext^j(F,ω_X)` is the `j`th cohomology of the dual canonical twist. -/
  extToCohomology : ∀ j : ℕ,
    S.extSpace F j ≃ₗ[k] (D.moduleH j).obj dualCanonicalTwist

namespace LocallyFreeSpecialization

variable {S} {F : Coh X}
variable (L : S.LocallyFreeSpecialization F)

/-- For a finite locally-free sheaf, coherent Serre duality becomes
`H^i(X,F)ᵛ ≃ H^(n-i)(X,Fᵛ ⊗ ω_X)`. -/
noncomputable def cohomologyDualityEquiv (i : ℕ) (hi : i ≤ n) :
    Module.Dual k ((D.moduleH i).obj F) ≃ₗ[k]
      (D.moduleH (n - i)).obj L.dualCanonicalTwist :=
  (S.coherentDualityEquiv F i hi).trans (L.extToCohomology (n - i))

/-- The cohomology dimensions of a locally free sheaf are reflected across the dimension. -/
theorem dimension_symmetry (i : ℕ) (hi : i ≤ n) :
    D.dimension F i = D.dimension L.dualCanonicalTwist (n - i) := by
  rw [S.dimension_eq_ext F i hi]
  exact (L.extToCohomology (n - i)).finrank_eq

/-- The Euler characteristic may be summed exactly through the geometric dimension. -/
theorem eulerCharacteristic_eq_sum_dimension
    (S : Data K D) (G : Coh X) :
    D.eulerCharacteristic G =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * D.dimension G i := by
  simpa only [FiniteCohomology.eulerCharacteristic, FiniteCohomology.dimension,
    FiniteCohomology.gradedModule, FiniteCohomology.upNat_sign] using
      GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
        (ComplexShape.up ℕ) (D.gradedModule G) (Finset.range (n + 1)) (by
          intro i hi
          change D.dimension G i ≠ 0 at hi
          have hle : i ≤ n := by
            by_contra h
            haveI : Subsingleton ((D.moduleH i).obj G) :=
              Data.vanishesAboveDimension S G i (Nat.lt_of_not_ge h)
            exact hi Module.finrank_zero_of_subsingleton
          simpa only [Finset.mem_coe, Finset.mem_range] using Nat.lt_succ_of_le hle)

private theorem negOnePow_rev (i : Fin (n + 1)) :
    (-1 : ℤ) ^ i.rev.val = (-1 : ℤ) ^ n * (-1 : ℤ) ^ i.val := by
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hsq : (-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hrev : i.rev.val = n - i.val := by
    simp only [Fin.val_rev, Nat.succ_sub_succ_eq_sub]
  rw [hrev]
  calc
    (-1 : ℤ) ^ (n - i.val) = (-1 : ℤ) ^ (n - i.val) * 1 := by simp
    _ = (-1 : ℤ) ^ (n - i.val) *
        ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val) := by rw [hsq]
    _ = ((-1 : ℤ) ^ (n - i.val) * (-1 : ℤ) ^ i.val) *
        (-1 : ℤ) ^ i.val := by ring
    _ = (-1 : ℤ) ^ n * (-1 : ℤ) ^ i.val := by
      rw [← pow_add, Nat.sub_add_cancel hi]

private theorem reflected_dimension (i : Fin (n + 1)) :
    D.dimension F i.rev.val = D.dimension L.dualCanonicalTwist i.val := by
  rw [L.dimension_symmetry i.rev (Nat.le_of_lt_succ i.rev.isLt)]
  congr 1
  have hrev : i.rev.val = n - i.val := by
    simp only [Fin.val_rev, Nat.succ_sub_succ_eq_sub]
  rw [hrev]
  omega

/-- Euler-characteristic symmetry for the locally free specialization:
`χ(F) = (-1)^n χ(Fᵛ ⊗ ω_X)`.

This is the sign convention needed downstream; in dimension two the sign is positive. -/
theorem eulerCharacteristic_symmetry :
    D.eulerCharacteristic F =
      (-1 : ℤ) ^ n * D.eulerCharacteristic L.dualCanonicalTwist := by
  rw [eulerCharacteristic_eq_sum_dimension S F,
    eulerCharacteristic_eq_sum_dimension S L.dualCanonicalTwist]
  simp only [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ i.val * (D.dimension F i.val : ℤ) =
        ∑ i : Fin (n + 1),
          (-1 : ℤ) ^ i.rev.val * (D.dimension F i.rev.val : ℤ) :=
      (Fintype.sum_equiv (Fin.revPerm)
        (fun i : Fin (n + 1) ↦
          (-1 : ℤ) ^ i.rev.val * (D.dimension F i.rev.val : ℤ))
        (fun i : Fin (n + 1) ↦
          (-1 : ℤ) ^ i.val * (D.dimension F i.val : ℤ))
        (fun _ ↦ rfl)).symm
    _ = ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ n *
          ((-1 : ℤ) ^ i.val *
            (D.dimension L.dualCanonicalTwist i.val : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [negOnePow_rev, L.reflected_dimension]
      ring
    _ = (-1 : ℤ) ^ n *
        ∑ i : Fin (n + 1),
          (-1 : ℤ) ^ i.val *
            (D.dimension L.dualCanonicalTwist i.val : ℤ) := by
      rw [Finset.mul_sum]

/-- On a surface, Serre duality preserves Euler characteristic. -/
theorem surface_eulerCharacteristic_symmetry (hn : n = 2) :
    D.eulerCharacteristic F = D.eulerCharacteristic L.dualCanonicalTwist := by
  subst n
  simpa using L.eulerCharacteristic_symmetry

end LocallyFreeSpecialization

/-- Picard-level Euler symmetry supplied by locally free Serre duality on a surface.

This small interface is the exact #40 output used by geometric surface Riemann--Roch.  Its field
is a theorem produced by the locally free specialization once line-bundle representatives and
their dual canonical twists are identified in the Picard group. -/
structure SurfacePicardSymmetry
    {C : D.LinearConnectingSystem}
    (I : AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext D C 2)
    (canonicalClass : Scheme.Modules.Pic X) where
  symmetry : ∀ L : Scheme.Modules.Pic X,
    I.eulerPic L = I.eulerPic (canonicalClass * L⁻¹)

/-- Geometric line-bundle representatives realizing the Picard Euler function and their
locally free Serre-dual twists. -/
structure SurfaceLineBundleFamily
    {C : D.LinearConnectingSystem}
    (I : AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext D C 2)
    (canonicalClass : Scheme.Modules.Pic X) where
  /-- The geometric relative dimension is two. -/
  dimension_eq_two : n = 2
  /-- A coherent representative of each Picard class. -/
  representative : Scheme.Modules.Pic X → Coh X
  /-- Locally free Serre duality for every representative. -/
  specialization : ∀ L : Scheme.Modules.Pic X,
    S.LocallyFreeSpecialization (representative L)
  /-- The representative realizes the intrinsic Picard Euler value. -/
  representativeEuler : ∀ L : Scheme.Modules.Pic X,
    D.eulerCharacteristic (representative L) = I.eulerPic L
  /-- Its dual canonical twist realizes `K_X ⊗ L⁻¹`. -/
  dualEuler : ∀ L : Scheme.Modules.Pic X,
    D.eulerCharacteristic (specialization L).dualCanonicalTwist =
      I.eulerPic (canonicalClass * L⁻¹)

namespace SurfaceLineBundleFamily

variable {C : D.LinearConnectingSystem}
variable {I : AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext D C 2}
variable {canonicalClass : Scheme.Modules.Pic X}

/-- Locally free Serre duality for the chosen representatives proves Picard Euler symmetry. -/
theorem toSurfacePicardSymmetry
    (P : S.SurfaceLineBundleFamily I canonicalClass) :
    SurfacePicardSymmetry I canonicalClass where
  symmetry L := by
    calc
      I.eulerPic L = D.eulerCharacteristic (P.representative L) :=
        (P.representativeEuler L).symm
      _ = D.eulerCharacteristic (P.specialization L).dualCanonicalTwist :=
        (P.specialization L).surface_eulerCharacteristic_symmetry P.dimension_eq_two
      _ = I.eulerPic (canonicalClass * L⁻¹) := P.dualEuler L

end SurfaceLineBundleFamily

namespace SurfacePicardSymmetry

variable {C : D.LinearConnectingSystem}
variable {I : AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext D C 2}
variable {canonicalClass : Scheme.Modules.Pic X}

/-- The trivial line bundle and the canonical bundle have the same Euler characteristic. -/
theorem canonical (P : SurfacePicardSymmetry I canonicalClass) :
    I.eulerPic canonicalClass = I.eulerPic 1 := by
  simpa using (P.symmetry 1).symm

/-- K3 sign check: when the canonical class is trivial, `χ(L) = χ(L⁻¹)`. -/
theorem k3 (P : SurfacePicardSymmetry I canonicalClass)
    (hK : canonicalClass = 1) (L : Scheme.Modules.Pic X) :
    I.eulerPic L = I.eulerPic L⁻¹ := by
  simpa [hK] using P.symmetry L

end SurfacePicardSymmetry

end Data

end Ext


end

end AlgebraicGeometry.Duality.Serre
