/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.AlgebraicGeometry.Duality.Canonical.Differentials

/-!
# The canonical dualizing complex

For canonical-sheaf data on a smooth proper variety of pure dimension `n`, this file constructs
the coherent canonical sheaf and places it in cohomological degree `n`. Thus the dualizing
complex used by the Serre interface is the actual derived-category object `ω_X[n]`; it is no
longer a field supplied by downstream data.

The construction also records the geometric hypotheses supplied automatically by a smooth
proper variety over a field, integrates degreewise finite-dimensional cohomology with the
finite-cohomology package, and checks the shift on the zero-dimensional smooth proper point.

This is an object construction and shift convention, not a proof of Grothendieck duality.
The derived `RHom` functor and its Serre-duality equivalence remain explicit realization data.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace SmoothProperVariety

variable {k : Type u} [Field k]

/-- Degreewise finite-dimensional cohomology on a smooth proper variety has the boundedness
needed by the repository's `FiniteCohomology` interface. -/
noncomputable def finiteCohomology (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
    (D : Cohomology.FiniteDimensionalCohomology k X) :
    Cohomology.FiniteCohomology k X :=
  D.toFiniteCohomology

/-- The smooth proper point over `k`: `Spec k` itself. It provides the zero-dimensional
shift test below. Its structure morphism is the identity, recorded as the `Scheme.Over`
instance `instOverPoint`. -/
noncomputable abbrev point (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k)

/-- The point lies over itself by the identity. -/
noncomputable instance instOverPoint (k : Type u) [Field k] : (point k).Over (point k) :=
  ⟨𝟙 _⟩

/-- The point is a smooth proper variety over `k`: every constituent is a property of the
identity morphism or of the spectrum of a field. -/
instance isSmoothProperVariety_point (k : Type u) [Field k] :
    IsSmoothProperVariety k (point k) where
  toIsIntegral := inferInstance
  toSmooth := inferInstanceAs (Smooth (𝟙 (point k)))
  toIsProper := inferInstanceAs (IsProper (𝟙 (point k)))

namespace CanonicalSheafData

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}

/-- The canonical line bundle as an object of the coherent-sheaf category. Coherence follows
automatically from invertibility. -/
noncomputable def canonicalCohObject (K : SmoothProperVariety.CanonicalSheafData k X n) :
    Coh X :=
  ⟨K.canonicalSheaf, K.canonicalLineBundle.isCoherent⟩

/-- The canonical dualizing-complex candidate `ω_X[n]` in the coherent derived category. -/
noncomputable def dualizingComplex (K : SmoothProperVariety.CanonicalSheafData k X n) :
    DerivedCategory.SchemeCoherentDerivedCategory X :=
  (DerivedCategory.singleFunctor (Coh X) (n : ℤ)).obj
    K.canonicalCohObject

/-- The defining identification of the constructed dualizing complex with `ω_X[n]`. -/
noncomputable def dualizingComplexIso (K : SmoothProperVariety.CanonicalSheafData k X n) :
    K.dualizingComplex ≅
      (DerivedCategory.singleFunctor (Coh X) (n : ℤ)).obj
        K.canonicalCohObject :=
  Iso.refl _

/-- Explicit dimension-zero canonical-sheaf data on the smooth proper point. Its cotangent
model is the free sheaf on no generators and its determinant is the structure line. -/
noncomputable def pointCanonicalSheafData (k : Type u) [Field k] :
    SmoothProperVariety.CanonicalSheafData k (point k) 0 := by
  let q := (SheafOfModules.free.generatingSections
    (R := (point k).ringCatSheaf)
      (ULift.{u} Empty)).localGeneratorsData
  let F : Scheme.Modules.FiniteLocallyFreeData
      (SheafOfModules.free (R := (point k).ringCatSheaf)
        (ULift.{u} Empty)) 0 :=
    { localGenerators := q
      isLocallyFreeData := inferInstance
      rankEquiv := fun i => by
        change Nonempty (ULift.{u} Empty ≃ Fin 0)
        exact ⟨Equiv.equivOfIsEmpty _ _⟩ }
  exact
    { smoothOfRelativeDimension := by
        change SmoothOfRelativeDimension 0 (𝟙 _)
        infer_instance
      cotangent := SheafOfModules.free (ULift.{u} Empty)
      cotangentDeterminant :=
        { rank := 0
          finiteLocallyFree := F
          topExteriorPower := Scheme.Modules.LineBundleData.unit _ }
      cotangent_rank := rfl }

/-- On the smooth proper point, the chosen canonical sheaf is the structure sheaf. -/
@[simp]
theorem pointCanonicalSheafData_canonicalSheaf (k : Type u) [Field k] :
    (pointCanonicalSheafData k).canonicalSheaf =
      SheafOfModules.unit (point k).ringCatSheaf :=
  rfl

/-- Shift sanity check: the dualizing complex of the smooth proper point is the canonical
object in degree zero. -/
noncomputable def pointDualizingComplexIso (k : Type u) [Field k] :
    (pointCanonicalSheafData k).dualizingComplex ≅
      (DerivedCategory.singleFunctor
        (Coh (point k)) (0 : ℤ)).obj
        (pointCanonicalSheafData k).canonicalCohObject :=
  (pointCanonicalSheafData k).dualizingComplexIso

end CanonicalSheafData

end SmoothProperVariety

end AlgebraicGeometry
