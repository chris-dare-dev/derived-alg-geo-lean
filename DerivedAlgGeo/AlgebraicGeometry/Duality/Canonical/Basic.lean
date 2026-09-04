/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.AssociatedSheaf
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.Variety.Basic
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# Canonical sheaf data and the duality construction boundary

For a smooth variety of pure relative dimension `n`, the canonical sheaf is the determinant of
the relative cotangent sheaf. This file packages that construction using DerivedAlgGeo's existing
fixed-rank locally-free and determinant interfaces, and exposes its Picard and Cartier-divisor
classes.

`CanonicalSheafData` retains explicit cotangent and determinant fields so callers may package a
chosen model. The companion `Canonical.Differentials` module constructs the relative cotangent
sheaf for varieties over a field, while `Canonical.Descent` carries the standard-smooth chart
calculation through sheafification, proves fixed-rank local freeness, constructs the determinant
line and its explicit tensor inverse, and supplies
`CanonicalSheafData.ofSmoothRelativeDifferentials`. Mathlib's general relative-differentials
construction for arbitrary morphisms of ringed spaces remains outside this variety-specific API.

`Canonical.Derived` constructs the derived-category object `ω_X[n]` from this package. Likewise,
`DualizingSheafComparison` only compares a separately constructed candidate with the canonical
sheaf; it does not assert that an arbitrary module sheaf is dualizing or postulate Serre duality as
an axiom.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace SmoothProperVariety

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]

variable (k) in
/-- Explicit canonical-sheaf construction data on a smooth proper variety of pure dimension `n`.

The cotangent object and determinant descent are fields because the current scheme-sheaf API does
not yet construct them. The relative-dimension certificate is the genuine Mathlib morphism
property, not a numerical dimension assertion. -/
structure CanonicalSheafData (n : ℕ) where
  /-- The structure morphism is smooth of pure relative dimension `n`. -/
  smoothOfRelativeDimension :
    SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))
  /-- The chosen relative cotangent module sheaf. -/
  cotangent : X.Modules
  /-- Fixed-rank and determinant data for the chosen cotangent sheaf. -/
  cotangentDeterminant : Scheme.Modules.DeterminantData cotangent
  /-- Its locally free rank agrees with the geometric relative dimension. -/
  cotangent_rank : cotangentDeterminant.rank = n

namespace CanonicalSheafData

variable {X} {n : ℕ} (C : CanonicalSheafData k X n)

/-- The canonical line bundle, defined as the determinant of the cotangent sheaf. -/
noncomputable abbrev canonicalLineBundle :
    Scheme.Modules.LineBundleData X :=
  C.cotangentDeterminant.topExteriorPower

/-- The underlying canonical module sheaf `ω_X`. -/
noncomputable abbrev canonicalSheaf : X.Modules :=
  C.canonicalLineBundle.line

/-- The inverse, or anticanonical, line bundle. -/
noncomputable def antiCanonicalLineBundle :
    Scheme.Modules.LineBundleData X :=
  C.canonicalLineBundle.dual

/-- The canonical Picard class `[ω_X]`. -/
noncomputable def canonicalClass : Scheme.Modules.Pic X :=
  C.canonicalLineBundle.toPic

/-- The canonical class in additive notation. -/
noncomputable def canonicalClassAdd : Additive (Scheme.Modules.Pic X) :=
  Additive.ofMul C.canonicalClass

omit [IsSmoothProperVariety k X] in
/-- The anticanonical Picard class is the inverse of the canonical class. -/
@[simp]
theorem antiCanonicalClass :
    C.antiCanonicalLineBundle.toPic = C.canonicalClass⁻¹ :=
  C.canonicalLineBundle.toPic_dual

omit [IsSmoothProperVariety k X] in
/-- The chosen cotangent determinant has the recorded pure relative dimension. -/
theorem determinant_rank : C.cotangentDeterminant.rank = n :=
  C.cotangent_rank

omit [IsSmoothProperVariety k X] in
/-- Two canonical-sheaf packages with isomorphic line representatives define the same class. -/
theorem canonicalClass_eq_of_iso {C' : CanonicalSheafData k X n}
    (e : C.canonicalSheaf ≅ C'.canonicalSheaf) :
    C.canonicalClass = C'.canonicalClass :=
  C.canonicalLineBundle.toPic_eq_of_iso C'.canonicalLineBundle e

/-- An explicit Cartier representative of a canonical-sheaf package.

Existence is kept as data because the present Cartier-to-Picard API does not prove essential
surjectivity for every line bundle. -/
structure CanonicalDivisorData where
  /-- A Cartier divisor representing the canonical class. -/
  divisor : Scheme.CartierDivisor X
  /-- Its associated invertible sheaf is the canonical sheaf. -/
  associatedSheafIso :
    Scheme.CartierDivisor.associatedSheaf divisor ≅ C.canonicalSheaf

namespace CanonicalDivisorData

variable (D : CanonicalDivisorData C)

/-- The associated Cartier divisor maps to the canonical Picard class. -/
theorem toPic_eq_canonicalClass :
    Scheme.CartierDivisor.toPic D.divisor = C.canonicalClass := by
  apply Units.ext
  change Scheme.Modules.PicardClass.mk
      (Scheme.CartierDivisor.associatedSheaf D.divisor) =
    Scheme.Modules.PicardClass.mk C.canonicalSheaf
  exact (Scheme.Modules.PicardClass.mk_eq_mk_iff _ _).2 ⟨D.associatedSheafIso⟩

/-- The canonical Cartier divisor class. -/
noncomputable def canonicalDivisorClass :
    Scheme.CartierDivisor.ClassGroup X :=
  Scheme.CartierDivisor.toClass X D.divisor

/-- The Cartier class-to-Picard map sends the canonical divisor class to `[ω_X]`. -/
theorem classToPic_eq_canonicalClass :
    Scheme.CartierDivisor.classToPic
        (Multiplicative.ofAdd D.canonicalDivisorClass) = C.canonicalClass := by
  rw [canonicalDivisorClass, Scheme.CartierDivisor.classToPic_toClass]
  exact D.toPic_eq_canonicalClass

end CanonicalDivisorData

/-- Comparison data between a separately constructed dualizing-sheaf candidate and `ω_X`.

This structure deliberately contains no field claiming that `dualizingCandidate` is dualizing;
that property must come from a comparison with the constructed canonical complex. -/
structure DualizingSheafComparison
    (dualizingCandidate : X.Modules) where
  /-- On a smooth pure-dimensional target, the candidate is identified with `ω_X`. -/
  iso : dualizingCandidate ≅ C.canonicalSheaf

namespace DualizingSheafComparison

variable {C} {D : X.Modules}

omit [IsSmoothProperVariety k X] in
/-- A dualizing-candidate comparison determines the candidate's Picard class whenever it is
equipped with line-bundle data. -/
theorem candidateClass_eq (E : DualizingSheafComparison C D)
    (L : Scheme.Modules.LineBundleData X)
    (hL : L.line ≅ D) :
    L.toPic = C.canonicalClass :=
  L.toPic_eq_of_iso C.canonicalLineBundle (hL ≪≫ E.iso)

end DualizingSheafComparison

end CanonicalSheafData

end SmoothProperVariety

end AlgebraicGeometry
