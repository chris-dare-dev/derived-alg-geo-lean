/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.TStructure
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.BoundedCoherent

/-!
# The standard t-structure on `Dqc(X)`

On an arbitrary scheme `X`, quasi-coherent sheaves form a weak Serre subcategory of
`X.Modules`, and `Dqc(X)` is `cohomologyIn` of it. The canonical t-structure of the
all-sheaf derived category therefore restricts to `Dqc(X)`, and its heart is the
category of quasi-coherent sheaves. No hypothesis on `X` is used.

The induced truncations are the ambient ones, so they keep the finite presentation of
cohomology sheaves. That is the premise `hfpLE` of
`Families.SchemeBaseChange.TargetBoundedTStructure.boundedCoherentTStructure` for this
t-structure.

## Main definitions

* `Dqc.standardTStructure`: the standard t-structure on `Dqc(X)`.
* `Dqc.standardHeartEquivalence`: its heart is `QCoh(X)`.

## Main results

* `Dqc.schemeQuasicoherentCohomology_hasInducedTStructure`: the canonical t-structure
  induces one on `Dqc(X)`.
* `Dqc.standardTStructure_bounded_iff`: its bounded objects are the ambiently bounded
  ones.
* `Dqc.standardTStructure_truncLE_mem_finitePresentation`: its truncations keep finite
  presentation of every cohomology sheaf.

## Implementation notes

`X.Modules` and `SheafOfModules X.ringCatSheaf` are the same type with two category
instances, and the weak Serre instances of quasi-coherence are stated for the second.
The generic results are therefore applied at `SheafOfModules X.ringCatSheaf` and
compared with statements at `X.Modules` by unfolding, as for the triangulated structure
of `Dqc(X)` in `Dqc.lean`.

## References

* Stacks Project, Section 36.3 (Tag 06YZ).
* A. Bayer, M. Lahoz, E. Macrì, H. Nuer, A. Perry, P. Stellari, *Stability conditions
  in families*, arXiv:1902.08184v4, Lemma 3.14.

## Tags

t-structure, heart, quasi-coherent sheaf, derived category, scheme
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable (X : Scheme.{u})

/-- The canonical t-structure of the all-sheaf derived category induces one on `Dqc(X)`.
This is `DerivedCategory.cohomologyIn_hasInducedTStructure` for quasi-coherence. -/
instance schemeQuasicoherentCohomology_hasInducedTStructure :
    (schemeQuasicoherentCohomology X).HasInducedTStructure
      (DerivedCategory.TStructure.t (C := X.Modules)) :=
  inferInstanceAs ((DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).HasInducedTStructure
      (DerivedCategory.TStructure.t (C := SheafOfModules X.ringCatSheaf)))

/-- The standard t-structure on `Dqc(X)`: the canonical t-structure of the all-sheaf
derived category, restricted to the objects with quasi-coherent cohomology. -/
def standardTStructure : TStructure (SchemeQuasicoherentDerivedCategory X) :=
  (schemeQuasicoherentCohomology X).tStructure DerivedCategory.TStructure.t

theorem standardTStructure_isLE_iff (E : SchemeQuasicoherentDerivedCategory X) (n : ℤ) :
    (standardTStructure X).IsLE E n ↔
      (DerivedCategory.TStructure.t (C := X.Modules)).IsLE E.obj n :=
  (schemeQuasicoherentCohomology X).tStructure_isLE_iff _ E n

theorem standardTStructure_isGE_iff (E : SchemeQuasicoherentDerivedCategory X) (n : ℤ) :
    (standardTStructure X).IsGE E n ↔
      (DerivedCategory.TStructure.t (C := X.Modules)).IsGE E.obj n :=
  (schemeQuasicoherentCohomology X).tStructure_isGE_iff _ E n

/-- The bounded objects of the standard t-structure are the ambiently bounded ones. -/
theorem standardTStructure_bounded_iff (E : SchemeQuasicoherentDerivedCategory X) :
    (standardTStructure X).bounded E ↔ schemeBoundedQuasicoherent X E := by
  let E' : (DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory := E
  exact DerivedCategory.cohomologyInTStructure_bounded_iff _ E'

/-- **The heart of the standard t-structure on `Dqc(X)` is `QCoh(X)`.** -/
def standardHeartEquivalence :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (standardTStructure X).heart.FullSubcategory :=
  DerivedCategory.cohomologyInHeartEquivalence (SheafOfModules.isQuasicoherent X.ringCatSheaf)

/-- The truncations of the standard t-structure keep finite presentation of every
cohomology sheaf. -/
theorem standardTStructure_truncLE_mem_finitePresentation
    (E : SchemeQuasicoherentDerivedCategory X) (hE : schemeFinitePresentationCohomology X E)
    (n : ℤ) :
    schemeFinitePresentationCohomology X (((standardTStructure X).truncLE n).obj E) := by
  have := SheafOfModules.isFinitePresentation_containsZero (R := X.ringCatSheaf)
  let E' : (DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory := E
  exact DerivedCategory.cohomologyIn_cohomologyInTStructure_truncLE _
    (SheafOfModules.isFinitePresentation X.ringCatSheaf) (E := E') hE n

end

end AlgebraicGeometry.DerivedCategory.Dqc
