/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HeartHomology
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExt
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundleLinear

/-!
# Sections of degree-zero homology through the heart

For any scheme and any scheme-derived object, maps from the structure sheaf
into its pure degree-zero truncation are the top sections of its actual
Mathlib degree-zero homology sheaf. No affineness, quasicoherence or
boundedness hypothesis is needed for this pointwise comparison.

## Main definitions

This file introduces no carrier, class, or instance.

## Main results

* `AlgebraicGeometry.Cohomology.homTruncH0SectionsAddEquiv` identifies the
  additive Hom group into the pure truncation with top sections of homology.

## Implementation notes

The generic single-homology/pure-truncation isomorphism transports the target.
Full faithfulness of the single functor then reduces the Hom group to sheaf
morphisms, and the unit-to-top-sections equivalence evaluates those maps.

## References

The generic comparison is in `DerivedCategory.singleH0TruncIso`; the sections
map is `AlgebraicGeometry.Scheme.Modules.unitHomTopLinearEquiv`.

## Tags

derived category, homology, global sections, scheme
-/

universe u

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry.DerivedCategory

namespace AlgebraicGeometry.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- Maps from the structure sheaf into the pure degree-zero truncation of an
arbitrary scheme-derived object are additively equivalent to the top sections
of its Mathlib degree-zero homology sheaf. This is pointwise and makes no
ambient derived-global-sections or naturality assertion. -/
noncomputable def homTruncH0SectionsAddEquiv
    (X : Scheme.{u}) (M : SchemeDerivedCategory X) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.Modules.unit X) ⟶
      (DerivedCategory.TStructure.t.truncGE 0).obj
        ((DerivedCategory.TStructure.t.truncLT 1).obj M)) ≃+
    Γ((DerivedCategory.homologyFunctor X.Modules 0).obj M,
      (⊤ : X.Opens)) := by
  let C := X.Modules
  let F := DerivedCategory.singleFunctor C 0
  let H := (DerivedCategory.homologyFunctor C 0).obj M
  let U := Scheme.Modules.unit X
  let T := (DerivedCategory.TStructure.t.truncGE 0).obj
    ((DerivedCategory.TStructure.t.truncLT 1).obj M)
  let e : F.obj H ≅ T := DerivedCategory.singleH0TruncIso C M
  let postHom : (F.obj U ⟶ T) →+ (F.obj U ⟶ F.obj H) :=
    { toFun := fun f => f ≫ e.inv
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.add_comp] }
  let post : (F.obj U ⟶ T) ≃+ (F.obj U ⟶ F.obj H) :=
    AddEquiv.ofBijective postHom (Iso.homToEquiv e.symm).bijective
  let mapHom : (U ⟶ H) →+ (F.obj U ⟶ F.obj H) :=
    { toFun := F.map
      map_zero' := by simp
      map_add' := by intros; simp [Functor.map_add] }
  let map : (U ⟶ H) ≃+ (F.obj U ⟶ F.obj H) :=
    AddEquiv.ofBijective mapHom
      ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective U H)
  exact post.trans map.symm |>.trans (Scheme.Modules.unitHomTopLinearEquiv H).toAddEquiv

end AlgebraicGeometry.Cohomology
