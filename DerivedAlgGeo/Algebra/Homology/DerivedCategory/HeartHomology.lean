/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Degree-zero homology and the canonical heart truncation

Mathlib's degree-zero homology object, embedded by the single functor, is
isomorphic to the pure degree-zero truncation of any derived object. The
comparison is pointwise and requires no boundedness hypothesis.

## Main definitions

This file introduces no carrier, class, or instance.

## Main results

* `DerivedCategory.singleH0TruncIso` identifies the single object on degree-zero
  homology with the nested t-structure truncation.

## Implementation notes

The heart equivalence first identifies the truncation with a single object.
The long exact homology sequence makes both degree-zero truncation maps into
isomorphisms, identifying that object with Mathlib's homology object.

## References

Mathlib's `DerivedCategory.HomologySequence.exact₁`,
`DerivedCategory.HomologySequence.exact₂`,
`DerivedCategory.HomologySequence.exact₃`, and
`DerivedCategory.singleFunctorCompHomologyFunctorIso` at the pinned revision.

## Tags

derived category, heart, t-structure, homology, truncation
-/

universe w v u

open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Pretriangulated
  CategoryTheory.Limits

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private noncomputable def h0HeartObject (M : DerivedCategory C) : C :=
  (heartEquivalence C).inverse.obj ((TStructure.t (C := C)).heartH0Functor.obj M)

private noncomputable def h0HeartTruncIso (M : DerivedCategory C) :
    (singleFunctor C 0).obj (h0HeartObject C M) ≅
      ((TStructure.t (C := C)).truncGE 0).obj
        (((TStructure.t (C := C)).truncLT 1).obj M) := by
  let t := TStructure.t (C := C)
  let H := t.heartH0Functor.obj M
  let e := heartEquivalence C
  exact t.heart.ι.mapIso (e.counitIso.app H)

private theorem h0TruncLTIsIso (M : DerivedCategory C) :
    IsIso ((homologyFunctor C 0).map ((TStructure.t.truncLTι 1).app M)) := by
  let t := TStructure.t (C := C)
  let T := (t.triangleLTGE 1).obj M
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished 1 M
  have h₃ : IsZero ((homologyFunctor C 0).obj T.obj₃) :=
    isZero_of_isGE T.obj₃ 1 0 (by omega)
  have h₃' : IsZero ((homologyFunctor C (-1)).obj T.obj₃) :=
    isZero_of_isGE T.obj₃ 1 (-1) (by omega)
  have hmono : Mono ((homologyFunctor C 0).map T.mor₁) :=
    (HomologySequence.exact₁ T hT (-1) 0 (by omega)).mono_g (h₃'.eq_of_src _ _)
  have hepi : Epi ((homologyFunctor C 0).map T.mor₁) :=
    (HomologySequence.exact₂ T hT 0).epi_f (h₃.eq_of_tgt _ _)
  change Mono ((homologyFunctor C 0).map ((t.truncLTι 1).app M)) at hmono
  change Epi ((homologyFunctor C 0).map ((t.truncLTι 1).app M)) at hepi
  letI := hmono
  letI := hepi
  exact isIso_of_mono_of_epi _

private theorem h0TruncGEIsIso (L : DerivedCategory C) :
    IsIso ((homologyFunctor C 0).map ((TStructure.t.truncGEπ 0).app L)) := by
  let t := TStructure.t (C := C)
  let T := (t.triangleLTGE 0).obj L
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished 0 L
  haveI : t.IsLE T.obj₁ (-1) := t.isLE_truncLT_obj L 0 (-1) (by omega)
  have h₁ : IsZero ((homologyFunctor C 0).obj T.obj₁) :=
    isZero_of_isLE T.obj₁ (-1) 0 (by omega)
  have h₁' : IsZero ((homologyFunctor C 1).obj T.obj₁) :=
    isZero_of_isLE T.obj₁ (-1) 1 (by omega)
  have hmono : Mono ((homologyFunctor C 0).map T.mor₂) :=
    (HomologySequence.exact₂ T hT 0).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi ((homologyFunctor C 0).map T.mor₂) :=
    (HomologySequence.exact₃ T hT 0 1 rfl).epi_f (h₁'.eq_of_tgt _ _)
  change Mono ((homologyFunctor C 0).map ((t.truncGEπ 0).app L)) at hmono
  change Epi ((homologyFunctor C 0).map ((t.truncGEπ 0).app L)) at hepi
  letI := hmono
  letI := hepi
  exact isIso_of_mono_of_epi _

private noncomputable def h0HeartObjectIsoHomology (M : DerivedCategory C) :
    h0HeartObject C M ≅ (homologyFunctor C 0).obj M := by
  let F := h0HeartObject C M
  let L := (TStructure.t.truncLT 1).obj M
  haveI : IsIso ((homologyFunctor C 0).map ((TStructure.t.truncLTι 1).app M)) :=
    h0TruncLTIsIso C M
  haveI : IsIso ((homologyFunctor C 0).map ((TStructure.t.truncGEπ 0).app L)) :=
    h0TruncGEIsIso C L
  let eLT : (homologyFunctor C 0).obj L ≅ (homologyFunctor C 0).obj M :=
    @asIso _ _ _ _ _ (h0TruncLTIsIso C M)
  exact ((singleFunctorCompHomologyFunctorIso C 0).app F).symm ≪≫
    (homologyFunctor C 0).mapIso (h0HeartTruncIso C M) ≪≫
    (asIso ((homologyFunctor C 0).map ((TStructure.t.truncGEπ 0).app L))).symm ≪≫
    eLT

/-- The single complex on Mathlib's degree-zero homology object is pointwise
isomorphic to the pure degree-zero t-structure truncation. The comparison uses
homology exactness for the two truncation triangles, rather than definitional
equality of the objects. -/
noncomputable def singleH0TruncIso (M : DerivedCategory C) :
    (singleFunctor C 0).obj ((homologyFunctor C 0).obj M) ≅
      ((TStructure.t (C := C)).truncGE 0).obj
        (((TStructure.t (C := C)).truncLT 1).obj M) :=
  (singleFunctor C 0).mapIso (h0HeartObjectIsoHomology C M).symm ≪≫
    h0HeartTruncIso C M

end DerivedCategory
