/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The canonical t-structure on objects with cohomology in a weak Serre subcategory

Let `A` be an abelian category and `P : ObjectProperty A` a weak Serre subcategory
containing zero. `cohomologyIn P` is a triangulated subcategory of `DerivedCategory A`
(`cohomologyIn_isTriangulated`), and the canonical truncations do not leave it
(`cohomologyIn_truncLT`, `cohomologyIn_truncGE`). So the canonical t-structure of
`DerivedCategory A` restricts to `D_P(A) := (cohomologyIn P).FullSubcategory`, and its
heart is `P`.

## Main definitions

* `DerivedCategory.cohomologyInTStructure`: the induced t-structure on `D_P(A)`.
* `DerivedCategory.cohomologyInHeartEquivalence`: the equivalence of `P` with its heart.

## Main results

* `DerivedCategory.cohomologyIn_hasInducedTStructure`: the canonical t-structure
  induces one on `cohomologyIn P`.
* `DerivedCategory.cohomologyIn_ι_isTExact`: the inclusion `D_P(A) ⥤ D(A)` is t-exact.
* `DerivedCategory.cohomologyInTStructure_bounded_iff`: an object of `D_P(A)` is bounded
  exactly when it is bounded in `D(A)`.
* `DerivedCategory.cohomologyIn_cohomologyInTStructure_truncLE`: the induced truncations
  keep cohomology in any class closed under isomorphism and containing zero.

## Implementation notes

`HasInducedTStructure.mk'` asks for stability under `τ_{≤ n}`, which Mathlib defines as
`τ_{< n + 1}`, so `cohomologyIn_truncLT` applies without a new homology computation.
The weak Serre hypotheses are load-bearing only for the triangulated structure; the
truncation step uses closure under isomorphism and `0 ∈ P` alone.

The heart equivalence restricts the functor of `DerivedCategory.heartEquivalence`, so
there is one comparison of the canonical heart with `A` and this is its restriction.

## References

* Stacks Project, Lemma 13.17.1 (Tag 06UQ) and Remark 13.12.4.
* A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*, Astérisque 100 (1982),
  §1.3.

## Tags

t-structure, heart, weak Serre subcategory, derived category
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

/-- A single complex on an object of `P` has cohomology in `P`: its cohomology is that
object in one degree and zero elsewhere. -/
lemma cohomologyIn_singleFunctor_obj {Y : A} (hY : P Y) (n : ℤ) :
    cohomologyIn P ((singleFunctor A n).obj Y) := by
  intro i
  rcases lt_trichotomy i n with h | rfl | h
  · exact P.prop_of_isZero (isZero_of_isGE _ n i h)
  · exact P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A i).app Y).symm hY
  · exact P.prop_of_isZero (isZero_of_isLE _ n i h)

variable [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- **The canonical t-structure of `D(A)` induces one on `cohomologyIn P`.**

`HasInducedTStructure.mk'` asks for stability under `τ_{≤ n}` and `τ_{≥ n}`. The second
is `cohomologyIn_truncGE`; the first is `cohomologyIn_truncLT` at `n + 1`, since
`τ_{≤ n}` is `τ_{< n + 1}`. -/
instance cohomologyIn_hasInducedTStructure :
    (cohomologyIn P).HasInducedTStructure (TStructure.t (C := A)) :=
  .mk' fun _ hE n ↦ ⟨cohomologyIn_truncLT P hE (n + 1), cohomologyIn_truncGE P hE n⟩

/-- The canonical t-structure on `D_P(A)`, the objects of `DerivedCategory A` with
cohomology in `P`. -/
noncomputable abbrev cohomologyInTStructure : TStructure (cohomologyIn P).FullSubcategory :=
  (cohomologyIn P).tStructure TStructure.t

/-- The inclusion `D_P(A) ⥤ D(A)` is t-exact: the induced `IsLE` and `IsGE` are the
ambient ones. -/
instance cohomologyIn_ι_isTExact :
    (cohomologyIn P).ι.IsTExact (cohomologyInTStructure P) TStructure.t := by
  have : (cohomologyIn P).ι.IsRightTExact (cohomologyInTStructure P) TStructure.t :=
    ⟨fun E n hE ↦ ((cohomologyIn P).tStructure_isLE_iff _ E n).1 hE⟩
  have : (cohomologyIn P).ι.IsLeftTExact (cohomologyInTStructure P) TStructure.t :=
    ⟨fun E n hE ↦ ((cohomologyIn P).tStructure_isGE_iff _ E n).1 hE⟩
  exact Functor.isTExact_of

/-- An object of `D_P(A)` is bounded for the induced t-structure exactly when its
underlying complex is bounded for the canonical t-structure of `D(A)`. -/
theorem cohomologyInTStructure_bounded_iff (E : (cohomologyIn P).FullSubcategory) :
    (cohomologyInTStructure P).bounded E ↔ TStructure.t.bounded E.obj := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, ((cohomologyIn P).tStructure_isGE_iff _ E a).1 ha⟩,
      ⟨b, ((cohomologyIn P).tStructure_isLE_iff _ E b).1 hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, ((cohomologyIn P).tStructure_isGE_iff _ E a).2 ha⟩,
      ⟨b, ((cohomologyIn P).tStructure_isLE_iff _ E b).2 hb⟩⟩

/-- The induced truncation `τ_{≤ n}` keeps cohomology in any class `Q` closed under
isomorphism and containing zero: its underlying complex is the ambient `τ_{≤ n}`. -/
theorem cohomologyIn_cohomologyInTStructure_truncLE (Q : ObjectProperty A)
    [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]
    {E : (cohomologyIn P).FullSubcategory} (hE : cohomologyIn Q E.obj) (n : ℤ) :
    cohomologyIn Q (((cohomologyInTStructure P).truncLE n).obj E).obj :=
  (cohomologyIn Q).prop_of_iso
    (Functor.mapTruncLEIso (cohomologyIn P).ι (cohomologyInTStructure P) TStructure.t n E).symm
    (cohomologyIn_truncLT Q hE (n + 1))

section Heart

/-- `DerivedCategory.heartEquivalence` restricted to `P`, as a functor into the heart of
the induced t-structure. -/
noncomputable def toCohomologyInHeart :
    P.FullSubcategory ⥤ (cohomologyInTStructure P).heart.FullSubcategory :=
  (cohomologyInTStructure P).heart.lift
    ((cohomologyIn P).lift (P.ι ⋙ (heartEquivalence A).functor ⋙ TStructure.t.heart.ι)
      fun Y ↦ cohomologyIn_singleFunctor_obj P Y.property 0)
    fun Y ↦ heart_singleFunctor_obj A Y.obj

/-- `toCohomologyInHeart P` is fully faithful: after the two inclusions it is `P.ι` followed
by the functor of `heartEquivalence` and the inclusion of the heart. -/
noncomputable def fullyFaithfulToCohomologyInHeart : (toCohomologyInHeart P).FullyFaithful :=
  .ofCompFaithful (G := (cohomologyInTStructure P).heart.ι ⋙ (cohomologyIn P).ι)
    (P.fullyFaithfulι.comp ((heartEquivalence A).fullyFaithfulFunctor.comp
      (TStructure.t (C := A)).heart.fullyFaithfulι))

instance toCohomologyInHeart_full : (toCohomologyInHeart P).Full :=
  (fullyFaithfulToCohomologyInHeart P).full

instance toCohomologyInHeart_faithful : (toCohomologyInHeart P).Faithful :=
  (fullyFaithfulToCohomologyInHeart P).faithful

instance toCohomologyInHeart_essSurj : (toCohomologyInHeart P).EssSurj where
  mem_essImage E := by
    have hE : (TStructure.t (C := A)).heart E.obj.obj := E.property
    rw [← essImage_singleFunctor_eq_heart] at hE
    obtain ⟨Y, ⟨e⟩⟩ := hE
    have hY : P Y := prop_of_cohomologyIn_singleFunctor_obj P
      ((cohomologyIn P).prop_of_iso e.symm E.obj.property)
    exact ⟨⟨Y, hY⟩, ⟨((cohomologyInTStructure P).heart.fullyFaithfulι.comp
      (cohomologyIn P).fullyFaithfulι).preimageIso e⟩⟩

instance toCohomologyInHeart_isEquivalence : (toCohomologyInHeart P).IsEquivalence where

/-- **The heart of the canonical t-structure on `D_P(A)` is `P`.** -/
noncomputable def cohomologyInHeartEquivalence :
    P.FullSubcategory ≌ (cohomologyInTStructure P).heart.FullSubcategory :=
  (toCohomologyInHeart P).asEquivalence

@[simp]
theorem cohomologyInHeartEquivalence_functor :
    (cohomologyInHeartEquivalence P).functor = toCohomologyInHeart P :=
  rfl

@[simp]
theorem toCohomologyInHeart_obj_obj_obj (Y : P.FullSubcategory) :
    ((toCohomologyInHeart P).obj Y).obj.obj = (singleFunctor A 0).obj Y.obj :=
  rfl

end Heart

end DerivedCategory
