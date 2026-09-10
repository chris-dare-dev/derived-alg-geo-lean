/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.QuasiIso
import DerivedAlgGeo.Algebra.Homology.DGCategory.H0

/-!
# A quasi-equivalence induces an equivalence on `H⁰`

`DGFunctor.IsQuasiEquivalence` asks that every Hom-complex map be a
quasi-isomorphism and that `H⁰ F` be essentially surjective.  This file proves
that such an `F` induces an equivalence `H⁰ C ≌ H⁰ D`.

This is `dg-enhancements-e10`, and it is what turns the recorded
`TwistCotwistEquivalenceConditions` from data into a conclusion: those
conditions are quasi-equivalences, and until now nothing in the repository
consumed a quasi-equivalence at all.

## The seam, and how it is crossed

A morphism of `H⁰` is a degree-zero cocycle modulo coboundaries, while
`QuasiIso` speaks about Mathlib's homology object.  Identifying the two is the
seam `LinearH0.lean` flagged as missing.

It is crossed without ever comparing the two descriptions of homology.
Mathlib's `ShortComplex.LeftHomologyMapData.quasiIso_iff` says a morphism of
short complexes is a quasi-isomorphism exactly when the `φH` of *any* left
homology map datum is an isomorphism, and `ShortComplex.abLeftHomologyData`
presents the homology of a short complex of abelian groups as the concrete
quotient.  So building one left homology map datum by hand, with `φH` the map
`F` induces on cocycles modulo coboundaries, converts the hypothesis directly
into that map being bijective.  No naturality statement about
`abHomologyIso` is needed, and Mathlib has none.

## What the two halves give

Bijectivity of that map is full faithfulness of `H⁰ F`: injectivity is
faithfulness, surjectivity is fullness.  With the essential surjectivity that
`IsQuasiEquivalence` already carries, `Functor.IsEquivalence` follows, since
that class is exactly the three conditions.

## What this does not say

Nothing about the converse, and nothing about dg functors that are only
quasi-equivalences up to homotopy.  It also says nothing about triangulated
structure: the equivalence produced here is an equivalence of ordinary
categories, and exactness of `H⁰ F` is a separate capability
(`DGFunctor.PreservesShifts` and `PreservesChosenCones`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]

/-- The degree-zero short complex of a Hom complex: `Hom⁻¹ ⟶ Hom⁰ ⟶ Hom¹`. -/
abbrev homSc (X Y : C) : ShortComplex AddCommGrpCat.{v} :=
  (dgHom X Y).sc' (-1) 0 1

/-- The cocycles of `H⁰` are the kernel appearing in `abLeftHomologyData`, and
the coboundaries are the range of `abToCycles`.  The first is definitional; this
is the second. -/
lemma range_abToCycles (X Y : C) :
    AddMonoidHom.range (homSc X Y).abToCycles = H0.coboundariesIn X Y := by
  ext ⟨z, hz⟩
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩

namespace DGFunctor

/-- The map of degree-zero short complexes a dg functor induces. -/
def mapHomSc (F : DGFunctor C D) (X Y : C) :
    homSc X Y ⟶ homSc (F.obj X) (F.obj Y) :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{v} (ComplexShape.up ℤ)
    (-1) 0 1).map (F.mapComplex X Y)

/-- The action of `F` on degree-zero cocycles. -/
def mapCocycles (F : DGFunctor C D) (X Y : C) :
    cocycles X Y →+ cocycles (F.obj X) (F.obj Y) :=
  ((F.map 0).comp (cocycles X Y).subtype).codRestrict _
    (fun z => F.map_mem_cocycles z.2)

/-- The action of `F` on `H⁰` Hom-groups, as a map of quotients. -/
def mapH0Hom (F : DGFunctor C D) (X Y : C) :
    (cocycles X Y ⧸ H0.coboundariesIn X Y) →+
      (cocycles (F.obj X) (F.obj Y) ⧸ H0.coboundariesIn (F.obj X) (F.obj Y)) :=
  QuotientAddGroup.map _ _ (F.mapCocycles X Y) (by
    -- Membership in `coboundariesIn` and in the `comap` are both definitionally
    -- the existence of a primitive, so both destructure without unfolding.
    intro x hx
    obtain ⟨w, hw⟩ := hx
    exact ⟨F.map (-1) w, by rw [← F.map_d (-1) 0 w, hw]; rfl⟩)

/-- **The left homology map datum whose `φH` is the map on `H⁰` Hom-groups.**

`abLeftHomologyData` presents the homology of each short complex as cocycles
modulo coboundaries, and this datum's `φH` is exactly what `F` does there.
`LeftHomologyMapData.quasiIso_iff` then converts the quasi-isomorphism
hypothesis into bijectivity of that map. -/
noncomputable def mapHomScData (F : DGFunctor C D) (X Y : C) :
    ShortComplex.LeftHomologyMapData (F.mapHomSc X Y)
      (homSc X Y).abLeftHomologyData
      (homSc (F.obj X) (F.obj Y)).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (F.mapCocycles X Y)
  φH := AddCommGrpCat.ofHom
    (QuotientAddGroup.map _ _ (F.mapCocycles X Y) (by
      rw [range_abToCycles, range_abToCycles]
      intro x hx
      obtain ⟨w, hw⟩ := hx
      exact ⟨F.map (-1) w, by rw [← F.map_d (-1) 0 w, hw]; rfl⟩))
  commi := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl
  commf' := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro w
    exact Subtype.ext (F.map_d (-1) 0 w)
  commπ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl


/-- `H⁰ F` acts on Hom-groups by `mapH0Hom`: both are the quotient map induced
by `F.map 0`. -/
lemma h0_map_eq_mapH0Hom (F : DGFunctor C D) (X Y : H0 C) :
    (F.h0.map (X := X) (Y := Y)) = F.mapH0Hom (H0.of C X) (H0.of C Y) := by
  funext f
  induction f using Quotient.ind with
  | _ f => rfl

/-- The comparison between the two quotients: `abLeftHomologyData` divides by
the range of `abToCycles`, and `H⁰` divides by the coboundaries. -/
noncomputable def homologyQuotientEquiv (X Y : C) :
    ((homSc X Y).abLeftHomologyData.H : Type v) ≃+
      (cocycles X Y ⧸ H0.coboundariesIn X Y) :=
  QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles X Y)

lemma mapH0Hom_comp_homologyQuotientEquiv (F : DGFunctor C D) (X Y : C)
    (z : (homSc X Y).abLeftHomologyData.H) :
    homologyQuotientEquiv (F.obj X) (F.obj Y) ((F.mapHomScData X Y).φH.hom z) =
      F.mapH0Hom X Y (homologyQuotientEquiv X Y z) := by
  induction z using QuotientAddGroup.induction_on with
  | _ z => rfl

/-- **The quasi-isomorphism hypothesis, read on `H⁰` Hom-groups.**

`LeftHomologyMapData.quasiIso_iff` turns the hypothesis into `IsIso` of the
datum's `φH`, `isIso_iff_bijective` turns that into bijectivity, and the
comparison above carries it to the map `H⁰ F` induces. -/
theorem bijective_mapH0Hom (F : DGFunctor C D) (hF : F.IsQuasiEquivalence)
    (X Y : C) : Function.Bijective (F.mapH0Hom X Y) := by
  have hq : QuasiIsoAt (F.mapComplex X Y) 0 := (hF.quasiIso X Y).quasiIsoAt 0
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)] at hq
  have hiso : IsIso (F.mapHomScData X Y).φH :=
    (ShortComplex.LeftHomologyMapData.quasiIso_iff (F.mapHomScData X Y)).1 hq
  have hbij : Function.Bijective (F.mapHomScData X Y).φH.hom :=
    ConcreteCategory.bijective_of_isIso (F.mapHomScData X Y).φH
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := (homologyQuotientEquiv X Y).surjective a
    obtain ⟨b, rfl⟩ := (homologyQuotientEquiv X Y).surjective b
    rw [← mapH0Hom_comp_homologyQuotientEquiv, ←
      mapH0Hom_comp_homologyQuotientEquiv] at hab
    exact congrArg _ (hbij.injective
      ((homologyQuotientEquiv (F.obj X) (F.obj Y)).injective hab))
  · intro c
    obtain ⟨c, rfl⟩ := (homologyQuotientEquiv (F.obj X) (F.obj Y)).surjective c
    obtain ⟨z, hz⟩ := hbij.surjective c
    exact ⟨homologyQuotientEquiv X Y z, by
      rw [← mapH0Hom_comp_homologyQuotientEquiv, hz]⟩

/-- `H⁰` of a quasi-equivalence is faithful. -/
theorem faithful_h0 (F : DGFunctor C D) (hF : F.IsQuasiEquivalence) :
    F.h0.Faithful where
  map_injective {X Y} := by
    rw [h0_map_eq_mapH0Hom]
    exact (F.bijective_mapH0Hom hF _ _).injective

/-- `H⁰` of a quasi-equivalence is full. -/
theorem full_h0 (F : DGFunctor C D) (hF : F.IsQuasiEquivalence) : F.h0.Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := (F.bijective_mapH0Hom hF (H0.of C X) (H0.of C Y)).surjective g
    exact ⟨f, by rw [h0_map_eq_mapH0Hom]; exact hf⟩

/-- **A quasi-equivalence induces an equivalence on `H⁰`.**

This is `dg-enhancements-e10`.  Faithfulness and fullness come from the
Hom-complex quasi-isomorphisms; essential surjectivity is the other field of
`IsQuasiEquivalence`. -/
theorem isEquivalence_h0 (F : DGFunctor C D) (hF : F.IsQuasiEquivalence) :
    F.h0.IsEquivalence where
  faithful := F.faithful_h0 hF
  full := F.full_h0 hF
  essSurj := hF.essSurj

/-- The equivalence `H⁰ C ≌ H⁰ D` a quasi-equivalence induces. -/
noncomputable def h0Equivalence (F : DGFunctor C D) (hF : F.IsQuasiEquivalence) :
    H0 C ≌ H0 D :=
  have := F.isEquivalence_h0 hF
  F.h0.asEquivalence

end DGFunctor

end CategoryTheory
