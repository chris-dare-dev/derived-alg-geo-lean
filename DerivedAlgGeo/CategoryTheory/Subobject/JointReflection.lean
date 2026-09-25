/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Joint reflection of subobject order

A family of pullback-preserving, mono-preserving functors that jointly reflects
isomorphisms also reflects order and equality between subobjects of a fixed
object. Local factorisations make the images of the global pullback projection
isomorphisms; joint reflection then gives the global factorisation.

The theorem compares existing subobjects. It does not construct a subobject
from local data or assert any gluing condition.
-/

open CategoryTheory.Limits

universe w v u v' u'

namespace CategoryTheory.Subobject

variable {I : Type w} {C : Type u} [Category.{v} C] [HasPullbacks C]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  (F : ∀ i, C ⥤ D i)
  [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
  [∀ i, (F i).PreservesMonomorphisms]

/-- A pullback-preserving family jointly reflecting isomorphisms reflects
subobject order. No finite-colimit or finite-cover hypothesis is needed. -/
theorem le_iff_mapFunctor_le_of_jointlyReflectsIsomorphisms
    (hF : JointlyReflectIsomorphisms F) {X : C} (P Q : Subobject X) :
    P ≤ Q ↔ ∀ i, mapFunctor (F i) P ≤ mapFunctor (F i) Q := by
  constructor
  · intro h i
    exact mapFunctor_monotone (F i) h
  · intro h
    have hlocal (i : I) : IsIso ((F i).map (pullback.fst P.arrow Q.arrow)) := by
      have hle : Subobject.mk ((F i).map P.arrow) ≤
          Subobject.mk ((F i).map Q.arrow) := by
        simpa only [mapFunctor_eq_mk_arrow] using h i
      let g := Subobject.ofMkLEMk ((F i).map P.arrow) ((F i).map Q.arrow) hle
      have hs : IsPullback (𝟙 _) g ((F i).map P.arrow) ((F i).map Q.arrow) :=
        IsPullback.of_horiz_isIso_mono ⟨by simp [g]⟩
      have hm := (IsPullback.of_hasPullback P.arrow Q.arrow).map (F i)
      let e := hm.isoIsPullback _ _ hs
      have he : e.hom = (F i).map (pullback.fst P.arrow Q.arrow) := by
        simpa only [Category.comp_id] using hm.isoIsPullback_hom_fst _ _ hs
      rw [← he]
      infer_instance
    letI : ∀ i, IsIso ((F i).map (pullback.fst P.arrow Q.arrow)) := hlocal
    haveI : IsIso (pullback.fst P.arrow Q.arrow) := hF.isIso _
    apply Subobject.le_of_comm
      (inv (pullback.fst P.arrow Q.arrow) ≫ pullback.snd P.arrow Q.arrow)
    rw [Category.assoc, IsIso.inv_comp_eq, pullback.condition]

/-- Equality of two existing subobjects is detected by the same family. -/
theorem eq_iff_mapFunctor_eq_of_jointlyReflectsIsomorphisms
    (hF : JointlyReflectIsomorphisms F) {X : C} (P Q : Subobject X) :
    P = Q ↔ ∀ i, mapFunctor (F i) P = mapFunctor (F i) Q := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply le_antisymm
    · exact (le_iff_mapFunctor_le_of_jointlyReflectsIsomorphisms F hF P Q).2
        (fun i => (h i).le)
    · exact (le_iff_mapFunctor_le_of_jointlyReflectsIsomorphisms F hF Q P).2
        (fun i => (h i).ge)

end CategoryTheory.Subobject
