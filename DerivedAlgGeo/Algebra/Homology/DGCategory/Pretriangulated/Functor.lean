/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift

/-!
# Preservation of pretriangulated dg structure

An arbitrary dg functor need not preserve the representability witnesses that
define shifts in a pretriangulated dg category. `DGFunctor.PreservesShifts`
records that capability entirely at the dg level.  Transport of this data to
the ordinary shift functors on `H⁰` belongs to the dg-enhancement layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u''

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} {E : Type u''}
  [DGCategory.{v} C] [DGCategory.{v} D] [DGCategory.{v} E]

/-- A dg functor preserves shifts when it sends every dg shift witness to a
shift witness on the image objects, with the defining homogeneous element
given by the dg functor's map.

No pretriangulated instance is required to state the capability: callers may
provide individual witnesses, while `H⁰` adapters add existence assumptions
only when they choose shifts for every object. -/
structure PreservesShifts (F : DGFunctor C D) where
  /-- The target shift witness associated to a source shift witness. -/
  mapShift {X Y : C} {n : ℤ} (s : IsShiftBy X n Y) :
    IsShiftBy (F.obj X) n (F.obj Y)
  /-- The associated shift element is the image of the source element. -/
  mapShift_hom {X Y : C} {n : ℤ} (s : IsShiftBy X n Y) :
    (mapShift s).hom = F.map (-n) s.hom

namespace PreservesShifts

/-- The identity dg functor preserves shift witnesses. -/
def id (C : Type u) [DGCategory.{v} C] : PreservesShifts (DGFunctor.id C) where
  mapShift s := s
  mapShift_hom _ := rfl

/-- Shift preservation is closed under composition of dg functors. -/
def comp {F : DGFunctor C D} {G : DGFunctor D E}
    (hF : PreservesShifts F) (hG : PreservesShifts G) :
    PreservesShifts (F.comp G) where
  mapShift s := hG.mapShift (hF.mapShift s)
  mapShift_hom s := by
    rw [hG.mapShift_hom, hF.mapShift_hom]
    rfl

end PreservesShifts

/-- Apply a dg functor to a chosen homotopy-commutative square.  The homotopy
itself is mapped, so this construction retains the witness needed by later
cone maps rather than merely proving that the image square commutes in `H⁰`. -/
def mapHomotopySquare (F : DGFunctor C D)
    {X₁ Y₁ X₂ Y₂ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {a : (dgHom X₁ X₂).X 0} {b : (dgHom Y₁ Y₂).X 0}
    (s : DGCategory.HomotopySquare f₁ f₂ a b) :
    DGCategory.HomotopySquare
      (F.map 0 f₁) (F.map 0 f₂) (F.map 0 a) (F.map 0 b) where
  a_closed := by
    rw [← F.map_d 0 1 a, s.a_closed, map_zero]
  b_closed := by
    rw [← F.map_d 0 1 b, s.b_closed, map_zero]
  homotopy := F.map (-1) s.homotopy
  homotopy_boundary := by
    rw [← F.map_d (-1) 0 s.homotopy, s.homotopy_boundary, map_sub,
      F.map_comp, F.map_comp]

/-- Strong dg-level preservation of cone witnesses.

For every supplied cone witness, the image object is equipped with a cone
witness whose two inclusions are exactly the images of the source inclusions.
This chosen, composable capability is intentionally stronger than the later
`H⁰` proposition that an image triangle is merely isomorphic to some cone
triangle. -/
structure PreservesChosenCones (F : DGFunctor C D) where
  /-- The target cone witness carried by the image object. -/
  mapCone {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    IsConeOf (F.map 0 f) (F.obj Z)
  /-- The target cone inclusion is the image of the source cone inclusion. -/
  mapCone_inr {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (mapCone hc).inr = F.map 0 hc.inr
  /-- The shifted source inclusion is the image of the source cone inclusion. -/
  mapCone_inl {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (mapCone hc).inl = F.map (-1) hc.inl

namespace PreservesChosenCones

variable {F : DGFunctor C D}

/-- The identity dg functor preserves chosen cone witnesses. -/
def id (C : Type u) [DGCategory.{v} C] :
    PreservesChosenCones (DGFunctor.id C) where
  mapCone hc := hc
  mapCone_inr _ := rfl
  mapCone_inl _ := rfl

/-- Strong cone preservation is closed under composition of dg functors. -/
def comp {F : DGFunctor C D} {G : DGFunctor D E}
    (hF : PreservesChosenCones F) (hG : PreservesChosenCones G) :
    PreservesChosenCones (F.comp G) where
  mapCone hc := hG.mapCone (hF.mapCone hc)
  mapCone_inr hc := by
    rw [hG.mapCone_inr, hF.mapCone_inr]
    rfl
  mapCone_inl hc := by
    rw [hG.mapCone_inl, hF.mapCone_inl]
    rfl

/-- The projection from an image cone to its source is the image of the source
cone projection.  This is forced by uniqueness of the cone splitting; it is
not an additional field of `PreservesChosenCones`. -/
lemma mapCone_fst (hF : PreservesChosenCones F)
    {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (hF.mapCone hc).fst = F.map 1 hc.fst := by
  symm
  refine ((hF.mapCone hc).splitId_unique
    (a := F.map 1 hc.fst) (b := F.map 0 hc.snd) ?_).1
  rw [hF.mapCone_inl, hF.mapCone_inr,
    ← F.map_comp, ← F.map_comp, ← map_add,
    hc.fst_inl_add_snd_inr, F.map_id]

/-- The projection from an image cone to its target is the image of the source
cone projection, again derived from uniqueness of the cone splitting. -/
lemma mapCone_snd (hF : PreservesChosenCones F)
    {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (hF.mapCone hc).snd = F.map 0 hc.snd := by
  symm
  refine ((hF.mapCone hc).splitId_unique
    (a := F.map 1 hc.fst) (b := F.map 0 hc.snd) ?_).2
  rw [hF.mapCone_inl, hF.mapCone_inr,
    ← F.map_comp, ← F.map_comp, ← map_add,
    hc.fst_inl_add_snd_inr, F.map_id]

/-- A cone-preserving, shift-preserving dg functor carries the connecting map
of a supplied cone to the connecting map built from the corresponding image
witnesses. -/
lemma mapCone_toShift (hCone : PreservesChosenCones F)
    (hShift : PreservesShifts F)
    {X Y Z X' : C} {f : (dgHom X Y).X 0}
    (hc : IsConeOf f Z) (s : IsShiftBy X 1 X') :
    F.map 0 (hc.toShift s) =
      (hCone.mapCone hc).toShift (hShift.mapShift s) := by
  rw [IsConeOf.toShift, IsConeOf.toShift, F.map_comp,
    hCone.mapCone_fst, hShift.mapShift_hom]

end PreservesChosenCones

variable {F : DGFunctor C D}

/-- The inverse of the image shift witness is forced by the image of the
source inverse. This removes the `Classical.choice` hidden in `IsShiftBy.inv`
from every later transport calculation. -/
lemma mapShift_inv_eq (hF : PreservesShifts F) {X Y : C} {n : ℤ}
    (s : IsShiftBy X n Y) :
    (hF.mapShift s).inv = F.map n s.inv := by
  symm
  apply IsShiftBy.inv_unique (hF.mapShift s)
  rw [hF.mapShift_hom]
  rw [← F.map_comp, s.inv_hom, F.map_id]

/-- `F` commutes with the dg action on morphisms induced by a shift witness. -/
lemma map_mapShift (hF : PreservesShifts F) {X X' Y Y' : C} {n : ℤ}
    (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (f : (dgHom X X').X 0) :
    F.map 0 (IsShiftBy.mapShift s s' f) =
      IsShiftBy.mapShift (hF.mapShift s) (hF.mapShift s') (F.map 0 f) := by
  rw [IsShiftBy.mapShift, IsShiftBy.mapShift, F.map_comp, F.map_comp,
    mapShift_inv_eq hF s, hF.mapShift_hom]

/-- `F` commutes with comparisons between two shifts of the same object. -/
lemma map_compare (hF : PreservesShifts F) {X Y Y' : C} {n : ℤ}
    (s : IsShiftBy X n Y) (t : IsShiftBy X n Y') :
    F.map 0 (IsShiftBy.compare s t) =
      IsShiftBy.compare (hF.mapShift s) (hF.mapShift t) := by
  rw [IsShiftBy.compare_eq_mapShift, map_mapShift hF, F.map_id,
    IsShiftBy.compare_eq_mapShift]

end DGFunctor

end CategoryTheory
