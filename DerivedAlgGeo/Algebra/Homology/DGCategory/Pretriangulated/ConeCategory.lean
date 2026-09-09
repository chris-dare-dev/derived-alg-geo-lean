/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift

/-!
# The category of chosen dg cones

A cone in a dg category is useful functorially only when morphisms retain the
degree-minus-one homotopy witnessing commutativity of the underlying square.
`DGCategory.ConePresentation` bundles a closed dg arrow with a chosen cone,
and its morphisms are the homotopy squares and closed cone maps constructed in
`Pretriangulated.Lift`.

The resulting category is the reusable dg-level owner of functorial cones.
Its composition uses the explicit composite homotopy and cone map; the
pretriangulated instance is used only to choose the intermediate shift needed
to certify the connecting square.  Passage to ordinary distinguished
triangles belongs to the `DGEnhancement/H0` layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct

namespace DGCategory

variable (C : Type u) [DGCategory.{v} C]

/-- A closed degree-zero dg arrow together with a chosen cone object and cone
witness. -/
structure ConePresentation where
  /-- Source of the presented arrow. -/
  source : C
  /-- Target of the presented arrow. -/
  target : C
  /-- The closed arrow whose cone is presented. -/
  arrow : cocycles source target
  /-- The chosen cone object. -/
  cone : C
  /-- The chosen representability witness for the cone. -/
  isCone : IsConeOf arrow.1 cone

namespace ConePresentation

variable {C}

/-- A morphism of chosen cone presentations.  The maps on source and target
are dg morphisms, and `coneMorphism` retains both the chosen homotopy and the
closed map on cones. -/
structure Hom (A B : ConePresentation C) where
  /-- Map between source objects. -/
  source : (dgHom A.source B.source).X 0
  /-- Map between target objects. -/
  target : (dgHom A.target B.target).X 0
  /-- The homotopy-coherent induced map between the chosen cones. -/
  coneMorphism : IsConeOf.Morphism A.isCone B.isCone source target

namespace Hom

variable {A B D : ConePresentation C}

/-- A morphism of cone presentations is determined by its two boundary maps,
chosen homotopy, and map on cones. -/
@[ext]
lemma ext {m n : Hom A B}
    (hsource : m.source = n.source)
    (htarget : m.target = n.target)
    (hhomotopy : m.coneMorphism.homotopy = n.coneMorphism.homotopy)
    (hcone : m.coneMorphism.hom.1 = n.coneMorphism.hom.1) :
    m = n := by
  cases m with
  | mk ms mt mm =>
    cases n with
    | mk ns nt nm =>
      dsimp at hsource htarget hhomotopy hcone
      cases hsource
      cases htarget
      congr 1
      apply IsConeOf.Morphism.ext
      · apply HomotopySquare.ext
        exact hhomotopy
      · exact Subtype.ext hcone

/-- Identity morphism of a chosen cone presentation. -/
def id (A : ConePresentation C) : Hom A A where
  source := dgId A.source
  target := dgId A.target
  coneMorphism := IsConeOf.Morphism.id A.isCone

/-- Composition of morphisms of chosen cone presentations. -/
noncomputable def comp [IsPretriangulated C]
    (m : Hom A B) (n : Hom B D) : Hom A D where
  source := dgComp 0 0 0 (by omega) m.source n.source
  target := dgComp 0 0 0 (by omega) m.target n.target
  coneMorphism := IsConeOf.Morphism.comp
    (hc₁ := A.isCone) (hc₂ := B.isCone) (hc₃ := D.isCone)
    m.coneMorphism n.coneMorphism

end Hom

/-- Chosen dg cones and their homotopy-coherent cone morphisms form a
category. -/
noncomputable instance [IsPretriangulated C] : Category.{v} (ConePresentation C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro A B m
    apply Hom.ext
    · exact dgId_comp 0 m.source
    · exact dgId_comp 0 m.target
    · dsimp only [Hom.comp, IsConeOf.Morphism.comp,
        IsConeOf.Morphism.compAt, Hom.id, IsConeOf.Morphism.id,
        IsConeOf.Morphism.homotopy, HomotopySquare.comp,
        HomotopySquare.id]
      change dgComp (-1) 0 (-1) (by omega) 0 m.target +
          dgComp 0 (-1) (-1) (by omega) (dgId A.source)
            m.coneMorphism.homotopy = m.coneMorphism.homotopy
      simp only [map_zero, AddMonoidHom.zero_apply, zero_add, dgId_comp]
    · dsimp only [Hom.comp, IsConeOf.Morphism.comp,
        IsConeOf.Morphism.compAt, Hom.id, IsConeOf.Morphism.id]
      exact dgId_comp 0 m.coneMorphism.hom.1
  comp_id := by
    intro A B m
    apply Hom.ext
    · exact dgComp_id 0 m.source
    · exact dgComp_id 0 m.target
    · dsimp only [Hom.comp, IsConeOf.Morphism.comp,
        IsConeOf.Morphism.compAt, Hom.id, IsConeOf.Morphism.id,
        IsConeOf.Morphism.homotopy, HomotopySquare.comp,
        HomotopySquare.id]
      change dgComp (-1) 0 (-1) (by omega)
          m.coneMorphism.homotopy (dgId B.target) +
          dgComp 0 (-1) (-1) (by omega) m.source 0 =
            m.coneMorphism.homotopy
      simp only [dgComp_id, map_zero, add_zero]
    · dsimp only [Hom.comp, IsConeOf.Morphism.comp,
        IsConeOf.Morphism.compAt, Hom.id, IsConeOf.Morphism.id]
      exact dgComp_id 0 m.coneMorphism.hom.1
  assoc := by
    intro A B D E m n p
    apply Hom.ext
    · exact dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
        m.source n.source p.source
    · exact dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
        m.target n.target p.target
    · dsimp only [Hom.comp, IsConeOf.Morphism.comp,
        IsConeOf.Morphism.compAt, IsConeOf.Morphism.homotopy,
        HomotopySquare.comp]
      change
        dgComp (-1) 0 (-1) (by omega)
            (dgComp (-1) 0 (-1) (by omega)
                m.coneMorphism.homotopy n.target +
              dgComp 0 (-1) (-1) (by omega) m.source
                n.coneMorphism.homotopy) p.target +
          dgComp 0 (-1) (-1) (by omega)
            (dgComp 0 0 0 (by omega) m.source n.source)
              p.coneMorphism.homotopy =
        dgComp (-1) 0 (-1) (by omega) m.coneMorphism.homotopy
            (dgComp 0 0 0 (by omega) n.target p.target) +
          dgComp 0 (-1) (-1) (by omega) m.source
            (dgComp (-1) 0 (-1) (by omega)
                n.coneMorphism.homotopy p.target +
              dgComp 0 (-1) (-1) (by omega) n.source
                p.coneMorphism.homotopy)
      simp only [map_add, AddMonoidHom.add_apply]
      rw [
        dgComp_assoc (-1) 0 0 (-1) 0 (-1) (by omega) (by omega) (by omega),
        dgComp_assoc 0 (-1) 0 (-1) (-1) (-1) (by omega) (by omega) (by omega),
        dgComp_assoc 0 0 (-1) 0 (-1) (-1) (by omega) (by omega) (by omega)]
      abel
    · dsimp only [Hom.comp, IsConeOf.Morphism.comp,
        IsConeOf.Morphism.compAt]
      exact dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
        m.coneMorphism.hom.1 n.coneMorphism.hom.1 p.coneMorphism.hom.1

@[simp]
lemma id_source [IsPretriangulated C] (A : ConePresentation C) :
    (CategoryStruct.id A : Hom A A).source = dgId A.source := rfl

@[simp]
lemma id_target [IsPretriangulated C] (A : ConePresentation C) :
    (CategoryStruct.id A : Hom A A).target = dgId A.target := rfl

@[simp]
lemma comp_source [IsPretriangulated C]
    {A B D : ConePresentation C} (m : A ⟶ B) (n : B ⟶ D) :
    (m ≫ n).source = dgComp 0 0 0 (by omega) m.source n.source := rfl

@[simp]
lemma comp_target [IsPretriangulated C]
    {A B D : ConePresentation C} (m : A ⟶ B) (n : B ⟶ D) :
    (m ≫ n).target = dgComp 0 0 0 (by omega) m.target n.target := rfl

end ConePresentation

end DGCategory

end CategoryTheory
