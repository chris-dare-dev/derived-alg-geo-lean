/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.BoundedAboveProjective

/-!
# Isomorphisms and units on the bounded-above projective locus

Natural isomorphisms between additive functors preserving projectives induce
isomorphisms of their supported derived functors.  In particular, the
identity functor acts as the identity on the bounded-above projective locus.
-/

namespace CategoryTheory

noncomputable section

universe v v' u u'

attribute [local instance] HasDerivedCategory.standard

/-- A natural isomorphism between additive functors preserving projectives
induces one on their bounded-above projective homotopy loci. -/
def mapBoundedAboveProjectiveHomotopyIso
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F G : C ⥤ D)
    [F.Additive] [G.Additive]
    [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects]
    (e : F ≅ G) :
    mapBoundedAboveProjectiveHomotopy F ≅
      mapBoundedAboveProjectiveHomotopy G := by
  let e' : F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) := {
    hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
    inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  refine NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk (boundedAboveProjectiveHomotopy D)
      (X := (mapBoundedAboveProjectiveHomotopy F).obj K)
      (Y := (mapBoundedAboveProjectiveHomotopy G).obj K)
      (e'.app K.obj)) ?_
  intro K L f
  apply ObjectProperty.hom_ext
  exact e'.hom.naturality f.hom

/-- Mapping homotopy complexes by the identity functor is the identity on
the bounded-above projective homotopy locus. -/
def mapBoundedAboveProjectiveHomotopyIdIso
    (C : Type u) [Category.{v} C] [Abelian C] :
    mapBoundedAboveProjectiveHomotopy (𝟭 C) ≅
      𝟭 (BoundedAboveProjectiveHomotopyCategory C) := by
  let e : (𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory C (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      ((𝟭 C).mapHomotopyCategoryFactors (ComplexShape.up ℤ) ≪≫
        Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ))
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ≪≫
        Functor.leftUnitor
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ≪≫
        (Functor.rightUnitor
          (HomotopyCategory.quotient C (ComplexShape.up ℤ))).symm)
  refine NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk (boundedAboveProjectiveHomotopy C)
      (X := (mapBoundedAboveProjectiveHomotopy (𝟭 C)).obj K)
      (Y := (𝟭 (BoundedAboveProjectiveHomotopyCategory C)).obj K)
      (e.app K.obj)) ?_
  intro K L f
  apply ObjectProperty.hom_ext
  exact e.hom.naturality f.hom

/-- Naturally isomorphic additive functors induce naturally isomorphic
supported derived functors. -/
def boundedAboveProjectiveDerivedFunctorIso
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F G : C ⥤ D)
    [F.Additive] [G.Additive]
    [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects]
    (e : F ≅ G) :
    boundedAboveProjectiveDerivedFunctor F ≅
      boundedAboveProjectiveDerivedFunctor G :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      (boundedAboveProjectiveQhEquivalence C).inverse
      (mapBoundedAboveProjectiveHomotopyIso F G e))
    (boundedAboveProjectiveQhEquivalence D).functor

/-- The supported derived functor of the identity is naturally isomorphic
to the identity functor on the supported derived locus. -/
def boundedAboveProjectiveDerivedFunctorIdIso
    (C : Type u) [Category.{v} C] [Abelian C] :
    boundedAboveProjectiveDerivedFunctor (𝟭 C) ≅
      𝟭 (BoundedAboveProjectiveDerivedCategory C) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (boundedAboveProjectiveQhEquivalence C).inverse
        (mapBoundedAboveProjectiveHomotopyIdIso C))
      (boundedAboveProjectiveQhEquivalence C).functor ≪≫
    Functor.isoWhiskerRight
      (Functor.rightUnitor
        (boundedAboveProjectiveQhEquivalence C).inverse)
      (boundedAboveProjectiveQhEquivalence C).functor ≪≫
    (boundedAboveProjectiveQhEquivalence C).counitIso

end

end CategoryTheory
