/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.LeftResolution.Augmented

/-!
# Degree-zero homology of a left resolution

The augmented initial segment identifies degree-zero homology of the mapped
left-resolution chain complex with the resolved object. This is an objectwise
identification; it does not totalize a resolution bicomplex or supply a K-flat
replacement of an unbounded complex.
-/

open CategoryTheory Category Limits Preadditive ZeroObject

namespace CategoryTheory.Abelian.LeftResolution

variable {A C : Type*} [Category C] [Category A]
variable (ι : C ⥤ A) [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]
variable (Λ : LeftResolution ι) (X : A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero homology of the mapped left resolution is the original object.
The isomorphism descends the augmentation through the cokernel of the first
differential, using exactness and the epi augmentation. -/
noncomputable def homologyZeroIso :
    (((ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj (Λ.chainComplex X)).homology 0) ≅ X := by
  let K : ChainComplex A ℕ :=
    (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj (Λ.chainComplex X)
  let φ : K.X 0 ⟶ X := ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X
  have hφ : K.d 1 0 ≫ φ = 0 := by
    change (Λ.augmentedShortComplex ι X).f ≫
      (Λ.augmentedShortComplex ι X).g = 0
    exact (Λ.augmentedShortComplex ι X).zero
  haveI : Epi φ := Λ.augmentedShortComplex_epi_g ι X
  have hS : (ShortComplex.mk (K.d 1 0) φ hφ).Exact := by
    change (Λ.augmentedShortComplex ι X).Exact
    exact Λ.augmentedShortComplex_exact ι X
  let ψ := K.descOpcycles φ 1 (by simp) hφ
  haveI : IsIso ψ :=
    (ChainComplex.isIso_descOpcycles_iff K φ hφ).2 ⟨hS, inferInstance⟩
  exact K.isoHomologyι₀ ≪≫ asIso ψ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma homologyZeroIso_hom_eq :
    let K : ChainComplex A ℕ :=
      (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj (Λ.chainComplex X)
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ (Λ.homologyZeroIso ι X).hom =
      ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X := by
  dsimp [homologyZeroIso]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero homology identification commutes with maps between resolved objects. -/
lemma homologyZeroIso_naturality {Y : A} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap
        ((ι.mapHomologicalComplex (ComplexShape.down ℕ)).map (Λ.chainComplexMap f)) 0 ≫
      (Λ.homologyZeroIso ι Y).hom =
      (Λ.homologyZeroIso ι X).hom ≫ f := by
  let KX : ChainComplex A ℕ :=
    (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj (Λ.chainComplex X)
  let KY : ChainComplex A ℕ :=
    (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj (Λ.chainComplex Y)
  let α : KX ⟶ KY :=
    (ι.mapHomologicalComplex (ComplexShape.down ℕ)).map (Λ.chainComplexMap f)
  change HomologicalComplex.homologyMap α 0 ≫ (Λ.homologyZeroIso ι Y).hom =
    (Λ.homologyZeroIso ι X).hom ≫ f
  apply (cancel_epi (KX.pOpcycles 0 ≫ KX.isoHomologyι₀.inv)).1
  calc
    (KX.pOpcycles 0 ≫ KX.isoHomologyι₀.inv) ≫
        (HomologicalComplex.homologyMap α 0 ≫ (Λ.homologyZeroIso ι Y).hom) =
      α.f 0 ≫ (KY.pOpcycles 0 ≫ KY.isoHomologyι₀.inv ≫
        (Λ.homologyZeroIso ι Y).hom) := by
        simp only [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality_assoc,
          HomologicalComplex.p_opcyclesMap_assoc]
    _ = α.f 0 ≫ (ι.map (Λ.chainComplexXZeroIso Y).hom ≫ Λ.π.app Y) := by
      rw [homologyZeroIso_hom_eq]
    _ = (ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X) ≫ f := by
      dsimp [α]
      change ι.map ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫
        (Λ.chainComplexXZeroIso Y).inv) ≫
          ι.map (Λ.chainComplexXZeroIso Y).hom ≫ Λ.π.app Y =
        (ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X) ≫ f
      simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
        Λ.π_naturality X Y f]
    _ = (KX.pOpcycles 0 ≫ KX.isoHomologyι₀.inv) ≫
        ((Λ.homologyZeroIso ι X).hom ≫ f) := by
      dsimp [KX]
      rw [← homologyZeroIso_hom_eq ι Λ X]
      simp [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Functorially, degree-zero homology of the mapped left resolution is the identity. -/
noncomputable def homologyZeroNatIso :
    Λ.chainComplexFunctor ⋙ ι.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) 0 ≅ 𝟭 A :=
  NatIso.ofComponents (fun X => Λ.homologyZeroIso ι X) (by
    intro X Y f
    exact Λ.homologyZeroIso_naturality ι X f)

end CategoryTheory.Abelian.LeftResolution
