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

end CategoryTheory.Abelian.LeftResolution
