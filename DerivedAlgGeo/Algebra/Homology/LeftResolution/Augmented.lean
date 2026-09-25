/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.LeftResolution.Basic

/-!
# The augmented initial segment of a left resolution

After applying `ι`, the functorial chain complex attached to a `LeftResolution`
is exact in positive degrees. This file also records exactness of its first two
terms after augmentation to the object being resolved. The result is objectwise;
it does not assert a totalization theorem or K-flatness for a bicomplex built
from such resolutions.
-/

open CategoryTheory Category Limits Preadditive ZeroObject

namespace CategoryTheory.Abelian.LeftResolution

variable {A C : Type*} [Category C] [Category A]
variable (ι : C ⥤ A) [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]
variable (Λ : LeftResolution ι) (X : A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The initial segment of `Λ.chainComplex X`, mapped to `A` and augmented by
the epimorphism `Λ.π.app X`. -/
noncomputable def augmentedShortComplex : ShortComplex A where
  f := ι.map ((Λ.chainComplex X).d 1 0)
  g := ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X
  zero := by
    rw [Λ.map_chainComplex_d_1_0]
    cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The first two terms of the mapped left resolution are exact after
augmentation. This is only exactness at the middle term; the epimorphicity of
the augmentation is recorded separately by
`augmentedShortComplex_epi_g`. -/
theorem augmentedShortComplex_exact : (Λ.augmentedShortComplex ι X).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  let S := Λ.augmentedShortComplex ι X
  change Epi (kernel.lift S.g S.f S.zero)
  let pi := Λ.π.app X
  let g := S.g
  let p := ι.map (Λ.chainComplexXZeroIso X).inv
  have hw : pi ≫ 𝟙 X = p ≫ g := by
    dsimp [p, g, S, augmentedShortComplex, pi]
    cat_disch
  let ψ := kernel.map pi g p (𝟙 X) hw
  have hLift : kernel.lift g S.f S.zero =
      ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel pi) ≫ ψ := by
    apply (cancel_mono (kernel.ι g)).1
    rw [kernel.lift_ι]
    change ι.map ((Λ.chainComplex X).d 1 0) = _
    rw [Λ.map_chainComplex_d_1_0]
    simp [ψ, kernel.map, p, g, S, augmentedShortComplex, pi, Category.assoc]
  change Epi (kernel.lift g S.f S.zero)
  rw [hLift]
  haveI : IsIso ψ := by
    dsimp [ψ]
    infer_instance
  haveI : Epi (ι.map (Λ.chainComplexXOneIso X).hom) := by infer_instance
  haveI : Epi (Λ.π.app (kernel pi)) := by infer_instance
  haveI : Epi (ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel pi)) :=
    epi_comp _ _
  exact epi_comp _ _

/-- The augmentation is epi because it composes the degree-zero identification
isomorphism with the epimorphism `Λ.π.app X`. Together with exactness at the
middle term, this records the right end of the augmented resolution. -/
theorem augmentedShortComplex_epi_g : Epi (Λ.augmentedShortComplex ι X).g := by
  change Epi (ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X)
  exact epi_comp' (by infer_instance) (Λ.epi_π_app X)

end CategoryTheory.Abelian.LeftResolution
