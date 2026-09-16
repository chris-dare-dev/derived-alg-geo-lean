/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.Abelian
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.Enriques
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.K3

/-!
# Comparisons between rank-one numerical surface models

The individual K3, abelian, and Enriques models depend only on their shared
rank-one foundation.  This downstream module owns declarations that mention
more than one model.
-/

namespace AlgebraicGeometry.Numerical.Examples

/-- Two numerical presentations on the same carriers coexist as ordinary data. -/
noncomputable def k3AndAbelianPresentations (d : ℕ) :
    NumericalVarietyData 2 SurfaceRing SurfaceNum ×
      NumericalVarietyData 2 SurfaceRing SurfaceNum :=
  (k3NumericalVariety d, abelianNumericalVariety d)

/-- Three numerical presentations on the same carriers coexist as ordinary data. -/
noncomputable def k3EnriquesAbelianPresentations (d : ℕ) :
    NumericalVarietyData 2 SurfaceRing SurfaceNum ×
      NumericalVarietyData 2 SurfaceRing SurfaceNum ×
        NumericalVarietyData 2 SurfaceRing SurfaceNum :=
  (k3NumericalVariety d, enriquesNumericalVariety d, abelianNumericalVariety d)

theorem chiStructureSheaf_enriques_ne_k3 (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (enriquesNumericalVariety d) ≠
      Surface.chiStructureSheaf (k3NumericalVariety d) := by
  rw [enriquesChiStructureSheaf d hd, k3ChiStructureSheaf d hd]
  norm_num

theorem chiStructureSheaf_enriques_ne_abelian (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (enriquesNumericalVariety d) ≠
      Surface.chiStructureSheaf (abelianNumericalVariety d) := by
  rw [enriquesChiStructureSheaf d hd, abelianChiStructureSheaf d]
  norm_num

theorem chiStructureSheaf_k3_ne_abelian (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (k3NumericalVariety d) ≠
      Surface.chiStructureSheaf (abelianNumericalVariety d) := by
  rw [k3ChiStructureSheaf d hd, abelianChiStructureSheaf d]
  norm_num

end AlgebraicGeometry.Numerical.Examples
