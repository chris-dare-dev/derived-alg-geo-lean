/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.AssociatedSheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The graded ring as its associated module sheaf

This file identifies the sheaf associated to the graded ring, considered as a graded module over
itself, with the structure sheaf of `Proj`.  It is the concrete degree-zero base case for the Proj
module comparison: the equivalence is defined on every open by applying the canonical equivalence
between the two degree-zero localizations pointwise, and the local-fraction predicates are checked
in both directions.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace
open scoped DirectSum Pointwise

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- The fiber comparison underlying the structure-module isomorphism. -/
noncomputable def selfFiberLinearEquiv (x : X) :
    Fiber 𝒜 𝒜 x ≃ₗ[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
      HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl :=
  (DegreeZeroLocalization.selfLinearEquiv 𝒜
    x.asHomogeneousIdeal.toIdeal.primeCompl).symm

@[simp]
theorem selfFiberLinearEquiv_apply_mk (x : X)
    (c : NumDenSameDeg 𝒜 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    selfFiberLinearEquiv 𝒜 x (DegreeZeroLocalization.mk c) =
      HomogeneousLocalization.mk
        { deg := c.deg
          num := c.num
          den := c.den
          den_mem := c.den_mem } :=
  DegreeZeroLocalization.selfLinearEquiv_symm_apply_mk 𝒜
    x.asHomogeneousIdeal.toIdeal.primeCompl c

@[simp]
theorem selfFiberLinearEquiv_symm_apply_mk (x : X)
    (c : HomogeneousLocalization.NumDenSameDeg 𝒜
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (selfFiberLinearEquiv 𝒜 x).symm (HomogeneousLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := c.num
          den := c.den
          den_mem := c.den_mem } :=
  DegreeZeroLocalization.selfLinearEquiv_apply_mk 𝒜
    x.asHomogeneousIdeal.toIdeal.primeCompl c

/-- Send a locally homogeneous module fraction for the graded ring to the same fraction in
Mathlib's structure sheaf. -/
noncomputable def selfSectionToStructure {U : (Opens X)ᵒᵖ}
    (s : (associatedSheafInType 𝒜 𝒜).1.obj U) : 𝒪.1.obj U := by
  refine ⟨fun x => selfFiberLinearEquiv 𝒜 x.1 (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, d, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, d, r, t, ht, fun y => ?_⟩
  have hy := h y
  change s.1 (i y) = _ at hy
  change selfFiberLinearEquiv 𝒜 (i y).1 (s.1 (i y)) = _
  rw [hy]
  exact selfFiberLinearEquiv_apply_mk 𝒜 (i y).1 _

/-- Send a locally homogeneous structure-sheaf fraction to the same fraction in the associated
module sheaf of the graded ring. -/
noncomputable def selfSectionFromStructure {U : (Opens X)ᵒᵖ}
    (s : 𝒪.1.obj U) : (associatedSheafInType 𝒜 𝒜).1.obj U := by
  refine ⟨fun x => (selfFiberLinearEquiv 𝒜 x.1).symm (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, d, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, d, r, t, ht, fun y => ?_⟩
  have hy := h y
  change s.1 (i y) = _ at hy
  change (selfFiberLinearEquiv 𝒜 (i y).1).symm (s.1 (i y)) = _
  rw [hy]
  exact selfFiberLinearEquiv_symm_apply_mk 𝒜 (i y).1 _

/-- On every open, the locally fractional sections of the graded ring as a module are additively
equivalent to the sections of the structure sheaf. -/
noncomputable def selfSectionAddEquiv (U : (Opens X)ᵒᵖ) :
    (associatedSheafInType 𝒜 𝒜).1.obj U ≃+ 𝒪.1.obj U where
  toFun := selfSectionToStructure 𝒜
  invFun := selfSectionFromStructure 𝒜
  left_inv s := by
    apply section_ext
    funext x
    exact (selfFiberLinearEquiv 𝒜 x.1).symm_apply_apply (s.1 x)
  right_inv s := by
    apply Subtype.ext
    funext x
    exact (selfFiberLinearEquiv 𝒜 x.1).apply_symm_apply (s.1 x)
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact (selfFiberLinearEquiv 𝒜 x.1).map_add (s.1 x) (t.1 x)

/-- The openwise comparison is linear over the structure-sheaf sections. -/
noncomputable def selfSectionLinearEquiv (U : (Opens X)ᵒᵖ) :
    (associatedSheafInType 𝒜 𝒜).1.obj U ≃ₗ[𝒪.1.obj U] 𝒪.1.obj U :=
  { selfSectionAddEquiv 𝒜 U with
    map_smul' := fun r s => by
      apply Subtype.ext
      funext x
      exact (selfFiberLinearEquiv 𝒜 x.1).map_smul
        (AlgebraicGeometry.openToLocalization 𝒜 U.unop x.1 x.2 r) (s.1 x) }

/-- The openwise comparisons commute with restriction and hence identify the two presheaves of
modules. -/
noncomputable def associatedPresheafSelfIso :
    associatedPresheaf 𝒜 𝒜 ≅
      PresheafOfModules.unit
        ((𝒪.1 ⋙ forget₂ CommRingCat RingCat)) := by
  refine PresheafOfModules.isoMk
    (fun U => LinearEquiv.toModuleIso (selfSectionLinearEquiv 𝒜 U)) ?_
  intro U V i
  ext s
  rfl

/-- The sheaf associated to the graded ring, considered as a module over itself, is canonically
the structure sheaf of `Proj`. -/
noncomputable def associatedSheafSelfIso :
    associatedSheaf 𝒜 𝒜 ≅
      SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget
    (AlgebraicGeometry.Proj 𝒜).ringCatSheaf).preimageIso
      (associatedPresheafSelfIso 𝒜)

/-! ## The canonical basic-open comparison for the structure module -/

/-- On a positive-degree basic open, the comparison for the graded ring as a module is the
composite of the degree-zero localization comparison, Mathlib's structure-sheaf comparison, and
the inverse of `associatedSheafSelfIso`. -/
noncomputable def selfBasicOpenSectionAddEquiv {f : A} {m : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    DegreeZeroLocalization 𝒜 𝒜 (.powers f) ≃+
      (associatedSheafInType 𝒜 𝒜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  (DegreeZeroLocalization.selfLinearEquiv 𝒜 (.powers f)).symm.toAddEquiv |>.trans
    (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f f_deg hm).commRingCatIsoToRingEquiv.toAddEquiv
      |>.trans (selfSectionAddEquiv 𝒜 _).symm

/-- The additive equivalence above has the canonical value on every homogeneous fraction. -/
theorem selfBasicOpenSectionAddEquiv_apply_mk {f : A} {m : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (c : NumDenSameDeg 𝒜 𝒜 (.powers f)) :
    selfBasicOpenSectionAddEquiv 𝒜 f_deg hm (DegreeZeroLocalization.mk c) =
      moduleAwayToSection 𝒜 𝒜 f (DegreeZeroLocalization.mk c) := by
  change selfSectionFromStructure 𝒜
    ((AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f f_deg hm).hom
      ((DegreeZeroLocalization.selfLinearEquiv 𝒜 (.powers f)).symm
        (DegreeZeroLocalization.mk c))) = _
  rw [DegreeZeroLocalization.selfLinearEquiv_symm_apply_mk]
  apply section_ext
  funext x
  rw [moduleAwayToSection_apply, DegreeZeroLocalization.mapOfLE_mk]
  apply DegreeZeroLocalization.ext
  change
    (((DegreeZeroLocalization.selfLinearEquiv 𝒜
        x.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (((AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f f_deg hm).hom
          (HomogeneousLocalization.mk
            { deg := c.deg
              num := c.num
              den := c.den
              den_mem := c.den_mem })).1 x) :
      DegreeZeroLocalization 𝒜 𝒜
        x.1.asHomogeneousIdeal.toIdeal.primeCompl) :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) = _
  rw [DegreeZeroLocalization.coe_selfLinearEquiv]
  rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom]
  erw [AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply]
  simp only [HomogeneousLocalization.val_mk, DegreeZeroLocalization.coe_mk,
    NumDenSameDeg.embedding]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  let Sx : Submonoid A := x.1.asHomogeneousIdeal.toIdeal.primeCompl
  let den : Sx :=
    ⟨(c.den : A), (Submonoid.powers_le.mpr x.2) c.den_mem⟩
  have h := (Localization.mk_eq_mk'_apply (M := Sx) (c.num : A) den).symm
  convert h using 1
  with_unfolding_all rfl

/-- For the graded ring as a module over itself, the canonical basic-open section map is
bijective on every positive-degree homogeneous chart. -/
theorem moduleAwayToSection_self_bijective {f : A} {m : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Bijective (moduleAwayToSection 𝒜 𝒜 f) := by
  rw [← moduleAwayToSection_unique 𝒜 𝒜 f
    (selfBasicOpenSectionAddEquiv 𝒜 f_deg hm).toAddMonoidHom
    (selfBasicOpenSectionAddEquiv_apply_mk 𝒜 f_deg hm)]
  exact (selfBasicOpenSectionAddEquiv 𝒜 f_deg hm).bijective

end AlgebraicGeometry.Proj
