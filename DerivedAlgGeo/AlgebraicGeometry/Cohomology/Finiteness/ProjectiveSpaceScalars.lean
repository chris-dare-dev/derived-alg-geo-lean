/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.StructureSections
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.LinearCech
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentFinite

/-!
# The base field acting on sections of a twist

`FiniteDimensionalCohomology` asks for `Module.Finite k`, and the `k`-action it means is
`coherentScalarAction`: multiplication by the global function a scalar becomes under the
structure morphism. The Čech lane, by contrast, computes in graded localizations, where `k` acts
through the constants (`polynomialToHomogeneousLocalization`). Nothing so far says these are the
same action, and #666's finiteness statement is meaningless until they are.

This file closes that gap at the level of sections.

* `openToLocalization_baseFieldToGlobalSections` — the global function a scalar becomes has value
  `r / 1` at every point. This is `openToLocalization_toSpecZero_appTop` composed with the
  surjection `k → 𝒜 0`, since the structure morphism of `Pⁿ` is `Proj.toSpecZero` followed by the
  spectrum of that surjection.
* `varietyScalarAction_apply_fiber` — hence the action on sections of an associated sheaf is
  plain scalar multiplication in each fiber. The structure-sheaf action on those sections is
  pointwise by construction (`sectionsSubmodule`), so this is the previous lemma plus
  `globalSectionSmul_app` and nothing else.

## What is still missing

The comparison `intCechTermSectionAddEquiv` between a Čech term and these sections is five steps,
and none has been shown `k`-linear yet. Two of them are already `LinearEquiv`s over
`HomogeneousLocalization`, two are pointwise linear, and one is a `RingEquiv`; the content of this
file is what makes each of those statements true rather than merely plausible. Until that is done,
`module_finite_linearCoherentH_of_cech` cannot be fed and #666 is not closed.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k] [Finite ι] [Nonempty ι]
variable {σM : Type u} [SetLike σM (MvPolynomial ι k)]
  [AddSubgroupClass σM (MvPolynomial ι k)] (𝓜 : ℕ → σM)
  [SetLike.GradedSMul (polynomialGrading ι k) 𝓜]

/-- **The base field acts through the constants.** The global function a scalar becomes on
projective space has value `r / 1` at every point, which is exactly the map
`polynomialToHomogeneousLocalization` that the graded localizations are `k`-modules by.

This is `openToLocalization_toSpecZero_appTop` composed with the surjection `k → 𝒜 0`: the
structure morphism of `Pⁿ` is `Proj.toSpecZero` followed by the spectrum of that surjection. -/
theorem openToLocalization_baseFieldToGlobalSections (r : k)
    (x : ProjectiveSpectrum.top (polynomialGrading ι k)) :
    (openToLocalization (polynomialGrading ι k) ⊤ x trivial).hom
        (Cohomology.baseFieldToGlobalSections (projectiveSpaceVariety ι k) r) =
      polynomialToHomogeneousLocalization ι k _ r := by
  show (openToLocalization (polynomialGrading ι k) ⊤ x trivial).hom
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (projectiveSpaceToSpec ι k).appTop).hom r) = _
  rw [projectiveSpaceToSpec, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact openToLocalization_toSpecZero_appTop (polynomialGrading ι k)
    (algebraMap k ↥(polynomialGrading ι k 0) r) x

/-- **The base-field action on sections is scalar multiplication, fiber by fiber.**

`varietyScalarAction` is multiplication by the global function attached to the scalar, and the
structure-sheaf action on an associated sheaf is pointwise on fibers by construction. Combining
those with the previous lemma leaves plain scalar multiplication in each fiber — which is what
lets the Čech lane's `k`-action be compared against the one the finiteness interface consumes. -/
theorem varietyScalarAction_apply_fiber (r : k)
    (U : Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))
    (m : (associatedSheafInType (polynomialGrading ι k) 𝓜).1.obj (op U))
    (x : ProjectiveSpectrum.top (polynomialGrading ι k)) (hx : x ∈ U) :
    ((((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
        (associatedSheaf (polynomialGrading ι k) 𝓜) r).val.app (op U)).hom m) :
          (associatedSheafInType (polynomialGrading ι k) 𝓜).1.obj (op U)).1 ⟨x, hx⟩ =
      polynomialToHomogeneousLocalization ι k
          x.asHomogeneousIdeal.toIdeal.primeCompl r • (m.1 ⟨x, hx⟩) := by
  have h := Cohomology.globalSectionSmul_app (associatedSheaf (polynomialGrading ι k) 𝓜)
    (Cohomology.baseFieldToGlobalSections (projectiveSpaceVariety ι k) r) U m
  refine Eq.trans (congrArg
    (fun z : (associatedSheafInType (polynomialGrading ι k) 𝓜).1.obj (op U) => z.1 ⟨x, hx⟩) h) ?_
  have h2 : (openToLocalization (polynomialGrading ι k) U x hx).hom
      ((Proj (polynomialGrading ι k)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (Cohomology.baseFieldToGlobalSections (projectiveSpaceVariety ι k) r)) =
      polynomialToHomogeneousLocalization ι k x.asHomogeneousIdeal.toIdeal.primeCompl r := by
    rw [openToLocalization_presheaf_map, openToLocalization_baseFieldToGlobalSections]
  exact congrArg (fun c => c • (m.1 ⟨x, hx⟩)) h2

/-- The constant `r` restricted to any open, at the type the sections module wants. -/
noncomputable def constSectionOn (U : Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))
    (r : k) :
    (ProjectiveSpectrum.Proj.structureSheaf (polynomialGrading ι k)).1.obj (op U) :=
  (Proj (polynomialGrading ι k)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (Cohomology.baseFieldToGlobalSections (projectiveSpaceVariety ι k) r)

/-- The restriction of the constant `r` to a chart, at the type the sections module wants. -/
noncomputable def constSection (f : MvPolynomial ι k) (r : k) :
    (ProjectiveSpectrum.Proj.structureSheaf (polynomialGrading ι k)).1.obj
      (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k) f)) :=
  (Proj (polynomialGrading ι k)).presheaf.map
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen (polynomialGrading ι k) f ≤ ⊤)).op
    (Cohomology.baseFieldToGlobalSections (projectiveSpaceVariety ι k) r)

/-- It agrees with the chart-level `constSection`. -/
theorem constSectionOn_basicOpen (f : MvPolynomial ι k) (r : k) :
    constSectionOn ι k (ProjectiveSpectrum.basicOpen (polynomialGrading ι k) f) r =
      constSection ι k f r := rfl

/-- The sheaf endomorphism is multiplication by the restricted constant, on any open. -/
theorem varietyScalarAction_app_eq (r : k)
    (U : Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))
    (m : (associatedSheafInType (polynomialGrading ι k) 𝓜).1.obj (op U)) :
    (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
        (associatedSheaf (polynomialGrading ι k) 𝓜) r).val.app (op U)).hom m :
        (associatedSheafInType (polynomialGrading ι k) 𝓜).1.obj (op U)) =
      constSectionOn ι k U r • m :=
  Cohomology.globalSectionSmul_app (associatedSheaf (polynomialGrading ι k) 𝓜)
    (Cohomology.baseFieldToGlobalSections (projectiveSpaceVariety ι k) r) U m

/-- **The canonical fraction-to-section map is `k`-linear.** It is pointwise `mapOfLE`, and the
constant `r` restricted to the chart has value `r / 1` at every point, so both sides scale the
same fiber by the same scalar. -/
theorem moduleAwayToSection_smul {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d)
    (f : MvPolynomial ι k) (r : k)
    (z : DegreeZeroLocalization (polynomialGrading ι k) 𝓜 (.powers f)) :
    moduleAwayToSection (polynomialGrading ι k) 𝓜 f (r • z) =
      constSection ι k f r • moduleAwayToSection (polynomialGrading ι k) 𝓜 f z := by
  apply Subtype.ext
  funext x
  have hsc : (openToLocalization (polynomialGrading ι k)
      (ProjectiveSpectrum.basicOpen (polynomialGrading ι k) f) x.1 x.2).hom
        (constSection ι k f r) =
      polynomialToHomogeneousLocalization ι k
        x.1.asHomogeneousIdeal.toIdeal.primeCompl r :=
    (openToLocalization_presheaf_map (polynomialGrading ι k)
      (ProjectiveSpectrum.basicOpen (polynomialGrading ι k) f) ⊤ (homOfLE le_top)
      x.1 x.2 _).trans (openToLocalization_baseFieldToGlobalSections ι k r x.1)
  have hle : (Submonoid.powers f) ≤ x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr x.2
  show DegreeZeroLocalization.mapOfLE (𝒜 := polynomialGrading ι k) (𝓜 := 𝓜)
      hle (r • z) =
    (openToLocalization (polynomialGrading ι k)
      (ProjectiveSpectrum.basicOpen (polynomialGrading ι k) f) x.1 x.2).hom
        (constSection ι k f r) •
      DegreeZeroLocalization.mapOfLE (𝒜 := polynomialGrading ι k) (𝓜 := 𝓜) hle z
  rw [hsc, mapOfLE_smul ι k 𝓜 h𝓜]
  rfl

/-- **The Čech comparison is `k`-linear.**

The five-step composite never has to be taken apart: `intCechTermSectionAddEquiv_apply_mk`
already identifies it with `moduleAwayToSection` on every `mk`, and `mk` is surjective. So the
linearity of the whole chain is the linearity of one pointwise `mapOfLE`.

This is what lets a spanning set computed in the graded localizations be read as a spanning set
for the action `module_finite_linearCoherentH_of_cech` consumes. -/
theorem intCechTermSectionAddEquiv_smul (d : ℤ) {n : ℕ} (x : Fin (n + 1) → ι) (r : k)
    (z : polynomialVariableIntCechTerm ι k d n x) :
    intCechTermSectionAddEquiv ι k d x (r • z) =
      constSection ι k (polynomialVariableCechDenominator ι k x) r •
        intCechTermSectionAddEquiv ι k d x z := by
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  have h1 : intCechTermSectionAddEquiv ι k d x (r • DegreeZeroLocalization.mk c) =
      moduleAwayToSection (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)
        (polynomialVariableCechDenominator ι k x) (r • DegreeZeroLocalization.mk c) := by
    rw [smul_mk ι k _ (isPolynomialTwist_intShift (R := k) d)]
    exact intCechTermSectionAddEquiv_apply_mk ι k d x _
  rw [h1, intCechTermSectionAddEquiv_apply_mk,
    moduleAwayToSection_smul ι k _ (isPolynomialTwist_intShift (R := k) d)]

end AlgebraicGeometry.Proj
