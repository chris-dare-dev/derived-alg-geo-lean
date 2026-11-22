/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.NegativeTwist
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.GlobalSections
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpaceScalars
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveSpaceVariety

/-!
# Cohomology of `O(d)` on projective space over a ring, base-ring linearly

For a commutative ring `R` and a type `ι` of homogeneous coordinates, this file states the
cohomology of the twisting sheaves on `Proj R[Xᵢ]` against `Cohomology.linearCoherentH R`, the
coherent cohomology with its canonical `R`-module structure (Stacks 01XT, EGA III 2.1.12). The
computations themselves are the Čech ones of `Cech/Vanishing.lean`, `Cech/NegativeTwist.lean` and
`ProjectiveSpectrum/Modules/ProjectiveSpace.lean`; what this file adds is the base-ring linearity of
the degree-zero comparison and the statements at the `linearCoherentH` interface.

## Main definitions

* `AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsLinearEquiv`: degree-`d` homogeneous
  polynomials are the global sections of `O(d)`, `R`-linearly for the canonical action.
* `AlgebraicGeometry.Proj.twistingSheafH0LinearEquiv`: `H⁰(Proj R[Xᵢ], O(d))` is the degree-`d`
  part of `R[Xᵢ]`, `R`-linearly.

## Main results

* `AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsAddEquiv_smul`: the global-section
  comparison is `R`-linear.
* `AlgebraicGeometry.Proj.twistingSheaf_H0_subsingleton_of_neg`: `H⁰(O(d)) = 0` for `d < 0`, with
  at least two variables.
* `AlgebraicGeometry.Proj.twistingSheaf_H_subsingleton`: `Hᵠ(O(d)) = 0` for `0 < q < N`, where
  `N + 1` is the number of variables, at either sign of `d`.

## Implementation notes

The canonical `R`-action on global sections is multiplication by the global function `r` becomes
under the structure morphism. On an associated sheaf it is scalar multiplication in each fiber
(`varietyScalarAction_apply_fiber`), and the polynomial comparison is pointwise `p ↦ p / 1`, so
linearity is checked point by point after passing to the natural shift through
`twistingSheafOfNatIso`, which is the identity on numerators.

### What is not here

* The top degree. Finite generation of `Hᴺ` over a Noetherian base is
  `module_finite_linearCoherentH_projectiveSpaceTwist`. Freeness over any ring through the
  inverse-monomial basis, and the vanishing of `Hᴺ(O(d))` for `d > -(N + 1)`, need the full-block
  classes to be independent modulo coboundaries, which is not proved yet.
* Degrees above `N`. The Čech complex used here is the full ordered one, whose vanishing above `N`
  is not proved yet.
* The transport to `ℙ(ι; Spec R)` and base change (Stacks 01XV).

## References

* Stacks Project, Lemma 30.8.1 (Tag 01XT).
* EGA III, Proposition 2.1.12.

## Tags

projective space, twisting sheaf, sheaf cohomology, global sections, base change of rings
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι R : Type u) [CommRing R]

/-! ## Degree zero -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **The polynomial comparison is `R`-linear, point by point.** At every point the section of
`r • p` is the fraction `r • p / 1`, which is `r` acting on `p / 1` through the constants. -/
theorem polynomialToNatGlobalSections_smul_apply (d : ℕ) (r : R) (p : homogeneousSubmodule ι R d)
    (x : ProjectiveSpectrum.top (polynomialGrading ι R)) (hx : x ∈ (⊤ : Opens _)) :
    (polynomialToNatGlobalSections ι R d (r • p)).1 ⟨x, hx⟩ =
      polynomialToHomogeneousLocalization ι R x.asHomogeneousIdeal.toIdeal.primeCompl r •
        (polynomialToNatGlobalSections ι R d p).1 ⟨x, hx⟩ := by
  rw [polynomialToNatGlobalSections_apply, polynomialToNatGlobalSections_apply]
  exact (smul_mk ι R (natShift (polynomialGrading ι R) d) (isPolynomialTwist_natShift d)
    x.asHomogeneousIdeal.toIdeal.primeCompl
    { deg := 0
      num := ⟨p.1, by change p.1 ∈ polynomialGrading ι R (0 + d); simp⟩
      den := ⟨1, SetLike.one_mem_graded (polynomialGrading ι R)⟩
      den_mem := Ideal.IsPrime.one_notMem inferInstance } r).symm

/-- **The global-section comparison for `O(d)` is `R`-linear** for the canonical action of the base
ring on global sections, the one the structure morphism to `Spec R` induces.

That action is multiplication by the global function `r` becomes, and on an associated sheaf it is
scalar multiplication fiber by fiber (`varietyScalarAction_apply_fiber`). Passing to the natural
shift through `twistingSheafOfNatIso`, which is the identity on numerators, reduces the claim to
`polynomialToNatGlobalSections_smul_apply`. -/
theorem polynomialTwistingGlobalSectionsAddEquiv_smul [Nonempty ι] (d : ℕ) (r : R)
    (p : homogeneousSubmodule ι R d) :
    letI := Cohomology.globalSectionsModule (k := R) (Proj (polynomialGrading ι R))
      ((Coh.ι (Proj (polynomialGrading ι R))).obj (projectiveSpaceTwist ι R d))
    (show Γ((Coh.ι (Proj (polynomialGrading ι R))).obj (projectiveSpaceTwist ι R d), ⊤) from
        polynomialTwistingGlobalSectionsAddEquiv ι R d (r • p)) =
      r • (show Γ((Coh.ι (Proj (polynomialGrading ι R))).obj (projectiveSpaceTwist ι R d), ⊤) from
        polynomialTwistingGlobalSectionsAddEquiv ι R d p) := by
  let _ := Cohomology.globalSectionsModule (k := R) (Proj (polynomialGrading ι R))
    ((Coh.ι (Proj (polynomialGrading ι R))).obj (projectiveSpaceTwist ι R d))
  -- The base-ring action is the sheaf endomorphism induced by the global function `r`.
  have hres : (Proj (polynomialGrading ι R)).presheaf.map
      (homOfLE (show (⊤ : (Proj (polynomialGrading ι R)).Opens) ≤ ⊤ from le_top)).op
        (Cohomology.baseFieldToGlobalSections (Proj (polynomialGrading ι R)) r) =
      Cohomology.baseFieldToGlobalSections (Proj (polynomialGrading ι R)) r := by
    rw [show (homOfLE (show (⊤ : (Proj (polynomialGrading ι R)).Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : (Proj (polynomialGrading ι R)).Opens)) from Subsingleton.elim _ _]
    simp
  have hsmul : ∀ m : Γ((Coh.ι (Proj (polynomialGrading ι R))).obj (projectiveSpaceTwist ι R d), ⊤),
      r • m = ((Cohomology.varietyScalarAction (Proj (polynomialGrading ι R))
        (associatedSheaf (polynomialGrading ι R) (intShift (polynomialGrading ι R) d))
          r).asHom.val.app (op ⊤)).hom m := by
    intro m
    symm
    change ((Cohomology.globalSectionSmul _
      (Cohomology.baseFieldToGlobalSections (Proj (polynomialGrading ι R)) r)).val.app
        (op ⊤)).hom m = _
    rw [Cohomology.globalSectionSmul_app, hres]
    rfl
  -- Compare on the natural shift, where the comparison is `polynomialToNatGlobalSections`.
  have hA : ∀ q : homogeneousSubmodule ι R d,
      (polynomialNatToTwistingGlobalSectionsAddEquiv ι R d).symm
        (polynomialTwistingGlobalSectionsAddEquiv ι R d q) =
          polynomialToNatGlobalSections ι R d q := fun q =>
    (polynomialNatToTwistingGlobalSectionsAddEquiv ι R d).symm_apply_apply
      (polynomialToNatGlobalSections ι R d q)
  rw [hsmul]
  apply (polynomialNatToTwistingGlobalSectionsAddEquiv ι R d).symm.injective
  rw [hA]
  have hp : ((twistingSheafOfNatIso (polynomialGrading ι R) d).hom.app ⊤).hom
      (polynomialTwistingGlobalSectionsAddEquiv ι R d p) =
        polynomialToNatGlobalSections ι R d p := hA p
  change polynomialToNatGlobalSections ι R d (r • p) =
    ((twistingSheafOfNatIso (polynomialGrading ι R) d).hom.app ⊤).hom
      (((Cohomology.varietyScalarAction (Proj (polynomialGrading ι R))
        (associatedSheaf (polynomialGrading ι R) (intShift (polynomialGrading ι R) d))
          r).asHom.val.app (op ⊤)).hom (polynomialTwistingGlobalSectionsAddEquiv ι R d p))
  apply section_ext
  funext y
  obtain ⟨x, hx⟩ := y
  have hp' := congrArg (fun z => z.1 ⟨x, hx⟩) hp
  simp only at hp'
  erw [associatedMap_app_apply] at hp' ⊢
  erw [varietyScalarAction_apply_fiber, LinearMap.map_smul, hp']
  exact polynomialToNatGlobalSections_smul_apply ι R d r p x hx

/-- The global-section comparison for `O(d)` as an `R`-linear equivalence onto the global sections
with their canonical base-ring action. -/
noncomputable def polynomialTwistingGlobalSectionsLinearEquiv [Nonempty ι] (d : ℕ) :
    homogeneousSubmodule ι R d ≃ₗ[R]
      Cohomology.linearGlobalSectionsObj (k := R) (Proj (polynomialGrading ι R))
        ((Coh.ι (Proj (polynomialGrading ι R))).obj (projectiveSpaceTwist ι R d)) where
  __ := polynomialTwistingGlobalSectionsAddEquiv ι R d
  map_smul' := polynomialTwistingGlobalSectionsAddEquiv_smul ι R d

/-- **Stacks 01XT, degree 0.** `H⁰(Proj R[Xᵢ], O(d))` is the module of homogeneous polynomials of
degree `d`, `R`-linearly for the canonical action of the base ring on cohomology. -/
noncomputable def twistingSheafH0LinearEquiv [Nonempty ι] (d : ℕ) :
    (Cohomology.linearCoherentH R (Proj (polynomialGrading ι R)) 0).obj
        (projectiveSpaceTwist ι R d) ≃ₗ[R] homogeneousSubmodule ι R d :=
  (Cohomology.coherentHZeroSectionsLinearEquiv (Proj (polynomialGrading ι R))
    (projectiveSpaceTwist ι R d)).trans (polynomialTwistingGlobalSectionsLinearEquiv ι R d).symm

/-! ## Vanishing -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Stacks 01XT, degree 0, negative twist.** `H⁰(Proj R[Xᵢ], O(d)) = 0` for `d < 0`.

`Nontrivial ι` cannot be dropped: with one variable `Proj R[X]` is `Spec R` and every twist has
`R` as global sections. -/
theorem twistingSheaf_H0_subsingleton_of_neg [Nontrivial ι] (d : ℤ) (hd : d < 0) :
    Subsingleton ((Cohomology.linearCoherentH R (Proj (polynomialGrading ι R)) 0).obj
      (projectiveSpaceTwist ι R d)) :=
  polynomialIntTwisting_H_zero_subsingleton ι R d hd (hExt := HasExt.standard _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Stacks 01XT, middle degrees.** `Hᵠ(Proj R[Xᵢ], O(d)) = 0` for `0 < q < N`, where `N + 1` is
the number of variables, at either sign of `d`. -/
theorem twistingSheaf_H_subsingleton [Fintype ι] (d : ℤ) (q : ℕ) (hq₀ : 0 < q)
    (hq : q + 1 < Fintype.card ι) :
    Subsingleton ((Cohomology.linearCoherentH R (Proj (polynomialGrading ι R)) q).obj
      (projectiveSpaceTwist ι R d)) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact polynomialIntTwisting_H_subsingleton ι R d n (by omega) (hExt := HasExt.standard _)

end AlgebraicGeometry.Proj
