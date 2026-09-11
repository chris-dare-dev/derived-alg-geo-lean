/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Devissage
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpaceTopFinite
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.NegativeTwist
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInverse

/-!
# Serre finiteness on projective space

**Every coherent sheaf on `Pⁿ_k` has finite-dimensional cohomology in every degree**, and
`FiniteDimensionalCohomology k Pⁿ` is inhabited by a theorem rather than a supplied field.

This is S3 of `#332` (`#571`). The two inputs are:

* **Serre's theorem** (`exists_epi_coproduct_twistingSheaf_ge`): every coherent `F` is a quotient
  of `∐ O(-N)`, with `N ≥ 1` chosen so that the twist is negative.
* **Cohomology of the twists**: `Hⁿ⁺¹(Pⁿ, O(d))` is finite-dimensional for every `d`
  (`module_finite_linearCoherentH_projectiveSpaceTwist`, S1), and `H⁰(Pⁿ, O(d)) = 0` for `d < 0`
  (`polynomialIntTwisting_H_zero_subsingleton`). Taking `N ≥ 1` is what makes the second
  statement the one needed: the degree-zero group of a *nonnegative* twist is the space of
  homogeneous polynomials, whose finiteness is a separate computation that never has to be made.

The dévissage itself is `module_finite_linearCoherentH_of_devissage`: descending induction from
the finite-cover vanishing bound along the linear exact sequence `Hⁱ(∐ O(-N)) → Hⁱ(F) → Hⁱ⁺¹(K)`.

## The surjection, read in `Coh`

Serre's surjection lives in `Pⁿ.Modules`; the long exact sequence wants a short exact sequence
in `Coh Pⁿ`. `Coh.ι` is fully faithful and preserves finite colimits, so the coproduct of the
twists in `Coh` maps to the coproduct in `Modules` and the surjection lifts along the
`preimage`; faithfulness reflects the epimorphism, and the kernel in `Coh` completes the
sequence.

## Not here

Closed subvarieties of `Pⁿ`. Step 3 of `#332` transports finiteness along a closed immersion
through `cohCohomologyPushforwardAddEquiv`, and the `k`-linearity of that comparison is what
`Variety.IsProjective` still needs.
-/

universe u

open CategoryTheory CategoryTheory.Limits GradedModule MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Proj

variable (ι k : Type u) [Field k] [Fintype ι] [Nontrivial ι]

/-- **`Hⁱ(Pⁿ, O(d))` is finite-dimensional in every degree for a negative twist.**

Degree zero vanishes (`polynomialIntTwisting_H_zero_subsingleton`); positive degrees are S1
(`module_finite_linearCoherentH_projectiveSpaceTwist`). -/
theorem module_finite_linearCoherentH_projectiveSpaceTwist_of_neg (d : ℤ) (hd : d < 0) (i : ℕ) :
    Module.Finite k ((Cohomology.linearCoherentH k (Proj (polynomialGrading ι k)) i).obj
      (projectiveSpaceTwist ι k d)) := by
  cases i with
  | zero =>
    haveI : Subsingleton ((Cohomology.linearCoherentH k (Proj (polynomialGrading ι k)) 0).obj
        (projectiveSpaceTwist ι k d)) :=
      polynomialIntTwisting_H_zero_subsingleton ι k d hd (hExt := HasExt.standard _)
    exact Module.Finite.of_finite
  | succ n => exact module_finite_linearCoherentH_projectiveSpaceTwist ι k d n

/-- **Every coherent sheaf on `Pⁿ` is the quotient, in `Coh Pⁿ`, of a finite coproduct of copies
of a negative twist**, with coherent kernel: Serre's surjection lifted along `Coh.ι`. -/
theorem exists_shortExact_coproduct_twist (F : Coh (Proj (polynomialGrading ι k))) :
    ∃ (S : ShortComplex (Coh (Proj (polynomialGrading ι k)))) (_ : S.ShortExact)
      (_ : S.X₃ ≅ F) (N : ℕ) (_ : 1 ≤ N) (I : Type u) (_ : Finite I),
      S.X₂ = ∐ (fun _ : I => projectiveSpaceTwist ι k (-(N : ℤ))) := by
  classical
  obtain ⟨N, hN, I, hI, q, hq⟩ := exists_epi_coproduct_twistingSheaf_ge (polynomialGrading ι k)
    ((Coh.ι _).obj F) F.2 (g := fun i => MvPolynomial.X i)
    (fun i => MvPolynomial.isHomogeneous_X k i) (polynomialVariable_adjoin_eq_top ι k) 1
  haveI := Fintype.ofFinite I
  -- the coproduct of the twists in `Coh`, and its image in `Modules`
  let G : Coh (Proj (polynomialGrading ι k)) := ∐ (fun _ : I => projectiveSpaceTwist ι k (-(N : ℤ)))
  let e : (Coh.ι _).obj G ≅ ∐ (fun _ : I => twistingSheaf (polynomialGrading ι k) (-(N : ℤ))) :=
    PreservesCoproduct.iso (Coh.ι _) (fun _ : I => projectiveSpaceTwist ι k (-(N : ℤ)))
  let q' : G ⟶ F := (Coh.ι _).preimage (e.hom ≫ q)
  haveI : Epi ((Coh.ι _).map q') := by
    rw [Functor.map_preimage]
    exact epi_comp _ _
  haveI : Epi q' := (Coh.ι _).epi_of_epi_map inferInstance
  refine ⟨ShortComplex.mk (kernel.ι q') q' (kernel.condition q'), ?_, Iso.refl F, N, hN, I, hI,
    rfl⟩
  exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel q')
          mono_f := inferInstance
          epi_g := inferInstance }

/-- **Serre finiteness on projective space**: every coherent sheaf on `Pⁿ_k` has
finite-dimensional cohomology in every degree. -/
theorem module_finite_linearCoherentH_projectiveSpace (i : ℕ)
    (F : Coh (Proj (polynomialGrading ι k))) :
    Module.Finite k ((Cohomology.linearCoherentH k (Proj (polynomialGrading ι k)) i).obj F) := by
  haveI : IsProper (Proj (polynomialGrading ι k) ↘ Spec (CommRingCat.of k)) :=
    isProper_projectiveSpaceToSpec ι k
  haveI : IsNoetherian (Proj (polynomialGrading ι k)) :=
    Variety.isNoetherian_of_isProper (k := k)
  haveI : (Proj (polynomialGrading ι k)).IsSeparated :=
    Variety.isSeparated_of_isProper (k := k)
  refine Cohomology.module_finite_linearCoherentH_of_devissage ?_ i F
  intro F
  obtain ⟨S, hS, e, N, hN, I, hI, hG⟩ := exists_shortExact_coproduct_twist ι k F
  refine ⟨S, hS, e, fun j => ?_⟩
  rw [hG]
  exact Cohomology.module_finite_linearCoherentH_coproduct _ j fun _ =>
    module_finite_linearCoherentH_projectiveSpaceTwist_of_neg ι k (-(N : ℤ)) (by omega) j

/-- **The finite-dimensional cohomology package of projective space, proved rather than
supplied.** The linear realization is the canonical one; the `finite` field is Serre finiteness. -/
noncomputable def projectiveSpaceFiniteDimensionalCohomology :
    Cohomology.FiniteDimensionalCohomology k (Proj (polynomialGrading ι k)) where
  toLinearCohomology := Cohomology.canonicalLinearCohomology (Proj (polynomialGrading ι k))
  finite := fun i F => module_finite_linearCoherentH_projectiveSpace ι k i F

/-- **The finite cohomology package of projective space**: Serre finiteness together with the
finite-affine-cover vanishing bound. Every Euler characteristic on `Pⁿ` now rests on theorems
alone. -/
noncomputable def projectiveSpaceFiniteCohomology :
    Cohomology.FiniteCohomology k (Proj (polynomialGrading ι k)) :=
  haveI : IsProper (Proj (polynomialGrading ι k) ↘ Spec (CommRingCat.of k)) :=
    isProper_projectiveSpaceToSpec ι k
  haveI : IsNoetherian (Proj (polynomialGrading ι k)) :=
    Variety.isNoetherian_of_isProper (k := k)
  haveI : (Proj (polynomialGrading ι k)).IsSeparated :=
    Variety.isSeparated_of_isProper (k := k)
  (projectiveSpaceFiniteDimensionalCohomology ι k).toFiniteCohomology

end AlgebraicGeometry.Proj
