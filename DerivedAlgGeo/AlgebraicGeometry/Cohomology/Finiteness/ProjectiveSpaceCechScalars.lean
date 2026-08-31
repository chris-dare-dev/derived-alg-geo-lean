/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpaceScalars
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.TopDegree

/-!
# The per-index Čech comparison is `k`-linear

`intCechTermSectionAddEquiv_smul` says the comparison between a Čech *term* and its sections
respects the base-field action. `intCechIndexEquiv` is that comparison composed with one
transport, because a Čech index names sections over a categorical product of charts while the
term comparison is stated over a basic open, and `piObj_polynomialVariableChart` only says those
two opens are *equal*. This file carries the linearity across that transport.

## The transport is the whole content

`eqToIso_transport_varietyScalarAction` is `subst h; rfl` — moving sections along an equality of
opens cannot fail to commute with anything. All the difficulty is in getting the statement to
elaborate, and that difficulty has a single diagnosed cause.

## The scalar-type rule, and why it is not a diamond to be fixed

`Γ(Proj 𝒜, U)` and `(ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U)` are **definitionally
equal at default transparency and not at reducible transparency**. Instance search runs at
reducible. The `Module` instance on associated-sheaf sections is stated over the second, so a `•`
whose left factor is written as the first leaves `HSMul` unsolved — even though the two are the
same type.

That is the same shape as #662, where `Coh X` carries two `Preadditive` instances defeq at default
but not at reducible. So the obvious repair — adding a second `Module` instance over
`(Proj 𝒜).presheaf.obj` — would **reproduce that bug** rather than fix this one: lemmas stated
against one instance would stop applying to goals carrying the other.

The rule instead is a convention, and it costs nothing:

* **state** scalar actions on sections with `varietyScalarAction`'s `app`, never with `•`. That
  form always elaborates, and it is the definitionally canonical one anyway;
* **convert** to `•` with `varietyScalarAction_app_eq` only inside a proof, where the expected
  type is already fixed and search has what it needs;
* when a scalar genuinely has to be named, give it a definition with an explicit result type —
  `constSectionOn` is that, and it is the only such definition needed so far.

Occurrences before the rule was written down: `cechBlockSpan` (#670), `constSection` and
`constSectionOn` (#674), and the transport here.

## Next

Degreewise linearity of `intCechCochainsDegreewiseAddEquiv` is a product of this over the tuple
index; the homology statement `r • [s] = [r • s]` is then `homologyπ` naturality. Neither is here.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k] [Finite ι] [Nonempty ι]

/-- Transport along an equality of opens commutes with the endomorphism a scalar induces. -/
theorem eqToIso_transport_varietyScalarAction (d : ℤ)
    {W W' : Opens (ProjectiveSpectrum.top (polynomialGrading ι k))} (h : W = W') (r : k)
    (s : (intTwistPresheaf ι k d).obj (op W)) :
    (eqToIso (congrArg (fun V => (intTwistPresheaf ι k d).obj (op V)) h)
        ).addCommGroupIsoToAddEquiv
        (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
            (associatedSheaf (polynomialGrading ι k)
              (intShift (polynomialGrading ι k) d)) r).val.app (op W)).hom s) =
      ((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
          (associatedSheaf (polynomialGrading ι k)
            (intShift (polynomialGrading ι k) d)) r).val.app (op W')).hom
        ((eqToIso (congrArg (fun V => (intTwistPresheaf ι k d).obj (op V)) h)
          ).addCommGroupIsoToAddEquiv s) := by
  subst h; rfl

/-- The symm form of the term-level comparison lemma, against the sheaf endomorphism. -/
theorem intCechTermSectionAddEquiv_symm_varietyScalarAction (d : ℤ) {n : ℕ}
    (x : Fin (n + 1) → ι) (r : k)
    (w : (associatedSheafInType (polynomialGrading ι k)
      (intShift (polynomialGrading ι k) d)).1.obj
      (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x)))) :
    (intCechTermSectionAddEquiv ι k d x).symm
        (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
            (associatedSheaf (polynomialGrading ι k)
              (intShift (polynomialGrading ι k) d)) r).val.app _).hom w) =
      r • (intCechTermSectionAddEquiv ι k d x).symm w := by
  refine (congrArg (intCechTermSectionAddEquiv ι k d x).symm
    (varietyScalarAction_app_eq ι k (intShift (polynomialGrading ι k) d) r _ w)).trans ?_
  apply (intCechTermSectionAddEquiv ι k d x).injective
  rw [AddEquiv.apply_symm_apply, intCechTermSectionAddEquiv_smul, AddEquiv.apply_symm_apply]
  rfl

/-- **The per-index comparison is `k`-linear.** -/
theorem intCechIndexEquiv_smul (d : ℤ) {n : ℕ} (x : Fin (n + 1) → ι) (r : k)
    (s : (intTwistPresheaf ι k d).obj (op (∏ᶜ (polynomialVariableChart ι k ∘ x)))) :
    intCechIndexEquiv ι k d x
        (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
            (associatedSheaf (polynomialGrading ι k)
              (intShift (polynomialGrading ι k) d)) r).val.app
          (op (∏ᶜ (polynomialVariableChart ι k ∘ x)))).hom s) =
      r • intCechIndexEquiv ι k d x s := by
  refine Eq.trans (congrArg (intCechTermSectionAddEquiv ι k d x).symm
    (eqToIso_transport_varietyScalarAction ι k d (piObj_polynomialVariableChart ι k x) r s)) ?_
  exact intCechTermSectionAddEquiv_symm_varietyScalarAction ι k d x r _

end AlgebraicGeometry.Proj
