/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpaceCechScalars
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.LinearCech

/-!
# The degreewise Čech comparison is `k`-linear

`intCechIndexEquiv_smul` is the statement at one Čech index. Degree `n` of the Čech complex is the
product of those indices over the tuples `x : Fin (n + 1) → ι`, and
`intCechCochainsDegreewiseAddEquiv` is the corresponding product of comparisons, so degreewise
linearity is the per-index statement read off one projection at a time.

## The endomorphism, named once

The Čech lane takes a presheaf; the scalar action is defined on a sheaf of modules.
`cechScalarAction` crosses that gap by pushing `varietyScalarAction` through
`Scheme.Modules.toSheaf` and then `sheafToPresheaf`, and `intTwistScalarHom` is exactly that
composite named at the twist. Naming it
is what makes the reconciliation visible: its source and target elaborate as `intTwistPresheaf`,
which is the presheaf the explicit complex is built from, so no transport is needed between the two
descriptions of degree `n`.

## What carries the projection

`cechComplexFunctor_map_f_π` says the induced map commutes with the projections, because `evalOp`
sends a morphism to `Pi.map` componentwise. That is the exact analogue for a morphism of what
`cechComplexFunctor_d_π` is for the differential, and `intCechScalar_proj` instantiates it here in
the same shape `intCechCochainsDegreewiseAddEquiv_d` uses.

The proof is written with `congrArg` and `Eq.trans` rather than `rw`. The projection family in the
goal is spelled through the Čech nerve (`(rightOp cech).obj ⦋n⦌`) while the general lemma spells it
through `cechTermFamily`; the two are definitionally equal but not syntactically so, and `rw` will
not match across that gap while `congrArg` only needs defeq. This is the same obstruction recorded
for `intCechIndexEquiv_smul`.

## Scope

Degreewise only. The homology statement, the surjection from the full blocks, and the
`module_finite_linearCoherentH_of_cech` wiring are in
`Cohomology/Finiteness/ProjectiveSpaceTopFinite.lean`, which consumes this file.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace CategoryTheory.Limits

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k] [Finite ι] [Nonempty ι]

/-- **The endomorphism of the twist presheaf a base scalar induces.**

This is `varietyScalarAction` carried through the two functors `cechScalarAction` uses. That it
elaborates with `intTwistPresheaf` on both sides is the reconciliation the Čech lane needs: the
sheaf-side presheaf and the presheaf the explicit complex is built from are the same object. -/
noncomputable def intTwistScalarHom (d : ℤ) (r : k) :
    intTwistPresheaf ι k d ⟶ intTwistPresheaf ι k d :=
  (sheafToPresheaf _ _).map ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).map
    (Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
      (associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)) r))

/-- The induced map on degree `n`, read at one Čech index.

`cechComplexFunctor_map_f_π` in the shape the degreewise comparison consumes: the index object is
written as `∏ᶜ (polynomialVariableChart ι k ∘ x)` rather than through the nerve. -/
theorem intCechScalar_proj (d : ℤ) (n : ℕ) (r : k)
    (t : ((intCechComplexOfTwist ι k d).X n : AddCommGrpCat)) (x : Fin (n + 1) → ι) :
    AddCommGrpCat.piAddEquivPi _
        (ConcreteCategory.hom (((cechComplexFunctor (polynomialVariableChart ι k)).map
          (intTwistScalarHom ι k d r)).f n) t) x =
      ConcreteCategory.hom
        ((intTwistScalarHom ι k d r).app (op (∏ᶜ (polynomialVariableChart ι k ∘ x))))
        (AddCommGrpCat.piAddEquivPi _ t x) := by
  refine Eq.trans ?_ (congrArg
    (fun z => ConcreteCategory.hom
      ((intTwistScalarHom ι k d r).app (op (∏ᶜ (polynomialVariableChart ι k ∘ x)))) z)
    (AddCommGrpCat.piIsoPi_hom_eval_apply _ x t))
  refine Eq.trans (AddCommGrpCat.piIsoPi_hom_eval_apply _ x _) ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ t)
  exact congrArg (fun m : ((intCechComplexOfTwist ι k d).X n ⟶
      (intTwistPresheaf ι k d).obj (op (∏ᶜ (polynomialVariableChart ι k ∘ x)))) =>
      ConcreteCategory.hom m t)
    (cechComplexFunctor_map_f_π (polynomialVariableChart ι k) (intTwistScalarHom ι k d r) n x)

/-- **The degreewise comparison is `k`-linear.**

Cochains in degree `n` form a product over the tuples, the scalar acts on each factor, and
`intCechIndexEquiv_smul` is the statement on one factor. -/
theorem intCechCochainsDegreewiseAddEquiv_smul (d : ℤ) (n : ℕ) (r : k)
    (t : ((intCechComplexOfTwist ι k d).X n : AddCommGrpCat)) :
    intCechCochainsDegreewiseAddEquiv ι k d n
        (ConcreteCategory.hom
          (((cechComplexFunctor (polynomialVariableChart ι k)).map
            (intTwistScalarHom ι k d r)).f n) t) =
      r • intCechCochainsDegreewiseAddEquiv ι k d n t := by
  funext x
  refine Eq.trans (intCechCochainsDegreewiseAddEquiv_apply ι k d n _ x) ?_
  refine Eq.trans (congrArg (intCechIndexEquiv ι k d x)
    (intCechScalar_proj ι k d n r t x)) ?_
  exact intCechIndexEquiv_smul ι k d x r _

end AlgebraicGeometry.Proj
