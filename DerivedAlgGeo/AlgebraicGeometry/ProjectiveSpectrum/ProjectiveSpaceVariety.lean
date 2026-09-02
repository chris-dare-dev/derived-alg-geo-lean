/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.Grading
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Integral
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Finiteness
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistCoherence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Basic.Definitions
import DerivedAlgGeo.AlgebraicGeometry.Variety.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType

/-!
# Polynomial projective space as a variety over the base field

`IsVariety k X` asks for an integral scheme with a finite-type morphism to `Spec k`. For
`Pⁿ = Proj k[Xᵢ]` the integrality is `AlgebraicGeometry.Proj.isIntegral`, and this file supplies
the rest, as instances on `Proj (polynomialGrading ι k)` itself rather than on a bundle:

* the degree-zero part of the standard grading is the constants, so the base field maps
  isomorphically onto `𝒜 0` and `Proj.toSpecZero` becomes a morphism to `Spec k`;
* `k[Xᵢ]` is of finite type over `𝒜 0` when the variables are finite in number, which is what
  Mathlib's `LocallyOfFiniteType (Proj.toSpecZero 𝒜)` consumes.

Finiteness of the variable set is genuinely required here and not elsewhere in the Čech lane:
acyclicity of the variable cover holds for any index type, but `Pⁿ` is of finite type over `k`
only for finitely many variables.
-/

universe u

open CategoryTheory MvPolynomial

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

variable (ι k : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-zero part of the standard grading consists of the constants, so the base field
maps onto it. -/
theorem algebraMap_polynomialGradeZero_surjective :
    Function.Surjective (algebraMap k ↥(polynomialGrading ι k 0)) := by
  rintro ⟨p, hp⟩
  have hp' : p ∈ (1 : Submodule k (MvPolynomial ι k)) := by
    rwa [← MvPolynomial.homogeneousSubmodule_zero]
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp'
  exact ⟨r, Subtype.ext hr⟩

/-- The degree-zero part of the standard grading is of finite type over the base field, being a
quotient of it. -/
instance finiteType_polynomialGradeZero :
    Algebra.FiniteType k ↥(polynomialGrading ι k 0) :=
  Algebra.FiniteType.of_surjective (Algebra.ofId k ↥(polynomialGrading ι k 0))
    (algebraMap_polynomialGradeZero_surjective ι k)

/-- The base field acts on the polynomial ring through the degree-zero part of its grading. -/
instance isScalarTower_polynomialGradeZero :
    IsScalarTower k ↥(polynomialGrading ι k 0) (MvPolynomial ι k) :=
  inferInstanceAs (IsScalarTower k
    ↥(SetLike.GradeZero.subalgebra (polynomialGrading ι k)) (MvPolynomial ι k))

/-- With finitely many variables the polynomial ring is of finite type over the degree-zero
part of its grading. -/
instance finiteType_polynomialGrading [Finite ι] :
    Algebra.FiniteType ↥(polynomialGrading ι k 0) (MvPolynomial ι k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

/-- The structure morphism of polynomial projective space to the base field.

`Proj.toSpecZero` lands in the spectrum of the degree-zero part; composing with the spectrum of
the base field's map onto that part gives the morphism `Variety` asks for. -/
noncomputable def projectiveSpaceToSpec :
    Proj (polynomialGrading ι k) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (polynomialGrading ι k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k ↥(polynomialGrading ι k 0)))

instance locallyOfFiniteType_projectiveSpaceToSpec [Finite ι] :
    LocallyOfFiniteType (projectiveSpaceToSpec ι k) := by
  have hsurj : Function.Surjective (algebraMap k ↥(polynomialGrading ι k 0)) :=
    algebraMap_polynomialGradeZero_surjective ι k
  haveI : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k ↥(polynomialGrading ι k 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- Polynomial projective space is nonempty once there is a variable.

Nonemptiness is a hypothesis of `Proj.isIntegral` rather than a consequence: `Proj` of a graded
ring concentrated in degree zero is empty. A variable supplies the missing point. -/
instance nonempty_projectiveSpace [Nonempty ι] :
    Nonempty (Proj (polynomialGrading ι k)) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, -⟩ := basicOpen_nonempty (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) Nat.one_pos (MvPolynomial.X_ne_zero i)
  exact ⟨x⟩

/-- **Polynomial projective space is a scheme over the base field**, with structure morphism
`projectiveSpaceToSpec`. This is the `Scheme.Over` instance every statement about `Pⁿ` over
`k` consumes; `Proj (polynomialGrading ι k) ↘ Spec (CommRingCat.of k)` unfolds to it. -/
noncomputable instance instOverProjectiveSpace :
    (Proj (polynomialGrading ι k)).Over (Spec (CommRingCat.of k)) :=
  ⟨projectiveSpaceToSpec ι k⟩

/-- **Polynomial projective space is a variety over the base field.**

Finiteness of the variable set is what makes the structure morphism of finite type;
nonemptiness is what makes the space irreducible rather than vacuously so. -/
instance isVariety_projectiveSpace [Finite ι] [Nonempty ι] :
    IsVariety k (Proj (polynomialGrading ι k)) where
  toIsIntegral := Proj.isIntegral (polynomialGrading ι k)
  toLocallyOfFiniteType :=
    inferInstanceAs (LocallyOfFiniteType (projectiveSpaceToSpec ι k))

/-- The twisting sheaf `O(d)` on polynomial projective space is coherent. -/
theorem polynomialIntShift_isCoherent (d : ℤ) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj (polynomialGrading ι k))
      (associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)) :=
  intShift_isCoherent (polynomialGrading ι k)
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
    (polynomialVariable_adjoin_eq_top ι k)

/-- **`O(d)` as a coherent sheaf on polynomial projective space.**

This is the object `coherentScalarAction` and `linearCoherentH` are stated about, so with it the
finiteness interface can name `Hⁱ(Pⁿ, O(d))` as a `k`-vector space. Coherence of `O(d)` needs
no finiteness of the index type; that enters only through `isVariety_projectiveSpace`. -/
noncomputable def projectiveSpaceTwist (d : ℤ) :
    Coh (Proj (polynomialGrading ι k)) :=
  ⟨associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d),
    polynomialIntShift_isCoherent ι k d⟩

/-- The coherent-sheaf bundle changes nothing about the underlying module sheaf, so the Čech
lane's results about the twist apply to it directly. -/
lemma projectiveSpaceTwist_obj (d : ℤ) :
    (Coh.ι (Proj (polynomialGrading ι k))).obj (projectiveSpaceTwist ι k d) =
      associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d) :=
  rfl

end AlgebraicGeometry.Proj
