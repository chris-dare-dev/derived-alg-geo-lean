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
# Polynomial projective space over the base ring, and as a variety over a field

Over a commutative ring `k`, this file makes `Pⁿ = Proj k[Xᵢ]` a proper scheme over `Spec k` and
`O(d)` a coherent sheaf, as instances on `Proj (polynomialGrading ι k)` itself rather than on a
bundle:

* the degree-zero part of the standard grading is the constants, so the base ring maps
  isomorphically onto `𝒜 0` and `Proj.toSpecZero` becomes a morphism to `Spec k`;
* `k[Xᵢ]` is of finite type over `𝒜 0` when the variables are finite in number, which is what
  Mathlib's `LocallyOfFiniteType (Proj.toSpecZero 𝒜)` consumes.

Over a field it is moreover a variety: `IsVariety k X` asks for an integral scheme with a
finite-type morphism to `Spec k`, and the integrality is `AlgebraicGeometry.Proj.isIntegral`.

## Main definitions

* `AlgebraicGeometry.Proj.projectiveSpaceToSpec` — the structure morphism of polynomial
  projective space to the base ring.
* `AlgebraicGeometry.Proj.projectiveSpaceTwist` — the twisting sheaf `O(d)` as a coherent sheaf.

## Main results

* `AlgebraicGeometry.Proj.isProper_projectiveSpaceToSpec` — the structure morphism is proper.
* `AlgebraicGeometry.Proj.isVariety_projectiveSpace` — polynomial projective space over a field
  is a variety.
* `AlgebraicGeometry.Proj.polynomialIntShift_isCoherent` — every twist `O(d)` is coherent.

## Implementation notes

Finiteness of the variable set is genuinely required here and not elsewhere in the Čech
computation: acyclicity of the variable cover holds for any index type, but `Pⁿ` is of finite
type over `k` only for finitely many variables.

## References

Integrality is Mathlib's `AlgebraicGeometry.Proj.isIntegral`; properness comes from
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`.

## Tags

projective space, variety, proper morphism, finite type, twisting sheaf
-/

universe u

open CategoryTheory MvPolynomial

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

section CommRing

variable (ι k : Type u) [CommRing k]

/-- The degree-zero part of the standard grading consists of the constants, so the base ring
maps onto it. -/
theorem algebraMap_polynomialGradeZero_surjective :
    Function.Surjective (algebraMap k ↥(polynomialGrading ι k 0)) := by
  rintro ⟨p, hp⟩
  have hp' : p ∈ (1 : Submodule k (MvPolynomial ι k)) := by
    rwa [← MvPolynomial.homogeneousSubmodule_zero]
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp'
  exact ⟨r, Subtype.ext hr⟩

/-- The degree-zero part of the standard grading is of finite type over the base ring, being a
quotient of it. -/
instance finiteType_polynomialGradeZero :
    Algebra.FiniteType k ↥(polynomialGrading ι k 0) :=
  Algebra.FiniteType.of_surjective (Algebra.ofId k ↥(polynomialGrading ι k 0))
    (algebraMap_polynomialGradeZero_surjective ι k)

/-- The base ring acts on the polynomial ring through the degree-zero part of its grading. -/
instance isScalarTower_polynomialGradeZero :
    IsScalarTower k ↥(polynomialGrading ι k 0) (MvPolynomial ι k) :=
  inferInstanceAs (IsScalarTower k
    ↥(SetLike.GradeZero.subalgebra (polynomialGrading ι k)) (MvPolynomial ι k))

/-- With finitely many variables the polynomial ring is of finite type over the degree-zero
part of its grading. -/
instance finiteType_polynomialGrading [Finite ι] :
    Algebra.FiniteType ↥(polynomialGrading ι k 0) (MvPolynomial ι k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

/-- The structure morphism of polynomial projective space to the base ring.

`Proj.toSpecZero` lands in the spectrum of the degree-zero part; composing with the spectrum of
the base ring's map onto that part gives the morphism to `Spec k`. -/
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

/-- **The structure morphism of polynomial projective space is proper.**

`Proj.toSpecZero` is proper because the polynomial ring is of finite type over its degree-zero
part, and the identification of `k` with that part is an isomorphism: surjective by
`algebraMap_polynomialGradeZero_surjective`, injective because constants are
(`MvPolynomial.C_injective`). This is what makes `Pⁿ` Noetherian and separated through
`Variety.isNoetherian_of_isProper` and `Variety.isSeparated_of_isProper`, which the finite-cover
cohomology bound consumes. -/
instance isProper_projectiveSpaceToSpec [Finite ι] : IsProper (projectiveSpaceToSpec ι k) := by
  have : IsIso (CommRingCat.ofHom (algebraMap k ↥(polynomialGrading ι k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨fun a b h => MvPolynomial.C_injective ι k (congrArg Subtype.val h),
        algebraMap_polynomialGradeZero_surjective ι k⟩
  show IsProper (Proj.toSpecZero (polynomialGrading ι k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k ↥(polynomialGrading ι k 0))))
  infer_instance

/-- **Polynomial projective space is a scheme over the base ring**, with structure morphism
`projectiveSpaceToSpec`. This is the `Scheme.Over` instance every statement about `Pⁿ` over
`k` consumes; `Proj (polynomialGrading ι k) ↘ Spec (CommRingCat.of k)` unfolds to it. -/
noncomputable instance instOverProjectiveSpace :
    (Proj (polynomialGrading ι k)).Over (Spec (CommRingCat.of k)) :=
  ⟨projectiveSpaceToSpec ι k⟩

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
finiteness interface can name `Hⁱ(Pⁿ, O(d))` as a `k`-module. Coherence of `O(d)` needs
no finiteness of the index type; that enters only through `isVariety_projectiveSpace`. -/
noncomputable def projectiveSpaceTwist (d : ℤ) :
    Coh (Proj (polynomialGrading ι k)) :=
  ⟨associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d),
    polynomialIntShift_isCoherent ι k d⟩

/-- The coherent-sheaf bundle changes nothing about the underlying module sheaf, so the Čech
computation's results about the twist apply to it directly. -/
lemma projectiveSpaceTwist_obj (d : ℤ) :
    (Coh.ι (Proj (polynomialGrading ι k))).obj (projectiveSpaceTwist ι k d) =
      associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d) :=
  rfl

end CommRing

section Field

variable (ι k : Type u) [Field k]

/-- Polynomial projective space is nonempty once there is a variable.

Nonemptiness is a hypothesis of `Proj.isIntegral` rather than a consequence: `Proj` of a graded
ring concentrated in degree zero is empty. A variable supplies the missing point. -/
instance nonempty_projectiveSpace [Nonempty ι] :
    Nonempty (Proj (polynomialGrading ι k)) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, -⟩ := basicOpen_nonempty (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) Nat.one_pos (MvPolynomial.X_ne_zero i)
  exact ⟨x⟩

/-- **Polynomial projective space over a field is a variety.**

Finiteness of the variable set is what makes the structure morphism of finite type;
nonemptiness is what makes the space irreducible rather than vacuously so. -/
instance isVariety_projectiveSpace [Finite ι] [Nonempty ι] :
    IsVariety k (Proj (polynomialGrading ι k)) where
  toIsIntegral := Proj.isIntegral (polynomialGrading ι k)
  toLocallyOfFiniteType :=
    inferInstanceAs (LocallyOfFiniteType (projectiveSpaceToSpec ι k))

end Field

end AlgebraicGeometry.Proj
