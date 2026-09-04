/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Variety.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective varieties

This file separates the proposition that a scheme over `k` is projective from a chosen
projective presentation. A `ProjectivePresentation k X` is a finite-coordinate closed immersion
of the fixed `X` into projective space over the base field. `Variety.IsProjective k X` merely
asserts that such a presentation exists.

Consequently, two embeddings are two presentations of the same scheme, not two bundled
varieties, and there is no bundled projective-variety type: a projective variety is
`(X : Scheme) [X.Over (Spec k)] [IsVariety k X] [Variety.IsProjective k X]`.

## Properness is derived here, not assumed

Properness is derived from any presentation: `Proj.toSpecZero` is proper once the graded ring is
of finite type over its degree-zero part, a closed immersion is finite and hence proper, and
properness is stable under composition. The resulting instance depends only on the
proposition-valued `Variety.IsProjective`, not on a globally selected embedding.

## The degree-zero identification is a construction, not a coincidence

`Proj.toSpecZero 𝒜` lands in `Spec (𝒜 0)`, and for the standard grading `𝒜 0` is the submodule
of degree-zero homogeneous polynomials — not `k` on the nose. `homogeneousZeroRingEquiv` is the
identification, built from `MvPolynomial.C` and inverted by `constantCoeff`, and every statement
below that mentions the base field passes through it explicitly rather than through a defeq that
happens to fire.

## Naming

The grading used here is `MvPolynomial.homogeneousSubmodule ι k`, which is by definition
`MvPolynomial.polynomialGrading ι k` from `Algebra/MvPolynomial/Grading.lean`. The Mathlib
spelling is used so that the variety layer does not import the Proj Čech-comparison stack; the
two are the same term, so statements in either spelling compose.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section PolynomialGrading

variable (ι : Type u) (R : Type u) [CommRing R]

/-- The base ring is the degree-zero part of the standard graded polynomial ring.

Both directions are ring homomorphisms already: `MvPolynomial.C` on the way in, and
`MvPolynomial.constantCoeff` on the way out. What needs proof is that they are mutually inverse
*on the degree-zero submodule* — a degree-zero homogeneous polynomial is a constant, which is
`MvPolynomial.totalDegree_eq_zero_iff_eq_C` read through
`MvPolynomial.totalDegree_zero_iff_isHomogeneous`. -/
noncomputable def homogeneousZeroRingEquiv :
    R ≃+* ↥(MvPolynomial.homogeneousSubmodule ι R 0) where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ _⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    refine Subtype.ext ?_
    have hp : (p : MvPolynomial ι R).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).2
        ((MvPolynomial.mem_homogeneousSubmodule _ _).1 p.2)
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 hp
    show MvPolynomial.C (MvPolynomial.constantCoeff (p : MvPolynomial ι R)) = _
    rw [MvPolynomial.constantCoeff_eq]
    exact hc.symm
  map_mul' _ _ := by ext; simp
  map_add' _ _ := by ext; simp

/-- The identification is `MvPolynomial.C` underneath, which is what makes it usable as a rewrite
in statements phrased on the polynomial ring rather than on the degree-zero submodule. -/
@[simp]
lemma homogeneousZeroRingEquiv_apply_coe (r : R) :
    ((homogeneousZeroRingEquiv ι R r : ↥(MvPolynomial.homogeneousSubmodule ι R 0)) :
      MvPolynomial ι R) = MvPolynomial.C r :=
  rfl

/-- The tower `R → 𝒜₀ → R[ι]`. Both algebra structures are Mathlib's —
`SetLike.GradeZero.instAlgebra` on the way in, the subobject coercion on the way out — so the
tower is `rfl`; it is only missing because Mathlib does not register it for grade-zero parts in
general. Local: the finite-type transfer below is its only consumer. -/
local instance isScalarTower_homogeneousZero :
    IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := ↥(MvPolynomial.homogeneousSubmodule ι R 0))
    (A := MvPolynomial ι R) rfl

/-- The polynomial ring is of finite type over its degree-zero part when the variable set is
finite. This is what `Proj.toSpecZero`'s properness instance asks for, and it is the only place
the finiteness of the variable set is used. -/
instance finiteType_homogeneousZero [Finite ι] :
    Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

end PolynomialGrading

section ProjectiveSpace

variable (ι : Type u) (k : Type u) [Field k]

/-- Projective space over `k` on the variable set `ι`, as the `Proj` of the standard graded
polynomial ring. -/
noncomputable abbrev projectiveSpace : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule ι k)

/-- The structure morphism of projective space to `Spec k`: Mathlib's `Proj.toSpecZero`, followed
by the identification of `k` with the degree-zero part. -/
noncomputable def projectiveSpaceToSpec :
    projectiveSpace ι k ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (homogeneousZeroRingEquiv ι k).toRingHom)

instance isProper_projectiveSpaceToSpec [Finite ι] : IsProper (projectiveSpaceToSpec ι k) := by
  have : IsIso (CommRingCat.ofHom (homogeneousZeroRingEquiv ι k).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (homogeneousZeroRingEquiv ι k).bijective
  show IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (homogeneousZeroRingEquiv ι k).toRingHom))
  infer_instance

end ProjectiveSpace

/-- A projective presentation of `X` over `k`: a closed immersion into a projective space over
`k`, compatible with the two structure morphisms.

The variable set is data rather than a natural number because the ambient projective space is
`Proj` of a polynomial ring on an index *type*, which is how the Proj lane in this repository
states everything else. `Finite ι` is what makes the ambient space proper, and it is an instance
field so that the properness instance below fires without an explicit argument. -/
structure ProjectivePresentation (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] where
  /-- The homogeneous coordinates of the ambient projective space. -/
  index : Type u
  /-- Finitely many of them. -/
  [finiteIndex : Finite index]
  /-- The projective embedding. -/
  embedding : X ⟶ projectiveSpace index k
  /-- It is a closed immersion: this is the projectivity, and it is data. -/
  [isClosedImmersion : IsClosedImmersion embedding]
  /-- The embedding is a morphism over the base field. -/
  overBase : embedding ≫ projectiveSpaceToSpec index k = X ↘ Spec (CommRingCat.of k)

namespace ProjectivePresentation

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

attribute [instance] finiteIndex isClosedImmersion

instance instFiniteIndex (P : ProjectivePresentation k X) : Finite P.index := P.finiteIndex

instance instIsClosedImmersionEmbedding (P : ProjectivePresentation k X) :
    IsClosedImmersion P.embedding := P.isClosedImmersion

/-- A projective variety is proper over the base field.

Not a field of the variety, and not an appeal to a projective-morphism API that does not exist:
the closed immersion is finite hence proper, the ambient projective space is proper over `Spec k`
because the polynomial ring is of finite type over its degree-zero part, and `overBase` says the
structure morphism *is* their composite. -/
theorem isProper_structureMorphism (P : ProjectivePresentation k X) :
    IsProper (X ↘ Spec (CommRingCat.of k)) := by
  rw [← P.overBase]
  infer_instance

end ProjectivePresentation

namespace Variety

/-- Projectivity of `X` over `k`, expressed as the mere existence of a projective
presentation. The chosen embedding remains separate data. -/
class IsProjective (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] : Prop where
  presentation : Nonempty (ProjectivePresentation k X)

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

namespace IsProjective

/-- A chosen presentation proves the proposition that the variety is projective. -/
theorem ofPresentation (P : ProjectivePresentation k X) : IsProjective k X :=
  ⟨⟨P⟩⟩

end IsProjective

/-- A projective variety is proper, independently of which presentation witnesses
projectivity. -/
noncomputable instance isProper_of_isProjective [IsProjective k X] :
    IsProper (X ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨P⟩ := IsProjective.presentation (k := k) (X := X)
  exact P.isProper_structureMorphism

end Variety

end AlgebraicGeometry
