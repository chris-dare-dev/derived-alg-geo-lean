/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Presheaf
import DerivedAlgGeo.CategoryTheory.Moduli.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FiniteType

/-!
# Pointwise finite-type covers for relative-perfect complexes

A `PointwiseFiniteTypeCover` consists of an actual scheme over the base whose
structure morphism is locally of finite type and quasi-compact, a
universally-gluable relative-perfect family on that scheme, and objects
chosen over the residue fields of its points, covering the selected geometric
objects up to isomorphism.

## Main definitions

* `RelativePerfectModuliSelector` — the admitted families and the selected
  geometric objects of a relative-perfect moduli problem.
* `PointwiseFiniteTypeCover` — a finite-type parameter scheme with a universal
  family, and chosen objects over its residue fields covering the selected
  geometric objects.
* `relativePerfectPointwiseCoverProblem` — the predicate that a selector has a
  `PointwiseFiniteTypeCover`.
* `zeroRelativePerfectModuliSelector`, `zeroPointwiseFiniteTypeCover` — the
  supported zero selector and its cover.

## Main results

* `zeroRelativePerfectModuliSelector_hasPointwiseCover` — the zero selector has
  a pointwise finite-type cover.
* `universalBoundedness_zeroRelativePerfectPointwiseCoverProblem` — the zero
  model satisfies its pointwise cover problem.

## Implementation notes

The chosen objects are not tied to the family: the current derived-pullback
API does not construct the fiber of a relative-perfect family along a
non-flat residue-field morphism.  So a cover is not boundedness in the sense
of Definition 9.4 of arXiv:1902.08184v4, which asks every selected object to
be a fiber of one family on a finite-type scheme, and nothing here
discharges the boundedness clause of Definition 21.15(5) there.  The zero
family below inhabits this interface without postulating a base-change
theorem.  Bounded families, semistable-object boundedness and Quot parameter
spaces are not defined here.

## References

* arXiv:1902.08184v4, Definition 9.4 and Definition 21.15

## Tags

relative-perfect complex, moduli, finite type, residue field
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Moduli
open CategoryTheory.Triangulated.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

noncomputable section

universe u

/-- Two fiberwise, replete loci used to state a relative-perfect pointwise
cover problem. `familyLocus` specifies which total families are admitted,
while `geometricLocus` specifies the objects that a finite-type cover must
reach.

This is deliberately a selector, not a subprestack: it supplies neither an
ambient pseudofunctor nor preservation under restriction. A genuine
subprestack must separately use `Pseudofunctor.ObjectProperty` and prove
`IsClosedUnderMapObj`. -/
structure RelativePerfectModuliSelector (S : Scheme.{u}) where
  /-- Admissible total families on every actual base change. -/
  familyLocus (T : SchemeBaseChange S) :
    ObjectProperty (RelativePerfectModuliFiber T)
  /-- The selected geometric objects. -/
  geometricLocus (T : SchemeBaseChange S) :
    ObjectProperty (RelativePerfectModuliFiber T)
  /-- Family membership is invariant under isomorphism. -/
  familyLocus_iso (T : SchemeBaseChange S) :
    (familyLocus T).IsClosedUnderIsomorphisms
  /-- Geometric membership is invariant under isomorphism. -/
  geometricLocus_iso (T : SchemeBaseChange S) :
    (geometricLocus T).IsClosedUnderIsomorphisms

namespace RelativePerfectModuliSelector

variable {S : Scheme.{u}}

instance familyLocus_isClosedUnderIsomorphisms
    (P : RelativePerfectModuliSelector S) (T : SchemeBaseChange S) :
    (P.familyLocus T).IsClosedUnderIsomorphisms :=
  P.familyLocus_iso T

instance geometricLocus_isClosedUnderIsomorphisms
    (P : RelativePerfectModuliSelector S) (T : SchemeBaseChange S) :
    (P.geometricLocus T).IsClosedUnderIsomorphisms :=
  P.geometricLocus_iso T

/-- Data sufficient to transport a pointwise finite-type cover from `P` to `Q`.
Admissible families may be enlarged, while the geometric target may be
shrunk. -/
structure MonotoneTo (P Q : RelativePerfectModuliSelector S) : Prop where
  /-- Every `P`-family is admitted by `Q`. -/
  familyLocus {T : SchemeBaseChange S} {E : RelativePerfectModuliFiber T} :
    P.familyLocus T E → Q.familyLocus T E
  /-- Every geometric object requested by `Q` was already requested by `P`. -/
  geometricLocus {T : SchemeBaseChange S} {E : RelativePerfectModuliFiber T} :
    Q.geometricLocus T E → P.geometricLocus T E

end RelativePerfectModuliSelector

/-- Transport a moduli object across an equality of actual scheme base
changes. -/
def castRelativePerfectModuliObject {S : Scheme.{u}}
    {T U : SchemeBaseChange S} (h : T = U)
    (E : RelativePerfectModuliFiber T) : RelativePerfectModuliFiber U := by
  subst h
  exact E

/-- A finite-type parameter scheme with a universal family, and an object
chosen over the residue field of each of its points, such that every selected
geometric object is isomorphic to one of the chosen objects.

The fields impose no relation between `universalFamily` and `geometricFiber`:
`covers` holds whenever `geometricFiber x` is chosen to be the selected object
over `parameter.residue x`, whatever `universalFamily` is. This is not
boundedness in the sense of arXiv:1902.08184v4, Definition 9.4, which asks
every selected object to be a fibre of one family on a finite-type scheme.
Tying `geometricFiber x` to `universalFamily` needs derived pullback along
non-flat residue maps, which is not available; bounded families are not
defined here. -/
structure PointwiseFiniteTypeCover {S : Scheme.{u}}
    (P : RelativePerfectModuliSelector S) where
  /-- The parameter scheme with its structure morphism to `S`. -/
  parameter : SchemeBaseChange S
  /-- The structure morphism is locally of finite type and quasi-compact. -/
  finiteType : IsFiniteTypeBaseChange parameter
  /-- The universal relative-perfect, universally-gluable family. -/
  universalFamily : RelativePerfectModuliFiber parameter
  /-- The universal family belongs to the selected family locus. -/
  universalFamily_mem : P.familyLocus parameter universalFamily
  /-- An object chosen over the residue field of every point of the parameter
  scheme, unrelated to `universalFamily`. -/
  geometricFiber (x : parameter.left) :
    RelativePerfectModuliFiber (parameter.residue x)
  /-- Every selected geometric object occurs as one of the chosen objects, up
  to an isomorphism in the relative-perfect moduli groupoid. -/
  covers {T : SchemeBaseChange S} (E : RelativePerfectModuliFiber T) :
    P.geometricLocus T E →
      ∃ (x : parameter.left) (h : T = parameter.residue x),
        Nonempty (castRelativePerfectModuliObject h E ≅ geometricFiber x)

namespace PointwiseFiniteTypeCover

variable {S : Scheme.{u}}
  {P Q : RelativePerfectModuliSelector S}

/-- Pointwise finite-type covers are monotone under enlargement of the
allowed family class and restriction of the geometric target. -/
def monotone (W : PointwiseFiniteTypeCover P)
    (h : P.MonotoneTo Q) : PointwiseFiniteTypeCover Q where
  parameter := W.parameter
  finiteType := W.finiteType
  universalFamily := W.universalFamily
  universalFamily_mem := h.familyLocus W.universalFamily_mem
  geometricFiber := W.geometricFiber
  covers E hE := W.covers E (h.geometricLocus hE)

end PointwiseFiniteTypeCover

/-- The pointwise cover problem attached to relative-perfect moduli selectors:
its predicate is existence of a `PointwiseFiniteTypeCover`.

This is not boundedness in the sense of Definition 9.4 of
arXiv:1902.08184v4, which Definition 21.15(5) there requires. -/
def relativePerfectPointwiseCoverProblem (S : Scheme.{u}) :
    BoundednessProblem (RelativePerfectModuliSelector S) where
  IsBounded P := Nonempty (PointwiseFiniteTypeCover P)

/-- Pointwise finite-type covers for every selector give universal
satisfaction of the pointwise cover problem.

Definition 21.15(5) of arXiv:1902.08184v4 requires boundedness in the sense
of Definition 9.4 there, which this does not provide. -/
theorem universalRelativePerfectPointwiseCover_of_covers
    (S : Scheme.{u})
    (h : ∀ P : RelativePerfectModuliSelector S,
      Nonempty (PointwiseFiniteTypeCover P)) :
    UniversalBoundedness (relativePerfectPointwiseCoverProblem S) :=
  h

/-! ## A nonempty finite-type model: the zero family -/

/-- The identity scheme base change, used as the parameter scheme for the
zero family. -/
def identityRelativePerfectBaseChange (S : Scheme.{u}) :
    SchemeBaseChange S :=
  Over.mk (𝟙 S)

/-- The supported zero selector. Total families must be zero after
forgetting to the ambient derived category.  Its geometric objects are zero
objects over residue-field base changes of actual points of `S`. -/
def zeroRelativePerfectModuliSelector (S : Scheme.{u}) :
    RelativePerfectModuliSelector S where
  familyLocus T E := IsZero ((relativePerfectModuliForget T).obj E)
  geometricLocus T E :=
    ∃ (x : S) (h : T = (identityRelativePerfectBaseChange S).residue x),
      IsZero ((relativePerfectModuliForget T).obj E)
  familyLocus_iso T := by
    constructor
    intro E F e hE
    exact hE.of_iso ((relativePerfectModuliForget T).mapIso e.symm)
  geometricLocus_iso T := by
    constructor
    intro E F e hE
    obtain ⟨x, hT, hzero⟩ := hE
    exact ⟨x, hT,
      hzero.of_iso ((relativePerfectModuliForget T).mapIso e.symm)⟩

/-- The universal zero family is a selected family. -/
theorem relativePerfectZeroObject_mem_zeroFamilyLocus
    {S : Scheme.{u}} (T : SchemeBaseChange S) :
    (zeroRelativePerfectModuliSelector S).familyLocus T
      (relativePerfectZeroObject T) :=
  SchemeQuasicoherentDerivedCategory.zero_obj_isZero T.left

/-- The chosen zero fiber over a point of the identity parameter scheme. -/
def zeroRelativePerfectGeometricFiber (S : Scheme.{u}) (x : S) :
    RelativePerfectModuliFiber
      ((identityRelativePerfectBaseChange S).residue x) :=
  relativePerfectZeroObject
    ((identityRelativePerfectBaseChange S).residue x)

/-- The identity parameter scheme and zero universal family form a pointwise
finite-type cover of the zero selector. -/
def zeroPointwiseFiniteTypeCover (S : Scheme.{u}) :
    PointwiseFiniteTypeCover (zeroRelativePerfectModuliSelector S) where
  parameter := identityRelativePerfectBaseChange S
  finiteType := by
    change LocallyOfFiniteType (𝟙 S) ∧ QuasiCompact (𝟙 S)
    exact ⟨by infer_instance, by infer_instance⟩
  universalFamily := relativePerfectZeroObject (Over.mk (𝟙 S))
  universalFamily_mem := by
    change IsZero ((relativePerfectModuliForget (Over.mk (𝟙 S))).obj
      (relativePerfectZeroObject (Over.mk (𝟙 S))))
    exact relativePerfectZeroObject_mem_zeroFamilyLocus (Over.mk (𝟙 S))
  geometricFiber := zeroRelativePerfectGeometricFiber S
  covers E hE := by
    obtain ⟨x, hT, hzero⟩ := hE
    refine ⟨x, hT, ?_⟩
    cases hT
    refine ⟨Core.isoMk ?_⟩
    let Z := zeroRelativePerfectGeometricFiber S x
    have hZ : IsZero ((relativePerfectModuliForget
        ((identityRelativePerfectBaseChange S).residue x)).obj Z) := by
      dsimp [Z, zeroRelativePerfectGeometricFiber]
      exact SchemeQuasicoherentDerivedCategory.zero_obj_isZero _
    let eDerived := IsZero.iso hzero hZ
    let eDqc := ObjectProperty.isoMk
      (schemeQuasicoherentCohomology
        ((identityRelativePerfectBaseChange S).residue x).left) eDerived
    exact ObjectProperty.isoMk
      (schemeUniversallyGluableRelativePerfect
        ((identityRelativePerfectBaseChange S).residue x).hom) eDqc

/-- The zero selector has a pointwise finite-type cover, inhabited rather than
given by a constant-true predicate. -/
theorem zeroRelativePerfectModuliSelector_hasPointwiseCover
    (S : Scheme.{u}) :
    (relativePerfectPointwiseCoverProblem S).IsBounded
      (zeroRelativePerfectModuliSelector S) :=
  ⟨zeroPointwiseFiniteTypeCover S⟩

/-- The supported zero pointwise cover is available after every change of
base.  This deliberately does not claim a general pullback theorem for
nonzero universal families. -/
theorem zeroRelativePerfectPointwiseCover_afterBaseChange
    {S S' : Scheme.{u}} (_ : S' ⟶ S) :
    (relativePerfectPointwiseCoverProblem S').IsBounded
      (zeroRelativePerfectModuliSelector S') :=
  zeroRelativePerfectModuliSelector_hasPointwiseCover S'

/-- The pointwise cover problem of the single supported zero subproblem.

Definition 21.15(5) of arXiv:1902.08184v4 requires boundedness in the sense
of Definition 9.4 there, which this problem does not express. -/
def zeroRelativePerfectPointwiseCoverProblem (S : Scheme.{u}) :
    BoundednessProblem PUnit where
  IsBounded _ :=
    (relativePerfectPointwiseCoverProblem S).IsBounded
      (zeroRelativePerfectModuliSelector S)

/-- The supported zero model unconditionally satisfies its pointwise cover
problem. -/
theorem universalBoundedness_zeroRelativePerfectPointwiseCoverProblem
    (S : Scheme.{u}) :
    UniversalBoundedness (zeroRelativePerfectPointwiseCoverProblem S) :=
  fun _ ↦ zeroRelativePerfectModuliSelector_hasPointwiseCover S

end

end AlgebraicGeometry
