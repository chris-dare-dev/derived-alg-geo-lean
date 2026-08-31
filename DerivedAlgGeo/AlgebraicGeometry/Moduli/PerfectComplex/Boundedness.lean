/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Presheaf
import DerivedAlgGeo.CategoryTheory.Moduli.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FiniteType

/-!
# Finite-type boundedness witnesses for relative-perfect complexes

This file replaces a caller-selected boundedness proposition by geometric
data.  A witness consists of an actual scheme over the base whose structure
morphism is locally of finite type and quasi-compact, a universally-gluable
relative-perfect family on that scheme, and geometric fibers covering the
chosen subproblem up to isomorphism.

The current derived-pullback API does not yet construct the geometric fiber
of every relative-perfect family along every residue-field morphism.  Thus a
witness records those fibers explicitly and its coverage statement compares
objects only after an equality of the actual residue-field base changes.  The
zero family below inhabits this interface without postulating a general
base-change theorem.  General semistable-object boundedness and Quot
parameter spaces remain later results.
-/

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

/-- Two fiberwise, replete loci used to state a relative-perfect boundedness
problem. `familyLocus` specifies which total families are admitted, while
`geometricLocus` specifies the objects that a finite-type parameter family
must cover.

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

/-- Data sufficient to transport a boundedness witness from `P` to `Q`.
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

/-- An actual finite-type parameter family covering a selected relative-
perfect moduli boundedness problem. -/
structure FiniteTypeBoundednessWitness {S : Scheme.{u}}
    (P : RelativePerfectModuliSelector S) where
  /-- The parameter scheme with its structure morphism to `S`. -/
  parameter : SchemeBaseChange S
  /-- The structure morphism is locally of finite type and quasi-compact. -/
  finiteType : IsFiniteTypeBaseChange parameter
  /-- The universal relative-perfect, universally-gluable family. -/
  universalFamily : RelativePerfectModuliFiber parameter
  /-- The universal family belongs to the selected family locus. -/
  universalFamily_mem : P.familyLocus parameter universalFamily
  /-- A chosen geometric fiber over every point of the parameter scheme. -/
  geometricFiber (x : parameter.left) :
    RelativePerfectModuliFiber (parameter.residue x)
  /-- Every selected geometric object occurs as one of the chosen fibers, up
  to an isomorphism in the relative-perfect moduli groupoid. -/
  covers {T : SchemeBaseChange S} (E : RelativePerfectModuliFiber T) :
    P.geometricLocus T E →
      ∃ (x : parameter.left) (h : T = parameter.residue x),
        Nonempty (castRelativePerfectModuliObject h E ≅ geometricFiber x)

namespace FiniteTypeBoundednessWitness

variable {S : Scheme.{u}}
  {P Q : RelativePerfectModuliSelector S}

/-- Boundedness is monotone under enlargement of the allowed family class
and restriction of the geometric target. -/
def monotone (W : FiniteTypeBoundednessWitness P)
    (h : P.MonotoneTo Q) : FiniteTypeBoundednessWitness Q where
  parameter := W.parameter
  finiteType := W.finiteType
  universalFamily := W.universalFamily
  universalFamily_mem := h.familyLocus W.universalFamily_mem
  geometricFiber := W.geometricFiber
  covers E hE := W.covers E (h.geometricLocus hE)

end FiniteTypeBoundednessWitness

/-- The geometric boundedness problem attached to relative-perfect moduli
selectors. Its predicate is existence of actual finite-type parameter
data, rather than a caller-chosen proposition. -/
def relativePerfectGeometricBoundednessProblem (S : Scheme.{u}) :
    BoundednessProblem (RelativePerfectModuliSelector S) where
  IsBounded P := Nonempty (FiniteTypeBoundednessWitness P)

/-- Finite-type witnesses for every selected locus selector discharge the
boundedness clause of Definition 21.15(5). -/
theorem universalRelativePerfectBoundedness_of_witnesses
    (S : Scheme.{u})
    (h : ∀ P : RelativePerfectModuliSelector S,
      Nonempty (FiniteTypeBoundednessWitness P)) :
    UniversalBoundedness (relativePerfectGeometricBoundednessProblem S) :=
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
    {S : Scheme.{u}} (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] :
    (zeroRelativePerfectModuliSelector S).familyLocus T
      (relativePerfectZeroObject T) :=
  schemeQuasicoherentDerivedCategory_zero_obj_isZero T.left

/-- The chosen zero fiber over a point of the identity parameter scheme. -/
def zeroRelativePerfectGeometricFiber (S : Scheme.{u}) (x : S) :
    RelativePerfectModuliFiber
      ((identityRelativePerfectBaseChange S).residue x) := by
  letI : IsLocallyNoetherian
      ((identityRelativePerfectBaseChange S).residue x).left := by
    change IsLocallyNoetherian (Spec (S.residueField x))
    infer_instance
  exact relativePerfectZeroObject
    ((identityRelativePerfectBaseChange S).residue x)

/-- The identity parameter scheme and zero universal family form an actual
finite-type boundedness witness. -/
def zeroFiniteTypeBoundednessWitness (S : Scheme.{u})
    [IsLocallyNoetherian S] :
    FiniteTypeBoundednessWitness (zeroRelativePerfectModuliSelector S) where
  parameter := identityRelativePerfectBaseChange S
  finiteType := by
    change LocallyOfFiniteType (𝟙 S) ∧ QuasiCompact (𝟙 S)
    exact ⟨by infer_instance, by infer_instance⟩
  universalFamily := by
    letI : IsLocallyNoetherian (Over.mk (𝟙 S)).left := by
      change IsLocallyNoetherian S
      infer_instance
    change RelativePerfectModuliFiber (Over.mk (𝟙 S))
    exact relativePerfectZeroObject (Over.mk (𝟙 S))
  universalFamily_mem := by
    letI : IsLocallyNoetherian (Over.mk (𝟙 S)).left := by
      change IsLocallyNoetherian S
      infer_instance
    change IsZero ((relativePerfectModuliForget (Over.mk (𝟙 S))).obj
      (relativePerfectZeroObject (Over.mk (𝟙 S))))
    exact relativePerfectZeroObject_mem_zeroFamilyLocus (Over.mk (𝟙 S))
  geometricFiber := zeroRelativePerfectGeometricFiber S
  covers E hE := by
    obtain ⟨x, hT, hzero⟩ := hE
    refine ⟨x, hT, ?_⟩
    cases hT
    refine ⟨Core.isoMk ?_⟩
    letI : IsLocallyNoetherian
        ((identityRelativePerfectBaseChange S).residue x).left := by
      change IsLocallyNoetherian (Spec (S.residueField x))
      infer_instance
    let Z := zeroRelativePerfectGeometricFiber S x
    have hZ : IsZero ((relativePerfectModuliForget
        ((identityRelativePerfectBaseChange S).residue x)).obj Z) := by
      dsimp [Z, zeroRelativePerfectGeometricFiber]
      exact schemeQuasicoherentDerivedCategory_zero_obj_isZero _
    let eDerived := IsZero.iso hzero hZ
    let eDqc := ObjectProperty.isoMk
      (schemeQuasicoherentCohomology
        ((identityRelativePerfectBaseChange S).residue x).left) eDerived
    exact ObjectProperty.isoMk
      (schemeUniversallyGluableRelativePerfect
        ((identityRelativePerfectBaseChange S).residue x).hom) eDqc

/-- The zero selector is geometrically bounded by an inhabited finite-type
witness, not by a constant-true predicate. -/
theorem zeroRelativePerfectModuliSelector_isBounded
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    (relativePerfectGeometricBoundednessProblem S).IsBounded
      (zeroRelativePerfectModuliSelector S) :=
  ⟨zeroFiniteTypeBoundednessWitness S⟩

/-- The supported zero boundedness construction is available after every
change of base whose source is locally Noetherian.  This deliberately does
not claim a general pullback theorem for nonzero universal families. -/
theorem zeroRelativePerfectBoundedness_afterBaseChange
    {S S' : Scheme.{u}} (_ : S' ⟶ S) [IsLocallyNoetherian S'] :
    (relativePerfectGeometricBoundednessProblem S').IsBounded
      (zeroRelativePerfectModuliSelector S') :=
  zeroRelativePerfectModuliSelector_isBounded S'

/-- The Definition 21.15(5) adapter for the single supported zero
subproblem. -/
def zeroRelativePerfectBoundednessProblem (S : Scheme.{u}) :
    BoundednessProblem PUnit where
  IsBounded _ :=
    (relativePerfectGeometricBoundednessProblem S).IsBounded
      (zeroRelativePerfectModuliSelector S)

/-- The supported zero model unconditionally satisfies its honest geometric
boundedness problem on a locally Noetherian base. -/
theorem universalBoundedness_zeroRelativePerfect
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    UniversalBoundedness (zeroRelativePerfectBoundednessProblem S) :=
  fun _ ↦ zeroRelativePerfectModuliSelector_isBounded S

end

end AlgebraicGeometry
