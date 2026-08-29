/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Presheaf
import DerivedAlgGeo.CategoryTheory.Triangulated.Families.Boundedness
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
open CategoryTheory.Triangulated.Families
open CategoryTheory.Triangulated.StabilityCondition.Families

noncomputable section

universe u

/-- A selected relative-perfect moduli subproblem.  `family` specifies which
total families are admitted, while `geometric` specifies the objects that a
finite-type parameter family must cover. -/
structure RelativePerfectModuliSubproblem (S : Scheme.{u}) where
  /-- Admissible total families on every actual base change. -/
  family (T : SchemeBaseChange S) :
    ObjectProperty (RelativePerfectModuliFiber T)
  /-- The selected geometric objects. -/
  geometric (T : SchemeBaseChange S) :
    ObjectProperty (RelativePerfectModuliFiber T)
  /-- Family membership is invariant under isomorphism. -/
  family_iso (T : SchemeBaseChange S) :
    (family T).IsClosedUnderIsomorphisms
  /-- Geometric membership is invariant under isomorphism. -/
  geometric_iso (T : SchemeBaseChange S) :
    (geometric T).IsClosedUnderIsomorphisms

namespace RelativePerfectModuliSubproblem

variable {S : Scheme.{u}}

instance family_isClosedUnderIsomorphisms
    (P : RelativePerfectModuliSubproblem S) (T : SchemeBaseChange S) :
    (P.family T).IsClosedUnderIsomorphisms :=
  P.family_iso T

instance geometric_isClosedUnderIsomorphisms
    (P : RelativePerfectModuliSubproblem S) (T : SchemeBaseChange S) :
    (P.geometric T).IsClosedUnderIsomorphisms :=
  P.geometric_iso T

/-- Data sufficient to transport a boundedness witness from `P` to `Q`.
Admissible families may be enlarged, while the geometric target may be
shrunk. -/
structure MonotoneTo (P Q : RelativePerfectModuliSubproblem S) : Prop where
  /-- Every `P`-family is admitted by `Q`. -/
  family {T : SchemeBaseChange S} {E : RelativePerfectModuliFiber T} :
    P.family T E → Q.family T E
  /-- Every geometric object requested by `Q` was already requested by `P`. -/
  geometric {T : SchemeBaseChange S} {E : RelativePerfectModuliFiber T} :
    Q.geometric T E → P.geometric T E

end RelativePerfectModuliSubproblem

/-- Transport a moduli object across an equality of actual scheme base
changes. -/
def castRelativePerfectModuliObject {S : Scheme.{u}}
    {T U : SchemeBaseChange S} (h : T = U)
    (E : RelativePerfectModuliFiber T) : RelativePerfectModuliFiber U := by
  subst h
  exact E

/-- An actual finite-type parameter family covering a selected relative-
perfect moduli subproblem. -/
structure FiniteTypeBoundednessWitness {S : Scheme.{u}}
    (P : RelativePerfectModuliSubproblem S) where
  /-- The parameter scheme with its structure morphism to `S`. -/
  parameter : SchemeBaseChange S
  /-- The structure morphism is locally of finite type and quasi-compact. -/
  finiteType : IsFiniteTypeBaseChange parameter
  /-- The universal relative-perfect, universally-gluable family. -/
  universalFamily : RelativePerfectModuliFiber parameter
  /-- The universal family belongs to the selected family subfunctor. -/
  universalFamily_mem : P.family parameter universalFamily
  /-- A chosen geometric fiber over every point of the parameter scheme. -/
  geometricFiber (x : parameter.left) :
    RelativePerfectModuliFiber (parameter.residue x)
  /-- Every selected geometric object occurs as one of the chosen fibers, up
  to an isomorphism in the relative-perfect moduli groupoid. -/
  covers {T : SchemeBaseChange S} (E : RelativePerfectModuliFiber T) :
    P.geometric T E →
      ∃ (x : parameter.left) (h : T = parameter.residue x),
        Nonempty (castRelativePerfectModuliObject h E ≅ geometricFiber x)

namespace FiniteTypeBoundednessWitness

variable {S : Scheme.{u}}
  {P Q : RelativePerfectModuliSubproblem S}

/-- Boundedness is monotone under enlargement of the allowed family class
and restriction of the geometric target. -/
def monotone (W : FiniteTypeBoundednessWitness P)
    (h : P.MonotoneTo Q) : FiniteTypeBoundednessWitness Q where
  parameter := W.parameter
  finiteType := W.finiteType
  universalFamily := W.universalFamily
  universalFamily_mem := h.family W.universalFamily_mem
  geometricFiber := W.geometricFiber
  covers E hE := W.covers E (h.geometric hE)

end FiniteTypeBoundednessWitness

/-- The geometric boundedness problem attached to relative-perfect moduli
subproblems.  Its predicate is existence of actual finite-type parameter
data, rather than a caller-chosen proposition. -/
def relativePerfectGeometricBoundednessProblem (S : Scheme.{u}) :
    BoundednessProblem (RelativePerfectModuliSubproblem S) where
  IsBounded P := Nonempty (FiniteTypeBoundednessWitness P)

/-- Finite-type witnesses for every selected subproblem discharge the
boundedness clause of Definition 21.15(5). -/
theorem universalRelativePerfectBoundedness_of_witnesses
    (S : Scheme.{u})
    (h : ∀ P : RelativePerfectModuliSubproblem S,
      Nonempty (FiniteTypeBoundednessWitness P)) :
    UniversalBoundedness (relativePerfectGeometricBoundednessProblem S) :=
  h

/-! ## A nonempty finite-type model: the zero family -/

/-- The identity scheme base change, used as the parameter scheme for the
zero family. -/
def identityRelativePerfectBaseChange (S : Scheme.{u}) :
    SchemeBaseChange S :=
  Over.mk (𝟙 S)

/-- The supported zero subproblem.  Total families must be zero after
forgetting to the ambient derived category.  Its geometric objects are zero
objects over residue-field base changes of actual points of `S`. -/
def zeroRelativePerfectModuliSubproblem (S : Scheme.{u}) :
    RelativePerfectModuliSubproblem S where
  family T E := IsZero ((relativePerfectModuliForget T).obj E)
  geometric T E :=
    ∃ (x : S) (h : T = (identityRelativePerfectBaseChange S).residue x),
      IsZero ((relativePerfectModuliForget T).obj E)
  family_iso T := by
    constructor
    intro E F e hE
    exact hE.of_iso ((relativePerfectModuliForget T).mapIso e.symm)
  geometric_iso T := by
    constructor
    intro E F e hE
    obtain ⟨x, hT, hzero⟩ := hE
    exact ⟨x, hT,
      hzero.of_iso ((relativePerfectModuliForget T).mapIso e.symm)⟩

/-- The universal zero family is a selected family. -/
theorem relativePerfectZeroObject_mem_zeroFamily
    {S : Scheme.{u}} (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] :
    (zeroRelativePerfectModuliSubproblem S).family T
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
    FiniteTypeBoundednessWitness (zeroRelativePerfectModuliSubproblem S) where
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
    exact relativePerfectZeroObject_mem_zeroFamily (Over.mk (𝟙 S))
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

/-- The zero subproblem is geometrically bounded by an inhabited finite-type
witness, not by a constant-true predicate. -/
theorem zeroRelativePerfectModuliSubproblem_isBounded
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    (relativePerfectGeometricBoundednessProblem S).IsBounded
      (zeroRelativePerfectModuliSubproblem S) :=
  ⟨zeroFiniteTypeBoundednessWitness S⟩

/-- The supported zero boundedness construction is available after every
change of base whose source is locally Noetherian.  This deliberately does
not claim a general pullback theorem for nonzero universal families. -/
theorem zeroRelativePerfectBoundedness_afterBaseChange
    {S S' : Scheme.{u}} (_ : S' ⟶ S) [IsLocallyNoetherian S'] :
    (relativePerfectGeometricBoundednessProblem S').IsBounded
      (zeroRelativePerfectModuliSubproblem S') :=
  zeroRelativePerfectModuliSubproblem_isBounded S'

/-- The Definition 21.15(5) adapter for the single supported zero
subproblem. -/
def zeroRelativePerfectBoundednessProblem (S : Scheme.{u}) :
    BoundednessProblem PUnit where
  IsBounded _ :=
    (relativePerfectGeometricBoundednessProblem S).IsBounded
      (zeroRelativePerfectModuliSubproblem S)

/-- The supported zero model unconditionally satisfies its honest geometric
boundedness problem on a locally Noetherian base. -/
theorem universalBoundedness_zeroRelativePerfect
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    UniversalBoundedness (zeroRelativePerfectBoundednessProblem S) :=
  fun _ ↦ zeroRelativePerfectModuliSubproblem_isBounded S

end

end AlgebraicGeometry
