/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Algebraic

/-!
# Pointwise big-Zariski presentations of selected relative-perfect moduli problems

This file connects the relative-perfect and pointwise finite-type cover layers
to the pointwise stack-presentation layer without postulating an Artin
representability theorem.  A `PointwiseRelativePerfectZariskiPresentation`
contains pointwise big-Zariski stack data over the base and equivalences from
its geometric fibers to the selected full subgroupoids of universally-gluable
relative-perfect complexes.  The fibre identifications and the presentation
are pointwise, so it is not an algebraic-stack structure, and the algebraicity
of the moduli of universally gluable relative-perfect complexes is not claimed.

The covered refinement `PointwiseCoveredRelativePerfectZariskiPresentation`
turns the universal family of a `PointwiseFiniteTypeCover` into an actual
object of the corresponding stack fiber.  Pointwise open relative-perfect
presentations retain an actual pointwise open immersion and a commuting
structural triangle.

## Main definitions

* `PointwiseRelativePerfectZariskiPresentation` — a pointwise big-Zariski
  presentation whose fibers are identified with the selected relative-perfect
  moduli groupoids.
* `PointwiseCoveredRelativePerfectZariskiPresentation` — such a presentation
  together with a `PointwiseFiniteTypeCover`.
* `PointwiseRelativePerfectOpenZariskiPresentation` — an ambient and an open
  presentation with a pointwise open immersion between them.
* `zeroPointwiseRelativePerfectZariskiPresentation`,
  `zeroPointwiseCoveredRelativePerfectZariskiPresentation` — the supported zero
  subproblem.

## Main results

* `PointwiseRelativePerfectZariskiPresentation.pointwiseLocallyOfFinitePresentation`
  — the structure morphism of a presentation is pointwise locally of finite
  presentation.

## Implementation notes

The supported zero subproblem is constructed explicitly: the identity stack
over a locally Noetherian base has contractible fibers, as does the full
groupoid of zero relative-perfect objects.  This is a genuine pointwise covered
big-Zariski presentation, but it is not claimed to be an algebraic stack or
the full relative-perfect moduli stack.

## References

This file builds on `Moduli/PerfectComplex/Boundedness.lean` and
`Stacks/Algebraic.lean`.

## Tags

relative-perfect complex, moduli, stack presentation, Zariski topology
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open Opposite

noncomputable section

universe u

namespace RelativePerfectModuliSelector

variable {S : Scheme.{u}}

/-- The full subgroupoid selected inside one relative-perfect moduli fiber.
This construction is fiberwise only: it does not provide transition functors
and is not itself a subprestack. -/
abbrev Fiber (P : RelativePerfectModuliSelector S)
    (T : SchemeBaseChange S) :=
  (P.familyLocus T).FullSubcategory

instance fiber_isGroupoid (P : RelativePerfectModuliSelector S)
    (T : SchemeBaseChange S) : IsGroupoid (P.Fiber T) := by
  change IsGroupoid (InducedCategory (RelativePerfectModuliFiber T)
    ObjectProperty.FullSubcategory.obj)
  infer_instance

end RelativePerfectModuliSelector

namespace PointwiseFiniteTypeCover

variable {S : Scheme.{u}} {P : RelativePerfectModuliSelector S}

/-- Regard the universal family of a pointwise finite-type cover as an object
of the selected full moduli subgroupoid. -/
def universalObject (W : PointwiseFiniteTypeCover P) : P.Fiber W.parameter :=
  ⟨W.universalFamily, W.universalFamily_mem⟩

end PointwiseFiniteTypeCover

/-- A pointwise big-Zariski presentation of a selected relative-perfect moduli
problem.

For every locally Noetherian base change `T ⟶ S`, the fiber of the actual
structure morphism over that map is equivalent to the selected full
subgroupoid of universally-gluable relative-perfect complexes on `T`.
Restricting this field to the currently supported locally Noetherian locus
keeps the unresolved arbitrary-scheme Dqc comparison visible.

The fibre identifications and the presentation are pointwise, so this is not
an algebraicity statement for the moduli of universally gluable
relative-perfect complexes. -/
structure PointwiseRelativePerfectZariskiPresentation (S : Scheme.{u})
    (P : RelativePerfectModuliSelector S) where
  /-- The pointwise big-Zariski presentation locally of finite presentation
  over `S`. -/
  presentation : PointwiseZariskiStackPresentationOver S
  /-- Identification of each supported stack fiber with the selected
  relative-perfect moduli groupoid. -/
  fiberEquivalence (T : SchemeBaseChange S) [IsLocallyNoetherian T.left] :
    presentation.structureMorphism.FiberCategory
        (representableZariskiObject T.hom) (Over.mk (𝟙 T.left)) ≌
      P.Fiber T

namespace PointwiseRelativePerfectZariskiPresentation

variable {S : Scheme.{u}} {P : RelativePerfectModuliSelector S}

/-- The pointwise big-Zariski stack presentation underlying a pointwise
relative-perfect presentation. -/
abbrev stack (A : PointwiseRelativePerfectZariskiPresentation S P) :
    PointwiseZariskiStackPresentation :=
  A.presentation.toPointwiseZariskiStackPresentation

/-- The structure morphism underlying a pointwise relative-perfect big-Zariski
presentation is pointwise locally of finite presentation. -/
theorem pointwiseLocallyOfFinitePresentation
    (A : PointwiseRelativePerfectZariskiPresentation S P) :
    StackMorphism.IsPointwiseLocallyOfFinitePresentation
      A.presentation.structureMorphism :=
  A.presentation.pointwiseLocallyOfFinitePresentation

end PointwiseRelativePerfectZariskiPresentation

/-- A pointwise covered big-Zariski presentation co-locates a
`PointwiseFiniteTypeCover` with the pointwise stack presentation of the same
selected relative-perfect moduli problem.

The fibre identifications, the presentation and the cover are all pointwise,
so this is neither an algebraicity nor a boundedness statement for the moduli
of universally gluable relative-perfect complexes. -/
structure PointwiseCoveredRelativePerfectZariskiPresentation (S : Scheme.{u})
    (P : RelativePerfectModuliSelector S)
    extends PointwiseRelativePerfectZariskiPresentation S P where
  /-- The finite-type parameter scheme and its universal family. -/
  cover : PointwiseFiniteTypeCover P

namespace PointwiseCoveredRelativePerfectZariskiPresentation

variable {S : Scheme.{u}} {P : RelativePerfectModuliSelector S}
  (A : PointwiseCoveredRelativePerfectZariskiPresentation S P)

/-- The universal family of the cover, lifted through the fiber equivalence to
an actual object of the big-Zariski stack over the parameter scheme. -/
def universalStackObject [IsLocallyNoetherian A.cover.parameter.left] :
    A.presentation.structureMorphism.FiberCategory
      (representableZariskiObject A.cover.parameter.hom)
      (Over.mk (𝟙 A.cover.parameter.left)) :=
  (A.fiberEquivalence A.cover.parameter).inverse.obj
    A.cover.universalObject

/-- The lifted stack object realizes precisely the cover's universal
relative-perfect family. -/
def universalFamilyIso [IsLocallyNoetherian A.cover.parameter.left] :
    (A.fiberEquivalence A.cover.parameter).functor.obj
        A.universalStackObject ≅
      A.cover.universalObject :=
  (A.fiberEquivalence A.cover.parameter).counitIso.app
    A.cover.universalObject

end PointwiseCoveredRelativePerfectZariskiPresentation

/-- A pointwise open relative-perfect presentation keeps both moduli
interpretations, a pointwise open immersion of their big-Zariski stacks, and
the commuting triangle over the base. `familyLocus_le` states that the open
fiberwise locus selects only objects of the ambient problem.

The fibre identifications, the presentations and the open immersion are
pointwise, so this is not an algebraicity statement for the moduli of
universally gluable relative-perfect complexes. -/
structure PointwiseRelativePerfectOpenZariskiPresentation (S : Scheme.{u})
    (ambientProblem openProblem : RelativePerfectModuliSelector S) where
  /-- Pointwise big-Zariski presentation of the ambient selected problem. -/
  ambient : PointwiseRelativePerfectZariskiPresentation S ambientProblem
  /-- Pointwise big-Zariski presentation of the open selected problem. -/
  openPresentation : PointwiseRelativePerfectZariskiPresentation S openProblem
  /-- The open family locus is contained in the ambient fiberwise locus. -/
  familyLocus_le {T : SchemeBaseChange S} {E : RelativePerfectModuliFiber T} :
    openProblem.familyLocus T E → ambientProblem.familyLocus T E
  /-- The actual morphism from the open stack to the ambient stack. -/
  inclusion : StackMorphism
    openPresentation.stack.toStackInGroupoids
    ambient.stack.toStackInGroupoids
  /-- Every scheme pointwise representing a fiber of the inclusion is an open
  subscheme of the test scheme. -/
  isPointwiseOpenImmersion : StackMorphism.IsPointwiseOpenImmersion inclusion
  /-- The inclusion commutes with the actual structure morphisms to `S`. -/
  overBase (T : Scheme.{u}) :
    inclusion.app T ⋙ ambient.presentation.structureMorphism.app T ≅
      openPresentation.presentation.structureMorphism.app T

/-! ## The supported zero pointwise presentation -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable instance identityFiberArrowUnique {S : Scheme.{u}}
    (T : SchemeBaseChange S) :
    Unique (Over.mk (𝟙 T.left) ⟶
      Over.mk (pullback.snd (𝟙 S) T.hom)) := by
  let h : T.left ⟶ pullback (𝟙 S) T.hom :=
    pullback.lift T.hom (𝟙 T.left) (Category.id_comp T.hom).symm
  let sndIso : pullback (𝟙 S) T.hom ≅ T.left :=
    { hom := pullback.snd (𝟙 S) T.hom
      inv := h
      hom_inv_id := by
        apply pullback.hom_ext
        · change pullback.snd (𝟙 S) T.hom ≫
            (h ≫ pullback.fst (𝟙 S) T.hom) =
              pullback.fst (𝟙 S) T.hom
          dsimp [h]
          rw [pullback.lift_fst]
          simpa using (pullback.condition (f := 𝟙 S) (g := T.hom)).symm
        · change pullback.snd (𝟙 S) T.hom ≫
            (h ≫ pullback.snd (𝟙 S) T.hom) =
              pullback.snd (𝟙 S) T.hom
          dsimp [h]
          rw [pullback.lift_snd]
          simp
      inv_hom_id := by
        dsimp [h]
        exact pullback.lift_snd (f := 𝟙 S) (g := T.hom)
          T.hom (𝟙 T.left)
          (Category.id_comp T.hom).symm }
  let e : Over.mk (𝟙 T.left) ≅
      Over.mk (pullback.snd (𝟙 S) T.hom) :=
    (Over.isoMk sndIso (by
      change pullback.snd (𝟙 S) T.hom ≫ 𝟙 T.left =
        pullback.snd (𝟙 S) T.hom
      simp)).symm
  let h : IsTerminal (Over.mk (pullback.snd (𝟙 S) T.hom)) :=
    IsTerminal.ofIso Over.mkIdTerminal e
  exact { default := h.from _
          uniq := fun a ↦ h.hom_ext a (h.from _) }

private def identityStackFiberEquivPUnit {S : Scheme.{u}}
    (T : SchemeBaseChange S) :
    (representableZariskiStackMap (𝟙 S)).FiberCategory
        (representableZariskiObject T.hom) (Over.mk (𝟙 T.left)) ≌
      Discrete PUnit.{u + 1} := by
  let R := RepresentableZariskiStackMap.pointwiseFiberRepresentation
    (𝟙 S) (representableZariskiObject T.hom)
  letI : Unique (Over.mk (𝟙 T.left) ⟶ R.representing) := by
    change Unique (Over.mk (𝟙 T.left) ⟶
      Over.mk (pullback.snd (𝟙 S) T.hom))
    infer_instance
  exact (R.fiberEquivalence (Over.mk (𝟙 T.left))).symm.trans
    (Discrete.equivalence (Equiv.equivPUnit _))

private def zeroRelativePerfectFiberEquivPUnit {S : Scheme.{u}}
    (T : SchemeBaseChange S) :
    (zeroRelativePerfectModuliSelector S).Fiber T ≌
      Discrete PUnit.{u + 1} := by
  apply Nonempty.some
  rw [equiv_punit_iff_unique]
  constructor
  · exact ⟨⟨relativePerfectZeroObject T,
      relativePerfectZeroObject_mem_zeroFamilyLocus T⟩⟩
  · intro E F
    let eDerived := IsZero.iso E.property F.property
    let eDqc := ObjectProperty.isoMk
      (schemeQuasicoherentCohomology T.left) eDerived
    let eRelativePerfect := ObjectProperty.isoMk
      (schemeUniversallyGluableRelativePerfect T.hom) eDqc
    let f : E ⟶ F := ObjectProperty.homMk
      (Core.isoMk eRelativePerfect).hom
    have homSubsingleton : Subsingleton (E ⟶ F) := by
      letI : (relativePerfectModuliForget T).Faithful := by
        dsimp [relativePerfectModuliForget, relativePerfectForget]
        infer_instance
      constructor
      intro a b
      apply ObjectProperty.hom_ext
      apply (relativePerfectModuliForget T).map_injective
      exact E.property.eq_of_src _ _
    exact ⟨@uniqueOfSubsingleton _ homSubsingleton f⟩

/-- The zero relative-perfect subproblem has a pointwise big-Zariski
presentation: the identity stack over `S`.  Its fibers and the groupoids of
selected zero objects are both proved contractible. -/
def zeroPointwiseRelativePerfectZariskiPresentation (S : Scheme.{u}) :
    PointwiseRelativePerfectZariskiPresentation S
      (zeroRelativePerfectModuliSelector S) where
  presentation := representablePointwiseZariskiStackPresentationOver (𝟙 S)
  fiberEquivalence T :=
    (identityStackFiberEquivPUnit T).trans
      (zeroRelativePerfectFiberEquivPUnit T).symm

/-- The identity parameter scheme and universal zero family give the supported
zero pointwise big-Zariski presentation a pointwise finite-type cover. -/
def zeroPointwiseCoveredRelativePerfectZariskiPresentation
    (S : Scheme.{u}) :
    PointwiseCoveredRelativePerfectZariskiPresentation S
      (zeroRelativePerfectModuliSelector S) where
  toPointwiseRelativePerfectZariskiPresentation :=
    zeroPointwiseRelativePerfectZariskiPresentation S
  cover := zeroPointwiseFiniteTypeCover S

/-- A concrete positive-dimensional supported case: `Spec ℤ` carries the
pointwise covered big-Zariski presentation of its zero relative-perfect
subproblem. -/
def integerZeroPointwiseCoveredRelativePerfectZariskiPresentation :
    PointwiseCoveredRelativePerfectZariskiPresentation
      (Spec (.of ℤ))
      (zeroRelativePerfectModuliSelector (Spec (.of ℤ))) :=
  zeroPointwiseCoveredRelativePerfectZariskiPresentation (Spec (.of ℤ))

end

end AlgebraicGeometry
