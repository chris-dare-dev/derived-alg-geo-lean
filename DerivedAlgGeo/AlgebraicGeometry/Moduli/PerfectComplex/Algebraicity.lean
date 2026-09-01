/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Algebraic

/-!
# Big-Zariski presentations of selected relative-perfect moduli problems

This file connects the SF8 relative-perfect and boundedness layers to the
SF9 stack-presentation layer without postulating an Artin representability
theorem.  A presentation contains big-Zariski stack data over the base and
equivalences from its geometric fibers to the selected full subgroupoids of
universally-gluable relative-perfect complexes.  It is not an algebraic-stack
structure: fppf or étale descent has not yet been proved.

The bounded refinement turns the universal family of an SF8 finite-type
boundedness witness into an actual object of the corresponding stack fiber.
Open relative-perfect presentations retain an actual representable open
immersion and a commuting structural triangle.

The supported zero subproblem is constructed explicitly: the identity stack
over a locally Noetherian base has contractible fibers, as does the full
groupoid of zero relative-perfect objects.  This is a genuine bounded
big-Zariski presentation, but it is not claimed to be an algebraic stack or
the full relative-perfect moduli stack.
-/

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

namespace FiniteTypeBoundednessWitness

variable {S : Scheme.{u}} {P : RelativePerfectModuliSelector S}

/-- Regard the universal family in a boundedness witness as an object of the
selected full moduli subgroupoid. -/
def universalObject (W : FiniteTypeBoundednessWitness P) : P.Fiber W.parameter :=
  ⟨W.universalFamily, W.universalFamily_mem⟩

end FiniteTypeBoundednessWitness

/-- A big-Zariski presentation of a selected relative-perfect moduli problem.

For every locally Noetherian base change `T ⟶ S`, the fiber of the actual
structure morphism over that map is equivalent to the selected full
subgroupoid of universally-gluable relative-perfect complexes on `T`.
Restricting this field to the currently supported locally Noetherian locus
keeps the unresolved arbitrary-scheme Dqc comparison visible. -/
structure RelativePerfectZariskiPresentation (S : Scheme.{u})
    (P : RelativePerfectModuliSelector S) where
  /-- The big-Zariski presentation locally of finite presentation over `S`. -/
  presentation : ZariskiStackPresentationOver S
  /-- Identification of each supported stack fiber with the selected
  relative-perfect moduli groupoid. -/
  fiberEquivalence (T : SchemeBaseChange S) [IsLocallyNoetherian T.left] :
    presentation.structureMorphism.FiberCategory
        (representableZariskiObject T.hom) (Over.mk (𝟙 T.left)) ≌
      P.Fiber T

namespace RelativePerfectZariskiPresentation

variable {S : Scheme.{u}} {P : RelativePerfectModuliSelector S}

/-- The big-Zariski stack presentation underlying a relative-perfect
presentation. -/
abbrev stack (A : RelativePerfectZariskiPresentation S P) :
    ZariskiStackPresentation :=
  A.presentation.toZariskiStackPresentation

/-- The actual locally-finitely-presented structure morphism underlying a
relative-perfect big-Zariski presentation. -/
theorem locallyOfFinitePresentation
    (A : RelativePerfectZariskiPresentation S P) :
    StackMorphism.IsLocallyOfFinitePresentation
      A.presentation.structureMorphism :=
  A.presentation.locallyOfFinitePresentation

end RelativePerfectZariskiPresentation

/-- A bounded big-Zariski presentation co-locates an actual finite-type SF8
boundedness witness with the SF9 stack presentation of the same selected
relative-perfect moduli problem. -/
structure BoundedRelativePerfectZariskiPresentation (S : Scheme.{u})
    (P : RelativePerfectModuliSelector S)
    extends RelativePerfectZariskiPresentation S P where
  /-- The actual finite-type parameter scheme and its universal family. -/
  boundedness : FiniteTypeBoundednessWitness P

namespace BoundedRelativePerfectZariskiPresentation

variable {S : Scheme.{u}} {P : RelativePerfectModuliSelector S}
  (A : BoundedRelativePerfectZariskiPresentation S P)

/-- The SF8 universal family, lifted through the proved fiber equivalence to
an actual object of the SF9 big-Zariski stack over the parameter scheme. -/
def universalStackObject [IsLocallyNoetherian A.boundedness.parameter.left] :
    A.presentation.structureMorphism.FiberCategory
      (representableZariskiObject A.boundedness.parameter.hom)
      (Over.mk (𝟙 A.boundedness.parameter.left)) :=
  (A.fiberEquivalence A.boundedness.parameter).inverse.obj
    A.boundedness.universalObject

/-- The lifted stack object realizes precisely the boundedness witness's
universal relative-perfect family. -/
def universalFamilyIso [IsLocallyNoetherian A.boundedness.parameter.left] :
    (A.fiberEquivalence A.boundedness.parameter).functor.obj
        A.universalStackObject ≅
      A.boundedness.universalObject :=
  (A.fiberEquivalence A.boundedness.parameter).counitIso.app
    A.boundedness.universalObject

end BoundedRelativePerfectZariskiPresentation

/-- An open relative-perfect presentation keeps both moduli interpretations,
an actual representable open immersion of their big-Zariski stacks, and the
commuting triangle over the base. `familyLocus_le` states that the open
fiberwise locus selects only objects of the ambient problem. -/
structure RelativePerfectOpenZariskiPresentation (S : Scheme.{u})
    (ambientProblem openProblem : RelativePerfectModuliSelector S) where
  /-- Big-Zariski presentation of the ambient selected problem. -/
  ambient : RelativePerfectZariskiPresentation S ambientProblem
  /-- Big-Zariski presentation of the open selected problem. -/
  openPresentation : RelativePerfectZariskiPresentation S openProblem
  /-- The open family locus is contained in the ambient fiberwise locus. -/
  familyLocus_le {T : SchemeBaseChange S} {E : RelativePerfectModuliFiber T} :
    openProblem.familyLocus T E → ambientProblem.familyLocus T E
  /-- The actual morphism from the open stack to the ambient stack. -/
  inclusion : StackMorphism
    openPresentation.stack.toStackInGroupoids
    ambient.stack.toStackInGroupoids
  /-- Every scheme representing a fiber of the inclusion is an open
  subscheme of the test scheme. -/
  isOpenImmersion : StackMorphism.IsOpenImmersion inclusion
  /-- The inclusion commutes with the actual structure morphisms to `S`. -/
  overBase (T : Scheme.{u}) :
    inclusion.app T ⋙ ambient.presentation.structureMorphism.app T ≅
      openPresentation.presentation.structureMorphism.app T

/-! ## The supported zero presentation -/

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
        (Discrete.mk T.hom) (Over.mk (𝟙 T.left)) ≌
      Discrete PUnit.{u + 1} := by
  let R := RepresentableZariskiStackMap.fiberRepresentation
    (𝟙 S) (Discrete.mk T.hom)
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

/-- The zero relative-perfect subproblem has an actual big-Zariski
presentation: the identity stack over `S`.  Its fibers and the groupoids of
selected zero objects are both proved contractible. -/
def zeroRelativePerfectZariskiPresentation (S : Scheme.{u}) :
    RelativePerfectZariskiPresentation S
      (zeroRelativePerfectModuliSelector S) where
  presentation := representableZariskiStackPresentationOver (𝟙 S)
  fiberEquivalence T :=
    (identityStackFiberEquivPUnit T).trans
      (zeroRelativePerfectFiberEquivPUnit T).symm

/-- The identity parameter scheme and universal zero family make the supported
zero big-Zariski presentation genuinely finite-type bounded. -/
def zeroBoundedRelativePerfectZariskiPresentation
    (S : Scheme.{u}) :
    BoundedRelativePerfectZariskiPresentation S
      (zeroRelativePerfectModuliSelector S) where
  toRelativePerfectZariskiPresentation :=
    zeroRelativePerfectZariskiPresentation S
  boundedness := zeroFiniteTypeBoundednessWitness S

/-- A concrete positive-dimensional supported case: `Spec ℤ` carries the
bounded big-Zariski presentation of its zero relative-perfect subproblem. -/
def integerZeroBoundedRelativePerfectZariskiPresentation :
    BoundedRelativePerfectZariskiPresentation
      (Spec (.of ℤ))
      (zeroRelativePerfectModuliSelector (Spec (.of ℤ))) :=
  zeroBoundedRelativePerfectZariskiPresentation (Spec (.of ℤ))

end

end AlgebraicGeometry
