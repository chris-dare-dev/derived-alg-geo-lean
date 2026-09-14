/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.MorphismCone
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.KernelConeNormalization

/-!
# Kernel realizations of natural transformations

Two kernels may present functors through supplied endpoint isomorphisms.  A
`KernelTransformationData` says that a named natural transformation between
those functors is induced by an ordinary kernel morphism.  Its enhanced form
retains a closed representative and chosen dg cone.

The enhancement-independent and enhanced records are deliberately generic:
they know nothing about adjunctions, convolution, twists, or cotwists.  The
enhanced record produces `KernelConeNormalizationData`, so exactness in the
kernel variable yields the corresponding literal, source-natural,
pointwise-distinguished triangle without repeating endpoint transport.

Fullness of the kernel transform is only an explicit sufficient hypothesis
for constructing an ordinary realization.  Selected cocycles and cones are
noncanonical; only the ordinary-to-enhanced-to-ordinary round trip is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vX vY vW vE uX uY uW uE

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory

variable {X : Type uX} {Y : Type uY} {W : Type uW}
  [Category.{vX} X] [Category.{vY} Y] [Category.{vW} W]

/-- An ordinary kernel morphism realizing a named natural transformation
between two functors presented by kernel transforms. -/
structure KernelTransformationData
    (E : Correspondence X Y W) (K L : W) (F G : X ⥤ Y)
    (sourceIso : E.transform K ≅ F) (targetIso : E.transform L ≅ G)
    (α : F ⟶ G) where
  /-- The realizing kernel morphism. -/
  arrow : K ⟶ L
  /-- Its transform is the named transformation after changing both endpoint
  presentations. -/
  transform_arrow :
    E.transformMap arrow = sourceIso.hom ≫ α ≫ targetIso.inv

/-- An enhanced representative and chosen dg cone of a kernel morphism
realizing a named natural transformation. -/
structure KernelTransformationConeData
    (E : Correspondence X Y W) (e : Enhancement.{vE, uE} W)
    (K L : W) (F G : X ⥤ Y)
    (sourceIso : E.transform K ≅ F) (targetIso : E.transform L ≅ G)
    (α : F ⟶ G) where
  /-- A closed representative between the enhancement's chosen endpoint
  lifts. -/
  arrow : cocycles
    (H0.of e.dgCat (e.equiv.inverse.obj K))
    (H0.of e.dgCat (e.equiv.inverse.obj L))
  /-- A chosen dg cone of `arrow`. -/
  cone : e.dgCat
  /-- The cone representability witness. -/
  isCone : IsConeOf arrow.1 cone
  /-- After returning the representative to the ordinary kernel category, its
  transform is the named transformation in the supplied presentations. -/
  transform_arrow :
    E.transformMap
        ((e.equiv.counitIso.app K).inv ≫
          e.equiv.functor.map (H0.homMk (C := e.dgCat) arrow) ≫
          (e.equiv.counitIso.app L).hom) =
      sourceIso.hom ≫ α ≫ targetIso.inv

namespace KernelTransformationData

variable {E : Correspondence X Y W} {K L : W} {F G : X ⥤ Y}
  {sourceIso : E.transform K ≅ F} {targetIso : E.transform L ≅ G}
  {α : F ⟶ G}
  (S : KernelTransformationData E K L F G sourceIso targetIso α)

/-- Ordinary realization data are determined by their kernel arrow. -/
@[ext]
theorem ext
    {S T : KernelTransformationData E K L F G sourceIso targetIso α}
    (h : S.arrow = T.arrow) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Fullness of the kernel transform is sufficient to realize any named
natural transformation with supplied endpoint presentations. -/
noncomputable def ofFull [E.kernelTransform.Full] :
    KernelTransformationData E K L F G sourceIso targetIso α where
  arrow := E.kernelTransform.preimage
    (sourceIso.hom ≫ α ≫ targetIso.inv)
  transform_arrow := E.kernelTransform.map_preimage _

/-- Choose a closed representative and dg cone for an ordinary kernel
realization.  Both choices are noncanonical. -/
noncomputable def toConeData (e : Enhancement.{vE, uE} W) :
    KernelTransformationConeData E e K L F G sourceIso targetIso α := by
  let A := e.conePresentation S.arrow
  refine
    { arrow := A.arrow
      cone := A.cone
      isCone := A.isCone
      transform_arrow := ?_ }
  exact (congrArg E.transformMap
    (e.counit_conjugate_conePresentation_arrow S.arrow)).trans
      S.transform_arrow

end KernelTransformationData

namespace KernelTransformationConeData

variable {E : Correspondence X Y W} {e : Enhancement.{vE, uE} W}
  {K L : W} {F G : X ⥤ Y}
  {sourceIso : E.transform K ≅ F} {targetIso : E.transform L ≅ G}
  {α : F ⟶ G}
  (S : KernelTransformationConeData E e K L F G sourceIso targetIso α)

/-- Forget the enhanced choices while retaining the ordinary kernel arrow
they represent. -/
def toKernelTransformationData :
    KernelTransformationData E K L F G sourceIso targetIso α where
  arrow := (e.equiv.counitIso.app K).inv ≫
    e.equiv.functor.map (H0.homMk (C := e.dgCat) S.arrow) ≫
    (e.equiv.counitIso.app L).hom
  transform_arrow := S.transform_arrow

/-- The selected arrow and cone as a reusable dg cone presentation. -/
def presentation : DGCategory.ConePresentation e.dgCat where
  source := H0.of e.dgCat (e.equiv.inverse.obj K)
  target := H0.of e.dgCat (e.equiv.inverse.obj L)
  arrow := S.arrow
  cone := S.cone
  isCone := S.isCone

@[simp]
theorem presentation_source :
    S.presentation.source = H0.of e.dgCat (e.equiv.inverse.obj K) :=
  rfl

@[simp]
theorem presentation_target :
    S.presentation.target = H0.of e.dgCat (e.equiv.inverse.obj L) :=
  rfl

@[simp]
theorem presentation_arrow : S.presentation.arrow = S.arrow :=
  rfl

@[simp]
theorem presentation_cone : S.presentation.cone = S.cone :=
  rfl

/-- Compare the transformed enhanced source lift with the literal source
functor. -/
def sourceTransformIso :
    E.transform (e.equiv.functor.obj
      (H0.of e.dgCat (e.equiv.inverse.obj K))) ≅ F :=
  let _ := S
  E.transformMapIso (e.equiv.counitIso.app K) ≪≫ sourceIso

/-- Compare the transformed enhanced target lift with the literal target
functor. -/
def targetTransformIso :
    E.transform (e.equiv.functor.obj
      (H0.of e.dgCat (e.equiv.inverse.obj L))) ≅ G :=
  let _ := S
  E.transformMapIso (e.equiv.counitIso.app L) ≪≫ targetIso

@[simp]
theorem sourceTransformIso_hom :
    S.sourceTransformIso.hom =
      E.transformMap (e.equiv.counitIso.app K).hom ≫ sourceIso.hom :=
  rfl

@[simp]
theorem targetTransformIso_hom :
    S.targetTransformIso.hom =
      E.transformMap (e.equiv.counitIso.app L).hom ≫ targetIso.hom :=
  rfl

/-- The stored transform equation rewritten as the literal endpoint square. -/
theorem transform_arrow_square :
    E.transformMap (e.equiv.functor.map
        (H0.homMk (C := e.dgCat) S.arrow)) ≫
        S.targetTransformIso.hom =
      S.sourceTransformIso.hom ≫ α := by
  rw [S.sourceTransformIso_hom, S.targetTransformIso_hom]
  calc
    E.transformMap (e.equiv.functor.map
          (H0.homMk (C := e.dgCat) S.arrow)) ≫
        E.transformMap (e.equiv.counitIso.app L).hom ≫
          targetIso.hom =
      (E.transformMapIso (e.equiv.counitIso.app K)).hom ≫
        E.transformMap
          ((e.equiv.counitIso.app K).inv ≫
            e.equiv.functor.map (H0.homMk (C := e.dgCat) S.arrow) ≫
            (e.equiv.counitIso.app L).hom) ≫
          targetIso.hom := by
            rw [E.transformMap_comp, E.transformMap_comp]
            simp only [← Correspondence.transformMapIso_hom,
              ← Correspondence.transformMapIso_inv, Category.assoc,
              Iso.hom_inv_id_assoc]
            rfl
    _ = (E.transformMapIso (e.equiv.counitIso.app K)).hom ≫
        (sourceIso.hom ≫ α ≫ targetIso.inv) ≫
          targetIso.hom := by
            rw [S.transform_arrow]
            rfl
    _ = (E.transformMap (e.equiv.counitIso.app K).hom ≫
        sourceIso.hom) ≫ α := by
          simp [Category.assoc]

/-- The endpoint square packaged for generic cone normalization. -/
def normalizationData :
    E.KernelConeNormalizationData e S.presentation F G α where
  sourceIso := S.sourceTransformIso
  targetIso := S.targetTransformIso
  square := S.transform_arrow_square

end KernelTransformationConeData

namespace KernelTransformationData

variable {E : Correspondence X Y W} {K L : W} {F G : X ⥤ Y}
  {sourceIso : E.transform K ≅ F} {targetIso : E.transform L ≅ G}
  {α : F ⟶ G}
  (S : KernelTransformationData E K L F G sourceIso targetIso α)

/-- Forgetting the choices made by `toConeData` recovers the original ordinary
kernel realization.  This does not identify the selected cocycle or cone. -/
@[simp]
theorem toConeData_toKernelTransformationData
    (e : Enhancement.{vE, uE} W) :
    (S.toConeData e).toKernelTransformationData = S := by
  apply KernelTransformationData.ext
  exact e.counit_conjugate_conePresentation_arrow S.arrow

end KernelTransformationData

end CategoryTheory.Triangulated.FourierMukai
