/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.ExceptionalExtension
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Finite induction of Fourier--Mukai extension steps

`ExceptionalExtension.lean` states the output of one kernel-cone extension.
This file performs the finite categorical induction which the two refined
Torelli papers use: after adjoining corresponding exceptional objects one at
a time, the final kernel restricts to an equivalence on the iterated spans.

The construction is deliberately separated from the dg seam.  An
`ExtensionSequenceData` can only be built by providing a genuine
`OneStepExtensionData` at every successor.  Once those steps exist, however,
the final kernel, final equivalence, and its presentation by the transform are
derived recursively rather than supplied as a second finite conclusion.

When the two final spans are the top object properties, the restricted
equivalence is promoted directly to an equivalence of the ambient categories.
This is the route taken in the papers and does not require a separate
Bondal--Orlov unit/counit criterion.
-/

open CategoryTheory

universe w v v' v'' u u' u'' t t'

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory.Limits CategoryTheory.ObjectProperty

section AdjoinList

variable {X : Type u} [Category.{v} X] [Limits.HasZeroObject X]
  [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]

/-- Iteratively adjoin a finite ordered list of objects to a triangulated
object property. -/
def adjoinList (P : ObjectProperty X) : List X → ObjectProperty X
  | [] => P
  | E :: objects => adjoinList (adjoinObject P E) objects

@[simp]
theorem adjoinList_nil (P : ObjectProperty X) : adjoinList P [] = P :=
  rfl

@[simp]
theorem adjoinList_cons (P : ObjectProperty X) (E : X) (objects : List X) :
    adjoinList P (E :: objects) =
      adjoinList (adjoinObject P E) objects :=
  rfl

/-- The initial component remains inside every finite iterated span. -/
theorem le_adjoinList (P : ObjectProperty X) (objects : List X) :
    P ≤ adjoinList P objects := by
  induction objects generalizing P with
  | nil => exact le_rfl
  | cons E objects ih =>
      exact (le_trans (le_trans le_sup_left
        ((P ⊔ ObjectProperty.singleton E).le_triangEnvelope))
        (ih (adjoinObject P E)))

/-- Every object in the adjoining list belongs to the resulting iterated
span. -/
theorem singleton_le_adjoinList_of_mem (P : ObjectProperty X)
    {E : X} {objects : List X} (hE : E ∈ objects) :
    ObjectProperty.singleton E ≤ adjoinList P objects := by
  induction objects generalizing P with
  | nil => simp at hE
  | cons F objects ih =>
      rw [List.mem_cons] at hE
      rcases hE with rfl | hE
      · exact (le_trans (le_trans le_sup_right
          ((P ⊔ ObjectProperty.singleton E).le_triangEnvelope))
          (le_adjoinList (adjoinObject P E) objects))
      · exact ih (adjoinObject P F) hE

/-- Adjoining at least one object produces a triangulated iterated span. -/
theorem adjoinList_isTriangulated [IsTriangulated X]
    (P : ObjectProperty X) (E : X) (objects : List X) :
    (adjoinList P (E :: objects)).IsTriangulated := by
  induction objects generalizing P E with
  | nil =>
      change (adjoinObject P E).IsTriangulated
      infer_instance
  | cons F objects ih =>
      change (adjoinList (adjoinObject P E) (F :: objects)).IsTriangulated
      exact ih (adjoinObject P E) F

/-- Adjoining at least one object produces an iterated span closed under
retracts. -/
theorem adjoinList_isStableUnderRetracts
    (P : ObjectProperty X) (E : X) (objects : List X) :
    (adjoinList P (E :: objects)).IsStableUnderRetracts := by
  induction objects generalizing P E with
  | nil =>
      change (adjoinObject P E).IsStableUnderRetracts
      infer_instance
  | cons F objects ih =>
      change (adjoinList (adjoinObject P E) (F :: objects)).IsStableUnderRetracts
      exact ih (adjoinObject P E) F

/-- If the objects adjoined to a residual component contain the entire
exceptional part, right admissibility proves that the final iterated span is
the whole category.

This is the generation step used after the finite kernel induction: the SOD
triangle writes every object as an extension of an exceptional object by a
residual object, and the final span is closed under those extensions. -/
theorem adjoinList_eq_top_of_rightAdmissible [IsTriangulated X]
    (T P : ObjectProperty X) (E : X) (objects : List X)
    (hT : T.IsRightAdmissible) (hP : P = T.rightOrthogonal)
    (hcover : T ≤ adjoinList P (E :: objects)) :
    adjoinList P (E :: objects) = (⊤ : ObjectProperty X) := by
  letI : (adjoinList P (E :: objects)).IsTriangulated :=
    adjoinList_isTriangulated P E objects
  letI : (adjoinList P (E :: objects)).IsStableUnderRetracts :=
    adjoinList_isStableUnderRetracts P E objects
  apply top_unique
  rw [← hT.extensionProduct_rightOrthogonal_eq_top]
  apply ObjectProperty.extensionProduct_le_of_isTriangulatedClosed₂
  · exact hcover
  · rw [← hP]
    exact le_adjoinList P (E :: objects)

end AdjoinList

section Stages

variable {k : Type w} [Field k]
variable {X : Type u} {Y : Type u'} {W : Type u''}
  [Category.{v} X] [Preadditive X] [Linear k X]
  [Limits.HasZeroObject X] [HasShift X ℤ]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [Category.{v'} Y] [Preadditive Y] [Linear k Y]
  [Limits.HasZeroObject Y] [HasShift Y ℤ]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [Category.{v''} W]

/-- A kernel whose transform presents an equivalence between two current
extension stages. -/
structure KernelExtensionStage (P : ObjectProperty X) (Q : ObjectProperty Y)
    (corr : Correspondence X Y W) where
  /-- The kernel at this stage. -/
  kernel : W
  /-- The equivalence between the current source and target spans. -/
  equiv : P.FullSubcategory ≌ Q.FullSubcategory
  /-- The stage equivalence is induced by restricting the kernel transform. -/
  restrictionIso :
    P.ι ⋙ corr.transform kernel ≅ equiv.functor ⋙ Q.ι

namespace ResidualKernelEquivalence

variable {I : Type t} {J : Type t'}
  {B_X : Triangulated.OrthogonalExceptionalBlocks k X I}
  {B_Y : Triangulated.OrthogonalExceptionalBlocks k Y J}
  {corr : Correspondence X Y W}
variable (R : ResidualKernelEquivalence B_X B_Y corr)

/-- A residual Fourier--Mukai equivalence is the initial stage of the finite
exceptional-extension induction. -/
def toStage : KernelExtensionStage B_X.residual B_Y.residual corr where
  kernel := R.kernel
  equiv := R.equiv
  restrictionIso := R.restrictionIso

end ResidualKernelEquivalence

namespace OneStepExtensionData

variable {P : ObjectProperty X} {Q : ObjectProperty Y} {E : X} {F : Y}
  {base : P.FullSubcategory ≌ Q.FullSubcategory}
  {corr : Correspondence X Y W} {oldKernel : W}
variable (A : OneStepExtensionData P Q E F base corr oldKernel)

/-- One successful application of the extension proposition is the next
kernel-extension stage. -/
def toStage : KernelExtensionStage (adjoinObject P E) (adjoinObject Q F) corr where
  kernel := A.newKernel
  equiv := A.enlargedEquiv
  restrictionIso := A.enlargedIso

end OneStepExtensionData

/-- A finite derivation made only from one-step Fourier--Mukai extensions.

The indices record the current stage, so the successor constructor changes
both object properties, the kernel, and the restricted equivalence before
continuing. -/
inductive ExtensionSequenceData (corr : Correspondence X Y W) :
    {P : ObjectProperty X} → {Q : ObjectProperty Y} →
      KernelExtensionStage P Q corr → List X → List Y → Type _
  | nil {P : ObjectProperty X} {Q : ObjectProperty Y}
      (stage : KernelExtensionStage P Q corr) :
      ExtensionSequenceData corr stage [] []
  | cons {P : ObjectProperty X} {Q : ObjectProperty Y}
      {stage : KernelExtensionStage P Q corr} {E : X} {F : Y}
      {source : List X} {target : List Y}
      (step : OneStepExtensionData P Q E F stage.equiv corr stage.kernel)
      (tail : ExtensionSequenceData corr step.toStage source target) :
      ExtensionSequenceData corr stage (E :: source) (F :: target)

namespace ExtensionSequenceData

variable {P : ObjectProperty X} {Q : ObjectProperty Y}
  {corr : Correspondence X Y W} {stage : KernelExtensionStage P Q corr}
  {source : List X} {target : List Y}
variable (A : ExtensionSequenceData corr stage source target)

/-- The final stage obtained by recursively consuming all one-step
extensions. -/
noncomputable def finalStage :
    KernelExtensionStage (adjoinList P source) (adjoinList Q target) corr :=
  by
    induction A with
    | nil stage => exact stage
    | cons step tail ih => exact ih

/-- The final extended kernel. -/
noncomputable def finalKernel : W := A.finalStage.kernel

/-- The equivalence between the two final iterated spans. -/
noncomputable def finalEquiv :
    (adjoinList P source).FullSubcategory ≌
      (adjoinList Q target).FullSubcategory :=
  A.finalStage.equiv

/-- The final equivalence is presented by the restriction of the final
kernel transform. -/
noncomputable def finalRestrictionIso :
    (adjoinList P source).ι ⋙ corr.transform A.finalKernel ≅
      A.finalEquiv.functor ⋙ (adjoinList Q target).ι :=
  A.finalStage.restrictionIso

/-- If the iterated spans exhaust both categories, the final stage gives an
ambient equivalence directly. -/
noncomputable def ambientEquivalence
    (hX : adjoinList P source = (⊤ : ObjectProperty X))
    (hY : adjoinList Q target = (⊤ : ObjectProperty Y)) : X ≌ Y := by
  let e := A.finalEquiv
  rw [hX, hY] at e
  exact (ObjectProperty.topEquivalence X).symm.trans <|
    e.trans (ObjectProperty.topEquivalence Y)

/-- The ambient equivalence remains presented by the final Fourier--Mukai
kernel. -/
noncomputable def toKernelEquivalence
    (hX : adjoinList P source = (⊤ : ObjectProperty X))
    (hY : adjoinList Q target = (⊤ : ObjectProperty Y)) :
    KernelEquivalence corr := by
  let final : KernelExtensionStage (⊤ : ObjectProperty X)
      (⊤ : ObjectProperty Y) corr := hY ▸ hX ▸ A.finalStage
  refine
    { kernel := final.kernel
      equiv := (ObjectProperty.topEquivalence X).symm.trans <|
        final.equiv.trans (ObjectProperty.topEquivalence Y)
      iso := ?_ }
  exact ((ObjectProperty.topEquivalence X).inverse.isoWhiskerLeft
    final.restrictionIso).symm

end ExtensionSequenceData

/-! ## Generation-certified finite extension -/

/-- A finite exceptional extension sequence together with the admissibility
and coverage data which prove that its final source and target spans are the
ambient categories.

The source and target lists are visibly nonempty because the papers adjoin
ten exceptional objects.  Coverage says their iterated spans contain the
total exceptional parts; `sourceGenerates` and `targetGenerates` derive
generation rather than storing it. -/
structure GeneratedExtensionSequenceData
    (corr : Correspondence X Y W) (T_X : ObjectProperty X)
    (T_Y : ObjectProperty Y)
    (stage : KernelExtensionStage T_X.rightOrthogonal
      T_Y.rightOrthogonal corr) where
  /-- First source exceptional object. -/
  sourceHead : X
  /-- Remaining source exceptional objects. -/
  sourceTail : List X
  /-- First target exceptional object. -/
  targetHead : Y
  /-- Remaining target exceptional objects. -/
  targetTail : List Y
  /-- The dependent sequence of one-object kernel extensions. -/
  sequence : ExtensionSequenceData corr stage
    (sourceHead :: sourceTail) (targetHead :: targetTail)
  /-- The total source exceptional part is right admissible. -/
  sourceRightAdmissible : T_X.IsRightAdmissible
  /-- The source list covers the total exceptional part. -/
  sourceCover : T_X ≤ adjoinList T_X.rightOrthogonal
    (sourceHead :: sourceTail)
  /-- The total target exceptional part is right admissible. -/
  targetRightAdmissible : T_Y.IsRightAdmissible
  /-- The target list covers the total exceptional part. -/
  targetCover : T_Y ≤ adjoinList T_Y.rightOrthogonal
    (targetHead :: targetTail)

namespace GeneratedExtensionSequenceData

variable {T_X : ObjectProperty X} {T_Y : ObjectProperty Y}
  {corr : Correspondence X Y W}
  {stage : KernelExtensionStage T_X.rightOrthogonal
    T_Y.rightOrthogonal corr}
variable (A : GeneratedExtensionSequenceData corr T_X T_Y stage)

/-- The source residual category and adjoined exceptional objects generate
the ambient source category. -/
theorem sourceGenerates [IsTriangulated X] :
    adjoinList T_X.rightOrthogonal (A.sourceHead :: A.sourceTail) =
      (⊤ : ObjectProperty X) :=
  adjoinList_eq_top_of_rightAdmissible T_X T_X.rightOrthogonal
    A.sourceHead A.sourceTail A.sourceRightAdmissible rfl A.sourceCover

/-- The target residual category and adjoined exceptional objects generate
the ambient target category. -/
theorem targetGenerates [IsTriangulated Y] :
    adjoinList T_Y.rightOrthogonal (A.targetHead :: A.targetTail) =
      (⊤ : ObjectProperty Y) :=
  adjoinList_eq_top_of_rightAdmissible T_Y T_Y.rightOrthogonal
    A.targetHead A.targetTail A.targetRightAdmissible rfl A.targetCover

/-- The generation-certified sequence promotes the residual equivalence to
an ambient equivalence. -/
noncomputable def ambientEquivalence [IsTriangulated X] [IsTriangulated Y] :
    X ≌ Y :=
  A.sequence.ambientEquivalence A.sourceGenerates A.targetGenerates

/-- The promoted ambient equivalence is presented by the final extended
Fourier--Mukai kernel. -/
noncomputable def toKernelEquivalence [IsTriangulated X]
    [IsTriangulated Y] : KernelEquivalence corr :=
  A.sequence.toKernelEquivalence A.sourceGenerates A.targetGenerates

end GeneratedExtensionSequenceData

/-- The generation-certified finite extension specialized to orthogonal
exceptional blocks.

Coverage is now expressed concretely: every member of every block occurs in
the corresponding extension list.  The inequality saying that the list spans
the total exceptional part is derived from the universal property of the
block spans. -/
structure GeneratedBlockExtensionSequenceData
    {I : Type t} {J : Type t'}
    (B_X : Triangulated.OrthogonalExceptionalBlocks k X I)
    (B_Y : Triangulated.OrthogonalExceptionalBlocks k Y J)
    (corr : Correspondence X Y W)
    (R : ResidualKernelEquivalence B_X B_Y corr) where
  /-- First source exceptional object. -/
  sourceHead : X
  /-- Remaining source exceptional objects. -/
  sourceTail : List X
  /-- First target exceptional object. -/
  targetHead : Y
  /-- Remaining target exceptional objects. -/
  targetTail : List Y
  /-- The dependent sequence of one-object kernel extensions. -/
  sequence : ExtensionSequenceData corr R.toStage
    (sourceHead :: sourceTail) (targetHead :: targetTail)
  /-- Every source block member occurs in the extension order. -/
  sourceMember : ∀ (i : I) (j : Fin (B_X.length i)),
    (B_X.collection i).obj j ∈ sourceHead :: sourceTail
  /-- Every target block member occurs in the extension order. -/
  targetMember : ∀ (i : J) (j : Fin (B_Y.length i)),
    (B_Y.collection i).obj j ∈ targetHead :: targetTail
  /-- The total source exceptional part is right admissible. -/
  sourceRightAdmissible : B_X.total.IsRightAdmissible
  /-- The total target exceptional part is right admissible. -/
  targetRightAdmissible : B_Y.total.IsRightAdmissible

namespace GeneratedBlockExtensionSequenceData

variable {I : Type t} {J : Type t'}
  {B_X : Triangulated.OrthogonalExceptionalBlocks k X I}
  {B_Y : Triangulated.OrthogonalExceptionalBlocks k Y J}
  {corr : Correspondence X Y W}
  {R : ResidualKernelEquivalence B_X B_Y corr}
variable (A : GeneratedBlockExtensionSequenceData B_X B_Y corr R)

/-- The source extension list contains the total source exceptional part. -/
theorem sourceCover [IsTriangulated X] :
    B_X.total ≤ adjoinList B_X.residual (A.sourceHead :: A.sourceTail) := by
  letI : (adjoinList B_X.residual
      (A.sourceHead :: A.sourceTail)).IsTriangulated :=
    adjoinList_isTriangulated B_X.residual A.sourceHead A.sourceTail
  letI : (adjoinList B_X.residual
      (A.sourceHead :: A.sourceTail)).IsStableUnderRetracts :=
    adjoinList_isStableUnderRetracts B_X.residual A.sourceHead A.sourceTail
  apply B_X.total_le_of_forall_obj
    (P := adjoinList B_X.residual (A.sourceHead :: A.sourceTail))
  intro i j
  exact (singleton_le_adjoinList_of_mem B_X.residual (A.sourceMember i j))
    _ (by simp)

/-- The target extension list contains the total target exceptional part. -/
theorem targetCover [IsTriangulated Y] :
    B_Y.total ≤ adjoinList B_Y.residual (A.targetHead :: A.targetTail) := by
  letI : (adjoinList B_Y.residual
      (A.targetHead :: A.targetTail)).IsTriangulated :=
    adjoinList_isTriangulated B_Y.residual A.targetHead A.targetTail
  letI : (adjoinList B_Y.residual
      (A.targetHead :: A.targetTail)).IsStableUnderRetracts :=
    adjoinList_isStableUnderRetracts B_Y.residual A.targetHead A.targetTail
  apply B_Y.total_le_of_forall_obj
    (P := adjoinList B_Y.residual (A.targetHead :: A.targetTail))
  intro i j
  exact (singleton_le_adjoinList_of_mem B_Y.residual (A.targetMember i j))
    _ (by simp)

/-- Forget the block enumeration after deriving its exceptional-part
coverage. -/
def toGeneratedExtensionSequenceData [IsTriangulated X]
    [IsTriangulated Y] :
    GeneratedExtensionSequenceData corr B_X.total B_Y.total R.toStage where
  sourceHead := A.sourceHead
  sourceTail := A.sourceTail
  targetHead := A.targetHead
  targetTail := A.targetTail
  sequence := A.sequence
  sourceRightAdmissible := A.sourceRightAdmissible
  sourceCover := A.sourceCover
  targetRightAdmissible := A.targetRightAdmissible
  targetCover := A.targetCover

/-- The block-enumerated sequence produces an ambient Fourier--Mukai
equivalence. -/
noncomputable def toKernelEquivalence [IsTriangulated X]
    [IsTriangulated Y] : KernelEquivalence corr :=
  A.toGeneratedExtensionSequenceData.toKernelEquivalence

end GeneratedBlockExtensionSequenceData

end Stages

end CategoryTheory.Triangulated.FourierMukai
