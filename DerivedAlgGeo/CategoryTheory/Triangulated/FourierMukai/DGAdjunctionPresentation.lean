/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.AdjunctionH0Presentation
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Fourier--Mukai presentations of dg adjunctions

`DGAdjunction.H0Presentation` turns a strict dg adjunction into an ordinary
adjunction between named functors after transport through equivalences out of
the two homotopy categories.  When those named functors are Fourier--Mukai
transforms, the resulting ordinary adjunction is exactly the datum required
by `RightAdjointKernelData` or `LeftAdjointKernelData`.

The constructors in this file perform that specialization.  They reuse the
existing kernel-adjunction structures rather than adding a dg-flavoured copy,
and their two orientations agree definitionally with the existing operation
that reads a right-adjoint kernel as a left-adjoint kernel after swapping the
correspondences.

## What remains supplied

The equivalences and both endpoint natural isomorphisms are inputs.  Thus no
dg lift or kernel is constructed here.  In particular, these constructors do
not produce the kernel morphism realizing the unit or counit, an enhanced
kernel cone, or any comparison between a dg cone and a Fourier--Mukai kernel
cone.  Those are the separate realization obligations recorded by
`CounitKernelData` and its companions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY vW vW' uA uB uX uY uW uW'

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory

/-- Shift compatibility of a supplied natural isomorphism, relative to the
source functor's selected shift structure and an independently selected shift
structure on the target functor.

The source `CommShift` instance is an input to this record. In particular,
specializations must preserve the shift structure already chosen by their
presentation rather than replacing it with one transported from the target. -/
structure FunctorIsoShiftCompatibility
    {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (G F : C ⥤ D) [G.CommShift ℤ] (α : G ≅ F) where
  /-- The independently selected shift structure on the target functor. -/
  targetCommShift : F.CommShift ℤ
  /-- The supplied isomorphism respects the selected source and target shifts. -/
  hom_commShift :
    letI : F.CommShift ℤ := targetCommShift
    NatTrans.CommShift α.hom ℤ

namespace FunctorIsoShiftCompatibility

variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {G F : C ⥤ D} [G.CommShift ℤ] {α : G ≅ F}
  (h : FunctorIsoShiftCompatibility G F α)

/-- Transfer triangulatedness across the supplied isomorphism using the
selected source and target shift structures. -/
theorem targetIsTriangulated [G.IsTriangulated] :
    letI : F.CommShift ℤ := h.targetCommShift
    F.IsTriangulated := by
  letI : F.CommShift ℤ := h.targetCommShift
  letI : NatTrans.CommShift α.hom ℤ := h.hom_commShift
  exact Functor.isTriangulated_of_iso α

/-- Transfer triangulatedness to an equivalence whose functor is the target
of the supplied comparison, deriving the inverse and equivalence shift
structures from the selected forward structure. -/
theorem equivalenceIsTriangulatedOfEq {E : C ≌ D}
    (hEF : E.functor = F) [G.IsTriangulated] :
    letI : E.functor.CommShift ℤ := hEF ▸ h.targetCommShift
    letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
    letI : E.CommShift ℤ := E.commShift_of_functor ℤ
    E.IsTriangulated := by
  cases hEF
  letI : E.functor.CommShift ℤ := h.targetCommShift
  letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  letI : E.CommShift ℤ := E.commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' E h.targetIsTriangulated

end FunctorIsoShiftCompatibility

namespace RightAdjointKernelData

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W : Type uW} {W' : Type uW'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{vW} W] [Category.{vW'} W']
  {S : DGFunctor A B} {R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W} {C' : Correspondence Y X W'}
  {K : W} {Q : W'}

/-- Build a right-adjoint kernel datum from a strict dg adjunction whose two
`H⁰` functors are presented by the indicated Fourier--Mukai transforms.

The kernel `Q` and both functor identifications are supplied by `P`; this
constructor contributes only the ordinary adjunction obtained from the
generic `H0Presentation` bridge. -/
noncomputable def ofH0Presentation
    (P : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform K) (C'.transform Q))
    (adj : DGAdjunction S R) : RightAdjointKernelData C C' K where
  adjKernel := Q
  adj := P.toAdjunction adj

/-- The constructor records the supplied right-adjoint kernel `Q` verbatim;
it performs no kernel selection. -/
@[simp]
theorem ofH0Presentation_adjKernel
    (P : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform K) (C'.transform Q))
    (adj : DGAdjunction S R) :
    (ofH0Presentation P adj).adjKernel = Q :=
  rfl

/-- The adjunction stored by `ofH0Presentation` is exactly the generic
presented adjunction, with no second transport. -/
theorem ofH0Presentation_adj
    (P : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform K) (C'.transform Q))
    (adj : DGAdjunction S R) :
    (ofH0Presentation P adj).adj = P.toAdjunction adj :=
  rfl

end RightAdjointKernelData

namespace LeftAdjointKernelData

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W : Type uW} {W' : Type uW'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{vW} W] [Category.{vW'} W']
  {L : DGFunctor B A} {S : DGFunctor A B}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W} {C' : Correspondence Y X W'}
  {K : W} {Q : W'}

/-- Build a left-adjoint kernel datum from a strict dg adjunction whose two
`H⁰` functors are presented by the indicated Fourier--Mukai transforms.

Here `L : B ⥤ A` presents the opposite-correspondence transform with
kernel `Q`, while `S : A ⥤ B` presents the original transform with kernel
`K`. -/
noncomputable def ofH0Presentation
    (P : DGAdjunction.H0Presentation (L := L) (R := S) eB eA
      (C'.transform Q) (C.transform K))
    (adj : DGAdjunction L S) : LeftAdjointKernelData C C' K where
  adjKernel := Q
  adj := P.toAdjunction adj

/-- The constructor records the supplied left-adjoint kernel `Q` verbatim;
it performs no kernel selection. -/
@[simp]
theorem ofH0Presentation_adjKernel
    (P : DGAdjunction.H0Presentation (L := L) (R := S) eB eA
      (C'.transform Q) (C.transform K))
    (adj : DGAdjunction L S) :
    (ofH0Presentation P adj).adjKernel = Q :=
  rfl

/-- The adjunction stored by `ofH0Presentation` is exactly the generic
presented adjunction, with no second transport. -/
theorem ofH0Presentation_adj
    (P : DGAdjunction.H0Presentation (L := L) (R := S) eB eA
      (C'.transform Q) (C.transform K))
    (adj : DGAdjunction L S) :
    (ofH0Presentation P adj).adj = P.toAdjunction adj :=
  rfl

end LeftAdjointKernelData

namespace RightAdjointKernelData

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W : Type uW} {W' : Type uW'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{vW} W] [Category.{vW'} W']
  {S : DGFunctor A B} {R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W} {C' : Correspondence Y X W'}
  {K : W} {Q : W'}

/-- The two specialization directions agree with the existing operation that
reads a right-adjoint kernel datum as a left-adjoint kernel datum for the
swapped correspondences. -/
theorem ofH0Presentation_toLeftAdjointKernelData
    (P : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform K) (C'.transform Q))
    (adj : DGAdjunction S R) :
    (RightAdjointKernelData.ofH0Presentation P adj).toLeftAdjointKernelData =
      LeftAdjointKernelData.ofH0Presentation P adj :=
  rfl

end RightAdjointKernelData

namespace LeftAdjointKernelData

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W : Type uW} {W' : Type uW'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{vW} W] [Category.{vW'} W']
  {S : DGFunctor A B} {R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W} {C' : Correspondence Y X W'}
  {K : W} {Q : W'}

/-- The mirror conversion from a left-adjoint kernel datum back to a
right-adjoint kernel datum also agrees definitionally with the presentation
constructor. -/
theorem ofH0Presentation_toRightAdjointKernelData
    (P : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform K) (C'.transform Q))
    (adj : DGAdjunction S R) :
    (LeftAdjointKernelData.ofH0Presentation P adj).toRightAdjointKernelData =
      RightAdjointKernelData.ofH0Presentation P adj :=
  rfl

end LeftAdjointKernelData

end CategoryTheory.Triangulated.FourierMukai
