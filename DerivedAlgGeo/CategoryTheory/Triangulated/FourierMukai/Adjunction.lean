/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Kernel-presented adjoints of a Fourier--Mukai transform

`FourierMukai/Basic.lean` builds `Correspondence.transform`, and says in as
many words that it does not assume `pull` and `push` are adjoint or supply a
projection formula.  So a `Correspondence` gives no adjoint of `transform`,
and none is derivable from it.

Geometrically an adjoint of `Φ_P : D(X) ⥤ D(Y)` is again a transform, along
the correspondence read in the other direction, with kernel `P^∨ ⊗ p^*ω[dim]`
on one side and `P^∨ ⊗ q^*ω[dim]` on the other.  The statement that such a
kernel exists is Grothendieck duality; the statement that it is *some* kernel
is the part that has a use before the geometry arrives.  This file records
that part: a kernel for the opposite correspondence together with an
adjunction between the two transforms, as supplied data.

## Contents

* `LeftAdjointKernelData C C' K` -- a kernel `Q` for `C'` and an adjunction
  `C'.transform Q ⊣ C.transform K`;
* `RightAdjointKernelData C C' K` -- the mirror, `C.transform K ⊣ C'.transform Q`;
* uniqueness of adjoints in kernel form (`isoOfAdj`, `transformIso`): any
  functor adjoint to `C.transform K` on the matching side is isomorphic to the
  adjoint kernel's transform, hence is itself a kernel functor;
* transport along an isomorphism of either kernel;
* each structure read as the other with the two correspondences swapped.

## Direction of the correspondence

`C : Correspondence 𝒳 𝒴 𝒵` and `C' : Correspondence 𝒴 𝒳 𝒵'` are independent
data: nothing here builds `C'` from `C`, and the two kernel categories are not
assumed to be the same.  Geometrically both are `D(X × Y)` and `C'` is `C` with
the roles of the two projections exchanged, but "exchange the projections" is
not an operation the abstract `Correspondence` supports -- it has no product
and no projections, only three unrelated functors.

## What this file does not assert

* **Nothing constructs a `LeftAdjointKernelData` or a
  `RightAdjointKernelData`.**  That `Φ_P` has adjoints, let alone kernel-
  presented ones, is Grothendieck duality on smooth projective varieties; it
  needs the geometry the abstract `Correspondence` does not carry.  Every
  production in this repository either converts adjoint data that was already
  supplied (`toRightAdjointKernelData` here, `DualKernel.toLeftAdjointKernelData`
  in the stability track) or is the trivial case
  `UnitKernelData.toLeftAdjointKernelData`, which says only that `𝟭 C` is its
  own adjoint.
* Nothing **in this file** relates the left and right adjoint kernels of the
  *same* `K` to each other.  Classically they differ by the dualizing twist
  `ω[dim]`, and Serre duality is what identifies them; no dualizing object
  exists here.  The stability track does relate them for a kernel
  autoequivalence, but from the supplied equivalence rather than from any
  duality — see `KernelAutoequivalence.DualKernel.ofRightAdjointKernel`.
* Nothing says the adjoint kernel is unique as an *object*.  Uniqueness of
  adjoints gives an isomorphism of the two transforms, not of the two kernels
  -- that converse is Orlov's uniqueness theorem, which this repository does
  not state.
* No triangulated structure is used or required.  An adjunction between two
  transforms is a statement about the underlying functors, and the exactness
  hypotheses of `FourierMukai/Basic.lean` play no part.
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory

universe v v' v'' v''' u u' u'' u'''

variable {𝒳 : Type u} {𝒴 : Type u'} {𝒵 : Type u''} {𝒵' : Type u'''}
  [Category.{v} 𝒳] [Category.{v'} 𝒴] [Category.{v''} 𝒵] [Category.{v'''} 𝒵']

/-- A **left adjoint kernel** for the transform of `C` with kernel `K`: a
kernel `adjKernel` for the opposite correspondence `C'`, whose transform is
left adjoint to `C.transform K`.

Both the kernel and the adjunction are supplied.  Nothing here proves that a
transform has an adjoint, and a `Correspondence` on its own carries no
adjunction between `pull` and `push` from which one could be assembled. -/
structure LeftAdjointKernelData (C : Correspondence 𝒳 𝒴 𝒵)
    (C' : Correspondence 𝒴 𝒳 𝒵') (K : 𝒵) where
  /-- The kernel presenting the left adjoint. -/
  adjKernel : 𝒵'
  /-- Its transform is left adjoint to the transform with kernel `K`. -/
  adj : C'.transform adjKernel ⊣ C.transform K

/-- A **right adjoint kernel** for the transform of `C` with kernel `K`: a
kernel `adjKernel` for the opposite correspondence `C'`, whose transform is
right adjoint to `C.transform K`.

Supplied for the same reason as `LeftAdjointKernelData`, and independent of
it: classically the two kernels differ by the dualizing twist, and nothing
here relates them. -/
structure RightAdjointKernelData (C : Correspondence 𝒳 𝒴 𝒵)
    (C' : Correspondence 𝒴 𝒳 𝒵') (K : 𝒵) where
  /-- The kernel presenting the right adjoint. -/
  adjKernel : 𝒵'
  /-- Its transform is right adjoint to the transform with kernel `K`. -/
  adj : C.transform K ⊣ C'.transform adjKernel

namespace LeftAdjointKernelData

variable {C : Correspondence 𝒳 𝒴 𝒵} {C' : Correspondence 𝒴 𝒳 𝒵'} {K : 𝒵}
  (L : LeftAdjointKernelData C C' K)

include L in
/-- The transform with kernel `K` is a right adjoint. -/
theorem isRightAdjoint : (C.transform K).IsRightAdjoint := L.adj.isRightAdjoint

/-- The adjoint kernel's transform is a left adjoint. -/
theorem isLeftAdjoint : (C'.transform L.adjKernel).IsLeftAdjoint := L.adj.isLeftAdjoint

/-- **Uniqueness of left adjoints, in kernel form.**

Any functor left adjoint to `C.transform K` is isomorphic to the adjoint
kernel's transform.  This is `Adjunction.leftAdjointUniq` and nothing else;
what the wrapper adds is that the target of the isomorphism is a transform, so
the isomorphism identifies an abstract adjoint with kernel-computable data. -/
def isoOfAdj {F : 𝒴 ⥤ 𝒳} (h : F ⊣ C.transform K) : F ≅ C'.transform L.adjKernel :=
  Adjunction.leftAdjointUniq h L.adj

include L in
/-- **A left adjoint of a kernel functor is a kernel functor.**

The consequence of `isoOfAdj` phrased against `Correspondence.IsKernelFunctor`.
Note which correspondence it is a kernel functor *for*: `C'`, not `C`. -/
theorem isKernelFunctor_of_adj {F : 𝒴 ⥤ 𝒳} (h : F ⊣ C.transform K) :
    C'.IsKernelFunctor F :=
  ⟨L.adjKernel, ⟨L.isoOfAdj h⟩⟩

/-- Two left adjoint kernels for the same transform present isomorphic
functors.

This is uniqueness of the *transform*, not of the kernel: no isomorphism
`L.adjKernel ≅ L'.adjKernel` is produced, and none follows without a converse
to `transformMapIso`. -/
def transformIso (L' : LeftAdjointKernelData C C' K) :
    C'.transform L.adjKernel ≅ C'.transform L'.adjKernel :=
  L'.isoOfAdj L.adj

/-- An adjoint kernel transports along an isomorphism of the kernel it is
adjoint to. -/
def ofKernelIso {K' : 𝒵} (e : K ≅ K') : LeftAdjointKernelData C C' K' where
  adjKernel := L.adjKernel
  adj := L.adj.ofNatIsoRight (C.transformMapIso e)

@[simp]
theorem ofKernelIso_adjKernel {K' : 𝒵} (e : K ≅ K') :
    (L.ofKernelIso e).adjKernel = L.adjKernel := rfl

/-- The adjoint kernel may be replaced by an isomorphic object. -/
def mapAdjKernelIso {Q : 𝒵'} (e : L.adjKernel ≅ Q) : LeftAdjointKernelData C C' K where
  adjKernel := Q
  adj := L.adj.ofNatIsoLeft (C'.transformMapIso e)

@[simp]
theorem mapAdjKernelIso_adjKernel {Q : 𝒵'} (e : L.adjKernel ≅ Q) :
    (L.mapAdjKernelIso e).adjKernel = Q := rfl

/-- The same adjunction read from the other side: `K` is a right adjoint kernel
for the transform of `C'` with kernel `L.adjKernel`.

No content -- the adjunction field is reused verbatim.  It is stated so that
the left and right structures are one datum seen twice rather than two
independent interfaces. -/
def toRightAdjointKernelData : RightAdjointKernelData C' C L.adjKernel where
  adjKernel := K
  adj := L.adj

@[simp]
theorem toRightAdjointKernelData_adjKernel : L.toRightAdjointKernelData.adjKernel = K := rfl

end LeftAdjointKernelData

namespace RightAdjointKernelData

variable {C : Correspondence 𝒳 𝒴 𝒵} {C' : Correspondence 𝒴 𝒳 𝒵'} {K : 𝒵}
  (R : RightAdjointKernelData C C' K)

include R in
/-- The transform with kernel `K` is a left adjoint. -/
theorem isLeftAdjoint : (C.transform K).IsLeftAdjoint := R.adj.isLeftAdjoint

/-- The adjoint kernel's transform is a right adjoint. -/
theorem isRightAdjoint : (C'.transform R.adjKernel).IsRightAdjoint := R.adj.isRightAdjoint

/-- **Uniqueness of right adjoints, in kernel form.**  The mirror of
`LeftAdjointKernelData.isoOfAdj`. -/
def isoOfAdj {G : 𝒴 ⥤ 𝒳} (h : C.transform K ⊣ G) : G ≅ C'.transform R.adjKernel :=
  Adjunction.rightAdjointUniq h R.adj

include R in
/-- **A right adjoint of a kernel functor is a kernel functor**, for the
opposite correspondence. -/
theorem isKernelFunctor_of_adj {G : 𝒴 ⥤ 𝒳} (h : C.transform K ⊣ G) :
    C'.IsKernelFunctor G :=
  ⟨R.adjKernel, ⟨R.isoOfAdj h⟩⟩

/-- Two right adjoint kernels for the same transform present isomorphic
functors.  As on the left, this is uniqueness of the transform and not of the
kernel. -/
def transformIso (R' : RightAdjointKernelData C C' K) :
    C'.transform R.adjKernel ≅ C'.transform R'.adjKernel :=
  (R.isoOfAdj R'.adj).symm

/-- A right adjoint kernel transports along an isomorphism of the kernel it is
adjoint to. -/
def ofKernelIso {K' : 𝒵} (e : K ≅ K') : RightAdjointKernelData C C' K' where
  adjKernel := R.adjKernel
  adj := R.adj.ofNatIsoLeft (C.transformMapIso e)

@[simp]
theorem ofKernelIso_adjKernel {K' : 𝒵} (e : K ≅ K') :
    (R.ofKernelIso e).adjKernel = R.adjKernel := rfl

/-- The adjoint kernel may be replaced by an isomorphic object. -/
def mapAdjKernelIso {Q : 𝒵'} (e : R.adjKernel ≅ Q) : RightAdjointKernelData C C' K where
  adjKernel := Q
  adj := R.adj.ofNatIsoRight (C'.transformMapIso e)

@[simp]
theorem mapAdjKernelIso_adjKernel {Q : 𝒵'} (e : R.adjKernel ≅ Q) :
    (R.mapAdjKernelIso e).adjKernel = Q := rfl

/-- The same adjunction read from the other side, mirroring
`LeftAdjointKernelData.toRightAdjointKernelData`. -/
def toLeftAdjointKernelData : LeftAdjointKernelData C' C R.adjKernel where
  adjKernel := K
  adj := R.adj

@[simp]
theorem toLeftAdjointKernelData_adjKernel : R.toLeftAdjointKernelData.adjKernel = K := rfl

end RightAdjointKernelData

end CategoryTheory.Triangulated.FourierMukai
