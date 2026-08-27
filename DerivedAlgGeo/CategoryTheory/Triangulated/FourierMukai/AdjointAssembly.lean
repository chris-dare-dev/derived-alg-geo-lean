/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Adjunction

/-!
# Assembling an adjoint kernel from the constituents of a transform

`FourierMukai/Adjunction.lean` takes `LeftAdjointKernelData` and
`RightAdjointKernelData` as single opaque obligations: a kernel for the
opposite correspondence, and an adjunction between the two transforms.  The
only thing in the repository that produces either is the unit kernel saying
`𝟭 C` is its own adjoint, which is the trivial case.

This file splits that obligation the way the mathematics does.  A transform is
a composite of three functors, and classically each of the three has its own
adjoint for its own reason:

* `Lp^* ⊣ Rp_*` — the standard pullback/pushforward adjunction;
* `(− ⊗^L K) ⊣ (− ⊗^L K^∨)` — rigidity of the kernel;
* `Rq_* ⊣ q^!` — Grothendieck duality, which is where the dualizing object
  enters.

Adjoints compose, so those three give an adjoint of the transform for free.
What they do *not* give is that the composite is again a **transform**: that
step is the projection formula, plus the identification of `q^!` with a
twisted pullback, and it is the one thing left supplied here.

## What is free and what is supplied

`ConstituentRightAdjoints C K` collects the three adjunctions.  `adj` is then a
**theorem**, not a field: `Adjunction.comp` applied twice.  The assembly
`toRightAdjointKernelData` takes one further input, an isomorphism
`rightAdjoint ≅ C'.transform Q`, and that isomorphism is where the remaining
geometry lives.

So the ledger reads: one opaque obligation becomes three classical adjunctions
plus one identification, with the composition proved.  That is the same shape
as `Families/KernelCorrespondence.lean`, which reduces `Correspondence` to
named pullback, tensor, and pushforward obligations and assembles it.

It is worth being blunt about the size of the free part.  Composing adjunctions
is `Adjunction.comp`; there is no new mathematics in `adj`.  The value claimed
here is the decomposition — four separately-classical inputs instead of one
compound one — and the fact that the composite adjoint is written in a form a
projection formula can be compared against.

**And about the direction of strength.**  This ledger is *stronger* input than
what it produces, not weaker.  `RightAdjointKernelData` says only that two
transforms are adjoint; it does not say `pull` has a right adjoint, and there
is no converse construction here or anywhere — nothing recovers a
`ConstituentRightAdjoints` from a `RightAdjointKernelData`.  So this file does
not lower the bar for supplying an adjoint kernel.  What it does is replace one
compound obligation with four whose classical proofs are separate, which is
what makes them dischargeable one at a time.  A reader who wants the weaker
hypothesis should keep using `RightAdjointKernelData` directly.

## What this file does not assert

* **Nothing constructs a `ConstituentRightAdjoints` or a
  `ConstituentLeftAdjoints`.**  Each of the three adjunctions is a real
  theorem about real geometry, and an abstract `Correspondence` carries none
  of them — `FourierMukai/Basic.lean` says in as many words that it does not
  assume `pull` and `push` are adjoint in either order.
* **Nothing produces the identification `rightAdjoint ≅ C'.transform Q`.**  It
  is an argument to the assembly, not a field of the ledger, precisely so that
  it cannot be mistaken for something the three adjunctions imply.  They do
  not imply it: the composite of three right adjoints is a functor `𝒴 ⥤ 𝒳`
  with no reason to be a transform of anything.
* **Nothing relates `ConstituentLeftAdjoints` to `ConstituentRightAdjoints`.**
  Classically the two composites differ by the dualizing twist; no dualizing
  object exists in this repository.
* No projection formula, no base change, no Grothendieck duality, and no
  dualizing object is stated or used anywhere in this file.
* No triangulated structure is used.  Adjunctions of the constituents are
  statements about the underlying functors.
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory

universe v v' v'' v''' u u' u'' u'''

variable {𝒳 : Type u} {𝒴 : Type u'} {𝒵 : Type u''} {𝒵' : Type u'''}
  [Category.{v} 𝒳] [Category.{v'} 𝒴] [Category.{v''} 𝒵] [Category.{v'''} 𝒵']

/-- Right adjoints for the three functors a transform is built from.

The three fields are independent geometric inputs: pullback/pushforward
adjunction, rigidity of the kernel, and Grothendieck duality respectively.
Nothing here relates them, and nothing constructs any of them. -/
structure ConstituentRightAdjoints (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) where
  /-- A right adjoint of `pull`. -/
  pullRight : 𝒵 ⥤ 𝒳
  /-- The adjunction, in the role of `Lp^* ⊣ Rp_*`. -/
  pullAdj : C.pull ⊣ pullRight
  /-- A right adjoint of the twist by `K`. -/
  twistRight : 𝒵 ⥤ 𝒵
  /-- The adjunction, in the role of `(− ⊗ K) ⊣ (− ⊗ K^∨)`. -/
  twistAdj : C.tensor.obj K ⊣ twistRight
  /-- A right adjoint of `push`. -/
  pushRight : 𝒴 ⥤ 𝒵
  /-- The adjunction, in the role of `Rq_* ⊣ q^!`.  This is the Grothendieck
  duality slot, and the one a dualizing object would eventually describe. -/
  pushAdj : C.push ⊣ pushRight

/-- Left adjoints for the three functors a transform is built from, mirroring
`ConstituentRightAdjoints`.  Independent of it: classically the two composites
differ by the dualizing twist. -/
structure ConstituentLeftAdjoints (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) where
  /-- A left adjoint of `pull`. -/
  pullLeft : 𝒵 ⥤ 𝒳
  /-- The adjunction. -/
  pullAdj : pullLeft ⊣ C.pull
  /-- A left adjoint of the twist by `K`. -/
  twistLeft : 𝒵 ⥤ 𝒵
  /-- The adjunction. -/
  twistAdj : twistLeft ⊣ C.tensor.obj K
  /-- A left adjoint of `push`. -/
  pushLeft : 𝒴 ⥤ 𝒵
  /-- The adjunction. -/
  pushAdj : pushLeft ⊣ C.push

namespace ConstituentRightAdjoints

variable {C : Correspondence 𝒳 𝒴 𝒵} {K : 𝒵} (A : ConstituentRightAdjoints C K)

/-- The composite of the three right adjoints, in the order that makes it an
adjoint of the transform: `q^!`, then the dual twist, then `Rp_*`. -/
def rightAdjoint : 𝒴 ⥤ 𝒳 :=
  A.pushRight ⋙ A.twistRight ⋙ A.pullRight

/-- **The transform is left adjoint to the composite.**

`Adjunction.comp` twice, and nothing else.  Stated as a `def` producing the
adjunction rather than as a field, because it is derived: a caller who supplies
the three constituent adjunctions has already supplied this. -/
def adj : C.transform K ⊣ A.rightAdjoint :=
  A.pullAdj.comp (A.twistAdj.comp A.pushAdj)

include A in
/-- The transform is a left adjoint. -/
theorem isLeftAdjoint : (C.transform K).IsLeftAdjoint := A.adj.isLeftAdjoint

/-- **The assembly.**

Given an identification of the composite right adjoint with a transform of the
opposite correspondence, that transform's kernel is a right adjoint kernel.

`e` is the supplied remainder, and it is deliberately an argument rather than a
field: the three adjunctions do not imply it.  Geometrically it is the
projection formula together with the identification of `q^!` as a twisted
pullback, which is what puts `ω[dim]` into the kernel `Q`. -/
def toRightAdjointKernelData {C' : Correspondence 𝒴 𝒳 𝒵'} {Q : 𝒵'}
    (e : A.rightAdjoint ≅ C'.transform Q) : RightAdjointKernelData C C' K where
  adjKernel := Q
  adj := A.adj.ofNatIsoRight e

@[simp]
theorem toRightAdjointKernelData_adjKernel {C' : Correspondence 𝒴 𝒳 𝒵'} {Q : 𝒵'}
    (e : A.rightAdjoint ≅ C'.transform Q) :
    (A.toRightAdjointKernelData e).adjKernel = Q := rfl

include A in
/-- **A transform whose constituents have right adjoints, and whose composite
adjoint is a transform, has a kernel-presented right adjoint.**

The statement `toRightAdjointKernelData` proves, phrased against the existing
`Correspondence.IsKernelFunctor`.  Note again which correspondence: `C'`. -/
theorem isKernelFunctor_rightAdjoint {C' : Correspondence 𝒴 𝒳 𝒵'} {Q : 𝒵'}
    (e : A.rightAdjoint ≅ C'.transform Q) :
    C'.IsKernelFunctor A.rightAdjoint :=
  ⟨Q, ⟨e⟩⟩

end ConstituentRightAdjoints

namespace ConstituentLeftAdjoints

variable {C : Correspondence 𝒳 𝒴 𝒵} {K : 𝒵} (A : ConstituentLeftAdjoints C K)

/-- The composite of the three left adjoints. -/
def leftAdjoint : 𝒴 ⥤ 𝒳 :=
  A.pushLeft ⋙ A.twistLeft ⋙ A.pullLeft

/-- **The composite is left adjoint to the transform.**  `Adjunction.comp`
twice, mirroring `ConstituentRightAdjoints.adj`. -/
def adj : A.leftAdjoint ⊣ C.transform K :=
  A.pushAdj.comp (A.twistAdj.comp A.pullAdj)

include A in
/-- The transform is a right adjoint. -/
theorem isRightAdjoint : (C.transform K).IsRightAdjoint := A.adj.isRightAdjoint

/-- **The assembly**, mirroring `ConstituentRightAdjoints.toRightAdjointKernelData`.
`e` is supplied for the same reason and carries the same geometric content. -/
def toLeftAdjointKernelData {C' : Correspondence 𝒴 𝒳 𝒵'} {Q : 𝒵'}
    (e : A.leftAdjoint ≅ C'.transform Q) : LeftAdjointKernelData C C' K where
  adjKernel := Q
  adj := A.adj.ofNatIsoLeft e

@[simp]
theorem toLeftAdjointKernelData_adjKernel {C' : Correspondence 𝒴 𝒳 𝒵'} {Q : 𝒵'}
    (e : A.leftAdjoint ≅ C'.transform Q) :
    (A.toLeftAdjointKernelData e).adjKernel = Q := rfl

include A in
/-- **A transform whose constituents have left adjoints, and whose composite
adjoint is a transform, has a kernel-presented left adjoint.** -/
theorem isKernelFunctor_leftAdjoint {C' : Correspondence 𝒴 𝒳 𝒵'} {Q : 𝒵'}
    (e : A.leftAdjoint ≅ C'.transform Q) :
    C'.IsKernelFunctor A.leftAdjoint :=
  ⟨Q, ⟨e⟩⟩

end ConstituentLeftAdjoints

end CategoryTheory.Triangulated.FourierMukai
