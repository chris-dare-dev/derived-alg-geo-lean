/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.AdjointAssembly

/-!
# Satisfiability witnesses for the Fourier--Mukai interfaces

`Correspondence`, `ConstituentRightAdjoints` and `ConstituentLeftAdjoints` are
supplied data that nothing in this repository discharges, and until now nothing
inhabited them either.  An interface with no inhabitant at all is one nobody has
checked for consistency: a structure whose fields cannot be simultaneously
satisfied looks exactly like a structure nobody has tried.  This file supplies
the missing check.

Following `Triangulated/GrothendieckGroup/HomFiniteWitness.lean`, which does the
same for `HomFiniteBounded` and labels itself "satisfiability only".

## The witness, and how little it says

`trivialCorrespondence C` takes `pull`, `push` and every twist to be the
identity functor of `C`.  Its transform is then the identity **definitionally**
— `transform_eq` is `rfl` — so `Adjunction.id` discharges every adjunction field
below with no transport at all.

**This shows the interfaces are consistent.  It shows nothing else.**  In
particular it does *not* show that any geometric Fourier--Mukai transform
exists, that any transform is an equivalence, or that any contract in
`AlgebraicGeometry/StabilityCondition/Families/` is dischargeable.  The whole
geometric ledger remains uninhabited, and a reader must not take a witness here
as evidence about it.

A trivial witness is also not evidence that the interface is *useful*: it is
evidence that it is not vacuous.  Those are different claims, and only the
second is made.

## What this file does not assert

* No claim that the trivial correspondence is interesting, canonical, or the
  only degenerate one.
* Nothing is an `instance`.  A global `Correspondence` instance would put the
  trivial one in front of every instance search that mentions the structure,
  which is precisely the wrong trade for a witness whose only job is to exist.
* No witness for `CoherentConvolutionData`, which needs a `MonoidalCategory`
  presentation of the kernel category, or for `ConvolutionData`, which already
  has inhabitants.
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/-- **The trivial correspondence**: pull, push and every twist are the identity.

A witness that `Correspondence` is satisfiable, and nothing more. -/
def trivialCorrespondence : Correspondence C C C where
  pull := 𝟭 C
  tensor := (Functor.const C).obj (𝟭 C)
  push := 𝟭 C

variable {C}

@[simp]
theorem trivialCorrespondence_transform (K : C) :
    (trivialCorrespondence C).transform K = 𝟭 C := rfl

/-- The trivial correspondence's own kernel is a right adjoint kernel for it.

`Adjunction.id`, since the transform is the identity on the nose. -/
def trivialRightAdjointKernelData (K : C) :
    RightAdjointKernelData (trivialCorrespondence C) (trivialCorrespondence C) K where
  adjKernel := K
  adj := Adjunction.id

@[simp]
theorem trivialRightAdjointKernelData_adjKernel (K : C) :
    (trivialRightAdjointKernelData K).adjKernel = K := rfl

/-- The mirror on the left. -/
def trivialLeftAdjointKernelData (K : C) :
    LeftAdjointKernelData (trivialCorrespondence C) (trivialCorrespondence C) K where
  adjKernel := K
  adj := Adjunction.id

@[simp]
theorem trivialLeftAdjointKernelData_adjKernel (K : C) :
    (trivialLeftAdjointKernelData K).adjKernel = K := rfl

/-- **`ConstituentRightAdjoints` is satisfiable.**

All three constituents are the identity, so all three adjunctions are
`Adjunction.id`. -/
def trivialConstituentRightAdjoints (K : C) :
    ConstituentRightAdjoints (trivialCorrespondence C) K where
  pullRight := 𝟭 C
  pullAdj := Adjunction.id
  twistRight := 𝟭 C
  twistAdj := Adjunction.id
  pushRight := 𝟭 C
  pushAdj := Adjunction.id

/-- **`ConstituentLeftAdjoints` is satisfiable**, by the same witness read on
the other side.

This is the only inhabitant of `ConstituentLeftAdjoints` in the repository, and
that is deliberate rather than an omission: `KernelAdjunction.lean` builds no
geometric left-adjoint ledger because nothing consumes one — the left adjoint of
`Lp^*` is the exceptional `p_!`, which nothing here asks for. So the structure
stays at one inhabitant, and stays listed as thin. -/
def trivialConstituentLeftAdjoints (K : C) :
    ConstituentLeftAdjoints (trivialCorrespondence C) K where
  pullLeft := 𝟭 C
  pullAdj := Adjunction.id
  twistLeft := 𝟭 C
  twistAdj := Adjunction.id
  pushLeft := 𝟭 C
  pushAdj := Adjunction.id

end CategoryTheory.Triangulated.FourierMukai
