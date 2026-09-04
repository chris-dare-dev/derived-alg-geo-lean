/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelCorrespondence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.AdjointAssembly

/-!
# A geometric adjoint ledger for the Fourier--Mukai transform

`KernelCorrespondence.lean` assembles a `Correspondence` on `Dᵇ(Coh)` from
three named contracts, and says in its own docstring that it makes **no claim
that the derived pushforward is right adjoint to the derived pullback**. This
file is the ledger for that claim, and for the two others a right adjoint of
the transform needs.

`FourierMukai/AdjointAssembly.lean` says what those three are, abstractly: a
right adjoint of `pull`, a right adjoint of the twist by `K`, and a right
adjoint of `push`. Here each becomes a named class on `Dᵇ(Coh)`, and
`geometricConstituentRightAdjoints` assembles a
`ConstituentRightAdjoints (geometricCorrespondence X Y Z p q) K` from exactly
those and no others.

## The three contracts, and what each is classically

* `HasDerivedPullbackAdjunction p` — `Lp^* ⊣ Rp_*`. The standard adjunction,
  and the one `KernelCorrespondence` explicitly declined to assume. Note that
  it needs `HasDerivedPushforward` at **`p`**, not at `q`: the right adjoint of
  pullback along `p` is pushforward along the same `p`, which is a contract the
  correspondence itself never asks for.
* `HasKernelDual Z K` — `(− ⊗^L K) ⊣ (− ⊗^L K^∨)`. Rigidity of the kernel.
  This is the "derived duals" layer, and the reason it can be stated now is
  that it finally has a consumer; the substance is that `K^∨` is again an
  object of the same category and that the dual twist is *the same bifunctor*
  applied to it.
* `HasTwistedInversePullback q` — `Rq_* ⊣ q^!`. Grothendieck duality. This is
  where a dualizing object lives, and the class deliberately does **not**
  decompose `q^!`: it names the right adjoint and nothing about its shape.

## What this ledger produces, and what it still does not

It produces `ConstituentRightAdjoints`, hence — by
`ConstituentRightAdjoints.adj` — that the geometric transform is left adjoint
to the composite `q^! ⋙ (− ⊗ K^∨) ⋙ Rp_*`. That composite is a functor
`Dᵇ(Coh Y) ⥤ Dᵇ(Coh X)`.

It does **not** produce a `RightAdjointKernelData`, because it does not show
that composite is again a *transform*. `AdjointAssembly` takes that
identification as an argument, and supplying it geometrically is the next
ledger: it needs `q^!` decomposed as `Lq^*(−) ⊗ ω_q[dim]` and the tensor
rearranged, which is the projection formula plus a dualizing object. Only then
does the classical kernel `P^∨ ⊗ p^*ω_X[dim X]` appear. See the closing section.

## Only the right side

There is no mirror producing `ConstituentLeftAdjoints`. The left adjoint of
`Lp^*` is the exceptional `p_!`, a different and much less standard object than
anything above, and nothing in this repository asks for one. Filing a class for
it would be a contract with no consumer — the shape this lane's reviews have
attacked twice.

## What this file does not assert

* **Nothing constructs an instance of any class here**, and no scheme or
  morphism is shown to admit one. Inhabitant-free, like the two ledgers it
  builds on.
* No properness, projectivity, smoothness, or finite-dimensionality hypothesis
  appears. Classically all three contracts need some of these; naming them here
  without consuming them would be adding unconsumed hypotheses, so the
  hypothesis a caller is really asserting is recorded in each docstring instead.
* No dualizing complex, no `ω`, no projection formula, and no decomposition of
  `q^!` — only its existence as a right adjoint.
* Nothing relates `HasKernelDual Z K` for different `K`, and no
  double-dual isomorphism `K^∨∨ ≅ K` is asserted.
* No `DualKernel`, and no claim that any geometric transform is an
  equivalence.
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section Contracts

/-- **Derived pullback is left adjoint to derived pushforward, supplied.**

The `Lp^* ⊣ Rp_*` slot. `KernelCorrespondence.lean` names both functors as
contracts but relates them not at all; this is the relation.

The hypothesis a caller discharging this is really asserting is the derived
adjunction on bounded coherent derived categories — which classically needs
`f` proper enough for `Rf_*` to preserve coherence, already the content of
`HasDerivedPushforward`, plus the derived form of the sheaf-level
adjunction. -/
class HasDerivedPullbackAdjunction {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasDerivedPushforward f] where
  /-- The adjunction, in the role of `Lf^* ⊣ Rf_*`. -/
  adj : boundedCoherentDerivedPullback f ⊣ derivedPushforward f

/-- The pullback/pushforward adjunction, named. -/
def derivedPullbackAdjunction {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasDerivedPushforward f]
    [HasDerivedPullbackAdjunction f] :
    boundedCoherentDerivedPullback f ⊣ derivedPushforward f :=
  HasDerivedPullbackAdjunction.adj

/-- **A dual for the kernel, supplied.**

The rigidity slot: `(− ⊗^L K)` has a right adjoint, and that right adjoint is
again a twist by an object of the same category. Classically the object is
`K^∨ = R𝓗om(K, 𝒪)` and the adjunction is tensor-hom together with the
identification of the internal Hom out of `K` with a tensor by its dual —
which needs `K` perfect.

Asking for the adjoint *in the form of a twist* rather than as an arbitrary
functor is the whole content: an arbitrary right adjoint of `− ⊗^L K` would be
the internal `R𝓗om(K, −)`, and that it is a tensor is exactly what perfectness
buys. -/
class HasKernelDual (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) where
  /-- The dual kernel, in the role of `K^∨`. -/
  dualKernel : SchemeBoundedCoherentDerivedCategory Z.left
  /-- The adjunction, in the role of `(− ⊗ K) ⊣ (− ⊗ K^∨)`. -/
  adj : (derivedTensor Z).obj K ⊣ (derivedTensor Z).obj dualKernel

/-- The dual kernel, named. -/
def dualKernel (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasKernelDual Z K] : SchemeBoundedCoherentDerivedCategory Z.left :=
  HasKernelDual.dualKernel (Z := Z) K

/-- The tensor-dual adjunction, named. -/
def kernelDualAdjunction (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasKernelDual Z K] :
    (derivedTensor Z).obj K ⊣ (derivedTensor Z).obj (dualKernel Z K) :=
  HasKernelDual.adj

/-- **A right adjoint of derived pushforward, supplied.**

The Grothendieck duality slot, `Rf_* ⊣ f^!`. Deliberately opaque: the class
names the right adjoint and asserts nothing about its shape. The classical
description `f^!(−) ≅ Lf^*(−) ⊗ ω_f[dim]` for a smooth proper `f` is a
*second* obligation, and separating them is the point — the existence of the
adjoint is what `ConstituentRightAdjoints` consumes, and the description is
what a later ledger would need to turn the composite adjoint back into a
transform. -/
class HasTwistedInversePullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] where
  /-- The right adjoint, in the role of `f^!`. -/
  twistedInverse :
    SchemeBoundedCoherentDerivedCategory U.left ⥤
      SchemeBoundedCoherentDerivedCategory T.left
  /-- The adjunction, in the role of `Rf_* ⊣ f^!`. -/
  adj : derivedPushforward f ⊣ twistedInverse

/-- The twisted inverse image, named. -/
def twistedInversePullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] [HasTwistedInversePullback f] :
    SchemeBoundedCoherentDerivedCategory U.left ⥤
      SchemeBoundedCoherentDerivedCategory T.left :=
  HasTwistedInversePullback.twistedInverse f

/-- The Grothendieck-duality adjunction, named. -/
def twistedInverseAdjunction {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] [HasTwistedInversePullback f] :
    derivedPushforward f ⊣ twistedInversePullback f :=
  HasTwistedInversePullback.adj

end Contracts

section Assembly

variable (X Y Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian Z.left]

/-- **The three constituent right adjoints, assembled from the ledger.**

Given the pullback/pushforward adjunction at `p`, a dual for the kernel `K`,
and a right adjoint of pushforward along `q`, this is a genuine
`ConstituentRightAdjoints` for the geometric correspondence — so
`ConstituentRightAdjoints.adj` applies and the geometric transform is a left
adjoint.

**This constructs no geometry.** Every input is a hypothesis; the content is
that these are exactly the inputs `ConstituentRightAdjoints` needs and there
are no others. In particular note the two contracts that the correspondence
itself does not ask for: `HasDerivedPushforward p` — pushforward along the
*pullback's* morphism — and `HasDerivedPullbackAdjunction p` relating them. -/
noncomputable def geometricConstituentRightAdjoints (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q]
    [HasDerivedPushforward p] [HasDerivedPullbackAdjunction p]
    [HasKernelDual Z K] [HasTwistedInversePullback q] :
    ConstituentRightAdjoints (geometricCorrespondence X Y Z p q) K where
  pullRight := derivedPushforward p
  pullAdj := derivedPullbackAdjunction p
  twistRight := (derivedTensor Z).obj (dualKernel Z K)
  twistAdj := kernelDualAdjunction Z K
  pushRight := twistedInversePullback q
  pushAdj := twistedInverseAdjunction q

@[simp]
theorem geometricConstituentRightAdjoints_pullRight (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q]
    [HasDerivedPushforward p] [HasDerivedPullbackAdjunction p]
    [HasKernelDual Z K] [HasTwistedInversePullback q] :
    (geometricConstituentRightAdjoints X Y Z p q K).pullRight =
      derivedPushforward p := rfl

@[simp]
theorem geometricConstituentRightAdjoints_twistRight (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q]
    [HasDerivedPushforward p] [HasDerivedPullbackAdjunction p]
    [HasKernelDual Z K] [HasTwistedInversePullback q] :
    (geometricConstituentRightAdjoints X Y Z p q K).twistRight =
      (derivedTensor Z).obj (dualKernel Z K) := rfl

@[simp]
theorem geometricConstituentRightAdjoints_pushRight (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q]
    [HasDerivedPushforward p] [HasDerivedPullbackAdjunction p]
    [HasKernelDual Z K] [HasTwistedInversePullback q] :
    (geometricConstituentRightAdjoints X Y Z p q K).pushRight =
      twistedInversePullback q := rfl

/-- **The geometric transform is a left adjoint**, conditional on the ledger.

The payoff of the assembly, and the first statement in this repository that a
geometric Fourier--Mukai transform has an adjoint at all. It is still
conditional on three supplied contracts; what it is not is conditional on an
opaque adjunction between two transforms. -/
theorem geometricTransform_isLeftAdjoint (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q]
    [HasDerivedPushforward p] [HasDerivedPullbackAdjunction p]
    [HasKernelDual Z K] [HasTwistedInversePullback q] :
    ((geometricCorrespondence X Y Z p q).transform K).IsLeftAdjoint :=
  (geometricConstituentRightAdjoints X Y Z p q K).isLeftAdjoint

end Assembly

/-! ## The next ledger, and what is in it

What this file leaves undone is precisely the step
`ConstituentRightAdjoints.toRightAdjointKernelData` takes as an argument: that
the composite right adjoint `q^! ⋙ (− ⊗ K^∨) ⋙ Rp_*` is again a **transform**,
namely the transform of the reversed correspondence
`geometricCorrespondence Y X Z q p` with some kernel `Q`.

Supplying that geometrically needs two things this repository does not have:

* a **dualizing object** `ω_q` with `q^!(−) ≅ Lq^*(−) ⊗ ω_q[dim]`, which is the
  decomposition `HasTwistedInversePullback` deliberately refuses to assume;
* enough **tensor rearrangement** on `Z` to move that twist past `− ⊗ K^∨` and
  collect it into a single kernel `Q ≅ K^∨ ⊗ ω_q[dim]`.

Only once both are named does the classical dual kernel `P^∨ ⊗ p^*ω_X[dim X]`
appear as `Q`, and only then does a geometric `RightAdjointKernelData` — and
through `KernelAutoequivalence.DualKernel.ofRightAdjointKernel`, a geometric
`DualKernel` — become available. Neither is stated here.
-/

end AlgebraicGeometry.DerivedCategory.FourierMukai
