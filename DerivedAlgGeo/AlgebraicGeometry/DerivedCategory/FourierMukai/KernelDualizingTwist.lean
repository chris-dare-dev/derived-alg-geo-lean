/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelAdjunction
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelConvolution

/-!
# The dualizing twist, and a geometric adjoint kernel

`KernelAdjunction.lean` produces a `ConstituentRightAdjoints` for the geometric
correspondence, so the geometric transform is left adjoint to the composite

`q^! ⋙ (− ⊗ K^∨) ⋙ Rp_*`.

It stops there, deliberately: nothing said that composite is again a
*transform*, and `HasTwistedInversePullback` was kept opaque about the shape of
`q^!` precisely so the two obligations would stay apart.

This file supplies the missing shape and closes the gap. One new class says
`q^!` is a twisted pullback; the tensor associator — from the **existing** coherent
tensor root — collects the two twists into one; and the
composite becomes the transform of the *reversed* correspondence with the
classical kernel

`Q = K^∨ ⊗ ω_q`.

## The one new contract

`HasDualizingTwist q` supplies an object `ω_q` and
`q^! ≅ Lq^*(−) ⊗ ω_q`. Two things about its shape are deliberate.

**No shift index.** Classically the twist is `ω_q[dim q]`. The relative
dimension appears nowhere here, because nothing consumes it: `ω_q` is asked for
as the object already carrying whatever shift it carries. Asking for a
dimension and a shift separately would add a hypothesis the derivation never
uses, which is the shape this lane's reviews have attacked twice.

**A new contract at `q`.** The class needs `HasCoherentPullback q` — pullback
along the *pushforward's* morphism — which `geometricCorrespondence` never asks
for. That is the mirror of `KernelAdjunction.lean` needing
`HasDerivedPushforward p`, and it is not an accident: the two extra contracts
are exactly what makes the reversed correspondence
`geometricCorrespondence Y X Z q p` expressible, and the adjoint kernel lives
there.

## What comes out

`geometricRightAdjointKernelData` is a genuine
`FourierMukai.RightAdjointKernelData` for the geometric correspondence, with
the reversed correspondence as its opposite and `Q = K^∨ ⊗ ω_q` as its kernel.
Everything #768 proves about a right adjoint kernel then applies: uniqueness of
the adjoint, that the adjoint is itself a kernel functor, and the transport
lemmas.

## What does *not* come out, and why

**Not a `DualKernel`, and not for want of one more isomorphism.**
`KernelAutoequivalence.DualKernel` asks for the quasi-inverse to be a transform
of the **same** correspondence — its field is
`A.equiv.inverse ≅ A.corr.transform dual`, one `corr`. What this file produces
is a transform of the **reversed** correspondence
`geometricCorrespondence X X Z q p`, and for `p ≠ q` that is a different
`Correspondence` value even when both endpoints are `X`.

So `DualKernel.ofRightAdjointKernel` does not apply here, and nothing in this
file pretends otherwise. Bridging the two needs an identification of the two
correspondences' transforms — classically pullback along the swap
`σ : X × X → X × X`. That is a further ledger, named in the closing section;
`KernelSwap.lean` is it, and it lands `Rσ_* Q` rather than `σ^* Q` — the two
agree for an involution isomorphism, which that file does not need to assume.

## What this file does not assert

* **Nothing constructs a `HasDualizingTwist`**, and no morphism is shown to
  admit one. Inhabitant-free, like every ledger it builds on.
* Nothing identifies `ω_q` with a relative dualizing complex, a canonical
  bundle, or a shift of either; it is an object with one stated property.
* No Serre duality, no smoothness, no properness, no relative dimension.
* Nothing relates `HasDualizingTwist q` to `HasDualizingTwist p`, and no
  compatibility between the two directions is stated.
* No claim that any geometric transform is an equivalence.
-/

universe u

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section Contract

/-- **The twisted inverse image is a twisted pullback, supplied.**

The shape `HasTwistedInversePullback` refuses to assume: `f^!(−) ≅ Lf^*(−) ⊗ ω_f`.
Classically this holds for `f` smooth and proper with `ω_f` the relative
dualizing complex placed in degree `−dim f`, and a caller discharging this class
is asserting exactly that much.

The shift is folded into `dualizingTwist` rather than carried separately,
because no consumer here uses a relative dimension. -/
class HasDualizingTwist {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasDerivedTensor T] [HasDerivedPushforward f]
    [HasTwistedInversePullback f] where
  /-- The dualizing object, in the role of `ω_f[dim f]`. -/
  dualizingTwist : SchemeBoundedCoherentDerivedCategory T.left
  /-- `f^!` is pullback followed by the twist. -/
  iso : twistedInversePullback f ≅
    boundedCoherentDerivedPullback f ⋙ (derivedTensor T).obj dualizingTwist

/-- The dualizing object, named. -/
def dualizingTwist {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasDerivedTensor T] [HasDerivedPushforward f]
    [HasTwistedInversePullback f] [HasDualizingTwist f] :
    SchemeBoundedCoherentDerivedCategory T.left :=
  HasDualizingTwist.dualizingTwist f

/-- The decomposition of `f^!`, named. -/
def dualizingTwistIso {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasDerivedTensor T] [HasDerivedPushforward f]
    [HasTwistedInversePullback f] [HasDualizingTwist f] :
    twistedInversePullback f ≅
      boundedCoherentDerivedPullback f ⋙ (derivedTensor T).obj (dualizingTwist f) :=
  HasDualizingTwist.iso

/-- **The adjoint kernel, constructed.**

`Q = K^∨ ⊗ ω_q` — the classical dual kernel, with the twist that
`p^* ω_X [dim X]` contributes in the smooth projective case here carried
wholesale by `ω_q`.

This is a `def` with a value, not a supplied field: both factors come from
classes already on the table.  Written with explicit binders rather than from
the assembly section's `variable` block, because it depends on neither `p` nor
`X` and should not silently acquire them. -/
noncomputable def geometricAdjointKernel {Y Z : SchemeBaseChange S}
    [IsLocallyNoetherian Y.left] [IsLocallyNoetherian Z.left]
    (q : Z ⟶ Y) (K : SchemeBoundedCoherentDerivedCategory Z.left)
    [HasDerivedTensor Z] [HasDerivedPushforward q] [HasKernelDual Z K]
    [HasCoherentPullback q] [HasTwistedInversePullback q] [HasDualizingTwist q] :
    SchemeBoundedCoherentDerivedCategory Z.left :=
  ((derivedTensor Z).obj (dualKernel Z K)).obj (dualizingTwist q)

end Contract

section Assembly

variable (X Y Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian Z.left]

variable (p : Z ⟶ X) (q : Z ⟶ Y) (K : SchemeBoundedCoherentDerivedCategory Z.left)
  [HasCoherentPullback p] [HasCoherentDerivedTensor Z] [HasDerivedPushforward q]
  [HasDerivedPushforward p] [HasDerivedPullbackAdjunction p]
  [HasKernelDual Z K] [HasTwistedInversePullback q]
  [HasCoherentPullback q] [HasDualizingTwist q]

/-- **The composite right adjoint is the reversed transform.**

The whole content of this file. Reading the composite
`q^! ⋙ (− ⊗ K^∨) ⋙ Rp_*` left to right: replace `q^!` by `Lq^* ⋙ (− ⊗ ω_q)`,
then collect the two adjacent twists with the tensor associator. What is left
is `Lq^* ⋙ (− ⊗ Q) ⋙ Rp_*`, which is exactly the transform of the reversed
correspondence.

The associator is `coherentDerivedTensorAssoc`, from the existing
`HasCoherentDerivedTensor` root, consumed here at a further site.  The root
rather than the legacy associator-only class: `scripts/check_coherent_families.py`
requires it, and it also removes a diamond — `HasCoherentDerivedTensor` supplies
`HasDerivedTensor` through `hasDerivedTensorOfCoherent`, so the correspondence,
the kernel dual and the associator all read the *same* tensor instance. -/
noncomputable def geometricRightAdjointIso :
    (geometricConstituentRightAdjoints X Y Z p q K).rightAdjoint ≅
      (geometricCorrespondence Y X Z q p).transform
        (geometricAdjointKernel q K) :=
  Functor.isoWhiskerRight (dualizingTwistIso q)
      ((derivedTensor Z).obj (dualKernel Z K) ⋙ derivedPushforward p) ≪≫
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback q)
      (Functor.isoWhiskerRight
        (coherentDerivedTensorAssoc Z (dualKernel Z K) (dualizingTwist q))
        (derivedPushforward p))

/-- **A geometric right adjoint kernel.**

The payoff: a genuine `RightAdjointKernelData` for the geometric
correspondence, whose opposite is the reversed correspondence and whose kernel
is the constructed `K^∨ ⊗ ω_q`. Everything `FourierMukai/Adjunction.lean`
proves about a right adjoint kernel now applies geometrically, conditional on
the ledger.

It is **not** a `DualKernel`: that needs the opposite correspondence to be the
same one, and this one is reversed. See the module docstring. -/
@[reducible] noncomputable def geometricRightAdjointKernelData :
    RightAdjointKernelData (geometricCorrespondence X Y Z p q)
      (geometricCorrespondence Y X Z q p) K :=
  (geometricConstituentRightAdjoints X Y Z p q K).toRightAdjointKernelData
    (geometricRightAdjointIso X Y Z p q K)

@[simp]
theorem geometricRightAdjointKernelData_adjKernel :
    (geometricRightAdjointKernelData X Y Z p q K).adjKernel =
      geometricAdjointKernel q K := rfl

/-- **The composite adjoint is a kernel functor for the reversed
correspondence.**

`RightAdjointKernelData.isKernelFunctor_of_adj` at the assembled datum. Stated
because "the adjoint exists" and "the adjoint is again of Fourier--Mukai type"
are different claims, and the second is the one the lane is about. -/
theorem geometricRightAdjoint_isKernelFunctor :
    (geometricCorrespondence Y X Z q p).IsKernelFunctor
      (geometricConstituentRightAdjoints X Y Z p q K).rightAdjoint :=
  ⟨geometricAdjointKernel q K, ⟨geometricRightAdjointIso X Y Z p q K⟩⟩

end Assembly

/-! ## The next ledger, and what is in it

What stands between this file and a geometric `DualKernel` is not another
adjunction. It is that `DualKernel` asks for the quasi-inverse as a transform
of the **same** correspondence, while an adjoint is naturally a transform of
the **reversed** one.

Closing that needs, for an endocorrespondence `X = Y`:

* the swap `σ : Z ⟶ Z` over `X × X`, with `σ ≫ p = q` and `σ ≫ q = p`;
* pullback along it, and the identification
  `(geometricCorrespondence X X Z q p).transform Q ≅
   (geometricCorrespondence X X Z p q).transform (σ^* Q)`;
* and only then, given a supplied `KernelAutoequivalence` on that
  correspondence, `DualKernel.ofRightAdjointKernel` applies and the dual kernel
  is `Rσ_*(K^∨ ⊗ ω_q)` — the classical `P^∨ ⊗ p^* ω_X [dim X]`.

None of that is stated here; `KernelSwap.lean` states it. Note that all three
bullets are about the product's symmetry, not about duality: the duality half
of the classical statement is finished once `HasDualizingTwist` is discharged.
-/

end CategoryTheory.Triangulated.StabilityCondition.Families
