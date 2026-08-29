/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelDualizingTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.FourierMukai

/-!
# The swap of an endocorrespondence, and a geometric dual kernel

`KernelDualizingTwist.lean` produces a `RightAdjointKernelData` whose opposite
is the **reversed** correspondence `geometricCorrespondence X X Z q p`.
`KernelAutoequivalence.DualKernel` needs the **same** correspondence on both
sides, and for `p ≠ q` those are different values. That mismatch — not any
remaining duality — is all that stood between the previous file and a dual
kernel.

This file closes it. Classically `Z = X × X` and the missing ingredient is the
swap `σ` exchanging the two factors, under which the reversed correspondence
becomes the original one and the kernel is carried along.

## The derivation, and why the kernel is `Rσ_*Q` rather than `σ^*Q`

With `q = σ ≫ p` and `p = σ ≫ q`, pullback is contravariant and pushforward
covariant, so `Lq^* ≅ Lp^* ⋙ Lσ^*` and `Rp_* ≅ Rσ_* ⋙ Rq_*`.  Substituting
both into the reversed transform leaves

`Lp^* ⋙ [ Lσ^* ⋙ (Q ⊗ −) ⋙ Rσ_* ] ⋙ Rq_*`

and the bracket is exactly the right-slot projection formula at `σ`, which
collapses it to `(Rσ_* Q) ⊗ −`.  So the transported kernel is `Rσ_* Q`.

The classical statement uses `σ^* Q`, and the two agree because `σ` is an
involution *isomorphism*. That hypothesis is **not** assumed here: nothing in
the derivation needs `σ` invertible, and asking for it would be an unconsumed
hypothesis. `Rσ_*` is what the projection formula hands back, so `Rσ_*` is what
the kernel is written with.

## The three inputs

* `HasPullbackSwap σ p q` — `Lq^* ≅ Lp^* ⋙ Lσ^*`, with `σ ≫ p = q` as a
  **guard**;
* `HasPushforwardSwap σ p q` — `Rp_* ≅ Rσ_* ⋙ Rq_*`, with `σ ≫ q = p` as a
  guard;
* `HasProjectionFormulaRight σ` — an **existing** class, consumed here at a
  further site.

The guards follow `HasPullbackRetraction` and `HasPushforwardRetraction`: the
composition identity is carried but not consumed, and the `iso` field is what
the derivation uses. The guard is what makes `iso` the right thing to ask for.

Neither swap class is reduced to `GeometricDerivedPullbackComposition`, for the
reason `KernelConvolution.lean` already gives about a different pair: that class
is stated at the literal `f ≫ g`, so bridging it to `q` would need `eqToHom`
transport across compound terms.

## What comes out

`geometricDualAdjointKernelData` is a `RightAdjointKernelData` for the geometric
correspondence **against itself**, so `DualKernel.ofRightAdjointKernel` applies.
`geometricDualKernel` is the result: a `DualKernel` for a kernel
autoequivalence built on the geometric correspondence, with dual kernel

`Rσ_*(K^∨ ⊗ ω_q)`

— the classical `P^∨ ⊗ p^*ω_X[dim X]`, assembled entirely from named contracts.

## What this file does not assert

* **Nothing constructs a `HasPullbackSwap` or a `HasPushforwardSwap`**, and no
  morphism is shown to admit one. Inhabitant-free, like every ledger below it.
* Nothing identifies `Z` with `X × X` or `σ` with an actual factor exchange;
  the classes are stated at an arbitrary `σ : Z ⟶ Z` with the guards making the
  intended instantiation precise.
* `σ` is not assumed invertible, an involution, or an isomorphism, and
  `Rσ_* ≅ σ^*` is not claimed.
* **No criterion for the equivalence.** `geometricKernelAutoequivalence` takes
  the equivalence and its comparison isomorphism as arguments.
  `geometricKernelAutoequivalenceOfAdjoint` does not — it derives both from the
  invertibility of one adjunction's unit and counit — but that invertibility is
  itself assumed, and nothing here establishes it. Classically it is the
  Bondal--Orlov criterion, which needs geometry this repository does not have.
  So a transform is still never *shown* to be an equivalence; what changed is
  only the shape of the assumption.
* No Serre duality, no smoothness, no properness, no relative dimension.
-/

universe u

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section Contracts

/-- **Pullback along the swap, supplied.**

`Lq^* ≅ Lp^* ⋙ Lσ^*` for `σ ≫ p = q`. The composition identity is a guard: the
derivation uses `iso` alone, and the guard is what makes `iso` the right thing
to ask for. -/
class HasPullbackSwap {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (σ : Z ⟶ Z) (p q : Z ⟶ X)
    [HasCoherentPullback σ] [HasCoherentPullback p] [HasCoherentPullback q] where
  /-- The composition identity. A guard, not consumed. -/
  comm : σ ≫ p = q
  /-- Pullback along `q` is pullback along `p` followed by pullback along `σ`. -/
  iso : boundedCoherentDerivedPullback q ≅
    boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback σ

/-- **Pushforward along the swap, supplied.**

`Rp_* ≅ Rσ_* ⋙ Rq_*` for `σ ≫ q = p`. Guard as above. -/
class HasPushforwardSwap {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (σ : Z ⟶ Z) (p q : Z ⟶ X)
    [HasDerivedPushforward σ] [HasDerivedPushforward p] [HasDerivedPushforward q] where
  /-- The composition identity. A guard, not consumed. -/
  comm : σ ≫ q = p
  /-- Pushforward along `p` is pushforward along `σ` followed by along `q`. -/
  iso : derivedPushforward p ≅ derivedPushforward σ ⋙ derivedPushforward q

/-- The pullback swap comparison, named. -/
def pullbackSwapIso {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (σ : Z ⟶ Z) (p q : Z ⟶ X)
    [HasCoherentPullback σ] [HasCoherentPullback p] [HasCoherentPullback q]
    [HasPullbackSwap σ p q] :
    boundedCoherentDerivedPullback q ≅
      boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback σ :=
  HasPullbackSwap.iso

/-- The pushforward swap comparison, named. -/
def pushforwardSwapIso {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (σ : Z ⟶ Z) (p q : Z ⟶ X)
    [HasDerivedPushforward σ] [HasDerivedPushforward p] [HasDerivedPushforward q]
    [HasPushforwardSwap σ p q] :
    derivedPushforward p ≅ derivedPushforward σ ⋙ derivedPushforward q :=
  HasPushforwardSwap.iso

end Contracts

section Swap

variable (X Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
  (σ : Z ⟶ Z) (p q : Z ⟶ X)
  [HasCoherentPullback σ] [HasCoherentPullback p] [HasCoherentPullback q]
  [HasDerivedPushforward σ] [HasDerivedPushforward p] [HasDerivedPushforward q]
  [HasCoherentDerivedTensor Z]
  [HasPullbackSwap σ p q] [HasPushforwardSwap σ p q]
  [HasProjectionFormulaRight σ]

/-- **The reversed transform is the original one with the swapped kernel.**

The content of this file. Substitute the two swap comparisons into
`(geometricCorrespondence X X Z q p).transform Q`, and the middle three factors
`Lσ^* ⋙ (Q ⊗ −) ⋙ Rσ_*` are exactly the right-slot projection formula at `σ`,
which collapses them to the twist by `Rσ_* Q`. -/
noncomputable def geometricSwapIso (Q : SchemeBoundedCoherentDerivedCategory Z.left) :
    (geometricCorrespondence X X Z q p).transform Q ≅
      (geometricCorrespondence X X Z p q).transform
        ((derivedPushforward σ).obj Q) :=
  Functor.isoWhiskerRight (pullbackSwapIso σ p q)
      ((derivedTensor Z).obj Q ⋙ derivedPushforward p) ≪≫
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p)
        (Functor.isoWhiskerLeft
          (boundedCoherentDerivedPullback σ ⋙ (derivedTensor Z).obj Q)
          (pushforwardSwapIso σ p q)) ≪≫
      Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p)
        (Functor.isoWhiskerRight (HasProjectionFormulaRight.iso Q)
          (derivedPushforward q))

end Swap

section DualKernel

variable (X Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
  (σ : Z ⟶ Z) (p q : Z ⟶ X) (K : SchemeBoundedCoherentDerivedCategory Z.left)
  [HasCoherentPullback σ] [HasCoherentPullback p] [HasCoherentPullback q]
  [HasDerivedPushforward σ] [HasDerivedPushforward p] [HasDerivedPushforward q]
  [HasCoherentDerivedTensor Z]
  [HasPullbackSwap σ p q] [HasPushforwardSwap σ p q]
  [HasProjectionFormulaRight σ]
  [HasDerivedPullbackAdjunction p] [HasKernelDual Z K]
  [HasTwistedInversePullback q] [HasDualizingTwist q]

/-- **The geometric dual kernel object**: `Rσ_*(K^∨ ⊗ ω_q)`.

The classical `P^∨ ⊗ p^*ω_X[dim X]`, with `ω_q` carrying the dualizing twist
and `Rσ_*` the exchange of the two factors. Every ingredient is a `def`, not a
supplied field. -/
noncomputable def geometricDualKernelObj :
    SchemeBoundedCoherentDerivedCategory Z.left :=
  (derivedPushforward σ).obj (geometricAdjointKernel q K)

/-- **A right adjoint kernel against the same correspondence.**

The previous ledger's datum, transported along the swap. Its opposite
correspondence is now `geometricCorrespondence X X Z p q` itself, which is what
`DualKernel` requires. -/
@[reducible] noncomputable def geometricDualAdjointKernelData :
    RightAdjointKernelData (geometricCorrespondence X X Z p q)
      (geometricCorrespondence X X Z p q) K where
  adjKernel := geometricDualKernelObj X Z σ q K
  adj := ((geometricRightAdjointKernelData X X Z p q K).adj).ofNatIsoRight
    (geometricSwapIso X Z σ p q (geometricAdjointKernel q K))

@[simp]
theorem geometricDualAdjointKernelData_adjKernel :
    (geometricDualAdjointKernelData X Z σ p q K).adjKernel =
      geometricDualKernelObj X Z σ q K := rfl

/-- **A kernel autoequivalence on the geometric correspondence**, from a
supplied equivalence.

The equivalence and its comparison isomorphism are arguments, exactly as in
`KernelAutoequivalence` itself. That a geometric Fourier--Mukai transform *is*
an equivalence is the classical theorem this lane is conditional on, and
nothing here approaches it. The point of naming this is that its `corr` and
`kernel` are the geometric ones definitionally, so the dual kernel below
typechecks against it. -/
noncomputable def geometricKernelAutoequivalence
    (equiv : SchemeBoundedCoherentDerivedCategory X.left ≌
      SchemeBoundedCoherentDerivedCategory X.left)
    (iso : equiv.functor ≅
      (geometricCorrespondence X X Z p q).transform K) :
    Symmetry.KernelAutoequivalence
      (SchemeBoundedCoherentDerivedCategory X.left)
      (SchemeBoundedCoherentDerivedCategory Z.left) where
  corr := geometricCorrespondence X X Z p q
  kernel := K
  equiv := equiv
  iso := iso

/-- **A geometric dual kernel.**

The end of the arc. `DualKernel.ofRightAdjointKernel` at the swapped datum: the
quasi-inverse of the supplied equivalence is the transform of the same
correspondence with kernel `Rσ_*(K^∨ ⊗ ω_q)` — the classical
`P^∨ ⊗ p^*ω_X[dim X]` — and every step from the three constituent adjunctions
onward is derived rather than supplied.

What is still supplied is the equivalence itself, and the geometric contracts.
Nothing here constructs either. -/
noncomputable def geometricDualKernel
    (equiv : SchemeBoundedCoherentDerivedCategory X.left ≌
      SchemeBoundedCoherentDerivedCategory X.left)
    (iso : equiv.functor ≅
      (geometricCorrespondence X X Z p q).transform K) :
    Symmetry.KernelAutoequivalence.DualKernel
      (geometricKernelAutoequivalence X Z p q K equiv iso) :=
  Symmetry.KernelAutoequivalence.DualKernel.ofRightAdjointKernel _
    (geometricDualAdjointKernelData X Z σ p q K)

@[simp]
theorem geometricDualKernel_dual
    (equiv : SchemeBoundedCoherentDerivedCategory X.left ≌
      SchemeBoundedCoherentDerivedCategory X.left)
    (iso : equiv.functor ≅
      (geometricCorrespondence X X Z p q).transform K) :
    (geometricDualKernel X Z σ p q K equiv iso).dual =
      geometricDualKernelObj X Z σ q K := rfl

/-! ### The equivalence, no longer supplied

`geometricKernelAutoequivalence` above takes the equivalence as an argument.
This does not: given that the assembled adjunction's unit and counit are
invertible, `KernelAutoequivalence.ofRightAdjointKernel` builds the equivalence,
and the dual kernel comes with it at no further cost.

The invertibility is still an assumption — it is the second half of the layer-3
work, and classically it is the Bondal--Orlov criterion. What has changed is its
shape: it is pointwise and checkable, and its two halves are full faithfulness
and essential surjectivity, which is what a geometric criterion would deliver.
Nothing here supplies it. -/

/-- **A geometric kernel autoequivalence with no supplied equivalence.**

Everything is now the ledger plus the invertibility of one adjunction's unit and
counit. Compare `geometricKernelAutoequivalence`, which takes an equivalence and
a comparison isomorphism outright. -/
-- `@[reducible]` so that instance search sees `ofRightAdjointKernel` and finds
-- the six exactness instances stated against it; without this the geometric
-- equivalence cannot reach `actStabOfDual`. Same reason `trans` and `id` are
-- reducible in `Symmetry/Autoequivalence/FourierMukai`.
@[reducible] noncomputable def geometricKernelAutoequivalenceOfAdjoint
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)] :
    Symmetry.KernelAutoequivalence
      (SchemeBoundedCoherentDerivedCategory X.left)
      (SchemeBoundedCoherentDerivedCategory Z.left) :=
  Symmetry.KernelAutoequivalence.ofRightAdjointKernel
    (geometricCorrespondence X X Z p q) K
    (geometricDualAdjointKernelData X Z σ p q K)

@[simp]
theorem geometricKernelAutoequivalenceOfAdjoint_kernel
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)] :
    (geometricKernelAutoequivalenceOfAdjoint X Z σ p q K).kernel = K := rfl

/-- **Its dual kernel, for free.**

`toEquivalence`'s inverse is the adjunction's right adjoint definitionally, so
`invIso` is `Iso.refl` — the same datum that produced the equivalence produces
the dual kernel, with no trip through `rightAdjointUniq`. The dual is
`Rσ_*(K^∨ ⊗ ω_q)`, as before. -/
@[reducible] noncomputable def geometricDualKernelOfAdjoint
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)] :
    Symmetry.KernelAutoequivalence.DualKernel
      (geometricKernelAutoequivalenceOfAdjoint X Z σ p q K) :=
  Symmetry.KernelAutoequivalence.dualKernelOfRightAdjointKernel
    (geometricCorrespondence X X Z p q) K
    (geometricDualAdjointKernelData X Z σ p q K)

@[simp]
theorem geometricDualKernelOfAdjoint_dual
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)] :
    (geometricDualKernelOfAdjoint X Z σ p q K).dual =
      geometricDualKernelObj X Z σ q K := rfl

/-! ### The lane's payoff: a geometric transform transports a stability condition

Everything above is machinery; this is what it was for. `KernelAutoequivalence`
exists in order to act on `StabilityCondition.WithClassMap`, and until now the
*geometric* side could not reach that action at all — not for a mathematical
reason, but because instance search could not see through `geometricCorrespondence`
and the constructors above it to the exactness the contracts already carry.

`actStabOfDual` asks for twelve instance arguments about `A.corr` and
`A.equiv`. They are now all reachable. -/

/-- **A geometric kernel autoequivalence transports a stability condition.**

`KernelAutoequivalence.actStabOfDual` at the geometric autoequivalence and its
derived dual kernel. The compatibility hypothesis is stated against
`transformK₀` of the *constructed* dual kernel `Rσ_*(K^∨ ⊗ ω_q)`, so it is
checkable in kernel terms rather than against an opaque `K₀.map`.

Conditional, as everything in this lane is: on the adjoint ledger, on the swap,
and on the invertibility of the assembled adjunction's unit and counit. Nothing
here supplies any of those. What it does show is that the geometric side reaches
the transport once they are supplied — which, before this, it did not. -/
noncomputable def geometricActStabOfDual
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)]
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    (lam : Λ →+ Λ)
    (hlam : ∀ x, v ((geometricCorrespondence X X Z p q).transformK₀
        (geometricDualKernelObj X Z σ q K) x) = lam (v x))
    (s : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v) :
    StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v :=
  (geometricKernelAutoequivalenceOfAdjoint X Z σ p q K).actStabOfDual v
    (geometricDualKernelOfAdjoint X Z σ p q K) lam hlam s

/-! ### Into the group, not merely into a map

`geometricActStabOfDual` is a *function* on stability conditions.
`Stability/ClassMap.lean` builds a genuine `Group` — `GroupAction.AutPairQuot v`
— acting on `WithClassMap C v`, and "the transform transports" and "the
transform is an element of the group that acts" are different claims. The
abstract file makes the point and proves the second for a `KernelAutoequivalence`
with a `DualKernel`; both are now available geometrically, so the geometric side
reaches the group too.

The strengthening over `actStabOfDual` is `lam`'s **invertibility**, and it is a
real hypothesis rather than repackaging: a geometric kernel autoequivalence with
a non-invertible compatible `lam` still transports stability conditions, it just
is not a member of this group. -/

/-- **A geometric kernel autoequivalence is an element of the acting group.**

`KernelAutoequivalence.toAutPair` at the geometric autoequivalence and its
derived dual kernel, with the compatibility stated against the *constructed*
dual kernel `Rσ_*(K^∨ ⊗ ω_q)` rather than an opaque `K₀.map`. -/
noncomputable def geometricToAutPair
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)]
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    (lam : Λ ≃+ Λ)
    (hlam : ∀ x, v ((geometricCorrespondence X X Z p q).transformK₀
        (geometricDualKernelObj X Z σ q K) x) = lam (v x)) :
    GroupAction.AutPair v :=
  (geometricKernelAutoequivalenceOfAdjoint X Z σ p q K).toAutPair v
    (geometricDualKernelOfAdjoint X Z σ p q K) lam hlam

/-- **The group element acts by the transport it came from.**

At the quotient, where the `MulAction` actually lives. `rfl`, as in the abstract
file — but worth stating for the same reason it was worth stating there: the
transported stability condition is the image of `σ` under a group element, not
merely the value of a map. -/
theorem geometricMk_toAutPair_smul
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.unit.app E)]
    [∀ E, IsIso ((geometricDualAdjointKernelData X Z σ p q K).adj.counit.app E)]
    {Λ : Type u} [AddCommGroup Λ]
    (v : K₀ (SchemeBoundedCoherentDerivedCategory X.left) →+ Λ)
    (lam : Λ ≃+ Λ)
    (hlam : ∀ x, v ((geometricCorrespondence X X Z p q).transformK₀
        (geometricDualKernelObj X Z σ q K) x) = lam (v x))
    (s : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X.left) v) :
    GroupAction.AutPairQuot.mk (geometricToAutPair X Z σ p q K v lam hlam) • s =
      geometricActStabOfDual X Z σ p q K v lam.toAddMonoidHom
        (fun x => hlam x) s :=
  rfl

end DualKernel

end CategoryTheory.Triangulated.StabilityCondition.Families
