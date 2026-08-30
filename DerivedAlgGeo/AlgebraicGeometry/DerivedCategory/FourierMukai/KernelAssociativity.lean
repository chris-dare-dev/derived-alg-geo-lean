/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelConvolution

/-!
# Associativity of the geometric convolution: the quadruple product

#542 split associativity of convolution into a free transform-level theorem
and a supplied kernel-level layer (`ConvolutionAssocData`), and recorded that
the geometric route to the latter runs through the quadruple product. This
file is that route: `geometricConvolutionAssoc` **derives** the kernel-level
isomorphism

`(P ∗ Q) ∗ R ≅ P ∗ (Q ∗ R)`

for `convKernel`, by comparing both bracketings with a common
`quadKernel = Rρ₁₄_*(ρ₁₂^*P ⊗ ρ₂₃^*Q ⊗ ρ₃₄^*R)` on a supplied quadruple
product, and `geometricConvolutionAssocData` assembles a genuine
`ConvolutionAssocData` for the geometric convolution data with **zero
supplied fields**.

## What is consumed

Almost everything is an *existing* class at new instance sites — the same
seven-input vocabulary as `geometricCompIso`, evaluated at objects rather
than whiskered as functors: two `HasFlatBaseChange` squares, one
`HasProjectionFormula` and one `HasProjectionFormulaRight` (again at
*different* morphisms, which is again why they are separate classes), two
`HasMonoidalDerivedPullback` roots, and `HasCoherentDerivedTensor`. The
tensorator and associator used here therefore belong to structures that also
state their associativity, unitality, pentagon, and triangle laws.

Two classes are new, because no existing shape covers a one-step route:

* `HasPullbackFactorization π p r` — `p^* ⋙ π^* ≅ r^*` for a triangle
  `π ≫ p = r`. Not an instance of `HasCommonPullbackRoute`: that compares
  two *two-step* routes, and degenerating one leg to an identity would drag
  in a pullback-along-identity input plus unitor transport for every use.
  (Conversely a common route is two factorizations glued; the route classes
  are left as they are because #540 already consumes them in that form.)
* `HasPushforwardFactorization π q r` — the pushforward companion.

Each factorization carries its triangle identity as a `comm` **guard**, not
consumed by the derivation, in the pattern of the route classes.

## What this file does not assert

* **Nothing constructs an instance of any class here**, new or old, and no
  scheme is shown to admit one. `QuadrupleProductGeometry` carries the
  quadruple object and its projections as data and does not assert that
  anything is a product; the guards state the intended instantiation.
* This file does not assemble the geometric construction into abstract
  `CoherentConvolutionData`; that requires functoriality of `convKernel` on
  kernel morphisms and comparison of the geometric associator/unitors with
  the coherent root. The tensor and pullback inputs themselves are coherent.
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

section Factorizations

/-- **Derived pullback along a factorization, supplied.**

For a commuting triangle `π ≫ p = r`, the two-step pullback agrees with the
one-step pullback. The equation is a guard: the derivation consumes `iso`
alone, and `comm` is what makes it the right isomorphism to ask for.

Deliberately not expressed through `HasCommonPullbackRoute`: that class
compares two two-step routes, and using it with an identity leg would demand
a pullback-along-identity input plus unitor transport at every use site. -/
class HasPullbackFactorization {T Z U : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian Z.left]
    [IsLocallyNoetherian U.left]
    (π : T ⟶ Z) (p : Z ⟶ U) (r : T ⟶ U)
    [HasCoherentPullback π] [HasCoherentPullback p] [HasCoherentPullback r] where
  /-- The triangle commutes. A guard, not consumed. -/
  comm : π ≫ p = r
  /-- The two-step pullback is the one-step pullback. -/
  iso : boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback π ≅
    boundedCoherentDerivedPullback r

/-- **Derived pushforward along a factorization, supplied.**

The pushforward companion of `HasPullbackFactorization`; guard as there. -/
class HasPushforwardFactorization {T Z U : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian Z.left]
    [IsLocallyNoetherian U.left]
    (π : T ⟶ Z) (q : Z ⟶ U) (r : T ⟶ U)
    [HasDerivedPushforward π] [HasDerivedPushforward q]
    [HasDerivedPushforward r] where
  /-- The triangle commutes. A guard, not consumed. -/
  comm : π ≫ q = r
  /-- The two-step pushforward is the one-step pushforward. -/
  iso : derivedPushforward π ⋙ derivedPushforward q ≅ derivedPushforward r

end Factorizations

section QuadrupleProduct

/-- **The quadruple product and its projections, supplied.**

`quad` plays `X₁ ×_S X₂ ×_S X₃ ×_S X₄`; the `ρ`s play its projections onto
the four pairwise products the associativity statement mentions, and the
`σ`s its projections onto the four triple products carried by the given
`TripleProductGeometry`s.

Carried as data, like `TripleProductGeometry`, and for the same reason:
nothing here consumes an assertion that any object is a product. The
commuting triangles relating `σ`s, the triples' projections, and the `ρ`s
live as guards on the factorization-class instances a caller supplies. -/
structure QuadrupleProductGeometry
    {Z₁₂ Z₂₃ Z₃₄ Z₁₃ Z₂₄ Z₁₄ : SchemeBaseChange S}
    (G₁₂₃ : TripleProductGeometry Z₁₂ Z₂₃ Z₁₃)
    (G₂₃₄ : TripleProductGeometry Z₂₃ Z₃₄ Z₂₄)
    (G₁₃₄ : TripleProductGeometry Z₁₃ Z₃₄ Z₁₄)
    (G₁₂₄ : TripleProductGeometry Z₁₂ Z₂₄ Z₁₄) where
  /-- The quadruple product `X₁ ×_S X₂ ×_S X₃ ×_S X₄`. -/
  quad : SchemeBaseChange S
  /-- Projection to `X₁ ×_S X₂`. -/
  ρ₁₂ : quad ⟶ Z₁₂
  /-- Projection to `X₂ ×_S X₃`. -/
  ρ₂₃ : quad ⟶ Z₂₃
  /-- Projection to `X₃ ×_S X₄`. -/
  ρ₃₄ : quad ⟶ Z₃₄
  /-- Projection to `X₁ ×_S X₄`, along which `quadKernel` is pushed. -/
  ρ₁₄ : quad ⟶ Z₁₄
  /-- Projection to `X₁ ×_S X₂ ×_S X₃`. -/
  σ₁₂₃ : quad ⟶ G₁₂₃.triple
  /-- Projection to `X₂ ×_S X₃ ×_S X₄`. -/
  σ₂₃₄ : quad ⟶ G₂₃₄.triple
  /-- Projection to `X₁ ×_S X₃ ×_S X₄`. -/
  σ₁₃₄ : quad ⟶ G₁₃₄.triple
  /-- Projection to `X₁ ×_S X₂ ×_S X₄`. -/
  σ₁₂₄ : quad ⟶ G₁₂₄.triple

end QuadrupleProduct

section Derivation

variable {Z₁₂ Z₂₃ Z₃₄ Z₁₃ Z₂₄ Z₁₄ : SchemeBaseChange S}
  [IsLocallyNoetherian Z₁₂.left] [IsLocallyNoetherian Z₂₃.left]
  [IsLocallyNoetherian Z₃₄.left] [IsLocallyNoetherian Z₁₃.left]
  [IsLocallyNoetherian Z₂₄.left] [IsLocallyNoetherian Z₁₄.left]
  {G₁₂₃ : TripleProductGeometry Z₁₂ Z₂₃ Z₁₃}
  {G₂₃₄ : TripleProductGeometry Z₂₃ Z₃₄ Z₂₄}
  {G₁₃₄ : TripleProductGeometry Z₁₃ Z₃₄ Z₁₄}
  {G₁₂₄ : TripleProductGeometry Z₁₂ Z₂₄ Z₁₄}
  [IsLocallyNoetherian G₁₂₃.triple.left] [IsLocallyNoetherian G₂₃₄.triple.left]
  [IsLocallyNoetherian G₁₃₄.triple.left] [IsLocallyNoetherian G₁₂₄.triple.left]
  (Q4 : QuadrupleProductGeometry G₁₂₃ G₂₃₄ G₁₃₄ G₁₂₄)
  [IsLocallyNoetherian Q4.quad.left]
  [HasCoherentPullback Q4.ρ₁₂] [HasCoherentPullback Q4.ρ₂₃]
  [HasCoherentPullback Q4.ρ₃₄] [HasDerivedPushforward Q4.ρ₁₄]
  [HasCoherentPullback G₁₂₃.πXY] [HasCoherentPullback G₁₂₃.πYW]
  [HasCoherentDerivedTensor G₁₂₃.triple] [HasDerivedPushforward G₁₂₃.πXW]
  [HasCoherentPullback G₂₃₄.πXY] [HasCoherentPullback G₂₃₄.πYW]
  [HasCoherentDerivedTensor G₂₃₄.triple] [HasDerivedPushforward G₂₃₄.πXW]
  [HasCoherentPullback G₁₃₄.πXY] [HasCoherentPullback G₁₃₄.πYW]
  [HasCoherentDerivedTensor G₁₃₄.triple] [HasDerivedPushforward G₁₃₄.πXW]
  [HasCoherentPullback G₁₂₄.πXY] [HasCoherentPullback G₁₂₄.πYW]
  [HasCoherentDerivedTensor G₁₂₄.triple] [HasDerivedPushforward G₁₂₄.πXW]
  [HasCoherentDerivedTensor Q4.quad]
  [HasCoherentPullback Q4.σ₁₂₃] [HasCoherentPullback Q4.σ₂₃₄]
  [HasCoherentPullback Q4.σ₁₃₄] [HasCoherentPullback Q4.σ₁₂₄]
  [HasDerivedPushforward Q4.σ₁₃₄] [HasDerivedPushforward Q4.σ₁₂₄]

/-- **The quadruple kernel** `Rρ₁₄_*(ρ₃₄^*R ⊗ (ρ₂₃^*Q ⊗ ρ₁₂^*P))`, the common
value both bracketings of the convolution are compared with. Slot convention
as in `convKernel`: the outer kernel occupies the first bifunctor slot. -/
noncomputable def quadKernel
    (P : SchemeBoundedCoherentDerivedCategory Z₁₂.left)
    (Q : SchemeBoundedCoherentDerivedCategory Z₂₃.left)
    (R : SchemeBoundedCoherentDerivedCategory Z₃₄.left) :
    SchemeBoundedCoherentDerivedCategory Z₁₄.left :=
  (derivedPushforward Q4.ρ₁₄).obj
    (((derivedTensor Q4.quad).obj ((boundedCoherentDerivedPullback Q4.ρ₃₄).obj R)).obj
      (((derivedTensor Q4.quad).obj ((boundedCoherentDerivedPullback Q4.ρ₂₃).obj Q)).obj
        ((boundedCoherentDerivedPullback Q4.ρ₁₂).obj P)))

variable
  [HasFlatBaseChange G₁₂₃.πXW Q4.σ₁₃₄ Q4.σ₁₂₃ G₁₃₄.πXY]
  [HasFlatBaseChange G₂₃₄.πXW Q4.σ₁₂₄ Q4.σ₂₃₄ G₁₂₄.πYW]
  [HasProjectionFormula Q4.σ₁₃₄]
  [HasProjectionFormulaRight Q4.σ₁₂₄]
  [HasMonoidalDerivedPullback Q4.σ₁₂₃]
  [HasMonoidalDerivedPullback Q4.σ₂₃₄]
  [HasPullbackFactorization Q4.σ₁₂₃ G₁₂₃.πXY Q4.ρ₁₂]
  [HasPullbackFactorization Q4.σ₁₂₃ G₁₂₃.πYW Q4.ρ₂₃]
  [HasPullbackFactorization Q4.σ₁₃₄ G₁₃₄.πYW Q4.ρ₃₄]
  [HasPullbackFactorization Q4.σ₁₂₄ G₁₂₄.πXY Q4.ρ₁₂]
  [HasPullbackFactorization Q4.σ₂₃₄ G₂₃₄.πXY Q4.ρ₂₃]
  [HasPullbackFactorization Q4.σ₂₃₄ G₂₃₄.πYW Q4.ρ₃₄]
  [HasPushforwardFactorization Q4.σ₁₃₄ G₁₃₄.πXW Q4.ρ₁₄]
  [HasPushforwardFactorization Q4.σ₁₂₄ G₁₂₄.πXW Q4.ρ₁₄]
  (P : SchemeBoundedCoherentDerivedCategory Z₁₂.left)
  (Q : SchemeBoundedCoherentDerivedCategory Z₂₃.left)
  (R : SchemeBoundedCoherentDerivedCategory Z₃₄.left)

/-- **The left bracketing meets the quadruple kernel.** Five steps: flat base
change across the `(πXW, πXY)` square, the projection formula at `σ₁₃₄`, and
three factorizations, with the pullback of the inner convolution computed by
`HasMonoidalDerivedPullback` at `σ₁₂₃`. Every step is an isomorphism between
objects of `Dᵇ(Coh Z₁₄)`, obtained by evaluating a class isomorphism at an
object and transporting with `mapIso` — no whiskering. -/
noncomputable def leftAssocIso :
    convKernel G₁₃₄ (convKernel G₁₂₃ P Q) R ≅ quadKernel Q4 P Q R :=
  -- the three pulled-back kernels on the quadruple product
  let a := (boundedCoherentDerivedPullback Q4.ρ₁₂).obj P
  let b := (boundedCoherentDerivedPullback Q4.ρ₂₃).obj Q
  let c := (boundedCoherentDerivedPullback Q4.ρ₃₄).obj R
  -- the inner convolution's integrand and the outer twist
  let M : SchemeBoundedCoherentDerivedCategory G₁₂₃.triple.left :=
    ((derivedTensor G₁₂₃.triple).obj
        ((boundedCoherentDerivedPullback G₁₂₃.πYW).obj Q)).obj
      ((boundedCoherentDerivedPullback G₁₂₃.πXY).obj P)
  let B : SchemeBoundedCoherentDerivedCategory G₁₃₄.triple.left :=
    (boundedCoherentDerivedPullback G₁₃₄.πYW).obj R
  let N : SchemeBoundedCoherentDerivedCategory Q4.quad.left :=
    (boundedCoherentDerivedPullback Q4.σ₁₂₃).obj M
  -- step 1: base change moves the inner pushforward across the pullback
  let s₁ : convKernel G₁₃₄ (convKernel G₁₂₃ P Q) R ≅
      (derivedPushforward G₁₃₄.πXW).obj (((derivedTensor G₁₃₄.triple).obj B).obj
        ((derivedPushforward Q4.σ₁₃₄).obj N)) :=
    (derivedPushforward G₁₃₄.πXW).mapIso
      (((derivedTensor G₁₃₄.triple).obj B).mapIso
        ((HasFlatBaseChange.iso (q := G₁₂₃.πXW) (q' := Q4.σ₁₃₄)
          (u := Q4.σ₁₂₃) (v := G₁₃₄.πXY)).app M))
  -- step 2: the projection formula at `σ₁₃₄` pulls the twist inside
  let s₂ : (derivedPushforward G₁₃₄.πXW).obj (((derivedTensor G₁₃₄.triple).obj B).obj
        ((derivedPushforward Q4.σ₁₃₄).obj N)) ≅
      (derivedPushforward G₁₃₄.πXW).obj ((derivedPushforward Q4.σ₁₃₄).obj
        (((derivedTensor Q4.quad).obj
          ((boundedCoherentDerivedPullback Q4.σ₁₃₄).obj B)).obj N)) :=
    (derivedPushforward G₁₃₄.πXW).mapIso
      ((HasProjectionFormula.iso (q := Q4.σ₁₃₄) B).symm.app N)
  -- step 3: the pulled-back outer twist is `ρ₃₄^* R`
  let s₃ : (derivedPushforward G₁₃₄.πXW).obj ((derivedPushforward Q4.σ₁₃₄).obj
        (((derivedTensor Q4.quad).obj
          ((boundedCoherentDerivedPullback Q4.σ₁₃₄).obj B)).obj N)) ≅
      (derivedPushforward G₁₃₄.πXW).obj ((derivedPushforward Q4.σ₁₃₄).obj
        (((derivedTensor Q4.quad).obj c).obj N)) :=
    (derivedPushforward G₁₃₄.πXW).mapIso ((derivedPushforward Q4.σ₁₃₄).mapIso
      (((derivedTensor Q4.quad).mapIso
        ((HasPullbackFactorization.iso (π := Q4.σ₁₃₄) (p := G₁₃₄.πYW)
          (r := Q4.ρ₃₄)).app R)).app N))
  -- step 4: the pulled-back integrand is `ρ₂₃^*Q ⊗ ρ₁₂^*P`
  let e₄ : N ≅ ((derivedTensor Q4.quad).obj b).obj a :=
    (monoidalDerivedPullbackTensorIso Q4.σ₁₂₃
        ((boundedCoherentDerivedPullback G₁₂₃.πYW).obj Q)).app
      ((boundedCoherentDerivedPullback G₁₂₃.πXY).obj P) ≪≫
    ((derivedTensor Q4.quad).mapIso
        ((HasPullbackFactorization.iso (π := Q4.σ₁₂₃) (p := G₁₂₃.πYW)
          (r := Q4.ρ₂₃)).app Q)).app
      ((boundedCoherentDerivedPullback Q4.σ₁₂₃).obj
        ((boundedCoherentDerivedPullback G₁₂₃.πXY).obj P)) ≪≫
    ((derivedTensor Q4.quad).obj b).mapIso
      ((HasPullbackFactorization.iso (π := Q4.σ₁₂₃) (p := G₁₂₃.πXY)
        (r := Q4.ρ₁₂)).app P)
  let s₄ : (derivedPushforward G₁₃₄.πXW).obj ((derivedPushforward Q4.σ₁₃₄).obj
        (((derivedTensor Q4.quad).obj c).obj N)) ≅
      (derivedPushforward G₁₃₄.πXW).obj ((derivedPushforward Q4.σ₁₃₄).obj
        (((derivedTensor Q4.quad).obj c).obj
          (((derivedTensor Q4.quad).obj b).obj a))) :=
    (derivedPushforward G₁₃₄.πXW).mapIso ((derivedPushforward Q4.σ₁₃₄).mapIso
      (((derivedTensor Q4.quad).obj c).mapIso e₄))
  -- step 5: the two-step pushforward is `Rρ₁₄_*`
  let s₅ : (derivedPushforward G₁₃₄.πXW).obj ((derivedPushforward Q4.σ₁₃₄).obj
        (((derivedTensor Q4.quad).obj c).obj
          (((derivedTensor Q4.quad).obj b).obj a))) ≅
      quadKernel Q4 P Q R :=
    (HasPushforwardFactorization.iso (π := Q4.σ₁₃₄) (q := G₁₃₄.πXW)
      (r := Q4.ρ₁₄)).app
        (((derivedTensor Q4.quad).obj c).obj
          (((derivedTensor Q4.quad).obj b).obj a))
  s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅

/-- **The right bracketing meets the quadruple kernel.** Six steps this time:
the extra one is the associator from `HasCoherentDerivedTensor` — the convolved kernel sits in the
twist slot on this side, so after base change, the *right*-slot projection
formula at `σ₁₂₄`, and the factorizations, the tensors arrive bracketed the
other way and associativity of the derived tensor is what reconciles them.
This is the consumption site #542 promised that class. -/
noncomputable def rightAssocIso :
    convKernel G₁₂₄ P (convKernel G₂₃₄ Q R) ≅ quadKernel Q4 P Q R :=
  let a := (boundedCoherentDerivedPullback Q4.ρ₁₂).obj P
  let b := (boundedCoherentDerivedPullback Q4.ρ₂₃).obj Q
  let c := (boundedCoherentDerivedPullback Q4.ρ₃₄).obj R
  let M : SchemeBoundedCoherentDerivedCategory G₂₃₄.triple.left :=
    ((derivedTensor G₂₃₄.triple).obj
        ((boundedCoherentDerivedPullback G₂₃₄.πYW).obj R)).obj
      ((boundedCoherentDerivedPullback G₂₃₄.πXY).obj Q)
  let N : SchemeBoundedCoherentDerivedCategory Q4.quad.left :=
    (boundedCoherentDerivedPullback Q4.σ₂₃₄).obj M
  let E : SchemeBoundedCoherentDerivedCategory G₁₂₄.triple.left :=
    (boundedCoherentDerivedPullback G₁₂₄.πXY).obj P
  -- step 1: base change on the inner convolution, inside the twist slot
  let s₁ : convKernel G₁₂₄ P (convKernel G₂₃₄ Q R) ≅
      (derivedPushforward G₁₂₄.πXW).obj (((derivedTensor G₁₂₄.triple).obj
        ((derivedPushforward Q4.σ₁₂₄).obj N)).obj E) :=
    (derivedPushforward G₁₂₄.πXW).mapIso
      (((derivedTensor G₁₂₄.triple).mapIso
        ((HasFlatBaseChange.iso (q := G₂₃₄.πXW) (q' := Q4.σ₁₂₄)
          (u := Q4.σ₂₃₄) (v := G₁₂₄.πYW)).app M)).app E)
  -- step 2: the right-slot projection formula at `σ₁₂₄`
  let s₂ : (derivedPushforward G₁₂₄.πXW).obj (((derivedTensor G₁₂₄.triple).obj
        ((derivedPushforward Q4.σ₁₂₄).obj N)).obj E) ≅
      (derivedPushforward G₁₂₄.πXW).obj ((derivedPushforward Q4.σ₁₂₄).obj
        (((derivedTensor Q4.quad).obj N).obj
          ((boundedCoherentDerivedPullback Q4.σ₁₂₄).obj E))) :=
    (derivedPushforward G₁₂₄.πXW).mapIso
      ((HasProjectionFormulaRight.iso (q := Q4.σ₁₂₄) N).symm.app E)
  -- step 3: the pulled-back argument is `ρ₁₂^* P`
  let s₃ : (derivedPushforward G₁₂₄.πXW).obj ((derivedPushforward Q4.σ₁₂₄).obj
        (((derivedTensor Q4.quad).obj N).obj
          ((boundedCoherentDerivedPullback Q4.σ₁₂₄).obj E))) ≅
      (derivedPushforward G₁₂₄.πXW).obj ((derivedPushforward Q4.σ₁₂₄).obj
        (((derivedTensor Q4.quad).obj N).obj a)) :=
    (derivedPushforward G₁₂₄.πXW).mapIso ((derivedPushforward Q4.σ₁₂₄).mapIso
      (((derivedTensor Q4.quad).obj N).mapIso
        ((HasPullbackFactorization.iso (π := Q4.σ₁₂₄) (p := G₁₂₄.πXY)
          (r := Q4.ρ₁₂)).app P)))
  -- step 4: the pulled-back twist is `ρ₃₄^*R ⊗ ρ₂₃^*Q`
  let e₄ : N ≅ ((derivedTensor Q4.quad).obj c).obj b :=
    (monoidalDerivedPullbackTensorIso Q4.σ₂₃₄
        ((boundedCoherentDerivedPullback G₂₃₄.πYW).obj R)).app
      ((boundedCoherentDerivedPullback G₂₃₄.πXY).obj Q) ≪≫
    ((derivedTensor Q4.quad).mapIso
        ((HasPullbackFactorization.iso (π := Q4.σ₂₃₄) (p := G₂₃₄.πYW)
          (r := Q4.ρ₃₄)).app R)).app
      ((boundedCoherentDerivedPullback Q4.σ₂₃₄).obj
        ((boundedCoherentDerivedPullback G₂₃₄.πXY).obj Q)) ≪≫
    ((derivedTensor Q4.quad).obj c).mapIso
      ((HasPullbackFactorization.iso (π := Q4.σ₂₃₄) (p := G₂₃₄.πXY)
        (r := Q4.ρ₂₃)).app Q)
  let s₄ : (derivedPushforward G₁₂₄.πXW).obj ((derivedPushforward Q4.σ₁₂₄).obj
        (((derivedTensor Q4.quad).obj N).obj a)) ≅
      (derivedPushforward G₁₂₄.πXW).obj ((derivedPushforward Q4.σ₁₂₄).obj
        (((derivedTensor Q4.quad).obj
          (((derivedTensor Q4.quad).obj c).obj b)).obj a)) :=
    (derivedPushforward G₁₂₄.πXW).mapIso ((derivedPushforward Q4.σ₁₂₄).mapIso
      (((derivedTensor Q4.quad).mapIso e₄).app a))
  -- step 5: the two-step pushforward is `Rρ₁₄_*`
  let s₅ : (derivedPushforward G₁₂₄.πXW).obj ((derivedPushforward Q4.σ₁₂₄).obj
        (((derivedTensor Q4.quad).obj
          (((derivedTensor Q4.quad).obj c).obj b)).obj a)) ≅
      (derivedPushforward Q4.ρ₁₄).obj
        (((derivedTensor Q4.quad).obj
          (((derivedTensor Q4.quad).obj c).obj b)).obj a) :=
    (HasPushforwardFactorization.iso (π := Q4.σ₁₂₄) (q := G₁₂₄.πXW)
      (r := Q4.ρ₁₄)).app _
  -- step 6: associativity of the derived tensor rebrackets
  let s₆ : (derivedPushforward Q4.ρ₁₄).obj
        (((derivedTensor Q4.quad).obj
          (((derivedTensor Q4.quad).obj c).obj b)).obj a) ≅
      quadKernel Q4 P Q R :=
    (derivedPushforward Q4.ρ₁₄).mapIso
      ((coherentDerivedTensorAssoc Q4.quad c b).symm.app a)
  s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅ ≪≫ s₆

/-- **Associativity of the geometric convolution, derived.**

`(P ∗ Q) ∗ R ≅ P ∗ (Q ∗ R)` for `convKernel`, through the quadruple kernel.
The two comparisons consume disjoint instance packs except for the shared
factorizations onto the `ρ`s; nothing constructs any of the inputs, so this
moves the trust boundary of kernel-level associativity from "the isomorphism
exists" to the named classical isomorphisms on the quadruple product. -/
noncomputable def geometricConvolutionAssoc :
    convKernel G₁₃₄ (convKernel G₁₂₃ P Q) R ≅
      convKernel G₁₂₄ P (convKernel G₂₃₄ Q R) :=
  leftAssocIso Q4 P Q R ≪≫ (rightAssocIso Q4 P Q R).symm

end Derivation

section Assembly

variable {X Y Z W : SchemeBaseChange S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian Z.left] [IsLocallyNoetherian W.left]
  {Z₁₂ Z₂₃ Z₃₄ Z₁₃ Z₂₄ Z₁₄ : SchemeBaseChange S}
  [IsLocallyNoetherian Z₁₂.left] [IsLocallyNoetherian Z₂₃.left]
  [IsLocallyNoetherian Z₃₄.left] [IsLocallyNoetherian Z₁₃.left]
  [IsLocallyNoetherian Z₂₄.left] [IsLocallyNoetherian Z₁₄.left]

/-- **The geometric convolution associativity data, assembled — with no
supplied fields.**

A `ConvolutionAssocData` for the four geometric convolution data, with
`assocIso` the derived `geometricConvolutionAssoc`. Together with #542's
`convolutionTransformAssoc` this closes the associativity layer: the
transform level was free, the kernel level is now derived, and what is
supplied is the quadruple-product geometry with its named classical
isomorphisms. -/
noncomputable def geometricConvolutionAssocData
    (p₁₂ : Z₁₂ ⟶ X) (q₁₂ : Z₁₂ ⟶ Y) (p₂₃ : Z₂₃ ⟶ Y) (q₂₃ : Z₂₃ ⟶ Z)
    (p₃₄ : Z₃₄ ⟶ Z) (q₃₄ : Z₃₄ ⟶ W)
    (p₁₃ : Z₁₃ ⟶ X) (q₁₃ : Z₁₃ ⟶ Z) (p₂₄ : Z₂₄ ⟶ Y) (q₂₄ : Z₂₄ ⟶ W)
    (p₁₄ : Z₁₄ ⟶ X) (q₁₄ : Z₁₄ ⟶ W)
    [HasCoherentPullback p₁₂] [HasCoherentDerivedTensor Z₁₂] [HasDerivedPushforward q₁₂]
    [HasCoherentPullback p₂₃] [HasCoherentDerivedTensor Z₂₃] [HasDerivedPushforward q₂₃]
    [HasCoherentPullback p₃₄] [HasDerivedTensor Z₃₄] [HasDerivedPushforward q₃₄]
    [HasCoherentPullback p₁₃] [HasCoherentDerivedTensor Z₁₃] [HasDerivedPushforward q₁₃]
    [HasCoherentPullback p₂₄] [HasDerivedTensor Z₂₄] [HasDerivedPushforward q₂₄]
    [HasCoherentPullback p₁₄] [HasDerivedTensor Z₁₄] [HasDerivedPushforward q₁₄]
    {G₁₂₃ : TripleProductGeometry Z₁₂ Z₂₃ Z₁₃}
    {G₂₃₄ : TripleProductGeometry Z₂₃ Z₃₄ Z₂₄}
    {G₁₃₄ : TripleProductGeometry Z₁₃ Z₃₄ Z₁₄}
    {G₁₂₄ : TripleProductGeometry Z₁₂ Z₂₄ Z₁₄}
    [IsLocallyNoetherian G₁₂₃.triple.left] [IsLocallyNoetherian G₂₃₄.triple.left]
    [IsLocallyNoetherian G₁₃₄.triple.left] [IsLocallyNoetherian G₁₂₄.triple.left]
    [HasCoherentPullback G₁₂₃.πXY] [HasCoherentPullback G₁₂₃.πYW]
    [HasCoherentPullback G₁₂₃.πXW] [HasCoherentDerivedTensor G₁₂₃.triple]
    [HasDerivedPushforward G₁₂₃.πYW] [HasDerivedPushforward G₁₂₃.πXW]
    [HasCoherentPullback G₂₃₄.πXY] [HasCoherentPullback G₂₃₄.πYW]
    [HasCoherentPullback G₂₃₄.πXW] [HasCoherentDerivedTensor G₂₃₄.triple]
    [HasDerivedPushforward G₂₃₄.πYW] [HasDerivedPushforward G₂₃₄.πXW]
    [HasCoherentPullback G₁₃₄.πXY] [HasCoherentPullback G₁₃₄.πYW]
    [HasCoherentPullback G₁₃₄.πXW] [HasCoherentDerivedTensor G₁₃₄.triple]
    [HasDerivedPushforward G₁₃₄.πYW] [HasDerivedPushforward G₁₃₄.πXW]
    [HasCoherentPullback G₁₂₄.πXY] [HasCoherentPullback G₁₂₄.πYW]
    [HasCoherentPullback G₁₂₄.πXW] [HasCoherentDerivedTensor G₁₂₄.triple]
    [HasDerivedPushforward G₁₂₄.πYW] [HasDerivedPushforward G₁₂₄.πXW]
    [HasFlatBaseChange q₁₂ G₁₂₃.πYW G₁₂₃.πXY p₂₃] [HasProjectionFormula G₁₂₃.πYW]
    [HasMonoidalDerivedPullback G₁₂₃.πXY]
    [HasProjectionFormulaRight G₁₂₃.πXW]
    [HasCommonPullbackRoute p₁₂ G₁₂₃.πXY p₁₃ G₁₂₃.πXW]
    [HasCommonPushforwardRoute G₁₂₃.πYW q₂₃ G₁₂₃.πXW q₁₃]
    [HasFlatBaseChange q₂₃ G₂₃₄.πYW G₂₃₄.πXY p₃₄] [HasProjectionFormula G₂₃₄.πYW]
    [HasMonoidalDerivedPullback G₂₃₄.πXY]
    [HasProjectionFormulaRight G₂₃₄.πXW]
    [HasCommonPullbackRoute p₂₃ G₂₃₄.πXY p₂₄ G₂₃₄.πXW]
    [HasCommonPushforwardRoute G₂₃₄.πYW q₃₄ G₂₃₄.πXW q₂₄]
    [HasFlatBaseChange q₁₃ G₁₃₄.πYW G₁₃₄.πXY p₃₄] [HasProjectionFormula G₁₃₄.πYW]
    [HasMonoidalDerivedPullback G₁₃₄.πXY]
    [HasProjectionFormulaRight G₁₃₄.πXW]
    [HasCommonPullbackRoute p₁₃ G₁₃₄.πXY p₁₄ G₁₃₄.πXW]
    [HasCommonPushforwardRoute G₁₃₄.πYW q₃₄ G₁₃₄.πXW q₁₄]
    [HasFlatBaseChange q₁₂ G₁₂₄.πYW G₁₂₄.πXY p₂₄] [HasProjectionFormula G₁₂₄.πYW]
    [HasMonoidalDerivedPullback G₁₂₄.πXY]
    [HasProjectionFormulaRight G₁₂₄.πXW]
    [HasCommonPullbackRoute p₁₂ G₁₂₄.πXY p₁₄ G₁₂₄.πXW]
    [HasCommonPushforwardRoute G₁₂₄.πYW q₂₄ G₁₂₄.πXW q₁₄]
    (Q4 : QuadrupleProductGeometry G₁₂₃ G₂₃₄ G₁₃₄ G₁₂₄)
    [IsLocallyNoetherian Q4.quad.left]
    [HasCoherentPullback Q4.ρ₁₂] [HasCoherentPullback Q4.ρ₂₃]
    [HasCoherentPullback Q4.ρ₃₄] [HasDerivedPushforward Q4.ρ₁₄]
    [HasCoherentDerivedTensor Q4.quad]
    [HasCoherentPullback Q4.σ₁₂₃] [HasCoherentPullback Q4.σ₂₃₄]
    [HasCoherentPullback Q4.σ₁₃₄] [HasCoherentPullback Q4.σ₁₂₄]
    [HasDerivedPushforward Q4.σ₁₃₄] [HasDerivedPushforward Q4.σ₁₂₄]
    [HasFlatBaseChange G₁₂₃.πXW Q4.σ₁₃₄ Q4.σ₁₂₃ G₁₃₄.πXY]
    [HasFlatBaseChange G₂₃₄.πXW Q4.σ₁₂₄ Q4.σ₂₃₄ G₁₂₄.πYW]
    [HasProjectionFormula Q4.σ₁₃₄] [HasProjectionFormulaRight Q4.σ₁₂₄]
    [HasMonoidalDerivedPullback Q4.σ₁₂₃] [HasMonoidalDerivedPullback Q4.σ₂₃₄]
    [HasPullbackFactorization Q4.σ₁₂₃ G₁₂₃.πXY Q4.ρ₁₂]
    [HasPullbackFactorization Q4.σ₁₂₃ G₁₂₃.πYW Q4.ρ₂₃]
    [HasPullbackFactorization Q4.σ₁₃₄ G₁₃₄.πYW Q4.ρ₃₄]
    [HasPullbackFactorization Q4.σ₁₂₄ G₁₂₄.πXY Q4.ρ₁₂]
    [HasPullbackFactorization Q4.σ₂₃₄ G₂₃₄.πXY Q4.ρ₂₃]
    [HasPullbackFactorization Q4.σ₂₃₄ G₂₃₄.πYW Q4.ρ₃₄]
    [HasPushforwardFactorization Q4.σ₁₃₄ G₁₃₄.πXW Q4.ρ₁₄]
    [HasPushforwardFactorization Q4.σ₁₂₄ G₁₂₄.πXW Q4.ρ₁₄] :
    ConvolutionAssocData
      (geometricConvolutionData p₁₂ q₁₂ p₂₃ q₂₃ p₁₃ q₁₃ G₁₂₃)
      (geometricConvolutionData p₂₃ q₂₃ p₃₄ q₃₄ p₂₄ q₂₄ G₂₃₄)
      (geometricConvolutionData p₁₃ q₁₃ p₃₄ q₃₄ p₁₄ q₁₄ G₁₃₄)
      (geometricConvolutionData p₁₂ q₁₂ p₂₄ q₂₄ p₁₄ q₁₄ G₁₂₄) where
  assocIso P Q R := geometricConvolutionAssoc Q4 P Q R

end Assembly

/-! ## Where the associativity layer now stands

At the transform level associativity is a theorem for any convolution data
(#542). At the kernel level it is now *derived* for the geometric convolution
from the quadruple-product inputs above. What remains supplied is exactly
those inputs. The abstract `CoherentConvolutionData` root states the pentagon
and triangle; this geometric file has not yet promoted `convKernel` to that
functorial root, so it deliberately exports only the derived three-kernel
comparison.
-/

end CategoryTheory.Triangulated.StabilityCondition.Families
