/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.DerivedTensorCoherence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution

/-!
# Convolution of Fourier--Mukai kernels: the second ledger

`KernelCorrespondence.lean` reduced a geometric `Correspondence` to three named
inputs. This file does the same for the **composition law**: the abstract
`ConvolutionData` asks for a kernel operation `conv` *and* the family of
isomorphisms `Φ_P ⋙ Φ_Q ≅ Φ_{conv P Q}`, both as supplied data, and this ledger
reduces both.

## What this ledger buys

**`conv` stops being supplied.** Classically
`conv P Q = Rπ_{XW*}(π_{XY}^* P ⊗^L π_{YW}^* Q)` on the triple product. Every
functor in that expression is one the *first* ledger already names — two
derived pullbacks, one derived tensor, one derived pushforward — so given a
triple product with its three projections, `convKernel` is a **definition**.

**`compIso` stops being supplied.** Prop. 5.10 is *derived* here
(`geometricCompIso`) from seven named inputs: the projection formula on each
slot (`HasProjectionFormula`, `HasProjectionFormulaRight`), flat base change
(`HasFlatBaseChange`), monoidality of derived pullback
(`HasMonoidalDerivedPullback`), the coherent derived-tensor root
(`HasCoherentDerivedTensor`), and agreement of the two pullback and the two
pushforward routes across the triple product (`HasCommonPullbackRoute`,
`HasCommonPushforwardRoute`). The honest statement of this ledger's effect:

> Both fields of `ConvolutionData` are now constructed; what is supplied is
> the classical comparison data above, rooted in coherent functorial
> structures with the
> geometry it encodes stated in its docstring.

The earlier form of this file supplied `compIso` whole, as a
`HasConvolutionComparison` class naming the projection formula and flat base
change beside it without consuming them. That class is gone: the derivation
consumes its inputs or they would not be here.

## Where the product finally becomes load-bearing

`KernelCorrespondence.lean` deliberately did *not* require its middle scheme to
be a product, because `Correspondence` does not consume that. Here the
situation is different and the docstrings say so: the seven inputs are jointly
*false* without it. The base-change square is cartesian precisely because the
intermediate objects are honest fibre products, and the two route classes'
`comm` guards hold precisely because the projections really are projections.

`TripleProductGeometry` still carries the projections as data and does not
*assert* that the objects are products — nothing in this file consumes that
assertion. What consumes it is a caller discharging the seven classes, and
each class docstring says which piece of product geometry its instance
encodes. Asserting productness here would be an unconsumed hypothesis, which
is the shape both review rounds attacked.

## What this file does not assert

* **Nothing constructs an instance of any of the seven classes**, and no
  scheme is shown to admit any of them. Inhabitant-free, exactly like the
  first ledger: a clean axiom report on `geometricCompIso` means the
  *derivation* adds nothing, not that a geometric Fourier--Mukai transform
  exists in this repository. Nothing here constructs a `Correspondence`.
* No associativity of convolution — `Convolution.lean` says that needs a
  second data layer relating the two bracketings, and this ledger does not
  supply it.
* No unit: `𝒪_Δ` along the diagonal is absent, so `UnitKernelData` is still
  unreachable geometrically.
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

section TripleProduct

/-- **The triple product and its three projections, supplied.**

`triple` plays `X ×_S Y ×_S W`, and the three morphisms play the projections
onto the pairwise products `Z₁ = X ×_S Y`, `Z₂ = Y ×_S W`, `Z₃ = X ×_S W`.

Carried as data rather than constructed. `Over S` does have binary products
when `Scheme` has pullbacks, and it does, but nothing makes the resulting
objects locally Noetherian — which `Dᵇ(Coh)` requires — so a caller supplies
the objects together with that hypothesis anyway.

**Not asserted: that any of these objects is a product.** Nothing in this file
consumes it. What consumes it is a caller discharging the seven input classes
of `geometricCompIso`, whose instances are exactly where the product geometry
lives; see their docstrings. -/
structure TripleProductGeometry (Z₁ Z₂ Z₃ : SchemeBaseChange S) where
  /-- The triple product `X ×_S Y ×_S W`. -/
  triple : SchemeBaseChange S
  /-- Projection to `X ×_S Y`. -/
  πXY : triple ⟶ Z₁
  /-- Projection to `Y ×_S W`. -/
  πYW : triple ⟶ Z₂
  /-- Projection to `X ×_S W`, along which the convolution is pushed. -/
  πXW : triple ⟶ Z₃

end TripleProduct

section Convolution

variable {Z₁ Z₂ Z₃ : SchemeBaseChange S}
  [IsLocallyNoetherian Z₁.left] [IsLocallyNoetherian Z₂.left]
  [IsLocallyNoetherian Z₃.left]
  (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]

/-- **The convolution of two kernels — a definition, not supplied data.**

`conv P Q = Rπ_{XW*}(π_{XY}^* P ⊗^L π_{YW}^* Q)`, the classical formula, built
from functors the first ledger already names. This is the field that
`ConvolutionData` asks for as data and that this ledger removes from the
obligation list.

The kernel `π_{YW}^* Q` sits in the *first* slot of the tensor bifunctor, with
`π_{XY}^* P` as the argument. That choice is aligned with
`Correspondence.transform`, which pins its kernel to the first slot; keeping
the two conventions aligned is what lets `geometricCompIso` avoid asking for a
braiding. Flip either one and a braiding becomes a genuine eighth input. -/
noncomputable def convKernel
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasDerivedTensor G.triple] [HasDerivedPushforward G.πXW]
    (P : SchemeBoundedCoherentDerivedCategory Z₁.left)
    (Q : SchemeBoundedCoherentDerivedCategory Z₂.left) :
    SchemeBoundedCoherentDerivedCategory Z₃.left :=
  (derivedPushforward G.πXW).obj
    (((derivedTensor G.triple).obj
        ((boundedCoherentDerivedPullback G.πYW).obj Q)).obj
      ((boundedCoherentDerivedPullback G.πXY).obj P))

end Convolution

section ClassicalInputs

variable {Z : SchemeBaseChange S} [IsLocallyNoetherian Z.left]

/-- **The projection formula, supplied.**

`Rq_*(Lq^* B ⊗^L A) ≅ B ⊗^L Rq_* A` in the twist-by-`Lq^* B` reading: the
twist by a pulled-back kernel commutes with pushforward.

One of the seven inputs to `geometricCompIso`, consumed there at the morphism
`πYW` of the triple product. Discharging it for a projection of an honest
fibre product is the classical projection formula; for an arbitrary morphism
it is generally false, which is where the product geometry lives in this
input. -/
class HasProjectionFormula {Z U : SchemeBaseChange S}
    [IsLocallyNoetherian Z.left] [IsLocallyNoetherian U.left] (q : Z ⟶ U)
    [HasCoherentPullback q] [HasDerivedTensor Z] [HasDerivedTensor U]
    [HasDerivedPushforward q] where
  /-- The projection isomorphism, natural in both arguments. -/
  iso : ∀ B : SchemeBoundedCoherentDerivedCategory U.left,
    (derivedTensor Z).obj ((boundedCoherentDerivedPullback q).obj B) ⋙
        derivedPushforward q ≅
      derivedPushforward q ⋙ (derivedTensor U).obj B

/-- **Flat base change, supplied.**

For a cartesian square with `u`, `v` the two sides and `q`, `q'` the two
projections, `Lv^* Rq_* ≅ Rq'_* Lu^*`.

One of the seven inputs to `geometricCompIso`, consumed there at the square
`(q₁, πYW, πXY, p₂)`. That square is cartesian *because* the objects are
products — the place where productness does work in this input. Stated
abstractly on a supplied square so that the class does not itself have to
assert productness. -/
class HasFlatBaseChange {T T' U U' : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian T'.left]
    [IsLocallyNoetherian U.left] [IsLocallyNoetherian U'.left]
    (q : T ⟶ U) (q' : T' ⟶ U') (u : T' ⟶ T) (v : U' ⟶ U)
    [HasCoherentPullback u] [HasCoherentPullback v]
    [HasDerivedPushforward q] [HasDerivedPushforward q'] where
  /-- The square commutes. A **guard**: it is what makes `iso` the right thing
  to ask for, and the derivation deliberately consumes `iso` alone. -/
  comm : u ≫ q = q' ≫ v
  /-- Base-change isomorphism. -/
  iso : derivedPushforward q ⋙ boundedCoherentDerivedPullback v ≅
    boundedCoherentDerivedPullback u ⋙ derivedPushforward q'

/-- Compatibility record containing only the tensorator of derived pullback.

New stable convolution APIs require `HasMonoidalDerivedPullback`, which also
states tensorator associativity, unitality, naturality, and invertibility. -/
class HasDerivedPullbackTensor {T U : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] (f : T ⟶ U)
    [HasCoherentPullback f] [HasDerivedTensor T] [HasDerivedTensor U] where
  /-- Pullback carries a twist to the twist by the pullback. -/
  iso : ∀ K : SchemeBoundedCoherentDerivedCategory U.left,
    (derivedTensor U).obj K ⋙ boundedCoherentDerivedPullback f ≅
      boundedCoherentDerivedPullback f ⋙
        (derivedTensor T).obj ((boundedCoherentDerivedPullback f).obj K)

/-- Forget strong monoidality to the old tensorator-only capability. -/
noncomputable instance hasDerivedPullbackTensorOfMonoidal
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U] [HasMonoidalDerivedPullback f] :
    HasDerivedPullbackTensor f where
  iso := monoidalDerivedPullbackTensorIso f

/-- Compatibility record for callers that have only a chosen tensor
associator. New stable convolution APIs require `HasCoherentDerivedTensor`,
whose Mathlib `MonoidalCategory` parent also supplies naturality, the pentagon,
and the triangle.

Braiding is genuinely not needed, and that is a fact about this repository's
conventions rather than a general one: `Correspondence.transform` pins the
kernel to the *first* slot of the bifunctor, and `convKernel` puts
`πYW^* Q` in that same slot with `πXY^* P` as the argument. Flipping either
convention would force a braiding. -/
class HasDerivedTensorAssoc (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasDerivedTensor Z] where
  /-- `A ⊗ (B ⊗ −) ≅ (A ⊗ B) ⊗ −`. -/
  iso : ∀ A B : SchemeBoundedCoherentDerivedCategory Z.left,
    (derivedTensor Z).obj B ⋙ (derivedTensor Z).obj A ≅
      (derivedTensor Z).obj (((derivedTensor Z).obj A).obj B)

/-- Forget the coherent root to the old single-associator capability.

This adapter is retained for raw intermediate consumers. There is deliberately
no instance in the opposite direction. -/
noncomputable instance hasDerivedTensorAssocOfCoherent (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z] :
    HasDerivedTensorAssoc Z where
  iso := coherentDerivedTensorAssoc Z

/-- **The projection formula on the other slot**, `Rq_*(Lq^* E ⊗^L A) ≅ Rq_* A`-twisted:
as a functor in `E`, `Lq^* ⋙ (A ⊗ −) ⋙ Rq_* ≅ (Rq_* A) ⊗ −`.

A separate class from `HasProjectionFormula`, deliberately. The derivation
consumes the two at **different morphisms** — this one at `πXW`, that one at
`πYW` — so merging them into one class with two fields would leave one field
unconsumed at each of the two instances.

It is also not a consequence of `HasProjectionFormula` plus a braiding: that
one is a family in the target variable natural in the source, this one a family
in the source variable natural in the target. -/
class HasProjectionFormulaRight {Z U : SchemeBaseChange S}
    [IsLocallyNoetherian Z.left] [IsLocallyNoetherian U.left] (q : Z ⟶ U)
    [HasCoherentPullback q] [HasDerivedTensor Z] [HasDerivedTensor U]
    [HasDerivedPushforward q] where
  /-- The right-slot projection isomorphism. -/
  iso : ∀ A : SchemeBoundedCoherentDerivedCategory Z.left,
    boundedCoherentDerivedPullback q ⋙ (derivedTensor Z).obj A ⋙
        derivedPushforward q ≅
      (derivedTensor U).obj ((derivedPushforward q).obj A)

/-- **Two pullback routes to the same place agree.**

Bundles functoriality of derived pullback with the commuting triangle
`π₁ ≫ p₁ = π₃ ≫ p₃`, because the derivation needs exactly the composite and
never the two halves separately.

Not reducible to `GeometricDerivedPullbackComposition`: that is stated at the
literal `f ≫ g`, so bridging two different composites would need `eqToHom`
transport across compound terms, and it additionally demands three
`PreservesPerfectPullback` instances and carries a `perfectIso` field that
nothing here touches. -/
class HasCommonPullbackRoute {X T Z₁ Z₃ : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian T.left]
    [IsLocallyNoetherian Z₁.left] [IsLocallyNoetherian Z₃.left]
    (p₁ : Z₁ ⟶ X) (π₁ : T ⟶ Z₁) (p₃ : Z₃ ⟶ X) (π₃ : T ⟶ Z₃)
    [HasCoherentPullback p₁] [HasCoherentPullback π₁]
    [HasCoherentPullback p₃] [HasCoherentPullback π₃] where
  /-- The triangle commutes. A **guard**: it is what makes the isomorphism
  below the right thing to ask for, and it is deliberately not consumed by the
  derivation, which uses `iso` alone. -/
  comm : π₁ ≫ p₁ = π₃ ≫ p₃
  /-- The two pullback routes agree. -/
  iso : boundedCoherentDerivedPullback p₁ ⋙ boundedCoherentDerivedPullback π₁ ≅
    boundedCoherentDerivedPullback p₃ ⋙ boundedCoherentDerivedPullback π₃

/-- **Two pushforward routes to the same place agree.**

The pushforward companion of `HasCommonPullbackRoute`, and unlike it there is
no existing composition contract at all — nothing in the repository names
`R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`. -/
class HasCommonPushforwardRoute {W T Z₂ Z₃ : SchemeBaseChange S}
    [IsLocallyNoetherian W.left] [IsLocallyNoetherian T.left]
    [IsLocallyNoetherian Z₂.left] [IsLocallyNoetherian Z₃.left]
    (π₂ : T ⟶ Z₂) (q₂ : Z₂ ⟶ W) (π₃ : T ⟶ Z₃) (q₃ : Z₃ ⟶ W)
    [HasDerivedPushforward π₂] [HasDerivedPushforward q₂]
    [HasDerivedPushforward π₃] [HasDerivedPushforward q₃] where
  /-- The triangle commutes. A guard, as above. -/
  comm : π₂ ≫ q₂ = π₃ ≫ q₃
  /-- The two pushforward routes agree. -/
  iso : derivedPushforward π₂ ⋙ derivedPushforward q₂ ≅
    derivedPushforward π₃ ⋙ derivedPushforward q₃

end ClassicalInputs

section Derivation

/-! ### Deriving Prop. 5.10

`compIso` is no longer supplied. `geometricCompIso` below is the classical
argument, written as eight intermediate functors `E₀, …, E₇` and eight steps,
each naming the single input it consumes:

| step | rewrites | input |
|---|---|---|
| 1 | `q₁_* ⋙ p₂^*` → `πXY^* ⋙ πYW_*` | `HasFlatBaseChange` |
| 2 | `(⊗P) ⋙ πXY^*` → `πXY^* ⋙ (⊗πXY^*P)` | `HasMonoidalDerivedPullback` |
| 3 | `πYW_* ⋙ (⊗Q)` → `(⊗πYW^*Q) ⋙ πYW_*` | `HasProjectionFormula` (symm) |
| 4 | `(⊗a) ⋙ (⊗b)` → `(⊗(b ⊗ a))` | `HasCoherentDerivedTensor` |
| 5 | `πYW_* ⋙ q₂_*` → `πXW_* ⋙ q₃_*` | `HasCommonPushforwardRoute` |
| 6 | `p₁^* ⋙ πXY^*` → `p₃^* ⋙ πXW^*` | `HasCommonPullbackRoute` |
| 7 | `πXW^* ⋙ (⊗M) ⋙ πXW_*` → `(⊗ Rπ_{XW*} M)` | `HasProjectionFormulaRight` |

Every intermediate and every step is written with a fully ascribed type,
inside a single definition, so that no signature is left to section-variable
inclusion order and no composite is left to higher-order unification — the
two failure modes that consumed the first attempt at this proof. Mathlib's
own note on `Functor.associator` warns that leaning on the definitional
`Functor.assoc` "tends to make Lean slow"; the three private combinators
below spell the associators out once each.

**Naturality.** Every intermediate is a functor `Dᵇ(Coh X) ⥤ Dᵇ(Coh W)` and
every step is an isomorphism of such functors, so naturality **in the
argument object** is free and never checked by hand. Naturality in `P` or `Q`
is neither obtained nor claimed: `ConvolutionData.compIso` is a bare family
and every consumer evaluates it at a point, so asserting more would be an
unconsumed strengthening. -/

/-- Rewrite an adjacent pair at the head of a right-associated composite.
The two pairs may pass through different middle categories — every rewrite in
the chain below does. -/
private def pairCongr {A₁ A₂ A₂' A₃ A₄ : Type*} [Category A₁] [Category A₂]
    [Category A₂'] [Category A₃] [Category A₄]
    {F : A₁ ⥤ A₂} {G : A₂ ⥤ A₃} {F' : A₁ ⥤ A₂'} {G' : A₂' ⥤ A₃}
    (R : A₃ ⥤ A₄) (e : F ⋙ G ≅ F' ⋙ G') : F ⋙ G ⋙ R ≅ F' ⋙ G' ⋙ R :=
  (Functor.associator F G R).symm ≪≫ Functor.isoWhiskerRight e R ≪≫
    Functor.associator F' G' R

/-- Collapse an adjacent pair to one functor at the head of a right-associated
composite. -/
private def pairCollapse {A₁ A₂ A₃ A₄ : Type*} [Category A₁] [Category A₂]
    [Category A₃] [Category A₄] {F : A₁ ⥤ A₂} {G : A₂ ⥤ A₃} {H : A₁ ⥤ A₃}
    (R : A₃ ⥤ A₄) (e : F ⋙ G ≅ H) : F ⋙ G ⋙ R ≅ H ⋙ R :=
  (Functor.associator F G R).symm ≪≫ Functor.isoWhiskerRight e R

/-- Collapse an adjacent triple to one functor at the head of a
right-associated composite. -/
private def tripleCollapse {A₁ A₂ A₃ A₄ A₅ : Type*} [Category A₁] [Category A₂]
    [Category A₃] [Category A₄] [Category A₅] {F : A₁ ⥤ A₂} {G : A₂ ⥤ A₃}
    {H : A₃ ⥤ A₄} {K : A₁ ⥤ A₄} (R : A₄ ⥤ A₅) (e : F ⋙ G ⋙ H ≅ K) :
    F ⋙ G ⋙ H ⋙ R ≅ K ⋙ R :=
  Functor.isoWhiskerLeft F (Functor.associator G H R).symm ≪≫
    (Functor.associator F (G ⋙ H) R).symm ≪≫ Functor.isoWhiskerRight e R

/-- **Prop. 5.10, derived**: `Φ_P ⋙ Φ_Q ≅ Φ_{Q ∗ P}` for the geometric
correspondences, with `Q ∗ P = convKernel G P Q`.

Natural in the argument object (each side is a functor and the isomorphism is
an isomorphism of functors); a bare family in `P` and `Q`, which is exactly
what `ConvolutionData.compIso` consumes.

The seven instance arguments beyond the first ledger's are the seven classical
inputs; see the section docstring for which step consumes which. Nothing
constructs any of them, so this derivation moves the trust boundary — from
"Prop. 5.10 holds" to the seven standard isomorphisms it classically follows
from — without shrinking it to zero. -/
noncomputable def geometricCompIso
    {X Y W Z₁ Z₂ Z₃ : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
    [IsLocallyNoetherian W.left] [IsLocallyNoetherian Z₁.left]
    [IsLocallyNoetherian Z₂.left] [IsLocallyNoetherian Z₃.left]
    (p₁ : Z₁ ⟶ X) (q₁ : Z₁ ⟶ Y) (p₂ : Z₂ ⟶ Y) (q₂ : Z₂ ⟶ W)
    (p₃ : Z₃ ⟶ X) (q₃ : Z₃ ⟶ W)
    [HasCoherentPullback p₁] [HasCoherentDerivedTensor Z₁] [HasDerivedPushforward q₁]
    [HasCoherentPullback p₂] [HasDerivedTensor Z₂] [HasDerivedPushforward q₂]
    [HasCoherentPullback p₃] [HasDerivedTensor Z₃] [HasDerivedPushforward q₃]
    (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasCoherentPullback G.πXW] [HasCoherentDerivedTensor G.triple]
    [HasDerivedPushforward G.πYW] [HasDerivedPushforward G.πXW]
    [HasFlatBaseChange q₁ G.πYW G.πXY p₂] [HasProjectionFormula G.πYW]
    [HasMonoidalDerivedPullback G.πXY]
    [HasProjectionFormulaRight G.πXW]
    [HasCommonPullbackRoute p₁ G.πXY p₃ G.πXW]
    [HasCommonPushforwardRoute G.πYW q₂ G.πXW q₃]
    (P : SchemeBoundedCoherentDerivedCategory Z₁.left)
    (Q : SchemeBoundedCoherentDerivedCategory Z₂.left) :
    (geometricCorrespondence X Y Z₁ p₁ q₁).transform P ⋙
        (geometricCorrespondence Y W Z₂ p₂ q₂).transform Q ≅
      (geometricCorrespondence X W Z₃ p₃ q₃).transform (convKernel G P Q) :=
  -- The two pulled-back kernels and their tensor product on the triple product.
  let a : SchemeBoundedCoherentDerivedCategory G.triple.left :=
    (boundedCoherentDerivedPullback G.πXY).obj P
  let b : SchemeBoundedCoherentDerivedCategory G.triple.left :=
    (boundedCoherentDerivedPullback G.πYW).obj Q
  let M : SchemeBoundedCoherentDerivedCategory G.triple.left :=
    ((derivedTensor G.triple).obj b).obj a
  -- The eight intermediate functors, each ascribed in full.
  let E₀ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₁ ⋙ (derivedTensor Z₁).obj P ⋙
      derivedPushforward q₁ ⋙ boundedCoherentDerivedPullback p₂ ⋙
        (derivedTensor Z₂).obj Q ⋙ derivedPushforward q₂
  let E₁ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₁ ⋙ (derivedTensor Z₁).obj P ⋙
      boundedCoherentDerivedPullback G.πXY ⋙ derivedPushforward G.πYW ⋙
        (derivedTensor Z₂).obj Q ⋙ derivedPushforward q₂
  let E₂ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₁ ⋙ boundedCoherentDerivedPullback G.πXY ⋙
      (derivedTensor G.triple).obj a ⋙ derivedPushforward G.πYW ⋙
        (derivedTensor Z₂).obj Q ⋙ derivedPushforward q₂
  let E₃ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₁ ⋙ boundedCoherentDerivedPullback G.πXY ⋙
      (derivedTensor G.triple).obj a ⋙ (derivedTensor G.triple).obj b ⋙
        derivedPushforward G.πYW ⋙ derivedPushforward q₂
  let E₄ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₁ ⋙ boundedCoherentDerivedPullback G.πXY ⋙
      (derivedTensor G.triple).obj M ⋙
        derivedPushforward G.πYW ⋙ derivedPushforward q₂
  let E₅ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₁ ⋙ boundedCoherentDerivedPullback G.πXY ⋙
      (derivedTensor G.triple).obj M ⋙
        derivedPushforward G.πXW ⋙ derivedPushforward q₃
  let E₆ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₃ ⋙ boundedCoherentDerivedPullback G.πXW ⋙
      (derivedTensor G.triple).obj M ⋙
        derivedPushforward G.πXW ⋙ derivedPushforward q₃
  let E₇ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory W.left :=
    boundedCoherentDerivedPullback p₃ ⋙
      (derivedTensor Z₃).obj (convKernel G P Q) ⋙ derivedPushforward q₃
  -- Seam in: the composite of the two transforms is `E₀` definitionally.
  let s₀ : (geometricCorrespondence X Y Z₁ p₁ q₁).transform P ⋙
      (geometricCorrespondence Y W Z₂ p₂ q₂).transform Q ≅ E₀ := Iso.refl _
  -- Step 1, flat base change at the square `(q₁, πYW, πXY, p₂)`.
  let s₁ : E₀ ≅ E₁ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p₁)
      (Functor.isoWhiskerLeft ((derivedTensor Z₁).obj P)
        (pairCongr ((derivedTensor Z₂).obj Q ⋙ derivedPushforward q₂)
          (HasFlatBaseChange.iso (q := q₁) (q' := G.πYW)
            (u := G.πXY) (v := p₂))))
  -- Step 2, monoidality of the pullback along `πXY`, at the twist `P`.
  let s₂ : E₁ ≅ E₂ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p₁)
      (pairCongr
        (derivedPushforward G.πYW ⋙ (derivedTensor Z₂).obj Q ⋙
          derivedPushforward q₂)
        (monoidalDerivedPullbackTensorIso G.πXY P))
  -- Step 3, the projection formula along `πYW` at the twist `Q`, reversed.
  let s₃ : E₂ ≅ E₃ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p₁)
      (Functor.isoWhiskerLeft (boundedCoherentDerivedPullback G.πXY)
        (Functor.isoWhiskerLeft ((derivedTensor G.triple).obj a)
          (pairCongr (derivedPushforward q₂)
            (HasProjectionFormula.iso (q := G.πYW) Q).symm)))
  -- Step 4, associativity of the derived tensor on the triple product.
  let s₄ : E₃ ≅ E₄ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p₁)
      (Functor.isoWhiskerLeft (boundedCoherentDerivedPullback G.πXY)
        (pairCollapse (derivedPushforward G.πYW ⋙ derivedPushforward q₂)
          (coherentDerivedTensorAssoc G.triple b a)))
  -- Step 5, the two pushforward routes agree; tail whisker only.
  let s₅ : E₄ ≅ E₅ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p₁)
      (Functor.isoWhiskerLeft (boundedCoherentDerivedPullback G.πXY)
        (Functor.isoWhiskerLeft ((derivedTensor G.triple).obj M)
          (HasCommonPushforwardRoute.iso (π₂ := G.πYW) (q₂ := q₂)
            (π₃ := G.πXW) (q₃ := q₃))))
  -- Step 6, the two pullback routes agree; head whisker only. The route is
  -- ascribed first so `pairCongr`'s endpoints are determined before the
  -- expected type is checked.
  let route : boundedCoherentDerivedPullback p₁ ⋙
      boundedCoherentDerivedPullback G.πXY ≅
        boundedCoherentDerivedPullback p₃ ⋙
          boundedCoherentDerivedPullback G.πXW :=
    HasCommonPullbackRoute.iso (p₁ := p₁) (π₁ := G.πXY)
      (p₃ := p₃) (π₃ := G.πXW)
  let s₆ : E₅ ≅ E₆ :=
    pairCongr (F := boundedCoherentDerivedPullback p₁)
      (F' := boundedCoherentDerivedPullback p₃)
      (G := boundedCoherentDerivedPullback G.πXY)
      (G' := boundedCoherentDerivedPullback G.πXW)
      ((derivedTensor G.triple).obj M ⋙
        derivedPushforward G.πXW ⋙ derivedPushforward q₃)
      route
  -- Step 7, the right-slot projection formula along `πXW` at the twist `M`,
  -- landing on `convKernel` by one delta unfold.
  let s₇ : E₆ ≅ E₇ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p₃)
      (tripleCollapse (derivedPushforward q₃)
        (HasProjectionFormulaRight.iso (q := G.πXW) M))
  -- Seam out: `E₇` is the transform with kernel `convKernel` definitionally.
  let s₈ : E₇ ≅
      (geometricCorrespondence X W Z₃ p₃ q₃).transform (convKernel G P Q) :=
    Iso.refl _
  s₀ ≪≫ s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅ ≪≫ s₆ ≪≫ s₇ ≪≫ s₈

end Derivation

section Assembly

variable {X Y W Z₁ Z₂ Z₃ : SchemeBaseChange S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian W.left] [IsLocallyNoetherian Z₁.left]
  [IsLocallyNoetherian Z₂.left] [IsLocallyNoetherian Z₃.left]

/-- **The geometric convolution data, assembled — with no supplied fields.**

A `ConvolutionData` for the three geometric correspondences, with `conv` the
constructed `convKernel` and `compIso` the derived `geometricCompIso`.
Compare the abstract structure, which asks for both as data; that reduction —
from two supplied fields to zero, given the seven named classical inputs — is
the whole content of this ledger. -/
noncomputable def geometricConvolutionData
    (p₁ : Z₁ ⟶ X) (q₁ : Z₁ ⟶ Y) (p₂ : Z₂ ⟶ Y) (q₂ : Z₂ ⟶ W)
    (p₃ : Z₃ ⟶ X) (q₃ : Z₃ ⟶ W)
    [HasCoherentPullback p₁] [HasCoherentDerivedTensor Z₁] [HasDerivedPushforward q₁]
    [HasCoherentPullback p₂] [HasDerivedTensor Z₂] [HasDerivedPushforward q₂]
    [HasCoherentPullback p₃] [HasDerivedTensor Z₃] [HasDerivedPushforward q₃]
    (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasCoherentPullback G.πXW] [HasCoherentDerivedTensor G.triple]
    [HasDerivedPushforward G.πYW] [HasDerivedPushforward G.πXW]
    [HasFlatBaseChange q₁ G.πYW G.πXY p₂] [HasProjectionFormula G.πYW]
    [HasMonoidalDerivedPullback G.πXY]
    [HasProjectionFormulaRight G.πXW]
    [HasCommonPullbackRoute p₁ G.πXY p₃ G.πXW]
    [HasCommonPushforwardRoute G.πYW q₂ G.πXW q₃] :
    ConvolutionData (geometricCorrespondence X Y Z₁ p₁ q₁)
      (geometricCorrespondence Y W Z₂ p₂ q₂)
      (geometricCorrespondence X W Z₃ p₃ q₃) where
  conv P Q := convKernel G P Q
  compIso P Q := geometricCompIso p₁ q₁ p₂ q₂ p₃ q₃ G P Q

end Assembly

/-! ## What the two ledgers together leave

For a geometric Fourier--Mukai theory with composition, a caller must supply:

1. `HasDerivedTensor` on each of the four relevant schemes — absent from the
   repository;
2. `HasDerivedPushforward` along each of the five relevant morphisms — absent
   from the repository, and where properness lives;
3. `HasCoherentPullback` along each pullback used — an *existing* contract from
   #460--462, so no new kind of obligation;
4. a `TripleProductGeometry` — the objects and projections;
5. the classical comparison structures: `HasProjectionFormula`,
   `HasProjectionFormulaRight`, `HasFlatBaseChange`,
   `HasMonoidalDerivedPullback`, `HasCoherentDerivedTensor`,
   `HasCommonPullbackRoute`, `HasCommonPushforwardRoute` — where the product
   structure of the `TripleProductGeometry` finally does its work.

Prop. 5.10 itself is no longer on the list: `geometricCompIso` derives it from
item 5. Everything else in the Fourier--Mukai lane follows: `transform`,
`transformK₀`, closure of kernel functors under composition, the transport of
stability conditions, and — with a `KernelAutoequivalence` and a `DualKernel`
on top — the group action and the Mukai isometry.

Still unreachable geometrically, and not addressed by either ledger:
`UnitKernelData` (needs `𝒪_Δ`), `DualKernel` (needs `P^∨ ⊗ p^*ω[dim]`), and
associativity of convolution (needs a second comparison layer).
-/

end AlgebraicGeometry.DerivedCategory.FourierMukai
