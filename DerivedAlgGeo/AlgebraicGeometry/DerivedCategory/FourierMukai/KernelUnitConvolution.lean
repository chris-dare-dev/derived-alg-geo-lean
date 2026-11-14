/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelUnit
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelAssociativity

/-!
# The unit laws for the geometric convolution

The third ledger (`KernelUnit.lean`) builds the unit *object* — `diagonalKernel`
with its identity transform — but not the unit's compatibility with convolution.
The abstract side splits that compatibility (`Convolution.lean`): transform-level
unit laws are theorems, kernel-level
`ConvolutionLeftUnitData`/`ConvolutionRightUnitData` are supplied. This file
derives the kernel level for the geometric convolution:

* `geometricConvUnitLeft` : `convKernel G (diagonalKernel δ) Q ≅ Q`
* `geometricConvUnitRight` : `convKernel G' P (diagonalKernel δ') ≅ P`

each through a supplied section `τ` of the relevant triple product playing
`δ × 1` (resp. `1 × δ`), and the two assembly definitions discharge the
abstract structures with zero supplied fields.

## Main definitions

* `AlgebraicGeometry.DerivedCategory.FourierMukai.HasUnitPullbackRightUnitor` and
  `AlgebraicGeometry.DerivedCategory.FourierMukai.HasUnitPullbackLeftUnitor` — the pulled-back
  unit is a right, resp. left, unit; instances derive both from `HasMonoidalDerivedPullback`.
* `AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvUnitLeft` and
  `AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvUnitRight` — the two unit laws
  for the geometric convolution, derived.
* `AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvolutionLeftUnitData` and
  `AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvolutionRightUnitData` — the
  assembled abstract unit data, with no supplied fields.

## Main results

The isomorphisms `geometricConvUnitLeft` and `geometricConvUnitRight` are the results; the file
states no separate theorem.

## Implementation notes

### What is consumed

Existing classes at further sites: one `HasFlatBaseChange` square per law, the
projection formula at `τ` — **left slot** for the left law, **right slot**
for the right law, the same slot separation as everywhere else in the
Fourier--Mukai kernel files — the two retraction classes of `KernelUnit.lean`
at `τ` (their second consumption site), and one factorization-free identity:
nothing.

The two unitor compatibility classes mirror each other:

* `HasUnitPullbackRightUnitor f` — twisting *by anything* against the pulled
  unit is the identity: `(− ⊗ f^*𝒪) ≅ 𝟭` in the argument slot.
* `HasUnitPullbackLeftUnitor f` — the pulled unit twists trivially:
  `(f^*𝒪 ⊗ −) ≅ 𝟭`.

Stable consumers assume neither class. Both isomorphisms are derived
from one `HasMonoidalDerivedPullback`, whose strong-monoidal laws relate the
unit comparison to its tensorator and whose source and target
`HasCoherentDerivedTensor` roots own the triangle law.

### What this file does not assert

* Nothing constructs an instance of any class.
* No claim that `diagonalKernel` is unique with these properties. Compatibility
  of the tensor associator and unitors is inherited from the coherent roots;
  proving the geometric convolution itself realizes that abstract pentagon and
  triangle still requires a functorial geometric convolution realization.

## References

The repository's `CategoryTheory.Triangulated.FourierMukai.ConvolutionLeftUnitData`,
`CategoryTheory.Triangulated.FourierMukai.ConvolutionRightUnitData` and
`AlgebraicGeometry.DerivedCategory.FourierMukai.convKernel`.

## Tags

Fourier--Mukai kernel, convolution, unit law, diagonal, projection formula
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section UnitorInputs

/-- Compatibility record asserting that the pulled-back unit is a right unit.

`(− ⊗ f^*𝒪) ≅ 𝟭` — as a statement about the flipped tensor evaluated at the
pulled unit. Classically `f^*𝒪 ≅ 𝒪` and `𝒪` is a two-sided unit; here it is
one field, consumed exactly once, by the left unit law's final step.

Stable consumers use the value derived from
`HasMonoidalDerivedPullback`; this record serves raw intermediate callers. -/
class HasUnitPullbackRightUnitor {T U : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] (f : T ⟶ U)
    [HasCoherentPullback f] [HasDerivedTensor T] [HasDerivedTensor U]
    [HasTensorUnit U] where
  /-- Tensoring against the pulled unit, in the argument slot, is trivial. -/
  iso : (derivedTensor T).flip.obj
      ((boundedCoherentDerivedPullback f).obj (HasTensorUnit.unit (T := U))) ≅
    𝟭 (SchemeBoundedCoherentDerivedCategory T.left)

/-- Compatibility record asserting that the pulled-back unit is a left unit.
The twist-slot mirror of `HasUnitPullbackRightUnitor`; same classical
content, consumed by the right unit law. -/
class HasUnitPullbackLeftUnitor {T U : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] (f : T ⟶ U)
    [HasCoherentPullback f] [HasDerivedTensor T] [HasDerivedTensor U]
    [HasTensorUnit U] where
  /-- Twisting by the pulled unit is trivial. -/
  iso : (derivedTensor T).obj
      ((boundedCoherentDerivedPullback f).obj (HasTensorUnit.unit (T := U))) ≅
    𝟭 (SchemeBoundedCoherentDerivedCategory T.left)

/-- Forget strong monoidality to the right-unitor-only capability
`HasUnitPullbackRightUnitor`. -/
noncomputable instance hasUnitPullbackRightUnitorOfMonoidal
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U] [HasMonoidalDerivedPullback f] :
    HasUnitPullbackRightUnitor f where
  iso := monoidalDerivedPullbackRightUnitor f

/-- Forget strong monoidality to the left-unitor-only capability
`HasUnitPullbackLeftUnitor`. -/
noncomputable instance hasUnitPullbackLeftUnitorOfMonoidal
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U] [HasMonoidalDerivedPullback f] :
    HasUnitPullbackLeftUnitor f where
  iso := monoidalDerivedPullbackLeftUnitor f

end UnitorInputs

section LeftUnit

variable {X Y ZXX ZXY : SchemeBaseChange S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian ZXX.left] [IsLocallyNoetherian ZXY.left]
  (δ : X ⟶ ZXX) (pX : ZXY ⟶ X)
  {G : TripleProductGeometry ZXX ZXY ZXY} [IsLocallyNoetherian G.triple.left]
  (τ : ZXY ⟶ G.triple)
  [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
  [HasDerivedTensor G.triple] [HasDerivedPushforward G.πXW]
  [HasCoherentDerivedTensor X] [HasDerivedPushforward δ]
  [HasCoherentPullback pX] [HasCoherentPullback τ] [HasDerivedPushforward τ]
  [HasCoherentDerivedTensor ZXY]
  [HasFlatBaseChange δ τ pX G.πXY]
  [HasProjectionFormula τ]
  [HasPullbackRetraction τ G.πYW] [HasPushforwardRetraction τ G.πXW]
  [HasMonoidalDerivedPullback pX]

/-- **The left unit law for the geometric convolution, derived.**

`convKernel G (diagonalKernel δ) Q ≅ Q`, in five steps: flat base change
moves `Rδ_*` across `πXY^*` onto the section `τ`; the projection formula at
`τ` pulls the twist inside; the pullback retraction `τ ≫ πYW = 𝟙` computes
the pulled twist as `Q`; the pulled unit is a right unit; and the pushforward
retraction `τ ≫ πXW = 𝟙` finishes. -/
noncomputable def geometricConvUnitLeft
    (Q : SchemeBoundedCoherentDerivedCategory ZXY.left) :
    convKernel G (diagonalKernel δ) Q ≅ Q :=
  let o := coherentDerivedTensorUnit X
  let B := (boundedCoherentDerivedPullback G.πYW).obj Q
  let A := (boundedCoherentDerivedPullback pX).obj o
  let s₁ : convKernel G (diagonalKernel δ) Q ≅
      (derivedPushforward G.πXW).obj
        (((derivedTensor G.triple).obj B).obj ((derivedPushforward τ).obj A)) :=
    (derivedPushforward G.πXW).mapIso
      (((derivedTensor G.triple).obj B).mapIso
        ((HasFlatBaseChange.iso (q := δ) (q' := τ)
          (u := pX) (v := G.πXY)).app o))
  let s₂ : (derivedPushforward G.πXW).obj
        (((derivedTensor G.triple).obj B).obj ((derivedPushforward τ).obj A)) ≅
      (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj
          ((boundedCoherentDerivedPullback τ).obj B)).obj A)) :=
    (derivedPushforward G.πXW).mapIso
      ((HasProjectionFormula.iso (q := τ) B).symm.app A)
  let s₃ : (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj
          ((boundedCoherentDerivedPullback τ).obj B)).obj A)) ≅
      (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj Q).obj A)) :=
    (derivedPushforward G.πXW).mapIso ((derivedPushforward τ).mapIso
      (((derivedTensor ZXY).mapIso
        ((HasPullbackRetraction.iso (δ := τ) (p := G.πYW)).app Q)).app A))
  let s₄ : (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj Q).obj A)) ≅
      (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj Q) :=
    (derivedPushforward G.πXW).mapIso ((derivedPushforward τ).mapIso
      ((monoidalDerivedPullbackRightUnitor pX).app Q))
  let s₅ : (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj Q) ≅ Q :=
    (HasPushforwardRetraction.iso (δ := τ) (q := G.πXW)).app Q
  s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅

end LeftUnit

section RightUnit

variable {X Y ZYY ZXY : SchemeBaseChange S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian ZYY.left] [IsLocallyNoetherian ZXY.left]
  (δ : Y ⟶ ZYY) (pY : ZXY ⟶ Y)
  {G : TripleProductGeometry ZXY ZYY ZXY} [IsLocallyNoetherian G.triple.left]
  (τ : ZXY ⟶ G.triple)
  [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
  [HasDerivedTensor G.triple] [HasDerivedPushforward G.πXW]
  [HasCoherentDerivedTensor Y] [HasDerivedPushforward δ]
  [HasCoherentPullback pY] [HasCoherentPullback τ] [HasDerivedPushforward τ]
  [HasCoherentDerivedTensor ZXY]
  [HasFlatBaseChange δ τ pY G.πYW]
  [HasProjectionFormulaRight τ]
  [HasPullbackRetraction τ G.πXY] [HasPushforwardRetraction τ G.πXW]
  [HasMonoidalDerivedPullback pY]

/-- **The right unit law for the geometric convolution, derived.**

`convKernel G P (diagonalKernel δ) ≅ P`. The mirror of
`geometricConvUnitLeft`, with the unit kernel arriving in the *twist* slot:
base change acts inside the twist, the **right**-slot projection formula at
`τ` replaces the left one, the pullback retraction computes the pulled
argument as `P`, and the pulled unit acts as a left unit. -/
noncomputable def geometricConvUnitRight
    (P : SchemeBoundedCoherentDerivedCategory ZXY.left) :
    convKernel G P (diagonalKernel δ) ≅ P :=
  let o := coherentDerivedTensorUnit Y
  let A := (boundedCoherentDerivedPullback pY).obj o
  let E := (boundedCoherentDerivedPullback G.πXY).obj P
  let s₁ : convKernel G P (diagonalKernel δ) ≅
      (derivedPushforward G.πXW).obj
        (((derivedTensor G.triple).obj ((derivedPushforward τ).obj A)).obj E) :=
    (derivedPushforward G.πXW).mapIso
      (((derivedTensor G.triple).mapIso
        ((HasFlatBaseChange.iso (q := δ) (q' := τ)
          (u := pY) (v := G.πYW)).app o)).app E)
  let s₂ : (derivedPushforward G.πXW).obj
        (((derivedTensor G.triple).obj ((derivedPushforward τ).obj A)).obj E) ≅
      (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj A).obj
          ((boundedCoherentDerivedPullback τ).obj E))) :=
    (derivedPushforward G.πXW).mapIso
      ((HasProjectionFormulaRight.iso (q := τ) A).symm.app E)
  let s₃ : (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj A).obj
          ((boundedCoherentDerivedPullback τ).obj E))) ≅
      (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj A).obj P)) :=
    (derivedPushforward G.πXW).mapIso ((derivedPushforward τ).mapIso
      (((derivedTensor ZXY).obj A).mapIso
        ((HasPullbackRetraction.iso (δ := τ) (p := G.πXY)).app P)))
  let s₄ : (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj
        (((derivedTensor ZXY).obj A).obj P)) ≅
      (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj P) :=
    (derivedPushforward G.πXW).mapIso ((derivedPushforward τ).mapIso
      ((monoidalDerivedPullbackLeftUnitor pY).app P))
  let s₅ : (derivedPushforward G.πXW).obj ((derivedPushforward τ).obj P) ≅ P :=
    (HasPushforwardRetraction.iso (δ := τ) (q := G.πXW)).app P
  s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅

end RightUnit

section Assembly

variable {X Y ZXX ZXY : SchemeBaseChange S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian ZXX.left] [IsLocallyNoetherian ZXY.left]

/-- **The geometric left unit data, assembled — with no supplied fields.**

A `ConvolutionLeftUnitData` for the geometric convolution datum of the
self-correspondence with `(p, q)`, with unit kernel `diagonalKernel δ` and
`leftUnitIso` the derived `geometricConvUnitLeft`. -/
noncomputable def geometricConvolutionLeftUnitData
    (pu : ZXX ⟶ X) (qu : ZXX ⟶ X) (p : ZXY ⟶ X) (q : ZXY ⟶ Y)
    (δ : X ⟶ ZXX) (pX : ZXY ⟶ X)
    [HasCoherentPullback pu] [HasCoherentDerivedTensor ZXX] [HasDerivedPushforward qu]
    [HasCoherentPullback p] [HasCoherentDerivedTensor ZXY] [HasDerivedPushforward q]
    {G : TripleProductGeometry ZXX ZXY ZXY} [IsLocallyNoetherian G.triple.left]
    (τ : ZXY ⟶ G.triple)
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasCoherentPullback G.πXW]
    [HasCoherentDerivedTensor G.triple]
    [HasDerivedPushforward G.πYW] [HasDerivedPushforward G.πXW]
    [HasFlatBaseChange qu G.πYW G.πXY p] [HasProjectionFormula G.πYW]
    [HasMonoidalDerivedPullback G.πXY]
    [HasProjectionFormulaRight G.πXW]
    [HasCommonPullbackRoute pu G.πXY p G.πXW]
    [HasCommonPushforwardRoute G.πYW q G.πXW q]
    [HasCoherentDerivedTensor X] [HasDerivedPushforward δ]
    [HasCoherentPullback pX] [HasCoherentPullback τ] [HasDerivedPushforward τ]
    [HasFlatBaseChange δ τ pX G.πXY]
    [HasProjectionFormula τ]
    [HasPullbackRetraction τ G.πYW] [HasPushforwardRetraction τ G.πXW]
    [HasMonoidalDerivedPullback pX] :
    ConvolutionLeftUnitData
      (geometricConvolutionData pu qu p q p q G) (diagonalKernel δ) where
  leftUnitIso Q := geometricConvUnitLeft δ pX τ Q

/-- **The geometric right unit data, assembled — with no supplied fields.**
The mirror assembly, from `geometricConvUnitRight`. -/
noncomputable def geometricConvolutionRightUnitData
    {ZYY : SchemeBaseChange S} [IsLocallyNoetherian ZYY.left]
    (p : ZXY ⟶ X) (q : ZXY ⟶ Y) (pu : ZYY ⟶ Y) (qu : ZYY ⟶ Y)
    (δ : Y ⟶ ZYY) (pY : ZXY ⟶ Y)
    [HasCoherentPullback p] [HasCoherentDerivedTensor ZXY] [HasDerivedPushforward q]
    [HasCoherentPullback pu] [HasDerivedTensor ZYY] [HasDerivedPushforward qu]
    {G : TripleProductGeometry ZXY ZYY ZXY} [IsLocallyNoetherian G.triple.left]
    (τ : ZXY ⟶ G.triple)
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasCoherentPullback G.πXW]
    [HasCoherentDerivedTensor G.triple]
    [HasDerivedPushforward G.πYW] [HasDerivedPushforward G.πXW]
    [HasFlatBaseChange q G.πYW G.πXY pu] [HasProjectionFormula G.πYW]
    [HasMonoidalDerivedPullback G.πXY]
    [HasProjectionFormulaRight G.πXW]
    [HasCommonPullbackRoute p G.πXY p G.πXW]
    [HasCommonPushforwardRoute G.πYW qu G.πXW q]
    [HasCoherentDerivedTensor Y] [HasDerivedPushforward δ]
    [HasCoherentPullback pY] [HasCoherentPullback τ] [HasDerivedPushforward τ]
    [HasFlatBaseChange δ τ pY G.πYW]
    [HasProjectionFormulaRight τ]
    [HasPullbackRetraction τ G.πXY] [HasPushforwardRetraction τ G.πXW]
    [HasMonoidalDerivedPullback pY] :
    ConvolutionRightUnitData
      (geometricConvolutionData p q pu qu p q G) (diagonalKernel δ) where
  rightUnitIso P := geometricConvUnitRight δ pY τ P

end Assembly

/-! ## The unit layer

The unit side matches the associativity side: at the transform
level both laws are theorems (`Convolution.lean`); at the kernel level both
are derived for the geometric convolution; and what is supplied is the
diagonal/section geometry with its named classical isomorphisms. Tensor and
pullback coherence come from the monoidal roots. Not proved here: that the
geometric `convKernel` construction assembles the abstract
`CoherentConvolutionData`; nor does this file build a `DualKernel`. -/

end AlgebraicGeometry.DerivedCategory.FourierMukai
