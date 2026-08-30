/-
Geometric-ledgers slice of the AlgebraicGeometry audit. Neutral geometric
Fourier--Mukai declarations use their derived-category namespace, while
stability-specific kernel actions use their matching algebraic-geometry
namespace.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.FourierMukai
import DerivedAlgGeo.CategoryTheory.Monoidal.Triangulated.Instances.AlgebraicGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## The geometric Fourier--Mukai correspondence: a dependency ledger

INHABITANT-FREE BY DESIGN. Nothing constructs a `HasDerivedPushforward` or a
`HasDerivedTensor`, and no scheme is shown to admit either, so a clean axiom
list here is emphatically NOT evidence that a geometric Fourier--Mukai
transform exists in this repository. What it says is that
`geometricCorrespondence` assembles a `Correspondence` from exactly three
inputs -- the existing derived-pullback contract, a supplied derived tensor,
and a supplied derived pushforward -- and from nothing else.

Derived pushforward and derived tensor on `D^b(Coh)` do not exist anywhere in
the repository; this file names them rather than building them. The middle
scheme is deliberately NOT required to be a product: `Correspondence` does not
consume that, and it is the composition law (`ConvolutionData`) that needs it.
-/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.derivedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.commShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.derivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.commShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricCorrespondence
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricCorrespondence_pull
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricCorrespondence_tensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricCorrespondence_push
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforward_additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforwardCommShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforward_isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensor_additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensorCommShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensor_isTriangulated

/-! `HasDerivedTensor` above remains the intentionally raw first-ledger input.
Stable convolution consumers now pass through the coherent monoidal root below;
its parent structures own associator/unitor naturality, pentagon, triangle, and
strong-monoidal pullback laws together. The adapters are one-way only. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.commShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.toMonoidalCategory
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.hasCoherentDerivedTensorIsCompatibleWithTriangulation
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.hasDerivedTensorOfCoherent
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorAssoc
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorUnit
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorLeftUnitor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorRightUnitor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensor_pentagon
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensor_triangle
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasMonoidalDerivedPullback
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasMonoidalDerivedPullback.toMonoidal
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.monoidalDerivedPullbackTensorIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.monoidalDerivedPullbackLeftUnitor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.monoidalDerivedPullbackRightUnitor

/-! ## Convolution of kernels: the second ledger

INHABITANT-FREE, like the first. Nothing constructs an instance of the
comparison or coherent-root inputs.

What this ledger buys is that BOTH fields of `ConvolutionData` stop being
supplied: `convKernel` is the classical
`R(pi_XW)_*(pi_XY^* P (x)^L pi_YW^* Q)` built from functors the first ledger
already names, and `geometricCompIso` DERIVES Prop. 5.10 from projection
formulas (both slots), flat base change, strong-monoidal pullback, coherent
tensor associativity, and the two route-agreement classes. The old
`HasConvolutionComparison`, which supplied compIso whole, is deleted.

A clean axiom line on `geometricCompIso` means the derivation adds nothing
beyond its inputs; it is NOT evidence that any input is constructible, and
nothing here constructs a `Correspondence`. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry.mk.inj
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry.mk.sizeOf_spec
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry.triple
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry.πXY
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry.πYW
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.TripleProductGeometry.πXW
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.convKernel
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasProjectionFormula
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasProjectionFormula.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasFlatBaseChange
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasFlatBaseChange.comm
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasFlatBaseChange.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPullbackTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPullbackTensor.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.hasDerivedPullbackTensorOfMonoidal
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensorAssoc
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensorAssoc.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.hasDerivedTensorAssocOfCoherent
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasProjectionFormulaRight
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasProjectionFormulaRight.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCommonPullbackRoute
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCommonPullbackRoute.comm
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCommonPullbackRoute.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCommonPushforwardRoute
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCommonPushforwardRoute.comm
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCommonPushforwardRoute.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricCompIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvolutionData

/-! ## The unit kernel: the third ledger

INHABITANT-FREE, like the first two. `diagonalKernel` is a DEFINITION
(`Rdelta_*` of the tensor unit) and `geometricUnitIso` DERIVES that its
transform is the identity from `HasProjectionFormulaRight` at the diagonal,
the coherent tensor root, and the two retraction classes, whose `comm`
triangle identities are guards
the derivation deliberately does not consume. `DualKernel` remains a named
absence: its classical formula needs derived duals and a dualizing complex,
which have no substrate here. A clean axiom line on `geometricUnitIso` means
the derivation adds nothing beyond its inputs, not that any input is
constructible.
-/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasTensorUnit
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasTensorUnit.unit
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasTensorUnit.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.hasTensorUnitOfCoherent
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPullbackRetraction
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPullbackRetraction.comm
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPullbackRetraction.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPushforwardRetraction
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPushforwardRetraction.comm
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPushforwardRetraction.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.diagonalKernel
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricUnitIso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricUnitKernelData

/-! ## Associativity of the geometric convolution: the quadruple product

INHABITANT-FREE. `geometricConvolutionAssoc` DERIVES the kernel-level
`(P * Q) * R iso P * (Q * R)` for `convKernel` through a supplied quadruple
product, consuming the strong-monoidal pullback and coherent tensor roots at
new instance sites, plus
two new factorization classes whose `comm` triangle identities are unconsumed
guards. `geometricConvolutionAssocData` then has zero supplied fields. A
clean axiom line means the derivation adds nothing beyond its inputs; nothing
constructs any input. The abstract coherent convolution root states a
pentagon; this geometric layer has not yet assembled `convKernel` into it. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasPullbackFactorization
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasPullbackFactorization.comm
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasPullbackFactorization.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasPushforwardFactorization
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasPushforwardFactorization.comm
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasPushforwardFactorization.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.mk.inj
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.mk.sizeOf_spec
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.quad
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.ρ₁₂
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.ρ₂₃
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.ρ₃₄
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.ρ₁₄
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.σ₁₂₃
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.σ₂₃₄
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.σ₁₃₄
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.QuadrupleProductGeometry.σ₁₂₄
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.quadKernel
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.leftAssocIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.rightAssocIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvolutionAssoc
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConvolutionAssocData

/-! ## The unit laws for the geometric convolution

INHABITANT-FREE. Both kernel-level unit laws are DERIVED for `convKernel`
with unit kernel `diagonalKernel`, each through a supplied section `tau` of
the relevant triple product: the left law consumes `HasProjectionFormula` at
`tau`, the right law `HasProjectionFormulaRight` at `tau` -- the standing
slot separation -- plus the retraction classes of the third ledger at their
second consumption site and one new pulled-unit unitor class per slot.
Nothing constructs any input. The tensor and pullback triangle laws now come
from coherent roots; the remaining seam is promotion of `convKernel` itself
to abstract coherent convolution data. -/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasUnitPullbackRightUnitor
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasUnitPullbackRightUnitor.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasUnitPullbackLeftUnitor
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasUnitPullbackLeftUnitor.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.hasUnitPullbackRightUnitorOfMonoidal
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.hasUnitPullbackLeftUnitorOfMonoidal
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricConvUnitLeft
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricConvUnitRight
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricConvolutionLeftUnitData
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricConvolutionRightUnitData


/-! ## The adjoint ledger: three constituent adjunctions on Db(Coh)

`KernelCorrespondence.lean` names derived pullback, tensor, and pushforward but
relates them not at all -- its docstring explicitly declines to claim that
pushforward is right adjoint to pullback. These three classes are that claim
and the two others a right adjoint of the transform needs: the
pullback/pushforward adjunction at `p`, a dual for the kernel, and a right
adjoint of pushforward along `q` (Grothendieck duality).

All three are SUPPLIED and nothing constructs an instance of any of them. A
clean axiom list here says the assembly follows from them, not that any scheme
admits one.

`geometricConstituentRightAdjoints` is the payoff: it produces a genuine
`FourierMukai.ConstituentRightAdjoints`, so `geometricTransform_isLeftAdjoint`
is the first statement in this repository that a geometric Fourier--Mukai
transform has an adjoint at all.

What it does NOT produce is a `RightAdjointKernelData`: that the composite
adjoint is again a TRANSFORM is a further obligation, needing a dualizing
object and tensor rearrangement, and `HasTwistedInversePullback` deliberately
refuses to decompose the shriek functor so that the two stay separate.

Only the right side is ledgered. The left adjoint of `Lp^*` is the exceptional
`p_!`, and nothing consumes one.
-/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPullbackAdjunction
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPullbackAdjunction.adj
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasKernelDual
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasKernelDual.adj
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasKernelDual.dualKernel
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasTwistedInversePullback
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasTwistedInversePullback.adj
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasTwistedInversePullback.twistedInverse
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPullbackAdjunction
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.dualKernel
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConstituentRightAdjoints
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConstituentRightAdjoints_pullRight
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConstituentRightAdjoints_pushRight
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricConstituentRightAdjoints_twistRight
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricTransform_isLeftAdjoint
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.kernelDualAdjunction
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.twistedInverseAdjunction
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.twistedInversePullback


/-! ## The dualizing twist, and a geometric adjoint kernel

`HasDualizingTwist f` is the shape `HasTwistedInversePullback` refused to
assume: `f^!(-) = Lf^*(-) (x) w_f`. SUPPLIED, and nothing constructs one. The
shift is folded into the object because no consumer uses a relative dimension,
and the class needs `HasCoherentPullback` at the PUSHFORWARD's morphism -- the
mirror of the previous ledger needing pushforward at the pullback's.

`geometricAdjointKernel` is a def with a VALUE, not a field: `Q = K^v (x) w_q`,
the classical dual kernel, built from classes already on the table.

`geometricRightAdjointIso` is the derivation, and its only inputs are the
dualizing decomposition plus `HasDerivedTensorAssoc` -- an EXISTING class,
consumed here at a second site. A clean axiom list says the composite right
adjoint is the reversed transform and says nothing more.

`geometricRightAdjointKernelData` is a genuine
`FourierMukai.RightAdjointKernelData` for the geometric correspondence.

It is NOT a `DualKernel`. That structure asks for the quasi-inverse as a
transform of the SAME correspondence; this is a transform of the REVERSED one,
a different value whenever p and q differ. Bridging needs the swap of the
product, which is not stated anywhere.
-/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDualizingTwist
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDualizingTwist.dualizingTwist
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDualizingTwist.iso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.dualizingTwist
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.dualizingTwistIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricAdjointKernel
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricRightAdjointIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricRightAdjointKernelData
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricRightAdjointKernelData_adjKernel
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricRightAdjoint_isKernelFunctor


/-! ## The swap, and a geometric dual kernel

The previous ledger's `RightAdjointKernelData` had the REVERSED correspondence
as its opposite; `DualKernel` needs the same one on both sides. `HasPullbackSwap`
and `HasPushforwardSwap` close that gap. Both are SUPPLIED and uninhabited, and
both carry their composition identity as a `comm` GUARD that the derivation does
not consume -- the `HasPullbackRetraction` pattern.

`geometricSwapIso` is the derivation, and its third input is
`HasProjectionFormulaRight` at the swap: an EXISTING class, consumed here at a
further site. A clean axiom list says the reversed transform is the original one
with kernel `Rs_* Q`, and nothing more.

`Rs_* Q` rather than `s^* Q` deliberately: the two agree when `s` is an
involution isomorphism, and that hypothesis is NOT assumed anywhere -- the
projection formula hands back the pushforward, so the pushforward is what the
kernel is written with.

`geometricDualKernel` is the end of the arc: a `DualKernel` whose dual is
`Rs_*(K^v (x) w_q)`, the classical `P^v (x) p^* w_X [dim X]`. The EQUIVALENCE is
still supplied -- `geometricKernelAutoequivalence` takes it and its comparison
isomorphism as arguments, because that a geometric transform is an equivalence
is the classical theorem the whole lane is conditional on. What is now geometric
is the dual kernel of one, not the equivalence.
-/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPullbackSwap
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPullbackSwap.comm
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPullbackSwap.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPushforwardSwap
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPushforwardSwap.comm
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.HasPushforwardSwap.iso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualAdjointKernelData
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualAdjointKernelData_adjKernel
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualKernel
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualKernelObj
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualKernel_dual
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricKernelAutoequivalence
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricSwapIso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.pullbackSwapIso
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.pushforwardSwapIso


/-! ## A geometric kernel autoequivalence with no supplied equivalence

`geometricKernelAutoequivalenceOfAdjoint` is the consumer #795 said already
existed: it derives the equivalence from the assembled adjoint kernel rather
than taking one, and `geometricDualKernelOfAdjoint` gets the dual kernel with
it at no further cost.

The invertibility of the adjunction's unit and counit is still ASSUMED, as
instance arguments, and nothing here establishes it -- classically that is the
Bondal--Orlov criterion. A clean axiom list says the equivalence follows from
the ledger plus that invertibility, and says nothing about whether any transform
satisfies it.
-/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualKernelOfAdjoint
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricDualKernelOfAdjoint_dual
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricKernelAutoequivalenceOfAdjoint
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricKernelAutoequivalenceOfAdjoint_kernel


/-! ## The geometric side reaches the stability transport

`geometricCorrespondence` is now `@[reducible]`, as are the constructors above
it, and `ofRightAdjointKernel` gives its equivalence's `functor` and `inverse`
LITERALLY rather than through `Adjunction.toEquivalence`. Both changes exist for
one reason: instance search does not unfold plain definitions, so the exactness
the contracts already carry was unreachable at every use site that takes it as
an instance argument.

Hand-rolled instances were tried first and are the wrong tool here, for the
reason `Symmetry/Autoequivalence/FourierMukai` already documents about
`trans`: `IsTriangulated` is INDEXED BY the `CommShift` instance, so a copy
stated against the ambient one is a different term from the one the use site
synthesises. Reducibility reaches the originals, with the indexing intact.

`geometricTransform_isTriangulated` and `geometricTransform_additive` are the
first statements that the assembled geometric transform is exact.
`geometricActStabOfDual` is what the lane was for: a geometric kernel
autoequivalence transporting a Bridgeland stability condition, with the
compatibility hypothesis stated against the CONSTRUCTED dual kernel rather than
an opaque `K0.map`. Conditional on the whole uninhabited ledger, as ever -- a
clean axiom list here says the transport follows from it, not that any scheme
supplies it.
-/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricActStabOfDual
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricTransform_additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.geometricTransform_isTriangulated


/-! ## Composing two geometric transports

The one statement that needs both kernel ledgers: transporting along two
geometric Fourier--Mukai transforms is transporting along the transform of their
CONVOLVED kernel.

`KernelAutoequivalence.actStab_trans` proves this abstractly for a SUPPLIED
`ConvolutionData`. Here the convolution data is `geometricConvolutionData`,
whose own `conv` and `compIso` are derived rather than supplied -- so nothing in
`KernelComposition.lean` is supplied at all, and it introduces no class and asks
for no datum. A clean axiom list says the composition law follows from the two
ledgers already on the table.

It is the associativity clause of an action and nothing more. No identity law,
no monoid, no group of geometric kernel autoequivalences, and no `toAutPair` for
the composite.
-/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricActStabTrans
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricTransKernelAutoequivalence


/-! ## The geometric transform as an element of the acting group

`geometricActStabOfDual` is a FUNCTION on stability conditions.
`Stability/ClassMap.lean` builds a genuine `Group` -- `GroupAction.AutPairQuot v`
-- and "the transform transports" and "the transform is an element of the group
that acts" are different claims. The abstract file proves the second for a
`KernelAutoequivalence` with a `DualKernel`; both are available geometrically,
so this is the geometric side reaching the group.

The strengthening over `actStabOfDual` is `lam`'s INVERTIBILITY, and it is a
real hypothesis rather than repackaging: a geometric kernel autoequivalence with
a non-invertible compatible `lam` still transports stability conditions, it just
is not a member of this group.

`geometricMk_toAutPair_smul` is the statement at the quotient, where the
`MulAction` lives: the transported condition is the image of a group element,
not merely the value of a map. `rfl`, as abstractly -- worth stating for the
same reason it was worth stating there.

Still conditional on the whole uninhabited ledger, and still no monoid map: this
is membership for ONE element, not a homomorphism from anything.
-/

#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricMk_toAutPair_smul
#print axioms AlgebraicGeometry.StabilityCondition.FourierMukai.geometricToAutPair
