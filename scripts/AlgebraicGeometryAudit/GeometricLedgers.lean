/-
Geometric-ledgers slice of the AlgebraicGeometry audit. The declarations keep
their established stability-condition namespace while the owning modules and
audit records live in the geometry layer.
-/
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families
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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.derivedPushforward
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforward
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.derivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence_tensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence_push
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforward_additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforwardCommShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforward_isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensor_additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensorCommShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensor_isTriangulated

/-! `HasDerivedTensor` above remains the intentionally raw first-ledger input.
Stable convolution consumers now pass through the coherent monoidal root below;
its parent structures own associator/unitor naturality, pentagon, triangle, and
strong-monoidal pullback laws together. The adapters are one-way only. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCoherentDerivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCoherentDerivedTensor.additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCoherentDerivedTensor.commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCoherentDerivedTensor.isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCoherentDerivedTensor.toMonoidalCategory
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasDerivedTensorOfCoherent
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.coherentDerivedTensorAssoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.coherentDerivedTensorUnit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.coherentDerivedTensorLeftUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.coherentDerivedTensorRightUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.coherentDerivedTensor_pentagon
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.coherentDerivedTensor_triangle
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasMonoidalDerivedPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasMonoidalDerivedPullback.toMonoidal
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.monoidalDerivedPullbackTensorIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.monoidalDerivedPullbackLeftUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.monoidalDerivedPullbackRightUnitor

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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.triple
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.πXY
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.πYW
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.πXW
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.convKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormula
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormula.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasFlatBaseChange
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasFlatBaseChange.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasFlatBaseChange.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPullbackTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPullbackTensor.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasDerivedPullbackTensorOfMonoidal
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensorAssoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensorAssoc.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasDerivedTensorAssocOfCoherent
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormulaRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormulaRight.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPullbackRoute
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPullbackRoute.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPullbackRoute.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPushforwardRoute
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPushforwardRoute.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPushforwardRoute.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCompIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionData

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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTensorUnit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTensorUnit.unit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTensorUnit.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasTensorUnitOfCoherent
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackRetraction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackRetraction.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackRetraction.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardRetraction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardRetraction.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardRetraction.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.diagonalKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricUnitIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricUnitKernelData

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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackFactorization
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackFactorization.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackFactorization.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardFactorization
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardFactorization.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardFactorization.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.quad
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₁₂
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₂₃
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₃₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₁₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₁₂₃
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₂₃₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₁₃₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₁₂₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.quadKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.leftAssocIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.rightAssocIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionAssoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionAssocData

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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackRightUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackRightUnitor.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackLeftUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackLeftUnitor.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasUnitPullbackRightUnitorOfMonoidal
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasUnitPullbackLeftUnitorOfMonoidal
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvUnitLeft
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvUnitRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionLeftUnitData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionRightUnitData


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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPullbackAdjunction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPullbackAdjunction.adj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasKernelDual
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasKernelDual.adj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasKernelDual.dualKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTwistedInversePullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTwistedInversePullback.adj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTwistedInversePullback.twistedInverse
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPullbackAdjunction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.dualKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConstituentRightAdjoints
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConstituentRightAdjoints_pullRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConstituentRightAdjoints_pushRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConstituentRightAdjoints_twistRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricTransform_isLeftAdjoint
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.kernelDualAdjunction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.twistedInverseAdjunction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.twistedInversePullback


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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDualizingTwist
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDualizingTwist.dualizingTwist
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDualizingTwist.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.dualizingTwist
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.dualizingTwistIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricAdjointKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricRightAdjointIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricRightAdjointKernelData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricRightAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricRightAdjoint_isKernelFunctor


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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackSwap
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackSwap.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackSwap.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardSwap
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardSwap.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardSwap.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualAdjointKernelData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualKernelObj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualKernel_dual
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricKernelAutoequivalence
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricSwapIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.pullbackSwapIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.pushforwardSwapIso


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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualKernelOfAdjoint
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricDualKernelOfAdjoint_dual
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricKernelAutoequivalenceOfAdjoint
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricKernelAutoequivalenceOfAdjoint_kernel
