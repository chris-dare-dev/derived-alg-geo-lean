/-
Threefold slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
open CategoryTheory.Triangulated

/-! ## The (alpha, beta) charge of a compressed threefold class

NumClass is a QUADRUPLE of reals standing for the four H-degrees
(H^3 ch_0, H^2 ch_1, H ch_2, ch_3), with the first slot WEIGHTED by H^3 exactly
as the surface model weights its rank slot by H^2. It is not ch(E) for a sheaf.

reZ and imZ are the real and imaginary parts of -exp(-(beta + i alpha)H) ch
expanded to codimension three; they are derived from that one expression rather
than matched term by term against a source. reZ_eq_betaTwist and
imZ_eq_betaTwist are the consistency check that makes beta a twist rather than a
coordinate, and betaTwist_betaTwist is the group law
e^{-(b1+b2)H} = e^{-b1 H} e^{-b2 H} on the four degrees. betaTwist fixes deg0,
because the twist sums over j <= 0 in codimension zero.

chargeFamily is another child of Walls/ChargeFamily.lean; positivity alpha > 0
is NOT built into the parameter type. wallValue_div_alpha records that dropping
the outer alpha from the imaginary part -- the other normalisation found in the
literature -- rescales every wall expression by alpha and so moves no wall off
alpha = 0.

Q and nu are DEFINITIONS on four real numbers: the Bayer--Macri--Toda quantity
and the tilt slope. The conjectural inequality 0 <= Q appears NOWHERE in this
subtree. It is false in general -- it fails on the blow-up of P^3 at a point
(Schmidt, IMRN 2017) -- and AlgebraicGeometry/Numerical/Stability/BMT.lean
carries it as supplied data with that warning. Defining the quantity is not
assuming the conjecture. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.NumClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.NumClass.deg0
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.NumClass.deg1
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.NumClass.deg2
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.NumClass.deg3
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.Q
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.Q_zero_alpha
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.Q_zero_beta
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist_betaTwist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist_deg0
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist_deg1
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist_deg2
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist_deg3
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.betaTwist_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.chargeFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.chargeFamily_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.chargeFamily_wallValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.charge_im
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.charge_re
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.discr
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.imZ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.imZ_eq_betaTwist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.nu
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.nu_zero_alpha
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.reZ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.reZ_eq_betaTwist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Threefold.wallValue_div_alpha
