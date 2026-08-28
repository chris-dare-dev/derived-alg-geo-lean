/-
Core slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.Algebra
import DerivedAlgGeo.AlgebraicGeometry
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.ChernCharacter.Basic
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold
open AlgebraicGeometry AlgebraicGeometry.Numerical


-- Proj foundations: degree-zero homogeneous module localization is a submodule of Mathlib's
-- ordinary localized module; every homogeneous and denominator certificate remains explicit.
#print axioms AlgebraicGeometry.Proj.NumDenSameDeg
#print axioms AlgebraicGeometry.Proj.degreeZeroSubmodule
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mk_surjective
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mk_eq_mk_iff
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mapOfLE
-- mapOfLE needs S <= T, which a Cech face does not give: the denominators are .powers g1 and
-- .powers g2 with g1 * h = g2, and divisibility does not nest powers submonoids. These two
-- supply the universal-property route instead -- g1 is already invertible once g2 is.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.isUnit_algebraMap_localization_of_mul_mem
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.isUnit_algebraMap_end_of_mul_mem
-- The face map those two lemmas exist for. faceLift is the bare localized-module map from the
-- universal property; faceMap is its restriction to the degree-zero part, and faceMap_mk is the
-- explicit fraction m / g1^n |-> h^n m / g2^n that the Cech differential is computed with.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.faceLift
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.faceLift_mk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.isDegreeZero_faceLift
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.faceMap
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.coe_faceMap
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.faceMap_mk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk
-- awayMk as a normal form (#491): every away fraction is one, and equality is decided by
-- cross-multiplication rather than by the existential the general criterion leaves behind.
-- Both are prerequisites for any basis of the away localization.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.exists_awayMk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_eq_awayMk_iff
-- Numerator additivity at a fixed denominator, and the common-denominator move. Together these
-- are what a spanning argument over monomial numerators consumes; none needs cancellation.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_zero
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_add
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_sum
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_shift
-- Two fractions share a denominator (#491 -> #340): exists_awayMk twice plus awayMk_shift on
-- each side. Every additivity statement about maps defined on awayMk representatives opens
-- with this move.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.exists_awayMk_pair
-- A fraction is zero exactly when its numerator is (#491). This is what makes the numerator a
-- faithful record: independence of fractions reduces to independence of numerators.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_eq_zero_iff
-- The face map in awayMk normal form, and the degree-index transport its callers need.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk_deg_congr
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.faceMap_awayMk
-- Auto-generated, not hand-written: `awayMk` carries its membership certificate as a dependent
-- argument, so the first `rw [coe_awayMk]` in this file makes Lean emit a congruence lemma for
-- it. It is a public declaration and the completeness ratchet counts it, so it is recorded here
-- rather than left to widen the unaudited gap.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk.congr_simp
-- The Laurent exponent of a monomial fraction (#491). awayMk_monomial_eq_iff_laurentExponent is
-- the load-bearing one: it makes beta - m * gamma a complete invariant, so the monomial
-- fractions of a twist are indexed by exponents rather than by representatives. The other two
-- statements cut that index down to the set the basis needs -- total degree the twist, and
-- nonnegative off the support of gamma.
#print axioms AlgebraicGeometry.Proj.natToIntExponent
#print axioms AlgebraicGeometry.Proj.natToIntExponent_injective
#print axioms AlgebraicGeometry.Proj.degree_natToIntExponent
#print axioms AlgebraicGeometry.Proj.laurentExponent
#print axioms AlgebraicGeometry.Proj.laurentExponent_apply
#print axioms AlgebraicGeometry.Proj.laurentExponent_eq_iff
-- The twist abstraction (#568). IsPolynomialTwist isolates the only reading of a numerator the
-- Laurent argument makes -- an element of 𝓜 n is homogeneous of degree n + d -- so the stack can
-- be stated once and instantiated at natShift for d : N and intShift for d : Z. The p = 0
-- disjunct is what makes intShift fit: it carries zero in degrees where n + d is negative and
-- there is no graded piece to name.
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist
#print axioms AlgebraicGeometry.Proj.isPolynomialTwist_natShift
#print axioms AlgebraicGeometry.Proj.isPolynomialTwist_intShift
#print axioms AlgebraicGeometry.Proj.degree_laurentExponent_int
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.degree_eq_of_mem_support
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.monomial_coeff_mem
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.degree_laurentExponent_of_mem_support
-- The degree bookkeeping at either sign. The by_cases on the quotient is the only place the two
-- signs behave differently: a negative twist can put the numerator's degree below m * c, and then
-- the quotient is zero rather than a numerator of lower degree.
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.divMonomial_mem
-- The other two readings the port needs: multiplying a numerator by a homogeneous factor, and
-- filtering it to one block. Both are the same case split -- the numerator may be zero in a
-- degree the twist names no graded piece for -- where the nonnegative versions read membership
-- as homogeneity directly.
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.mul_mem_of_isHomogeneous
#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.laurentFilter_mem
-- The Cech term, cochains and face over an arbitrary twist, with the two instances recorded as
-- definitional. Naming the construction once is what lets the contracting-homotopy layer above
-- it be stated once instead of duplicated per twist.
#print axioms AlgebraicGeometry.Proj.cechTerm
#print axioms AlgebraicGeometry.Proj.cechCochains
#print axioms AlgebraicGeometry.Proj.cechFace
#print axioms AlgebraicGeometry.Proj.cechFace_natShift
#print axioms AlgebraicGeometry.Proj.cechFace_intShift
-- The short-tuple vanishing input (#568). A block containing every variable has Fintype.card
-- elements while a tuple of length n + 2 supports at most n + 2, so over a larger variable set
-- the block cannot sit inside the tuple's support -- whatever the twist. This is what replaces
-- the degree argument at a negative twist, and the first place the lane needs iota finite.
#print axioms AlgebraicGeometry.Proj.tupleExponent_support_card_le
#print axioms AlgebraicGeometry.Proj.cechBlockProj_eq_zero_of_card_lt
-- cechBlockProj and cechHomotopy now take the twist hypothesis, which is a Prop, so Lean emits
-- congruence lemmas for them; recorded here for the same reason AwayRep's projections are.
#print axioms AlgebraicGeometry.Proj.cechBlockProj.congr_simp
#print axioms AlgebraicGeometry.Proj.cechHomotopy.congr_simp
-- Vanishing below the top degree, either sign (#568). The nonnegative companion is stronger
-- where it applies -- no finiteness, every positive degree -- and is not a corollary.
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplex_exactAt
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplex_homology_isZero
#print axioms AlgebraicGeometry.Proj.polynomialIntTwisting_H_subsingleton
#print axioms AlgebraicGeometry.Proj.degree_laurentExponent
#print axioms AlgebraicGeometry.Proj.laurentExponent_nonneg_of_apply_eq_zero
#print axioms AlgebraicGeometry.Proj.monomial_one_mem_polynomialGrading
#print axioms AlgebraicGeometry.Proj.monomial_one_pow
#print axioms AlgebraicGeometry.Proj.monomial_one_ne_zero
#print axioms AlgebraicGeometry.Proj.monomial_mem_natShift
#print axioms AlgebraicGeometry.Proj.awayMk_monomial_eq_iff
#print axioms AlgebraicGeometry.Proj.awayMk_monomial_eq_iff_laurentExponent
-- Spanning (#491): the monomial fractions exhaust the localization. exists_sum_awayMk_monomial
-- puts every element over ONE common denominator, so a map defined on monomial fractions extends
-- with no further alignment; laurentExponent_mem_index says the exponents it contributes are
-- exactly the admissible ones.
#print axioms AlgebraicGeometry.Proj.monomial_one_pow_ne_zero
#print axioms AlgebraicGeometry.Proj.degree_eq_of_mem_support
#print axioms AlgebraicGeometry.Proj.monomial_coeff_mem_natShift
#print axioms AlgebraicGeometry.Proj.awayMk_eq_sum_monomial
#print axioms AlgebraicGeometry.Proj.exists_sum_awayMk_monomial
#print axioms AlgebraicGeometry.Proj.laurentExponent_mem_index
-- The numerator side of the sign projection (#491 -> #340). divMonomial_pow_mul is the
-- well-definedness identity: projecting commutes with raising a representative to a higher power
-- of the denominator, which is the move that relates any two representatives.
#print axioms AlgebraicGeometry.Proj.degree_eq_weight_one_apply
#print axioms AlgebraicGeometry.Proj.isHomogeneous_divMonomial
#print axioms AlgebraicGeometry.Proj.divMonomial_monomial_mul_add
#print axioms AlgebraicGeometry.Proj.divMonomial_monomial_mul_comm
#print axioms AlgebraicGeometry.Proj.divMonomial_pow_mul
#print axioms AlgebraicGeometry.Proj.divMonomial_mem_natShift
-- Independence (#491): a vanishing monomial combination at a fixed denominator has vanishing
-- coefficients. With exists_sum_awayMk_monomial this is the basis statement in usable form -- a
-- map may be DEFINED by its effect on monomial fractions.
#print axioms AlgebraicGeometry.Proj.sum_monomial_eq_zero_iff
#print axioms AlgebraicGeometry.Proj.sum_awayMk_monomial_eq_zero_iff
-- The projection descends to the localization and retracts the face inclusion (#491 -> #340).
-- signProjection is defined by choosing a representative; signProjection_awayMk is the equation
-- that pins it down, and signProjection_laurentFace is the first of the two properties the
-- contracting homotopy consumes. AwayRep's auto-generated projections are recorded too, since
-- the completeness ratchet counts them.
#print axioms AlgebraicGeometry.Proj.AwayRep
#print axioms AlgebraicGeometry.Proj.AwayRep.mk.inj
#print axioms AlgebraicGeometry.Proj.AwayRep.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Proj.AwayRep.pow
#print axioms AlgebraicGeometry.Proj.AwayRep.num
#print axioms AlgebraicGeometry.Proj.AwayRep.num_mem
#print axioms AlgebraicGeometry.Proj.AwayRep.frac
#print axioms AlgebraicGeometry.Proj.AwayRep.frac_surjective
#print axioms AlgebraicGeometry.Proj.AwayRep.project
#print axioms AlgebraicGeometry.Proj.AwayRep.pow_mul_num_mem
#print axioms AlgebraicGeometry.Proj.AwayRep.frac_project_raise
#print axioms AlgebraicGeometry.Proj.AwayRep.frac_project_congr
#print axioms AlgebraicGeometry.Proj.signProjection
#print axioms AlgebraicGeometry.Proj.signProjection_frac
#print axioms AlgebraicGeometry.Proj.signProjection_awayMk
#print axioms AlgebraicGeometry.Proj.monomial_single_mem
#print axioms AlgebraicGeometry.Proj.laurentFace_mul
#print axioms AlgebraicGeometry.Proj.monomial_mem_add_degree
#print axioms AlgebraicGeometry.Proj.laurentFace
#print axioms AlgebraicGeometry.Proj.laurentFace_awayMk
#print axioms AlgebraicGeometry.Proj.signProjection_laurentFace
-- Additivity of the projection (#491 -> #340): the homotopy applies it to an alternating sum
-- of faces, so it consumes the bundled additive form. signProjection_laurentFace_comm is the
-- second and last property the homotopy needs -- the projection commutes with every face other
-- than the retracted one; the delta' i0 = 0 hypothesis is the per-block restriction of the
-- proof plan, and the unrestricted square at e = i0 is false rather than unproved.
#print axioms AlgebraicGeometry.Proj.signProjection_add
#print axioms AlgebraicGeometry.Proj.signProjectionHom
#print axioms AlgebraicGeometry.Proj.signProjectionHom_apply
#print axioms AlgebraicGeometry.Proj.monomial_single_pow_smul_mem
#print axioms AlgebraicGeometry.Proj.signProjection_laurentFace_comm
-- The block decomposition (#340, step 2). Each away localization is decomposed by the negative
-- support N(alpha) of the Laurent exponent: laurentFilter selects one block of a numerator,
-- blockProj descends it to the localization (choice-based, pinned by blockProj_awayMk, same
-- pattern as signProjection), sum_blockProj says the finitely many blocks of gamma.support's
-- powerset exhaust every element, and laurentFace_blockProj says the Cech faces commute with
-- every block projection -- the differential preserves N(alpha). Deliberately NOT packaged as a
-- direct-sum iso or a product-indexed complex: the vanishing argument consumes exactly these
-- projections, elementwise, and nothing categorical.
#print axioms AlgebraicGeometry.Proj.intNegSupport
#print axioms AlgebraicGeometry.Proj.mem_intNegSupport
#print axioms AlgebraicGeometry.Proj.intNegSupport_laurentExponent_subset
-- The finite index set of the full block (#568 step 6.1). An exponent negative in every
-- coordinate whose coordinates sum to d has each coordinate trapped in [d + card - 1, -1], so
-- the exponents form a subset of a finite box. This is the finiteness the top cohomology rests
-- on; it is empty unless d <= -(card iota), which is Serre's vanishing in exponent form.
#print axioms AlgebraicGeometry.Proj.finite_setOf_degree_eq_of_neg
#print axioms AlgebraicGeometry.Proj.laurentExponent_sub_of_add_eq
#print axioms AlgebraicGeometry.Proj.laurentFilter
#print axioms AlgebraicGeometry.Proj.coeff_laurentFilter_of_eq
#print axioms AlgebraicGeometry.Proj.coeff_laurentFilter_of_ne
#print axioms AlgebraicGeometry.Proj.laurentFilter_add
#print axioms AlgebraicGeometry.Proj.laurentFilter_mem_natShift
#print axioms AlgebraicGeometry.Proj.sum_laurentFilter_powerset
#print axioms AlgebraicGeometry.Proj.laurentFilter_laurentFilter_self
#print axioms AlgebraicGeometry.Proj.laurentFilter_laurentFilter_of_ne
#print axioms AlgebraicGeometry.Proj.laurentFilter_eq_zero_of_not_subset
#print axioms AlgebraicGeometry.Proj.laurentFilter_monomial_mul
#print axioms AlgebraicGeometry.Proj.AwayRep.blockFilter
#print axioms AlgebraicGeometry.Proj.AwayRep.frac_blockFilter_raise
#print axioms AlgebraicGeometry.Proj.AwayRep.frac_blockFilter_congr
#print axioms AlgebraicGeometry.Proj.blockProj
#print axioms AlgebraicGeometry.Proj.blockProj_frac
#print axioms AlgebraicGeometry.Proj.blockProj_awayMk
#print axioms AlgebraicGeometry.Proj.blockProj_add
#print axioms AlgebraicGeometry.Proj.blockProjHom
#print axioms AlgebraicGeometry.Proj.blockProjHom_apply
#print axioms AlgebraicGeometry.Proj.sum_blockProj
#print axioms AlgebraicGeometry.Proj.blockProj_blockProj_self
#print axioms AlgebraicGeometry.Proj.blockProj_blockProj_of_ne
#print axioms AlgebraicGeometry.Proj.blockProj_eq_zero_of_not_subset
#print axioms AlgebraicGeometry.Proj.laurentFace_blockProj
-- The contracting homotopy of a block (#340, step 3). laurentHomotopy projects out ALL of the
-- cone variable and reinserts the surplus by a face, which makes it well defined whatever the
-- tuple contains and buys the two identities the homotopy computation d h + h d = id consumes:
-- an UNRESTRICTED square with every face (laurentHomotopy_laurentFace_comm -- including the
-- face in the cone variable itself, where the surplus shifts by one and rebalances), and the
-- retraction of the cone face on a block (laurentHomotopy_laurentFace_blockProj), which is the
-- only identity that sees the block and the only place i0 not-in F is spent.
#print axioms AlgebraicGeometry.Proj.monomial_mul_divMonomial_cancel
#print axioms AlgebraicGeometry.Proj.laurentFilter_apply_ge
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_split
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_back
#print axioms AlgebraicGeometry.Proj.laurentHomotopy
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_numerator_mem
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_awayMk
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_laurentFace_blockProj
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_laurentFace_comm
-- The block homotopy carried onto the variable Cech cover (#340, step 3). powersCongr
-- transports a degree-zero localization along an equality of denominators (the element never
-- moves; every equation is subst plus proof irrelevance), tupleExponent names the Cech
-- denominator as a monomial, and the Cech-level block projections and homotopy map are the
-- monomial-level maps conjugated by that transport. cechTermCongr_apply_section is the whole
-- of the dependent rewriting the vanishing computation needs; the three identities it runs on
-- are cechFace_cechBlockProj, cechHomotopy_cechFace_zero and cechHomotopy_cechFace_succ.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.powersCongr
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.powersCongr_awayMk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.powersCongr_trans
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.powersCongr_symm_apply_apply
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.powersCongr_symm_trans
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.powersCongr_faceMap
#print axioms AlgebraicGeometry.Proj.tupleExponent
#print axioms AlgebraicGeometry.Proj.tupleDenominator_eq
#print axioms AlgebraicGeometry.Proj.tupleExponent_cons
#print axioms AlgebraicGeometry.Proj.tupleExponent_succAbove
#print axioms AlgebraicGeometry.Proj.tupleDenominator_cons_eq
#print axioms AlgebraicGeometry.Proj.cons_comp_succAbove_zero
#print axioms AlgebraicGeometry.Proj.cons_comp_succAbove_succ
#print axioms AlgebraicGeometry.Proj.cechTermEquiv
#print axioms AlgebraicGeometry.Proj.cechTermEquiv_cechFace
#print axioms AlgebraicGeometry.Proj.cechBlockProj
#print axioms AlgebraicGeometry.Proj.cechBlockProj_apply
#print axioms AlgebraicGeometry.Proj.sum_cechBlockProj
#print axioms AlgebraicGeometry.Proj.cechBlockProj_eq_zero_of_not_subset
#print axioms AlgebraicGeometry.Proj.cechFace_cechBlockProj
#print axioms AlgebraicGeometry.Proj.cechHomotopy
#print axioms AlgebraicGeometry.Proj.cechHomotopy_apply
#print axioms AlgebraicGeometry.Proj.cechTermCongr
#print axioms AlgebraicGeometry.Proj.cechTermCongr_apply_section
#print axioms AlgebraicGeometry.Proj.cechTermCongr_symm_apply_section
#print axioms AlgebraicGeometry.Proj.cechTermCongr_cechBlockProj
#print axioms AlgebraicGeometry.Proj.laurentHomotopy_laurentFace_comm'
#print axioms AlgebraicGeometry.Proj.cechHomotopy_cechFace_zero
#print axioms AlgebraicGeometry.Proj.cechHomotopy_cechFace_succ
-- The primitive of a Cech cocycle (#340, step 3): the vanishing computation in cochain form.
-- Per block a cone point is chosen and the block component of the cocycle is contracted
-- through the homotopy; blocks with no cone point are empty because a nonnegative twist
-- cannot have every exponent negative (the ONLY place d >= 0 is spent); and the per-block
-- identities reassemble over the finitely many blocks of each tuple.
-- cechPrimitive_isPrimitive is the homotopy computation d h + h d = id itself.
#print axioms AlgebraicGeometry.Proj.laurentFilter_eq_zero_of_forall_mem
#print axioms AlgebraicGeometry.Proj.blockProj_eq_zero_of_forall_mem
#print axioms AlgebraicGeometry.Proj.cechBlockProj_eq_zero_of_forall_mem
#print axioms AlgebraicGeometry.Proj.tupleExponent_support_succAbove
#print axioms AlgebraicGeometry.Proj.subset_of_subset_cons
#print axioms AlgebraicGeometry.Proj.cechTermCongr_symm_cechBlockProj
#print axioms AlgebraicGeometry.Proj.cechBlockPrimitive
#print axioms AlgebraicGeometry.Proj.cechBlockPrimitive_of_exists
#print axioms AlgebraicGeometry.Proj.cechBlockPrimitive_of_forall
#print axioms AlgebraicGeometry.Proj.cechBlockPrimitive_eq_zero_of_not_subset
#print axioms AlgebraicGeometry.Proj.cechPrimitive
-- The cone-point case, separated out because it needs no hypothesis on the twist at all. Every
-- block except the one containing every variable has a cone point, so this alone says the
-- cohomology is carried entirely by the full block.
#print axioms AlgebraicGeometry.Proj.cechBlockPrimitive_faces_of_exists
#print axioms AlgebraicGeometry.Proj.cechBlockPrimitive_faces
#print axioms AlgebraicGeometry.Proj.cechPrimitive_isPrimitive
-- The headline of #340: H^n(P, O(d)) = 0 for n >= 1 and d >= 0, over an arbitrary --
-- possibly infinite -- variable set. cechPrimitive_isPrimitive becomes exactness of the
-- algebraic Cech complex through ab_exact_iff and the coordinate formula for the
-- differential, exactness becomes vanishing homology, and the comparison of #495 carries
-- the vanishing to the derived sections group. The HasExt witness is positional throughout.
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechComplex_exactAt
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechComplex_homology_isZero
#print axioms AlgebraicGeometry.Proj.polynomialTwisting_H_subsingleton
#print axioms AlgebraicGeometry.Proj.GradedLinearMap
#print axioms AlgebraicGeometry.Proj.GradedLinearMap.map
#print axioms AlgebraicGeometry.Proj.GradedLinearMap.map_mk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.selfLinearEquiv
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftSelfLinearEquiv
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftAwayLinearEquiv
-- The trivialization needs f invertible in the localization, not a member of it. A
-- homogeneous cofactor carrying f into S records that and keeps denominators inside S;
-- h = 1 is the membership case. Required by the Cech intersections, where the denominator
-- submonoid is .powers of a product and contains no degree-one element.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftToSelfLinearMapOfMulMem
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftLinearEquivOfMulMem
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftLinearEquivOfMem
-- Integer twists (#439). The integer-shift membership condition depends only on the integer
-- n + d, so lowering the twist by e while raising the fraction degree by e is literally the
-- same condition -- the zero branch of the zero-extension needs no separate treatment, and the
-- sign of d never enters. Taking d = 0 gives A ~ A(-e), the negative twist #332 needs.
-- The two congruence lemmas elaboration generates for the integer-shift defs, audited rather
-- than filtered: this repo already lists `.congr_simp` records elsewhere, and DGCategory needs
-- them to reach ceiling 0, so the sweep must keep seeing them.
#print axioms AlgebraicGeometry.Proj.intShift.congr_simp
#print axioms AlgebraicGeometry.Proj.intShiftPiece.congr_simp
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mem_intShift_sub_natCast_add
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mul_pow_mem_intShift
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftLowerLinearMap
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftRaiseLinearMap
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftLowerLinearEquiv
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftLowerLinearEquiv_apply_mk
-- Aiming at a prescribed twist. intShiftLowerLinearEquiv computes its target as d - e, which
-- cannot be pointed at A(0) without a transport; the hypothesis-carrying form takes the target
-- as a parameter instead. intShiftZeroLinearEquiv decides the sign of d once, and nothing
-- downstream sees the case split.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.transitionScalar_mul
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.smul_mk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mk_smul_mk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftShiftLinearEquiv
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mul_pow_toNat_mem_intShift_zero
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftZeroLinearEquiv
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftZeroLinearEquiv_apply_mk
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftZeroLinearEquiv_transition
#print axioms AlgebraicGeometry.Proj.intShiftFiberLinearEquivOfMem
#print axioms AlgebraicGeometry.Proj.intShiftFiberLinearEquiv
-- Sections over an open inside the chart. Because the two computation rules above are uniform
-- in the sign of d, these are a direct mirror of the nonnegative constructions -- nothing here
-- splits on the sign.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mul_pow_toNat_mem_intShift
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftZeroLinearEquiv_symm_apply_mk
-- The cofactor form (#467). A Cech intersection cannot supply f in S: its denominator has
-- degree n+1, so for n >= 1 the powers submonoid contains no degree-one element. A homogeneous
-- cofactor h with f*h in S is what is available. The scalar is parameterized by its exponents
-- rather than by d, so the inverse is the same definition with the pair swapped -- writing it
-- as the -d instance would put (- -d).toNat in the term, only propositionally d.toNat.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mul_pow_mul_pow_mem_intShift_zero
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.mul_pow_mul_pow_mem_intShift
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftZeroLinearEquivOfMulMem
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.intShiftZeroLinearEquivOfMulMem_apply_mk
#print axioms AlgebraicGeometry.Proj.intShiftSectionToZeroOn
#print axioms AlgebraicGeometry.Proj.intShiftSectionFromZeroOn
#print axioms AlgebraicGeometry.Proj.intShiftSectionAddEquivOn
#print axioms AlgebraicGeometry.Proj.intShiftSectionLinearEquivOn
#print axioms AlgebraicGeometry.Proj.isLocallyFraction
#print axioms AlgebraicGeometry.Proj.associatedSheaf
#print axioms AlgebraicGeometry.Proj.stalkEquiv
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_unique
-- Faces vs restriction (#340). moduleAwayToSection is pointwise mapOfLE and restriction only
-- reindexes the point, so the sheaf-level statement reduces to the algebraic one: once both
-- face denominators are inverted, h^n m / g^n and m / f^n are the same element.
#print axioms AlgebraicGeometry.Proj.mapOfLE_faceMap
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_res_faceMap
#print axioms AlgebraicGeometry.Proj.associatedSheafSelfIso
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_self_bijective
#print axioms AlgebraicGeometry.Proj.associatedMap
#print axioms AlgebraicGeometry.Proj.associatedPresheaf_res_apply
#print axioms AlgebraicGeometry.Proj.associatedIsoOfPiecewiseIff
#print axioms AlgebraicGeometry.Proj.natShift
#print axioms AlgebraicGeometry.Proj.intShift
#print axioms AlgebraicGeometry.Proj.mem_intShift_ofNat_iff
-- Integer shifts compose only where the intermediate degree exists (#584). The unrestricted
-- statement is false: an inner shift by a negative e asks for degree n + e, and when that integer
-- is negative the zero extension supplies 0 while the single shift by d + e may still land in a
-- genuine piece. eq_zero_of_mem_intShift_intShift_of_neg makes that failure a theorem rather than
-- a remark. It is a fact about the algebraic model only -- associatedSheaf reads these pieces
-- through homogeneous localizations, where the missing degrees are inverted back in -- so the
-- sheaf-level O(d)(e) = O(d+e) is not obstructed, but it cannot be transported from here.
#print axioms AlgebraicGeometry.Proj.mem_intShift_add_iff_of_nonneg
#print axioms AlgebraicGeometry.Proj.eq_zero_of_mem_intShift_intShift_of_neg

/-! ## The twisted multiplication A(d) (x) M -> M(d) (#584)

The map half of the comparison F (x) O(d) = F(d), at one localization. It is short because of a
fact about the model rather than a construction: DegreeZeroLocalization is a submodule of
LocalizedModule S M, and for the ring itself that ambient IS Localization S -- so an element of
DegreeZeroLocalization A (intShift A d) S is already a scalar acting on LocalizedModule S M. No
multiplication is defined on representatives and no well-definedness argument is needed; only the
certificate that the product lands in the right submodule, which is smul_mem_intShift on the
numerator and mul_mem_graded on the denominator.

twistMul_smul_right is the one thing that does not come free: SMulCommClass between
HomogeneousLocalization A S and LocalizedModule S A is not an instance, and the action is
Module.compHom along algebraMap, so that map has to be named. Same gap as #695's map_smul'.

The section map, the presheaf map through tensorLift, and the isomorphism proof are NOT here, so
#584 is not closed. -/

#print axioms AlgebraicGeometry.Proj.smul_mem_intShift
#print axioms AlgebraicGeometry.Proj.twistMul
#print axioms AlgebraicGeometry.Proj.coe_twistMul
#print axioms AlgebraicGeometry.Proj.twistMul_mk
#print axioms AlgebraicGeometry.Proj.twistMul_add_left
#print axioms AlgebraicGeometry.Proj.twistMul_add_right
#print axioms AlgebraicGeometry.Proj.twistMul_smul_left
#print axioms AlgebraicGeometry.Proj.twistMul_smul_right
-- ...and the same product on sections and as a map of presheaves of modules. The local-fraction
-- certificate is the product of the two factors' certificates on the intersection of their opens,
-- rebuilt by twistMul_mk. twistMultiplicationHom is tensorLift fed the four mk2 laws; the scalar
-- changes ring between the levels, so the two smul laws push it through openToLocalization and the
-- argument order flips with it. That this map is an ISOMORPHISM is not here.
#print axioms AlgebraicGeometry.Proj.monoidalCategoryAssociatedPresheaf
#print axioms AlgebraicGeometry.Proj.sectionTwistMul
#print axioms AlgebraicGeometry.Proj.sectionTwistMul_apply
#print axioms AlgebraicGeometry.Proj.sectionTwistMul_add_left
#print axioms AlgebraicGeometry.Proj.sectionTwistMul_add_right
#print axioms AlgebraicGeometry.Proj.sectionTwistMul_smul_left
#print axioms AlgebraicGeometry.Proj.sectionTwistMul_smul_right
#print axioms AlgebraicGeometry.Proj.twistMultiplicationHom
-- What the twisted multiplication looks like on a degree-one chart: the untwisted one, conjugated
-- by the two trivializations. Both are multiplication by the same scalar, so the proof is
-- associativity of that action. This is the local statement the isomorphism proof needs.
#print axioms AlgebraicGeometry.Proj.intShiftZeroModuleLinearEquiv_twistMul
-- The algebraic half of the sheaf-level composition O(d)(e) = O(d+e) that the two lemmas above
-- record as unobtainable from an algebraic identity: at a localization whose denominators contain
-- a homogeneous element of positive degree the two families have the same degree-zero part.
-- Carrying this to the sections of the associated sheaf is NOT here, so #584 is not closed.
#print axioms AlgebraicGeometry.Proj.mem_intShift_add_of_mem_intShift_intShift
#print axioms AlgebraicGeometry.Proj.isDegreeZero_intShift_intShift_iff

/-! ## The twists compose, on the sheaf side (#584)

Shift.lean proves the graded identity M(d)(e) = M(d+e) FALSE and says the sheaf-level version
"has to be proved on the sheaf side". This is that proof. The comparison is pointwise the identity
-- Fiber is a submodule of LocalizedModule S M, whose ambient does not mention the grading, so
degreeZeroSubmodule_intShift_intShift says the carriers coincide and nothing is transported.

The two directions of the local-fraction condition are not symmetric. Forward, only the numerator's
certificate is rebuilt. Backward, a fraction certified for the single shift is rewritten as
t^k r / t^k s, raising its degree until the double shift can certify it, and the neighbourhood
shrinks to V n D+(t) so that ONE t serves every point -- a per-point choice would not give the
single fraction isLocallyFraction demands. exists_homogeneous_pos_not_mem supplies that t, and is
where the geometry enters: a point of Proj is a relevant prime.

Relating this to the TENSOR product is a separate comparison and is NOT here, so #584 is not
closed. -/

#print axioms AlgebraicGeometry.Proj.exists_homogeneous_pos_not_mem
#print axioms AlgebraicGeometry.Proj.mem_primeCompl_of_not_mem
#print axioms AlgebraicGeometry.Proj.degreeZeroSubmodule_intShift_intShift
#print axioms AlgebraicGeometry.Proj.fiberIntShiftAddEquiv
#print axioms AlgebraicGeometry.Proj.fiberIntShiftAddEquiv_coe
#print axioms AlgebraicGeometry.Proj.pred_intShift_intShift_of_pred
#print axioms AlgebraicGeometry.Proj.pred_intShift_add_of_pred
#print axioms AlgebraicGeometry.Proj.sectionAddEquivIntShiftAdd
#print axioms AlgebraicGeometry.Proj.sectionLinearEquivIntShiftAdd
#print axioms AlgebraicGeometry.Proj.associatedSheafIntShiftAddIso
#print axioms AlgebraicGeometry.Proj.sheafTwistAddIso
#print axioms AlgebraicGeometry.Proj.twistingSheafAddIso

/-! ## The twist trivialization, for a graded module (#584)

TwistLocalization.lean and TwistChart.lean are stated for A as a module over itself, which is all
the twisting sheaf needs -- #688's invertibility only needed that case. The tensor comparison
F (x) O(d) = F(d) needs an ARBITRARY graded module, and there was no module analogue in the tree at
all. This is the localization and fiber halves of it.

Nothing in the construction resists: intTwistScalar lives in Localization S and acts on
LocalizedModule S M exactly as on LocalizedModule S A. Only two things are new -- the degree
bookkeeping is GradedSMul.smul_mem where the ring case used mul_mem_graded, and map_smul' must name
the algebraMap into Localization S, because the HomogeneousLocalization action is Module.compHom
along it and the two commute only once that is visible.

The section and .over halves follow below, completing the module trivialization and with it the
prerequisite the tensor comparison was blocked on. The comparison itself is still missing, so #584
is not closed. -/

#print axioms Proj.DegreeZeroLocalization.pow_smul_mem_intShift_zero
#print axioms Proj.DegreeZeroLocalization.pow_smul_mem_intShift
#print axioms Proj.DegreeZeroLocalization.intShiftZeroModuleLinearEquiv
#print axioms Proj.DegreeZeroLocalization.intShiftZeroModuleLinearEquiv_apply_mk
#print axioms Proj.DegreeZeroLocalization.intShiftZeroModuleLinearEquiv_symm_apply_mk
#print axioms AlgebraicGeometry.Proj.intShiftModuleFiberLinearEquivOfMem
-- The section and .over halves, which complete the module trivialization and with it the
-- prerequisite the tensor comparison was blocked on. Ports of intShiftSectionToZeroOn and
-- intShiftOverIso at an arbitrary graded module; the numerator becomes f ^ k . r rather than
-- r * f ^ k, matching the order LocalizedModule.mk_smul_mk produces.
#print axioms AlgebraicGeometry.Proj.intShiftModuleSectionToZeroOn
#print axioms AlgebraicGeometry.Proj.intShiftModuleSectionFromZeroOn
#print axioms AlgebraicGeometry.Proj.intShiftModuleSectionAddEquivOn
#print axioms AlgebraicGeometry.Proj.intShiftModuleSectionLinearEquivOn
#print axioms AlgebraicGeometry.Proj.intShiftModuleOverIso
#print axioms AlgebraicGeometry.Proj.intShiftModuleZeroIso
#print axioms AlgebraicGeometry.Proj.intShiftModuleOverSelfIso
#print axioms AlgebraicGeometry.Proj.intShiftModuleFiberLinearEquiv
#print axioms AlgebraicGeometry.Proj.sheafTwist
#print axioms AlgebraicGeometry.Proj.sheafTwistZeroIso
#print axioms AlgebraicGeometry.Proj.sheafNatTwistAddIso
#print axioms AlgebraicGeometry.Proj.twistingSheaf
#print axioms AlgebraicGeometry.Proj.twistingSheafOfNatIso
#print axioms AlgebraicGeometry.Proj.AffineComparisonData
#print axioms AlgebraicGeometry.Proj.localizedNatShiftDegreeOneIso
#print axioms AlgebraicGeometry.Proj.natShiftSectionLinearEquiv
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_natShift_degreeOne_bijective

-- The degree-one chart trivialization holds over every open below D₊(f), not only over the
-- chart itself: the underlying equivalence is pointwise and uses membership alone. The
-- basic-open forms above are now the `le_rfl` case of these.
#print axioms AlgebraicGeometry.Proj.natShiftFiberLinearEquivOfMem
#print axioms AlgebraicGeometry.Proj.natShiftSectionToSelfOn
#print axioms AlgebraicGeometry.Proj.natShiftSectionFromSelfOn
#print axioms AlgebraicGeometry.Proj.natShiftSectionAddEquivOn
#print axioms AlgebraicGeometry.Proj.natShiftSectionLinearEquivOn
-- The trivialization commutes with restriction, so it is a map of presheaves on the opens
-- below the chart, not an unrelated family. This is what a sheaf-level chart isomorphism
-- for O(d) will be assembled from.
#print axioms AlgebraicGeometry.Proj.natShiftSectionToSelfOn_map
#print axioms AlgebraicGeometry.Proj.natShiftSectionFromSelfOn_map
#print axioms AlgebraicGeometry.Proj.natShiftOverIso
#print axioms AlgebraicGeometry.Proj.standardAway_degreeOne_opensRange_le
#print axioms AlgebraicGeometry.Proj.natShiftLocalQuasicoherentData
-- G1b: the variable cover of polynomial projective space is Cech-acyclic for every
-- nonnegative twist, so the Cech-to-derived comparison applies to O(d).
#print axioms AlgebraicGeometry.Proj.polynomialVariable_coversTop
-- Acyclicity takes quasi-coherence as its hypothesis, not a twist (#439): the twist enters the
-- argument in exactly one place, so a negative twist is acyclic here the moment its
-- quasi-coherence lands. The O(d) statements are corollaries supplying that input.
#print axioms AlgebraicGeometry.Proj.polynomialVariable_isCechAcyclicFor_of_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.polynomialVariable_isCechAcyclicCover_of_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.polynomialVariable_isCechAcyclicFor
#print axioms AlgebraicGeometry.Proj.polynomialVariable_isCechAcyclicCover
-- Acyclicity (#338) and the complex identification (#339) combine into the statement the twist
-- computation starts from (#340): Hⁱ(Pⁿ, O(d)) is the homology of the explicit complex of
-- degree-zero homogeneous localizations.
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechComplex_computesCohomology
-- The same for an integer twist (#467 step 4). The acyclicity argument never mentions the
-- twist -- it needs quasi-coherence and affineness of the intersections, and the degree
-- restriction that constrains the trivialization plays no part -- so each is one application
-- of the quasi-coherent form to polynomialIntShift_isQuasicoherent.
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntShift_isCechAcyclicFor
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntShift_isCechAcyclicCover
-- The integer-twist form of the same conclusion (#332 step 1, negative half). Not a corollary
-- of the nonnegative statement: natShift and intShift are different graded families, so the two
-- complexes are related by transport rather than definitional equality. This is the shape
-- devissage consumes, which needs Hⁱ(Pⁿ, O(d)) as an explicit complex at negative d.
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplex_computesCohomology
#print axioms AlgebraicGeometry.Proj.polynomialVariable_adjoin_eq_top
#print axioms AlgebraicGeometry.Proj.natShiftQuasicoherentData
#print axioms AlgebraicGeometry.Proj.natShift_isQuasicoherent
-- Integer twists (#439). Same three steps as the nonnegative case; the only difference is that
-- the chart trivialization lands at A(0) rather than A, so the transport composes with the
-- zero-normalization -- an isomorphism because intShift 0 and the grading have equal members.
-- The sign of d never enters, because the trivialization it rests on is uniform in the sign.
#print axioms AlgebraicGeometry.Proj.intShiftOverIso
#print axioms AlgebraicGeometry.Proj.intShiftZeroIso
#print axioms AlgebraicGeometry.Proj.intShiftLocalQuasicoherentData
#print axioms AlgebraicGeometry.Proj.intShiftQuasicoherentData
#print axioms AlgebraicGeometry.Proj.intShift_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.polynomialNatShift_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.polynomialIntShift_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.affineComparisonDataSelf
#print axioms AlgebraicGeometry.Proj.associatedSheaf_self_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.AffineComparisonData.quasicoherentData
#print axioms AlgebraicGeometry.Proj.AffineComparisonData.associatedSheaf_isQuasicoherent
#print axioms AddCommGrpCat.productCone
#print axioms AddCommGrpCat.productConeIsLimit
#print axioms AddCommGrpCat.piIsoPi
#print axioms AddCommGrpCat.piIsoPi_inv_π
#print axioms AddCommGrpCat.piIsoPi_inv_π_apply
#print axioms AddCommGrpCat.piIsoPi_hom_eval
#print axioms AddCommGrpCat.piIsoPi_hom_eval_apply
#print axioms AddCommGrpCat.piAddEquivPi

-- The degreewise Cech comparison on polynomial Proj: degree n of Mathlib's Cech complex of
-- O(d) over the variable charts is the explicit product of homogeneous degree-zero
-- localizations. Degreewise only; the differential transport is separate.
#print axioms AlgebraicGeometry.Proj.polynomialVariableChart
#print axioms AlgebraicGeometry.Proj.twistPresheaf
#print axioms AlgebraicGeometry.Proj.piObj_polynomialVariableChart
#print axioms AlgebraicGeometry.Proj.cechCochainsDegreewiseAddEquiv
-- The comparison read one index at a time, and the per-index square (#340). The face
-- morphism is left arbitrary in cechIndexEquiv_map_face: Opens is a thin category, so the
-- inclusion Mathlib's Cech nerve produces is the only morphism there and Subsingleton.elim
-- supplies it, with no separate identification of the face.
#print axioms AlgebraicGeometry.Proj.cechIndexEquiv
#print axioms AlgebraicGeometry.Proj.cechCochainsDegreewiseAddEquiv_apply
#print axioms AlgebraicGeometry.Proj.cechCochainsDegreewiseAddEquiv_symm_apply
#print axioms AlgebraicGeometry.Proj.cechIndexEquiv_map_face
-- Mathlib's Cech differential read in coordinates (#340). Both proofs finish with `exact`
-- rather than `rw`: the two sides differ in the HasProduct instance that Pi.pi carries, which
-- rw will not see through but definitional unification will.
#print axioms CategoryTheory.cechNerve
#print axioms CategoryTheory.cechCosimplicial
#print axioms CategoryTheory.cechTermFamily
#print axioms CategoryTheory.cechComplexFunctor_delta_π
#print axioms CategoryTheory.cechComplexFunctor_d_π
-- The same projection statement for the map a morphism of presheaves induces, which is what
-- carries the base-field action from one Cech index up to a whole degree.
#print axioms CategoryTheory.cechComplexFunctor_map_f_π
-- The complex-level form (#340). The differential is carried across the degreewise comparison
-- rather than defined as an alternating sum, so d-squared and the comparison isomorphism are
-- both free; the alternating-sum formula is a separate lemma about this complex.
#print axioms AlgebraicGeometry.Proj.cechComplexOfTwist
#print axioms AlgebraicGeometry.Proj.cechCochainsIso
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechComplex
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechComplexIso
-- The differential in coordinates (#440). Stated twice: through the comparison, which is the
-- form to prove with, and against the complex's own d, which needs its cochain typed in the
-- carrier because CochainComplex.of.d hides behind a dite and .X n is semireducible.
#print axioms AddCommGrpCat.hom_sum_apply
#print axioms AddCommGrpCat.hom_sum_zsmul_apply
#print axioms AlgebraicGeometry.Proj.cechCochainsDegreewiseAddEquiv_d
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechComplex_d_apply
-- The whole layer again for a twist of either sign (#332 step 1, negative half). Nothing here
-- knows about the sign: the three shape mismatches are statements about the cover, so
-- piObj_polynomialVariableChart is reused rather than restated, and the only twist-dependent
-- inputs are intCechTermSectionAddEquiv and its face compatibility.
#print axioms AlgebraicGeometry.Proj.intTwistPresheaf
#print axioms AlgebraicGeometry.Proj.intCechIndexEquiv
#print axioms AlgebraicGeometry.Proj.intCechCochainsDegreewiseAddEquiv
#print axioms AlgebraicGeometry.Proj.intCechCochainsDegreewiseAddEquiv_apply
#print axioms AlgebraicGeometry.Proj.intCechCochainsDegreewiseAddEquiv_symm_apply
#print axioms AlgebraicGeometry.Proj.intCechIndexEquiv_map_face
#print axioms AlgebraicGeometry.Proj.intCechComplexOfTwist
#print axioms AlgebraicGeometry.Proj.intCechCochainsIso
#print axioms AlgebraicGeometry.Proj.intCechCochainsDegreewiseAddEquiv_d
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplex
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplexIso
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplex_d_apply
#print axioms AlgebraicGeometry.Proj.AffineComparisonDataOn
#print axioms AlgebraicGeometry.Proj.AffineComparisonDataOn.localQuasicoherentData
#print axioms AlgebraicGeometry.Proj.AffineComparisonDataOn.associatedSheaf_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.AffineComparisonData.toOn
#print axioms AlgebraicGeometry.Proj.degreeOneCharts_coversTop
#print axioms AlgebraicGeometry.Proj.associatedSheaf_isCoherent_of_finitePresentation
#print axioms AlgebraicGeometry.Proj.associatedSheaf_self_isCoherent
#print axioms AlgebraicGeometry.Proj.associatedSheaf_isCoherent_of_noetherian_finite
#print axioms AlgebraicGeometry.Proj.BasicOpenSectionData
#print axioms AlgebraicGeometry.Proj.basicOpenSectionDataSelf
#print axioms AlgebraicGeometry.Proj.basicOpenSectionEquiv
#print axioms AlgebraicGeometry.Proj.TwistingSectionRange
#print axioms AlgebraicGeometry.Proj.TwistingSectionRange.globalSections_finite
#print axioms AlgebraicGeometry.Proj.projectiveSpace_globalSections_finite
#print axioms AlgebraicGeometry.Proj.projectiveSpace_variableSection_bijective
#print axioms AlgebraicGeometry.Proj.polynomialVariableBasicOpen_cover
#print axioms AlgebraicGeometry.Proj.polynomialToNatGlobalSections_injective
#print axioms AlgebraicGeometry.Proj.polynomialToNatGlobalSections_surjective
#print axioms AlgebraicGeometry.Proj.polynomialNatGlobalSectionsAddEquiv
#print axioms AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsAddEquiv
#print axioms AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsModuleIso
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechDenominator_mem
-- The Cech faces (#340). Dropping index j divides the denominator by exactly one variable, so
-- the face is DegreeZeroLocalization.faceMap and not mapOfLE: powers of the smaller denominator
-- are not contained in powers of the larger one.
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechDenominator_succAbove
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechDenominator_succAbove_mem
#print axioms AlgebraicGeometry.Proj.polynomialVariableCechFace
-- The same three objects for an integer twist (#467 step 2). faceMap is generic in the grading,
-- so the face instantiates at intShift with the identical denominator arithmetic; the two
-- membership facts it consumes do not mention the twist at all.
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechTerm
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechCochains
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechFace
-- The integer Cech comparison (#467 step 3). Five steps where the nonnegative case has three;
-- the two extra ones are grading transports that move no data -- the integer trivializations
-- land at A(0) while the section comparison is stated against A.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.linearEquivOfMemIff
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.coe_linearEquivOfMemIff
#print axioms AlgebraicGeometry.Proj.sectionAddEquivOfMemIff
#print axioms AlgebraicGeometry.Proj.intCechTermSectionAddEquiv
-- Pointwise readings of the integer section maps, toward the bijectivity restatement (#467 3b).
#print axioms AlgebraicGeometry.Proj.sectionAddEquivOfMemIff_apply
#print axioms AlgebraicGeometry.Proj.intShiftSectionToZeroOn_apply
#print axioms AlgebraicGeometry.Proj.intShiftSectionFromZeroOn_apply
#print axioms AlgebraicGeometry.Proj.intShiftFiberLinearEquivOfMem_symm_apply_mk
-- 3b closed. The five-step composite has to be named by `change` before anything rewrites:
-- simp will not unfold it far enough to expose the mk argument, because two steps are AddEquiv
-- transports whose apply lemmas only fire once the argument is already in mk form.
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.linearEquivOfMemIff_mk
#print axioms AlgebraicGeometry.Proj.intCechTermSectionAddEquiv_apply_mk
#print axioms AlgebraicGeometry.Proj.intCechTermSectionAddEquiv_toAddMonoidHom
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_intCechDenominator_bijective
-- G2 (#339): the algebraic Cech term is the sections of O(d) on that intersection. The
-- denominator has degree n+1, so the algebraic trivialization goes through invertibility
-- (X_mul_cechCofactor) rather than membership, and the sheaf-level one through the first
-- variable's degree-one chart.
#print axioms AlgebraicGeometry.Proj.cechCofactor
#print axioms AlgebraicGeometry.Proj.X_mul_cechCofactor
#print axioms AlgebraicGeometry.Proj.cechCofactor_mem
#print axioms AlgebraicGeometry.Proj.basicOpen_denominator_le
#print axioms AlgebraicGeometry.Proj.cechTermSectionAddEquiv
-- The comparison is the canonical pointwise fraction-to-section map, not merely some
-- equivalence: the two trivializations by the index's first variable cancel. This is what makes
-- restriction to a smaller open a pointwise computation, which the Cech differential needs.
#print axioms AlgebraicGeometry.Proj.cechTermSectionAddEquiv_apply_mk
#print axioms AlgebraicGeometry.Proj.cechTermSectionAddEquiv_toAddMonoidHom
-- The consumable form: the comparison carries polynomialVariableCechFace to restriction.
#print axioms AlgebraicGeometry.Proj.cechTermSectionAddEquiv_res_face
-- The same face compatibility for a twist of either sign (#332 step 1, negative half). Once
-- intCechTermSectionAddEquiv_toAddMonoidHom has identified the five-step composite with the
-- canonical fraction-to-section map, this is moduleAwayToSection_res_faceMap, which is generic
-- in the graded module and never mentions the twist.
#print axioms AlgebraicGeometry.Proj.intCechTermSectionAddEquiv_res_face
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_cechDenominator_bijective
#print axioms AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftLinearEquivOfMulMem_apply_mk
#print axioms AlgebraicGeometry.Proj.natShiftSectionFromSelfOn_apply
#print axioms AlgebraicGeometry.Proj.natShiftFiberLinearEquivOfMem_symm_apply_mk
#print axioms AlgebraicGeometry.Proj.natShiftSectionFromSelfOn_selfBasicOpenSectionAddEquiv_mk
#print axioms AlgebraicGeometry.Proj.basicOpen_polynomialVariableCechDenominator

-- The geometric source has one over-scheme object and proof-irrelevant adjective layers.
#print axioms SchemeOverField
#print axioms SchemeOverField.IsVariety
#print axioms Variety
#print axioms SmoothProperVariety
#print axioms ChernClassData.chernCharacterFour
#print axioms ChernClassData.toddFour
#print axioms ChernClassData.chernCharacterComponent
#print axioms ChernClassData.toddComponent
#print axioms Variety.NumericalData.SatisfiesHRR
#print axioms Variety.NumericalData.SatisfiesHRR.eq
#print axioms Variety.NumericalData.toNumericalVariety
#print axioms Variety.NumericalData.toNumericalVariety_satisfiesHRR
#print axioms Variety.NumericalData.toNumericalVariety_chComp_four
#print axioms Variety.NumericalData.toNumericalVariety_toddComp_four

-- `classOf` was a function plus `classOf_iso` and `classOf_shortExact`; those two laws
-- said the function factors through `K₀Ab`, so they were never data. One hom, and the
-- laws as theorems under their original names.
#print axioms Variety.NumericalData.classOfHom
#print axioms Variety.NumericalData.classOf_apply
#print axioms Variety.NumericalData.classOfHom_of_iso
#print axioms Variety.NumericalData.classOfHom_of_shortExact
#print axioms Variety.NumericalData.classOf_iso
#print axioms Variety.NumericalData.classOf_shortExact

#print axioms Variety.NumericalData.chernCharacter_classOf
#print axioms Variety.NumericalData.chi_classOf
#print axioms Variety.NumericalData.coherentChernCharacter_shortExact
#print axioms Variety.NumericalData.coherentEulerCharacteristic_shortExact
#print axioms Cohomology.coherentH
#print axioms Cohomology.globalSectionSmul
#print axioms Cohomology.globalSectionSmul_naturality
#print axioms Cohomology.varietyScalarAction
#print axioms Cohomology.coherentScalarAction
#print axioms Cohomology.coherentHScalarAction
#print axioms Cohomology.coherentH_map_smul
#print axioms Cohomology.linearCoherentH
#print axioms Cohomology.linearCoherentHComparison
#print axioms Cohomology.canonicalLinearCohomology
#print axioms Cohomology.LinearCohomology
#print axioms Cohomology.FiniteDimensionalCohomology
#print axioms Cohomology.FiniteDimensionalCohomology.dimension_iso

-- Canonical-sheaf data is constructed from smooth relative differentials. Standard-smooth
-- charts globalize through sheafification, their determinant line has an explicit dual inverse,
-- and the derived object is constructed as `ω_X[n]`.
#print axioms LinearMap.exteriorPower
#print axioms LinearMap.exteriorPower_ιMulti
#print axioms PresheafOfModules.exteriorPower
#print axioms PresheafOfModules.exteriorPower.map
#print axioms PresheafOfModules.exteriorPower.mapIso
#print axioms PresheafOfModules.exteriorPowerFunctor
#print axioms Scheme.Modules.exteriorPower
#print axioms Scheme.Modules.exteriorPowerMapIso
#print axioms Scheme.Modules.exteriorPowerSheafification
#print axioms Scheme.Modules.topPowerset
#print axioms Scheme.Modules.topExteriorFreeEquiv
#print axioms Scheme.Modules.topExteriorFreeEquiv_ιMulti
#print axioms Scheme.Modules.topExteriorFreeIso
#print axioms Scheme.Modules.exteriorPowerOver
#print axioms Scheme.Modules.exteriorPowerOverMapIsoOfIso
#print axioms Scheme.Modules.exteriorPowerOverMapIso
#print axioms Scheme.Modules.topExteriorFreeOverIso
#print axioms Scheme.Modules.overExteriorPowerPresheafIso
#print axioms Scheme.Modules.exteriorPowerOverIso
#print axioms Scheme.Modules.dualPresheaf
#print axioms Scheme.Modules.evaluation
#print axioms Scheme.Modules.dualLine
#print axioms Scheme.Modules.tensorDualIso
#print axioms Scheme.Modules.dualLine_isInvertible
#print axioms Scheme.Modules.LineBundleData.ofIsInvertible
#print axioms SheafOfModules.IsInvertible.isFinitePresentation
#print axioms Scheme.Modules.LineBundleData.isCoherent
#print axioms Scheme.Modules.LineBundleData.finiteLocallyFree
#print axioms Scheme.Modules.LineBundleData.unit
#print axioms Variety.baseFieldPresheaf
#print axioms Variety.baseFieldToGlobalSections
#print axioms Variety.baseFieldToStructurePresheaf
#print axioms Variety.relativeDifferentialsPresheaf
#print axioms Variety.relativeDifferentials
#print axioms Variety.relativeDerivationPresheaf
#print axioms Variety.relativeDifferentialsSheafification
#print axioms Variety.relativeDerivation
#print axioms Variety.relativeDifferentialsDesc
#print axioms Variety.relativeDifferentialsDesc_fac
#print axioms Variety.relativeDifferentialsDesc_unique
#print axioms Variety.relativeDifferentials_hom_ext
#print axioms Variety.relativeDifferentialsPresheaf_obj
#print axioms Variety.relativeDerivationPresheaf_d
#print axioms Variety.relativeDifferentialsPresheaf_obj_free
#print axioms Variety.relativeDifferentialsPresheaf_obj_rank
#print axioms Scheme.Modules.FixedRankTrivializations
#print axioms Scheme.Modules.FixedRankTrivializations.localGenerators
#print axioms Scheme.Modules.FixedRankTrivializations.localGenerators_isLocallyFreeData
#print axioms Scheme.Modules.FixedRankTrivializations.finiteLocallyFree
#print axioms Scheme.Modules.FixedRankTrivializations.topExteriorTrivialization
#print axioms Scheme.Modules.FixedRankTrivializations.topExteriorPower_isInvertible
#print axioms Scheme.Modules.FixedRankTrivializations.exteriorDeterminantData
#print axioms Scheme.Modules.FixedRankTrivializations.determinantData
#print axioms Scheme.Modules.FixedRankTrivializations.isLocallyFree
#print axioms Variety.SmoothChart
#print axioms Variety.SmoothChart.ofSmooth
#print axioms Variety.SmoothChart.standardSmooth_baseField
#print axioms Variety.SmoothCotangentTrivializations
#print axioms Variety.relativeDifferentialsChartIso
#print axioms Variety.SmoothCotangentTrivializations.ofSmooth
#print axioms Variety.SmoothCotangentTrivializations.chartSources_coversTop
#print axioms Variety.SmoothCotangentTrivializations.fixedRankTrivializations
#print axioms Variety.SmoothCotangentTrivializations.finiteLocallyFree
#print axioms Variety.SmoothCotangentTrivializations.relativeDifferentials_isLocallyFree
#print axioms Variety.relativeDifferentialsFiniteLocallyFree
#print axioms Variety.relativeDifferentials_isLocallyFree_of_smooth
#print axioms Variety.relativeDifferentialsExteriorDeterminantData
#print axioms Variety.relativeDifferentialsDeterminantData
#print axioms SmoothProperVariety.finiteCohomology
#print axioms SmoothProperVariety.point
#print axioms SmoothProperVariety.CanonicalSheafData
#print axioms SmoothProperVariety.CanonicalSheafData.ofRelativeDifferentials
#print axioms SmoothProperVariety.CanonicalSheafData.ofRelativeDifferentials_cotangent
#print axioms SmoothProperVariety.CanonicalSheafData.ofSmoothRelativeDifferentials
#print axioms SmoothProperVariety.CanonicalSheafData.ofSmoothRelativeDifferentials_cotangent
#print axioms SmoothProperVariety.CanonicalSheafData.canonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.antiCanonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.canonicalClass_eq_of_iso
#print axioms SmoothProperVariety.CanonicalSheafData.CanonicalDivisorData
#print axioms SmoothProperVariety.CanonicalSheafData.CanonicalDivisorData.toPic_eq_canonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.CanonicalDivisorData.classToPic_eq_canonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.DualizingSheafComparison
#print axioms SmoothProperVariety.CanonicalSheafData.DualizingSheafComparison.candidateClass_eq
#print axioms SmoothProperVariety.CanonicalSheafData.canonicalCohObject
#print axioms SmoothProperVariety.CanonicalSheafData.dualizingComplex
#print axioms SmoothProperVariety.CanonicalSheafData.dualizingComplexIso
#print axioms SmoothProperVariety.CanonicalSheafData.pointCanonicalSheafData
#print axioms SmoothProperVariety.CanonicalSheafData.pointCanonicalSheafData_canonicalSheaf
#print axioms SmoothProperVariety.CanonicalSheafData.pointDualizingComplexIso

-- Layer B stage 5: algebraic linear duality is an exact contravariant functor and therefore has
-- an actual derived lift. The comparison between the opposite derived category and the derived
-- category of the opposite remains explicit, as do geometric RHom and Grothendieck duality.
#print axioms ModuleCat.linearDualFunctor
#print axioms ModuleCat.linearDualFunctor_map_shortExact
#print axioms ModuleCat.linearDualFunctor_preservesFiniteLimits_and_colimits
#print axioms ModuleCat.linearDualFunctor_preservesFiniteLimits
#print axioms ModuleCat.linearDualFunctor_preservesFiniteColimits
#print axioms ModuleCat.derivedLinearDualFunctor
#print axioms ModuleCat.DerivedOppositeComparison
#print axioms ModuleCat.DerivedOppositeComparison.derivedLinearDualFromOpposite
#print axioms ModuleCat.DerivedOppositeComparison.derivedLinearDualShift
#print axioms AlgebraicGeometry.Duality.Serre.DerivedStatement
#print axioms AlgebraicGeometry.Duality.Serre.DerivedStatement.linearDualShift
#print axioms AlgebraicGeometry.Duality.Serre.DerivedStatement.dualizingObject
#print axioms AlgebraicGeometry.Duality.Serre.DerivedStatement.canonicalShiftIso
#print axioms AlgebraicGeometry.Duality.Serre.Data
#print axioms AlgebraicGeometry.Duality.Serre.Data.coherentDualityEquiv
#print axioms AlgebraicGeometry.Duality.Serre.Data.pairing
#print axioms AlgebraicGeometry.Duality.Serre.Data.pairing_isPerfPair
#print axioms AlgebraicGeometry.Duality.Serre.Data.dimension_eq_ext
#print axioms AlgebraicGeometry.Duality.Serre.Data.LocallyFreeSpecialization
#print axioms AlgebraicGeometry.Duality.Serre.Data.LocallyFreeSpecialization.cohomologyDualityEquiv
#print axioms AlgebraicGeometry.Duality.Serre.Data.LocallyFreeSpecialization.dimension_symmetry
#print axioms AlgebraicGeometry.Duality.Serre.Data.LocallyFreeSpecialization.eulerCharacteristic_eq_sum_dimension
#print axioms AlgebraicGeometry.Duality.Serre.Data.LocallyFreeSpecialization.eulerCharacteristic_symmetry
#print axioms AlgebraicGeometry.Duality.Serre.Data.LocallyFreeSpecialization.surface_eulerCharacteristic_symmetry
#print axioms AlgebraicGeometry.Duality.Serre.Data.SurfaceLineBundleFamily
#print axioms AlgebraicGeometry.Duality.Serre.Data.SurfaceLineBundleFamily.toSurfacePicardSymmetry
#print axioms AlgebraicGeometry.Duality.Serre.Data.SurfacePicardSymmetry
#print axioms AlgebraicGeometry.Duality.Serre.Data.SurfacePicardSymmetry.canonical
#print axioms AlgebraicGeometry.Duality.Serre.Data.SurfacePicardSymmetry.k3

-- Serre duality in its bilinear form, `Ext^i(E,F)ᵛ ≃ Ext^(n-i)(F, E ⊗ ω)`. Supplied data in the
-- same idiom as `DerivedStatement` and `Data` above, and for the same upstream reason: the pin
-- has no derived global sections into `D(k)`, no coherent `RHom`, no Grothendieck duality.
-- `Data.duality` supplies only duality into `ω_X`; the bilinear form is what specialises at
-- `E = F` on a surface with trivial canonical to `Ext²(E,E) ≃ Hom(E,E)ᵛ`, which is what
-- Bridgeland's Lemma 5.1 runs on. The consequences below are proved from it, and reduce Lemma 5.1
-- to `hom(E,E) = 1` for a stable sheaf -- simplicity, which this repository does not have.
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.finrank_eq
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.TrivialCanonical
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.finrank_eq_of_trivialCanonical
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.finrank_top_eq_finrank_hom
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.eulerChar
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.surface_selfEuler_eq
#print axioms AlgebraicGeometry.Duality.Serre.BilinearData.surface_selfEuler_le
#print axioms Cohomology.FiniteCohomology
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic
#print axioms Cohomology.FiniteCohomology.finrankSupport_subset_range
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_eq_sum
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_eq_sum_of_bound
#print axioms Cohomology.FiniteCohomology.dimension_iso
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_iso
#print axioms Cohomology.coherentConnectingMap
#print axioms Cohomology.FiniteCohomology.LinearConnectingMaps
#print axioms Cohomology.FiniteCohomology.exact₂
#print axioms Cohomology.FiniteCohomology.LinearConnectingMaps.exact₃
#print axioms Cohomology.FiniteCohomology.LinearConnectingMaps.exact₁
#print axioms Cohomology.FiniteCohomology.alternating_finrank_eq_zero_of_exact
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_additive
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_additive_modules
#print axioms Cohomology.FiniteCohomology.grothendieckEulerHom
#print axioms Cohomology.FiniteCohomology.grothendieckEulerHom_class

-- Layer B stage 5: additive coherent-sheaf invariants ARE homs out of `K₀Ab (Coh X)`.
-- `CoherentAdditiveInvariant`, its free-group route and its bespoke universal property are
-- gone, and so are the surface compatibility aliases that forwarded to them.

-- Layer B stage 5: the scheme-derived surface numerical-variety assembly. The geometric HRR
-- input is stated on coherent sheaves; the audited theorem below descends it to every K₀Ab class.
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.SatisfiesSheafHRR
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.SatisfiesSheafHRR.eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.totalChernCharacterHom
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.totalTodd
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.riemannRochHom
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.rationalEulerHom
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.totalChernCharacterHom_class
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.riemannRochHom_class
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.rationalEulerHom_class
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.hirzebruch_riemannRoch
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toNumericalVariety
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toNumericalVariety_satisfiesHRR
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toNumericalVariety_rank_class
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toNumericalVariety_chComp_class
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toNumericalVariety_toddComp
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toNumericalVariety_chi_class
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.surface_chi_class_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.toIsK3
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.k3_eulerCharacteristic_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.GeometricData.numericalClass

-- Layer A: the graded-basis constructor. `ofGradedBasis` is what every concrete model
-- goes through, so a sorry here would silently contaminate every instance in the repo.
#print axioms NumericalRingData
#print axioms NumericalRingData.piece
#print axioms NumericalRingData.degree
#print axioms NumericalVarietyData
#print axioms NumericalVarietyData.ring
#print axioms NumericalVarietyData.chi
#print axioms gradedPiece
#print axioms gradedPiece_eq_bot
#print axioms gradedPiece_iSupIndep
#print axioms gradedPiece_iSup_eq_top
#print axioms gradedPiece_isInternal
#print axioms gradedPiece_mul_mem
#print axioms NumericalRingData.ofGradedBasis

-- Layer A: the general Riemann-Roch expansion and its surface specialisation.
#print axioms NumericalVarietyData.SatisfiesHRR
#print axioms NumericalVarietyData.SatisfiesHRR.eq
#print axioms NumericalVarietyData.hrr
#print axioms NumericalVarietyData.degree_ch_mul_todd
#print axioms NumericalVarietyData.chi_eq_sum
#print axioms NumericalVarietyData.discriminant_mem_piece_two
#print axioms NumericalVarietyData.degree_discriminant
#print axioms NumericalVarietyData.chComp_eq_zero_of_lt
#print axioms NumericalVarietyData.toddComp_eq_zero_of_lt
#print axioms Surface.chi_eq
#print axioms Surface.discriminant_mem_piece_two
#print axioms Surface.degree_discriminant

-- Layer A: the threefold and fourfold specialisations. These are the check that
-- degree_ch_mul_todd is dimension-general, so they must not acquire axioms that the
-- n = 2 case does not have.
#print axioms Threefold.chi_eq
#print axioms Threefold.chiStructureSheaf
#print axioms CalabiYauThreefold.IsCalabiYau
#print axioms CalabiYauThreefold.IsCalabiYau.toddComp_one
#print axioms CalabiYauThreefold.IsCalabiYau.degree_toddComp_three
#print axioms CalabiYauThreefold.chi_eq
#print axioms CalabiYauThreefold.chi_eq_of_chComp_eq
#print axioms Fourfold.chi_eq
#print axioms Fourfold.chiStructureSheaf
#print axioms CalabiYauFourfold.IsCalabiYau
#print axioms CalabiYauFourfold.IsCalabiYau.toddComp_one
#print axioms CalabiYauFourfold.IsCalabiYau.toddComp_three
#print axioms CalabiYauFourfold.IsCalabiYau.degree_toddComp_four
#print axioms CalabiYauFourfold.chi_eq

-- Layer A: the dual involution and the Euler pairing. chi2 is what Bridgeland stability
-- is defined against, so a sorry here would contaminate the downstream repos.
#print axioms NumericalRingDualData
#print axioms NumericalVarietyData.dual_ch
#print axioms NumericalVarietyData.chDual_add
#print axioms NumericalVarietyData.chi₂_eq_sum
#print axioms NumericalVarietyData.chi₂_eq_degree_dual_ch
#print axioms NumericalVarietyData.chi₂_add_left
#print axioms NumericalVarietyData.chi₂_add_right
#print axioms Surface.chi₂_eq
#print axioms Surface.chi₂_eq_chi_of_isStructureSheafLike
#print axioms Surface.chi₂_sub_chi₂_swap
#print axioms Surface.chi₂_symm_of_toddComp_one_eq_zero
#print axioms K3.mukaiPairing_self
#print axioms K3.chi₂_eq_neg_mukaiPairing
#print axioms K3.chi₂_self

-- Layer A: the numerical Grothendieck quotient and lattice. The pairing is descended only
-- under explicit symmetry, and the finite/free conclusion must retain its finiteness and
-- torsion-freeness hypotheses.
#print axioms ZLattice
#print axioms ZLattice.ofFiniteTorsionFree
#print axioms NumericalVarietyData.eulerPairingRow
#print axioms NumericalVarietyData.eulerPairing
#print axioms NumericalVarietyData.eulerPairingFlip
#print axioms NumericalVarietyData.eulerPairing_apply
#print axioms NumericalVarietyData.eulerPairingFlip_apply
#print axioms NumericalVarietyData.leftRadical
#print axioms NumericalVarietyData.rightRadical
#print axioms NumericalVarietyData.mem_leftRadical_iff
#print axioms NumericalVarietyData.mem_rightRadical_iff
#print axioms NumericalVarietyData.IsEulerPairingSymmetric
#print axioms NumericalVarietyData.leftRadical_eq_rightRadical
#print axioms NumericalVarietyData.NumericalQuotient
#print axioms NumericalVarietyData.eulerPairingDescendRight
#print axioms NumericalVarietyData.eulerPairingDescendRight_mk
#print axioms NumericalVarietyData.eulerPairingToQuotient
#print axioms NumericalVarietyData.eulerPairingToQuotient_mk
#print axioms NumericalVarietyData.numericalPairing
#print axioms NumericalVarietyData.numericalPairing_mk
#print axioms NumericalVarietyData.numericalPairing_symm
#print axioms NumericalVarietyData.numericalPairing_left_nondegenerate
#print axioms NumericalVarietyData.numericalPairing_right_nondegenerate
#print axioms NumericalVarietyData.numericalPairing_ker_eq_bot
#print axioms NumericalVarietyData.numericalZLattice
#print axioms K3.isEulerPairingSymmetric
#print axioms K3.leftRadical_eq_rightRadical
#print axioms K3.numericalPairing_mk_eq_neg_mukaiPairing

-- Layer A: the K3 specialisation.
#print axioms K3.chi_eq
#print axioms K3.chi_eq_rank_add_mukaiS
#print axioms K3.mukaiSelfPairing_eq
#print axioms K3.mukaiSelfPairing_of_rank_eq_zero

-- Layer A: the consistency witness. If this depended on `sorryAx` the whole
-- interface would be unmodelled.
#print axioms Examples.pointNumericalRing
#print axioms Examples.pointNumericalVariety
#print axioms Examples.pointNumericalVariety_satisfiesHRR
#print axioms Examples.pointPiece_isInternal

-- Layer A: the K3 model. If these carried a sorry the K3 theorems would still be
-- conditional, which is exactly what this model exists to stop being true.
#print axioms Examples.SurfaceRing
#print axioms Examples.H_pow_three
#print axioms Examples.surfaceNumericalRing
#print axioms Examples.surfaceDegree_normalForm
#print axioms Examples.surfaceDegree_ch_mul_todd
#print axioms Examples.k3NumericalVariety
#print axioms Examples.k3NumericalVariety_satisfiesHRR
#print axioms Examples.k3_isK3

-- Layer A: the projective plane. Its td1 is nonzero, so it is the model that can
-- detect an error in the c1.td1 term of Surface.chi_eq.
#print axioms Examples.p2NumericalVariety
#print axioms Examples.p2NumericalVariety_satisfiesHRR
#print axioms Examples.p2_chi_structureSheaf
#print axioms Examples.p2Chi_lineBundle
#print axioms Examples.p2ChCoeff_lineBundle

-- Layer A: the abelian surface. Both Todd components above td0 vanish, so it is the
-- surface model on which chi sees neither the rank nor c1.
#print axioms Examples.abelianTodd
#print axioms Examples.abelianTodd_mem
#print axioms Examples.abelianTodd_sum
#print axioms Examples.abelianNumericalVariety
#print axioms Examples.abelianNumericalVariety_satisfiesHRR
#print axioms Examples.k3AndAbelianPresentations
#print axioms Examples.abelianToddComp_one
#print axioms Examples.abelianChiStructureSheaf
#print axioms Examples.abelianChi_eq_of_chComp_two_eq

-- Layer A: the dimension-general Picard-rank-one construction. Every threefold and
-- fourfold model below is built from it, so a sorry here would unmodel dimensions three
-- and four at once.
#print axioms Examples.rankOneRel
#print axioms Examples.rankOneRel_ne_zero
#print axioms Examples.RankOneRing
#print axioms Examples.rankOnePB
#print axioms Examples.rankOnePB_dim
#print axioms Examples.rankOneH
#print axioms Examples.rankOnePB_gen
#print axioms Examples.rankOnePB_basis_apply
#print axioms Examples.rankOneH_pow_succ_eq_zero
#print axioms Examples.rankOneH_pow_eq_zero
#print axioms Examples.rankOneW
#print axioms Examples.rankOneW_le
#print axioms Examples.lt_rankOnePB_dim
#print axioms Examples.rankOneIdx
#print axioms Examples.rankOneIdx.congr_simp
#print axioms Examples.rankOnePB_basis_eq_pow
#print axioms Examples.rankOneH_pow_mem_piece
#print axioms Examples.rankOne_one_mem
#print axioms Examples.rankOne_mul_mem
#print axioms Examples.rankOne_algebraMap_mul_mem
#print axioms Examples.rankOneDegree
#print axioms Examples.rankOneDegree_basis_of_ne
#print axioms Examples.rankOneDegree_basis_top
#print axioms Examples.rankOneDegree_pow
#print axioms Examples.rankOneDegree_algebraMap_mul_pow
#print axioms Examples.rankOneDegree_sum_mul_sum
#print axioms Examples.rankOneNumericalRing
#print axioms Examples.rankOneCh
#print axioms Examples.rankOneCh_mem
#print axioms Examples.rankOneCh_sum
#print axioms Examples.rankOneTodd
#print axioms Examples.rankOneTodd_mem
#print axioms Examples.rankOneTodd_sum
#print axioms Examples.rankOneNumericalVariety
#print axioms Examples.rankOneNumericalVariety_satisfiesHRR

-- Layer A: linear-section coordinates in dimensions three and four. These are what make
-- chi integral on the lattice, so an axiom here would undermine every Euler
-- characteristic the threefold and fourfold models report.
#print axioms Examples.ThreefoldNum
#print axioms Examples.threefoldChCoeff
#print axioms Examples.threefoldChCoeff_add
#print axioms Examples.threefoldRank
#print axioms Examples.threefoldChCoeff_zero
#print axioms Examples.threefoldChi_sum
#print axioms Examples.FourfoldNum
#print axioms Examples.fourfoldChCoeff
#print axioms Examples.fourfoldChCoeff_add
#print axioms Examples.fourfoldRank
#print axioms Examples.fourfoldChCoeff_zero
#print axioms Examples.fourfoldChi_sum

-- Layer A: the threefold models. p3 has no vanishing Todd component and so is the model
-- that can detect an error anywhere in Threefold.chi_eq; the quintic is what makes
-- CalabiYauThreefold.IsCalabiYau inhabited.
#print axioms Examples.p3Todd
#print axioms Examples.p3Chi
#print axioms Examples.p3NumericalVariety
#print axioms Examples.p3NumericalVariety_satisfiesHRR
#print axioms Examples.p3ChiStructureSheaf
#print axioms Examples.p3Chi_lineBundle
#print axioms Examples.p3ChCoeff_lineBundle_two
#print axioms Examples.p3ChCoeff_lineBundle_three
#print axioms Examples.quinticTodd
#print axioms Examples.quinticChi
#print axioms Examples.quinticNumericalVariety
#print axioms Examples.quinticNumericalVariety_satisfiesHRR
#print axioms Examples.quintic_isCalabiYau
#print axioms Examples.quinticChi_structureSheaf
#print axioms Examples.quinticChi_hyperplaneSection
#print axioms Examples.quinticChi_curveSection
#print axioms Examples.quinticChi_point
#print axioms Examples.quinticChi_lineBundle

-- Layer A: the fourfold models. Same division of labour one dimension up, and the sextic
-- is what makes CalabiYauFourfold.IsCalabiYau inhabited.
#print axioms Examples.p4Todd
#print axioms Examples.p4Chi
#print axioms Examples.p4NumericalVariety
#print axioms Examples.p4NumericalVariety_satisfiesHRR
#print axioms Examples.p4ChiStructureSheaf
#print axioms Examples.p4Chi_lineBundle
#print axioms Examples.p4ChCoeff_lineBundle_four
#print axioms Examples.sexticTodd
#print axioms Examples.sexticChi
#print axioms Examples.sexticNumericalVariety
#print axioms Examples.sexticNumericalVariety_satisfiesHRR
#print axioms Examples.sextic_isCalabiYau
#print axioms Examples.sexticChi_structureSheaf
#print axioms Examples.sexticChi_hyperplaneSection
#print axioms Examples.sexticChi_surfaceSection
#print axioms Examples.sexticChi_curveSection
#print axioms Examples.sexticChi_point
#print axioms Examples.sexticChi_lineBundle

-- Layer B: the Mathlib gap that blocks the local-to-global criterion for coherence.
#print axioms SheafOfModules.Presentation.isFinite_of_isIso
#print axioms SheafOfModules.Presentation.isFinite_map
#print axioms SheafOfModules.Presentation.isFinitePresentation_quasicoherentData
#print axioms SheafOfModules.IsFinitePresentation.of_presentation

-- Layer B stage 1.
#print axioms Scheme.Modules.IsCoherent
#print axioms Coh
#print axioms Coh.ι
#print axioms SheafOfModules.QuasicoherentData.ofIso
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_ofIso
#print axioms SheafOfModules.IsFinitePresentation.of_iso
#print axioms SheafOfModules.isFinitePresentation_isClosedUnderIsomorphisms
#print axioms Scheme.coherent_isClosedUnderIsomorphisms
#print axioms SheafOfModules.QuasicoherentData.presentationOver
#print axioms SheafOfModules.QuasicoherentData.presentationOver_generators_I
#print axioms SheafOfModules.QuasicoherentData.presentationOver_relations_I
#print axioms SheafOfModules.QuasicoherentData.over
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_over
#print axioms SheafOfModules.IsFinitePresentation.over
#print axioms SheafOfModules.IsFinitePresentation.of_coversTop
#print axioms TopCat.Opens.grothendieckTopology_coversTop
#print axioms basicOpen_coversTop_of_span_eq_top
#print axioms Scheme.Hom.opensRangeEquivalence
#print axioms Scheme.Hom.opensRangeModulesEquivalence
#print axioms Scheme.Hom.restrictFunctorIsoOver
#print axioms Scheme.Hom.isFinitePresentation_restrict

-- Layer B stage 1: the reverse transport, making finite presentation invariant under the
-- open-immersion/slice equivalence rather than merely carried one way.
#print axioms Scheme.Hom.presentationOverOfEq
#print axioms Scheme.Hom.presentationOverOfEq_isFinite
#print axioms Scheme.Hom.overQuasicoherentData
#print axioms Scheme.Hom.overQuasicoherentData_isFinitePresentation
#print axioms Scheme.Hom.isFinitePresentation_over_of_restrict
#print axioms Scheme.Hom.isFinitePresentation_over_iff_restrict
#print axioms Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion
#print axioms Scheme.Modules.IsCoherent.of_affineOpenCover
#print axioms Scheme.Modules.isCoherent_iff_of_affineOpenCover
#print axioms Scheme.Modules.IsCoherent.restrict_affineOpenCover

-- Layer B stage 1: the scheme-level affine-local criterion, stated without `Over`.
#print axioms Scheme.Modules.isCoherent_iff_restrict_affineOpenCover
-- Layer B stage 1: finite limits on the site, which is what lets a global presentation
-- be turned into finite presentation on a scheme at all. One file, replacing the two
-- independent workarounds that preceded it.
#print axioms TopologicalSpace.Opens.hasBinaryProducts
#print axioms TopologicalSpace.Opens.hasFiniteLimits

-- Layer B stage 1: the affine comparison, forward direction.
#print axioms isFinitePresentation_tilde
#print axioms isCoherent_tilde
#print axioms isCoherent_tilde_of_finite
-- Layer B stage 1: the geometric half of the affine comparison theorem. The first two
-- are general sheaf theory; the rest reduce `IsIso fromTildeΓ` to a statement about
-- localisation of modules.
#print axioms TopCat.Presheaf.stalkFunctor_map_surjective_of_isBasis
#print axioms TopCat.Sheaf.isIso_of_isIso_app_of_isBasis
#print axioms Scheme.Modules.basicOpenRestriction
#print axioms Scheme.Modules.toOpen_comp_fromTildeΓ_app
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde
#print axioms isIso_fromTildeΓ_app_basicOpen
#print axioms isIso_fromTildeΓ_of_isLocalizedModule

-- Layer B stage 1: the converse, making the affine comparison a characterisation.
#print axioms Scheme.Modules.basicOpenRestriction_naturality
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation
#print axioms Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule

-- Layer B stage 1: a quasi-coherent sheaf on an affine scheme has presentations on a
-- basic-open cover. The first declaration is the reusable iterated-slice restriction step.
#print axioms SheafOfModules.Presentation.over
#print axioms Scheme.Modules.exists_basicOpen_presentation_cover
#print axioms Scheme.Hom.opensRangeModulesEquivalenceInverseUnitIso
#print axioms Scheme.Hom.restrictPresentation

-- Layer B stage 1: Mathlib v4.32 provides Hartshorne II.5.1 upstream; retain the
-- compatibility exports consumed by the affine comparison layer.
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent
#print axioms Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent

-- Layer B stage 1: the finiteness corollaries of the affine comparison. Finite local
-- generators and presentations are transported to affine basic opens, where the comparison
-- turns them into finite modules; localisation patching then returns to `Spec R`.
#print axioms SheafOfModules.GeneratingSections.map
#print axioms SheafOfModules.GeneratingSections.over
#print axioms SheafOfModules.GeneratingSections.isFiniteType_over
#print axioms Scheme.Modules.basicOpenSpecMap
#print axioms Scheme.Modules.basicOpenSpecMap_opensRange
#print axioms Scheme.Modules.restrictBasicOpenTopLinearEquiv
#print axioms Scheme.Modules.GeneratingSections.restrictBasicOpen
#print axioms Scheme.Modules.GeneratingSections.isFiniteType_restrictBasicOpen
#print axioms Scheme.Modules.QuasicoherentData.restrictBasicOpen
#print axioms Scheme.Modules.exists_basicOpen_presentation_cover_of_quasicoherentData
#print axioms Scheme.Modules.isIso_fromTildeΓ_of_quasicoherentData
#print axioms Scheme.Modules.isIso_fromTildeΓ_restrictBasicOpen_of_quasicoherentData
#print axioms Scheme.Modules.moduleFinite_globalSections_of_generatingSections
#print axioms Scheme.Modules.moduleFinite_globalSections_of_presentation

-- Layer B stage 1, the CONVERSE direction (#586). moduleFinite_globalSections_of_generatingSections
-- above takes a finite generating family to a finite module of global sections; these three take a
-- finite module of global sections back to a finite free EPIMORPHISM, which is the direction
-- Serre's global generation needs. Paired with GeneratingSections.ofFreeEpi the loop closes.
--
-- The mathematics is short: tilde is a left adjoint (tilde.adjunction) so it preserves colimits and
-- hence epimorphisms, Finsupp.linearCombination is surjective exactly when the span is everything,
-- and the two outer maps are isomorphisms. The cost was entirely elaboration, and both hazards are
-- recorded on epi_freeEpiOfSpan because each was diagnosed wrongly the first time:
--
--   * a PreservesEpimorphisms instance left in context makes later instance searches diverge, and
--     the heartbeat timeout is REPORTED as a plain "failed to synthesize" -- which reads like a
--     missing instance, and was misread here as a structural defect in the X.Modules wrapper. It is
--     not: IsIso -> Epi synthesizes fine in that wrapper, checked by compiling both forms.
--   * backward.isDefEq.respectTransparency false is required, the same trap #585 recorded: without
--     it the goal is "not type-correct under the instances transparency level" and every later rw
--     silently fails to match.
#print axioms Scheme.Modules.freeEpiOfSpan
#print axioms Scheme.Modules.epi_freeEpiOfSpan
#print axioms Scheme.Modules.exists_finite_free_epi_of_moduleFinite
#print axioms Scheme.Modules.exists_basicOpen_finiteGenerating_cover
#print axioms Scheme.Modules.moduleFinite_globalSections_of_isFiniteType
#print axioms Scheme.Modules.moduleFinite_globalSections
#print axioms moduleFinite_globalSections_of_isFiniteType
#print axioms moduleFinitePresentation_globalSections_of_isCoherent

-- Layer B stage 1: the affine equivalence. The two objectwise finiteness directions
-- restrict Mathlib's tilde-global-sections adjunction to the corresponding full
-- subcategories; its unit and counit are then pointwise isomorphisms.
#print axioms Coh.affineGlobalSections
#print axioms FGModuleCat.affineTilde
#print axioms Coh.affineAdjunction
#print axioms Coh.affineEquivalence
#print axioms Coh.affineEquivalence_functor
#print axioms Coh.affineEquivalence_inverse

-- Layer B stage 1: kernels and cokernels. Restriction along open immersions is left exact,
-- localization commutes with kernels, and the affine comparison transports both ambient
-- (co)kernels to finite modules. The final instances create (co)kernels in `Coh X`.
#print axioms AlgebraicGeometry.modulesSpecToSheaf_preservesFiniteLimits
#print axioms Scheme.Modules.restrictFunctor_preservesFiniteLimits
#print axioms LinearMap.kerMap
#print axioms IsLocalizedModule.kerMap
#print axioms IsLocalizedModule.kernelMap
#print axioms IsLocalizedModule.kernelNatTrans
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_kernel
#print axioms Scheme.Modules.isCoherent_kernel_affine
#print axioms Scheme.Modules.isCoherent_cokernel_affine
#print axioms Scheme.Modules.restrictKernelIso
#print axioms Scheme.Modules.restrictCokernelIso
#print axioms Scheme.Modules.isCoherent_kernel
#print axioms Scheme.Modules.isCoherent_cokernel
#print axioms Scheme.coherent_isClosedUnderKernels
#print axioms Scheme.coherent_isClosedUnderCokernels

-- Layer B stage 1, quasi-coherent half: the same closure with every noetherian
-- hypothesis deleted. This is what makes the inclusion of quasi-coherent sheaves
-- into all module sheaves exact, and it is the first half of the weak Serre
-- property `Dqc(X)` needs for its triangulated structure (#720).
#print axioms AlgebraicGeometry.Scheme.Hom.isQuasicoherent_over_of_restrict
#print axioms AlgebraicGeometry.Scheme.Hom.isQuasicoherent_restrict
#print axioms AlgebraicGeometry.Scheme.Hom.isQuasicoherent_over_iff_restrict
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affineOpenCover
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_restrict_affineOpenCover
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel_affine
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel_affine
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel
#print axioms AlgebraicGeometry.quasicoherent_isClosedUnderKernels
#print axioms AlgebraicGeometry.quasicoherent_isClosedUnderCokernels

-- Layer B stage 1: extensions. Local lifts of finite generators and relations produce a
-- finite horseshoe presentation of the middle term, without a noetherian hypothesis.
#print axioms SheafOfModules.IsFinitePresentation.middle_of_shortExact
#print axioms SheafOfModules.isFinitePresentation_isClosedUnderExtensions
#print axioms Scheme.coherent_isClosedUnderExtensions

-- Layer B stage 1: abelianity and the exact inclusion. The full subcategory contains zero
-- and finite products; kernel/cokernel closure then supplies the abelian structure and makes
-- the inclusion preserve all finite limits and colimits.
#print axioms SheafOfModules.isFinitePresentation_containsZero
#print axioms Scheme.coherent_containsZero
#print axioms Scheme.coherent_isClosedUnderBinaryProducts
#print axioms Scheme.coherent_isClosedUnderFiniteProducts
#print axioms Coh.preadditive
#print axioms Coh.abelian
#print axioms Coh.ι_preservesZeroMorphisms
#print axioms Coh.ι_additive
#print axioms Coh.ι_preservesFiniteLimits
#print axioms Coh.ι_preservesFiniteColimits
#print axioms Coh.exactInclusion
#print axioms Coh.shortExact_map_ι

-- Layer B stage 2: Cartier divisors as locally representable sections of
-- `K(X)ˣ / 𝒪_{X,x}ˣ`, principal equivalence, codimension-one coefficients,
-- and pullback from explicit compatible function-field data.
#print axioms Scheme.localCartierClass_eq_iff
#print axioms Scheme.isCartier_zero
#print axioms Scheme.IsCartier.add
#print axioms Scheme.IsCartier.neg
#print axioms Scheme.CartierDivisor.ext
#print axioms Scheme.CartierDivisor.zero_apply
#print axioms Scheme.CartierDivisor.add_apply
#print axioms Scheme.CartierDivisor.neg_apply
#print axioms Scheme.CartierDivisor.exists_localEquation
#print axioms Scheme.CartierDivisor.toClass_eq_iff
#print axioms Scheme.CartierDivisor.toClass_eq_iff_exists
#print axioms Scheme.CartierDivisor.toClass_principal
#print axioms Scheme.CartierDivisor.ordUnitHom_eq_zero_of_mem_localUnits
#print axioms Scheme.CartierDivisor.localOrder_localCartierClass
#print axioms Scheme.CartierDivisor.coefficient_add
#print axioms Scheme.CartierDivisor.coefficient_principal
#print axioms Scheme.CartierDivisor.coefficient_eq_zero_of_coheight_ne_one
#print axioms Scheme.CartierPullbackData.localMap_localCartierClass
#print axioms Scheme.CartierPullbackData.pullback_principal

-- Layer B stage 3: exactness of the bridge from sheaves of modules to abelian sheaves.
-- This is what lets a short exact sequence in `X.Modules` reach `Ext`, and hence the
-- cohomology long exact sequence. The first two are general category theory and have
-- nothing to do with sheaves.
#print axioms CategoryTheory.Adjunction.preservesColimit_comp_left
#print axioms CategoryTheory.Adjunction.preservesColimitsOfShape_of_comp_left
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf'
#print axioms SheafOfModules.preservesEpimorphisms_toSheaf
#print axioms SheafOfModules.shortExact_map_toSheaf
#print axioms SheafOfModules.epi_of_isLocallySurjective
#print axioms SheafOfModules.reflectsEpimorphisms_toSheaf

-- Layer B stage 3: the link between cosimplicial (Cech) and simplicial (extra degeneracy)
-- machinery. Not the whole of the Cech vanishing chain -- see the module docstring of
-- DerivedAlgGeo/AlgebraicGeometry/Cohomology/Simplicial/ExtraCodegeneracy.lean
-- for what is still missing.
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso_hom_f
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso_inv_f
#print axioms AlgebraicTopology.exactAt_succ_of_extraDegeneracy
#print axioms AlgebraicTopology.exactAt_succ_of_extraDegeneracy_map

-- Layer B stage 3: Mathlib's construction assembling a spectral object into a spectral
-- sequence, including its page-homology and first-page comparison isomorphisms.
#print axioms CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isColimitCc
#print axioms CategoryTheory.Abelian.SpectralObject.SpectralSequence.homologyData
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequence
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIso
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequence_page_d_eq
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequence_first_page_d_eq

-- Layer B stage 3: filtered complexes and column-filtered total complexes now feed the
-- spectral-object constructor above.  The last declaration is the packaged E₂ sequence.
#print axioms CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor
#print axioms HomotopyCategory.filteredComplexSpectralObject
#print axioms CategoryTheory.Abelian.SpectralObject.coreE₂CohomologicalInt
#print axioms CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt
#print axioms HomologicalComplex.stupidTruncGEι
#print axioms HomologicalComplex.stupidTruncGEMap
#print axioms HomologicalComplex₂.columnFiltrationBicomplex
#print axioms HomologicalComplex₂.columnFilteredTotalComplex
#print axioms HomologicalComplex₂.columnFilteredTotalι
#print axioms HomologicalComplex₂.columnFilteredTotal_map_comp_ι
#print axioms HomologicalComplex₂.columnFilteredTotalιNat
#print axioms HomologicalComplex₂.columnFilteredTotalSpectralObject
#print axioms HomologicalComplex₂.columnFilteredTotalSpectralSequence

-- Layer B stage 3: consecutive column truncations form a degreewise split short exact
-- sequence. Its totalized mapping cone is quasi-isomorphic to the newly added shifted column,
-- which identifies an adjacent filtration layer with fixed-column homology.
#print axioms HomologicalComplex₂.truncatedBicomplex
#print axioms HomologicalComplex₂.singleColumnBicomplex
#print axioms HomologicalComplex₂.singleColumnXIso
#print axioms HomologicalComplex₂.singleColumnXIso_hom_inv_f
#print axioms HomologicalComplex₂.singleColumnXIso_inv_hom_f
#print axioms HomologicalComplex₂.adjacentColumnInclusion
#print axioms HomologicalComplex₂.adjacentColumnProjection
#print axioms HomologicalComplex₂.adjacentColumnBicomplexShortComplex
#print axioms HomologicalComplex₂.totalFunctor_additive
#print axioms HomologicalComplex₂.adjacentColumnTotalShortComplex
#print axioms HomologicalComplex₂.stupidTruncGEXIso
#print axioms HomologicalComplex₂.stupidTruncXIso_eq_stupidTruncGEXIso
#print axioms HomologicalComplex₂.stupidTruncGEXIso_inv_hom_f
#print axioms HomologicalComplex₂.stupidTruncGEXIso_hom_inv_f
#print axioms HomologicalComplex₂.complexIso_inv_hom_f
#print axioms HomologicalComplex₂.complexIso_hom_inv_f
#print axioms HomologicalComplex₂.adjacentColumnTotalRetraction
#print axioms HomologicalComplex₂.adjacentColumnTotalSection
#print axioms HomologicalComplex₂.adjacentColumnTotalDegreewiseSplitting
#print axioms HomologicalComplex₂.singleZeroBicomplex
#print axioms HomologicalComplex₂.singleZeroXIso
#print axioms HomologicalComplex₂.singleZeroTotalXIso
#print axioms HomologicalComplex₂.singleZeroTotalIso
#print axioms HomologicalComplex₂.singleColumnShiftIso
#print axioms HomologicalComplex₂.singleColumnTotalIso
#print axioms HomologicalComplex₂.adjacentColumnTotalShortExact
#print axioms HomologicalComplex₂.adjacentColumnConeToShift
#print axioms HomologicalComplex₂.adjacentColumnConeToShift_quasiIso
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerComplex
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerComplex_eq
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerConeToShift
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerConeToShift_quasiIso
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerHomologyIso
#print axioms HomologicalComplex₂.columnFilteredStageIso
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerIso
#print axioms HomologicalComplex₂.columnFilteredInitialPageColumnHomologyIso
#print axioms HomologicalComplex₂.columnFilteredFirstPage_d_eq
#print axioms HomologicalComplex₂.columnFilteredInitialPage_d_eq_horizontalHomologyMap

-- Layer B stage 3: an explicit injective resolution now produces the augmented Cech
-- bicomplex, its total complex, the column-filtered spectral sequence, and the formal
-- initial-page identification. Over a general site the pin still has no EnoughInjectives
-- instance for sheaves, and SpectralSequence still has no convergence/abutment field;
-- neither gap is hidden by an axiom.
#print axioms CategoryTheory.Limits.FormalCoproduct.evalOp_additive
#print axioms CategoryTheory.Sheaf.cechComplexFunctor_additive
#print axioms CategoryTheory.Sheaf.cechCochainFunctorInt
#print axioms CategoryTheory.Sheaf.cechResolutionBicomplexUnflipped
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplex
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexXXIso
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentation
#print axioms CategoryTheory.Sheaf.cechInjectiveTotalComplex
#print axioms CategoryTheory.Sheaf.cechInjectiveFilteredToTotal
#print axioms CategoryTheory.Sheaf.cechInjectiveFilteredToTotalNat
#print axioms CategoryTheory.Sheaf.cechInjectiveSpectralObject
#print axioms CategoryTheory.Sheaf.cechInjectiveSpectralSequence
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageXIso
#print axioms CategoryTheory.Sheaf.cechInjectiveAdjacentLayerComplex
#print axioms CategoryTheory.Sheaf.cechInjectiveAdjacentLayerHomologyIso
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageColumnHomologyIso

-- Layer B stage 3: over a SMALL site the resolution hypothesis is redundant. Mathlib's
-- Grothendieck-abelian chain supplies enough injectives, so the Cech spectral sequence and
-- its acyclicity consequences are restated with no InjectiveResolution argument. These are
-- inferInstance and wrapper terms, not new instances or axioms.
#print axioms CategoryTheory.Sheaf.enoughInjectives_of_small
#print axioms CategoryTheory.Sheaf.hasInjectiveResolutions_of_small
#print axioms CategoryTheory.Sheaf.enoughInjectives_opens
#print axioms CategoryTheory.Sheaf.canonicalInjectiveResolution
#print axioms CategoryTheory.Sheaf.canonicalSectionsCohomologyAddEquivHPrime
#print axioms CategoryTheory.Sheaf.canonicalCechBicomplex
#print axioms CategoryTheory.Sheaf.canonicalCechSpectralSequence
#print axioms CategoryTheory.Sheaf.canonicalCechInitialPageColumnHomologyIso
#print axioms CategoryTheory.Sheaf.isZero_canonicalCechInitialPage_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.subsingleton_canonicalCechInitialPage_of_isCechAcyclicFor

-- Layer B stage 3: the initial page's degree-zero row, including its horizontal
-- differential, is the ordinary Cech complex. Consequently the following page is
-- ordinary Cech cohomology along that row.
#print axioms CategoryTheory.Sheaf.cechInjectiveColumnAugmentationHomologyIso
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageZeroRowXIso
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageZeroRow_d
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageZeroRowIso
#print axioms CategoryTheory.Sheaf.cechInjectiveFollowingPageCechCohomologyIso

-- Layer B stage 3: first-quadrant total comparison and the Cech augmentation into the total
-- complex of an explicit injective resolution. The general engine uses finite column tails;
-- local Cech acyclicity supplies the columnwise quasi-isomorphisms.
#print axioms CochainComplex.mappingCone.quasiIso_compMap
#print axioms CochainComplex.mappingCone.quasiIsoAt_inr_of_isZero_X
#print axioms HomologicalComplex.HomologySequence.quasiIso_τ₂
#print axioms HomologicalComplex₂.IsVerticallyConnective
#print axioms HomologicalComplex₂.IsHorizontallyConnective
#print axioms HomologicalComplex₂.totalMap_quasiIso
#print axioms CategoryTheory.Sheaf.cechInjectiveColumnAugmentation_quasiIso
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentationSource_verticallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentationSource_horizontallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplex_verticallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplex_horizontallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentation_total_quasiIso
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentationSourceTotalIso
#print axioms CategoryTheory.Sheaf.cechToInjectiveTotalMap
#print axioms CategoryTheory.Sheaf.cechToInjectiveTotalMap_quasiIso
#print axioms CategoryTheory.Sheaf.cechCohomologyIsoInjectiveTotalHomology

-- Layer B stage 3: the global-sections edge of the Cech bicomplex. Sheaf gluing proves
-- exactness at degree zero, injectivity proves positive row exactness, and the resulting
-- rowwise quasi-isomorphism passes to first-quadrant totals. Together with local Cech
-- acyclicity this gives the full Cech-to-derived comparison for open covers.
#print axioms CategoryTheory.Sheaf.globalSectionsToCechZero_exact
#print axioms CategoryTheory.Sheaf.globalSectionsToCechZero_mono
#print axioms CategoryTheory.Sheaf.globalSectionsToCechRowMap_quasiIso
#print axioms CategoryTheory.Sheaf.globalSectionsToCechBicomplexMap
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsToCechTotalMap
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsToCechTotalMap_quasiIso
#print axioms CategoryTheory.Sheaf.cechCochainFunctorIntHomologyIso
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsComplexUnliftedIso
#print axioms CategoryTheory.Sheaf.isCechAcyclicCover_cechComputesDerivedCohomology

-- On the small site Opens X the comparison needs no witness arguments at all: the
-- injective resolution and the HasExt instance both come from Mathlib's Grothendieck
-- abelian chain. The witness-carrying form above is retained for a general site.
#print axioms CategoryTheory.Sheaf.isCechAcyclicCover_cechComputesDerivedCohomology_opens
#print axioms CategoryTheory.Sheaf.isCechAcyclicCover_cechComputesDerivedCohomologyAt_opens

#print axioms AlgebraicGeometry.Cohomology.AffineTildeCechDerivedComparisonAt
#print axioms AlgebraicGeometry.Cohomology.AffineTildeCechDerivedComparison
#print axioms AlgebraicGeometry.Cohomology.affineTildeCechDerivedComparisonAt_of_pos
-- The denominator-clearing step behind "a section over a basic open extends after multiplying by
-- a power of the defining element" (#585). It was a private lemma inside the Cech affine file,
-- where it was used once; it is pure commutative algebra with no Cech content, so it now lives in
-- DerivedAlgGeo/Algebra/Module/LocalizedRadical.lean and the Cech file imports it. Nothing about
-- the proof changed in the move. Not in Mathlib at the pin; upstream-candidate.
#print axioms Submodule.exists_pow_smul_mem_of_isLocalized_radical
#print axioms AlgebraicGeometry.Cohomology.tilde_H_subsingleton_of_comparisonAt
#print axioms AlgebraicGeometry.Cohomology.tilde_H_subsingleton_of_comparison
#print axioms AlgebraicGeometry.Cohomology.H_subsingleton_of_iso_tilde_of_comparisonAt
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_iso_tilde_of_comparisonAt
#print axioms AlgebraicGeometry.Cohomology.tilde_H_subsingleton
#print axioms AlgebraicGeometry.Cohomology.H_subsingleton_of_iso_tilde
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_iso_tilde
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_isQuasicoherent

-- Layer B stage 3: the non-circular compact-basis comparison (Stacks, Tag 01EW).
-- Compact refinements and Cech correction make the acyclicity condition stable under
-- injective quotients, so dimension shifting kills positive derived cohomology.
#print axioms CategoryTheory.Sheaf.CompactOpenBasis
#print axioms CategoryTheory.Sheaf.CompactOpenBasis.ofIsBasis
#print axioms CategoryTheory.Sheaf.CompactOpenBasis.exists_finite_refinement
#print axioms CategoryTheory.Sheaf.IsCechAcyclicOnCompactBasis
#print axioms CategoryTheory.Sheaf.isCechAcyclicOnCompactBasis_of_injective
#print axioms CategoryTheory.Sheaf.epi_app_of_isCechAcyclicOnCompactBasis
#print axioms CategoryTheory.Sheaf.isCechAcyclicOnCompactBasis_quotient
#print axioms CategoryTheory.Sheaf.HPrime_subsingleton_of_isCechAcyclicOnCompactBasis
#print axioms CategoryTheory.Sheaf.H_subsingleton_of_isCechAcyclicOnCompactBasis

-- Layer B stage 3: positive-degree exactness of the explicit Cech complex for a module
-- sheaf on a finite distinguished-open cover of an affine scheme. This is the affine Cech
-- vanishing theorem, not a comparison with derived-functor sheaf cohomology.
#print axioms CategoryTheory.Sheaf.cechComplex_exactAt_succ_of_injective'
#print axioms CategoryTheory.cechComplex_exactAt_succ_of_isTerminal
#print axioms PrimeSpectrum.basicOpen_prod_eq_pi
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_succ
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_succ_of_eq_iSup
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_of_pos

-- Layer B stage 3: bridge the relative distinguished-open calculation through the
-- underlying additive-group functor and specialize the compact-basis criterion to affine
-- schemes.
#print axioms CategoryTheory.evalOpForget₂AddCommGrpIso
#print axioms CategoryTheory.map_alternatingCofaceMapComplex
#print axioms CategoryTheory.cechComplexForget₂AddCommGrpIso
#print axioms CategoryTheory.cechComplex_exactAt_forget₂AddCommGrp_of_exactAt
#print axioms AlgebraicGeometry.Cohomology.affineBasicOpenBasis
#print axioms AlgebraicGeometry.Cohomology.top_mem_affineBasicOpenBasis
#print axioms AlgebraicGeometry.Cohomology.underlyingTilde_isCechAcyclicOnCompactBasis

-- Layer B stage 3: finite-cover cohomological boundedness. Local compact-basis dimension
-- shifting proves ambient `H'`-vanishing on affine opens; affine diagonal makes every finite
-- intersection affine; Mayer--Vietoris then gives a numerical bound for actual `Sheaf.H`.
#print axioms CategoryTheory.Sheaf.opensUnion
#print axioms CategoryTheory.Sheaf.IntersectionAcyclic
#print axioms CategoryTheory.Sheaf.HPrime_subsingleton_opensUnion_of_intersectionAcyclic
#print axioms AlgebraicGeometry.Cohomology.affineBasicOpenBasisAt
#print axioms AlgebraicGeometry.Cohomology.mem_affineBasicOpenBasisAt
#print axioms AlgebraicGeometry.Cohomology.modulesSpec_isCechAcyclicOnCompactBasis
#print axioms AlgebraicGeometry.Cohomology.modules_isCechAcyclicOn_affineBasicOpenBasisAt
#print axioms AlgebraicGeometry.Cohomology.modules_HPrime_subsingleton_of_isAffineOpen
#print axioms AlgebraicGeometry.Cohomology.modules_intersectionAcyclic_of_forall_isAffineOpen
#print axioms AlgebraicGeometry.Cohomology.finiteAffineCoverOpens
#print axioms AlgebraicGeometry.Cohomology.opensUnion_finiteAffineCoverOpens
#print axioms AlgebraicGeometry.Cohomology.isAffineOpen_of_mem_finiteAffineCoverOpens
#print axioms AlgebraicGeometry.Cohomology.cohomologicalBound
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_cohomologicalBound
#print axioms AlgebraicGeometry.Cohomology.coherent_H_subsingleton_of_cohomologicalBound
#print axioms AlgebraicGeometry.Cohomology.FiniteDimensionalCohomology.toFiniteCohomology

-- Layer B stage 3: the first Cech-to-derived comparison layer. The terminal-object
-- natural isomorphism closes the explicit TODO in Mathlib's sheaf-cohomology API; the
-- singleton theorem is the first positive-degree case of the Leray comparison.
#print axioms CategoryTheory.cechCohomology_isZero_of_exactAt
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaPresheafIsoConstant
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheafIsoConstant
#print axioms CategoryTheory.Sheaf.HPrimeNatIsoH
#print axioms CategoryTheory.Sheaf.HPrimeAddEquivH
#print axioms CategoryTheory.Sheaf.subsingleton_HPrime_iff_H
#print axioms CategoryTheory.Sheaf.cechComputesDerivedCohomologyAt_singleton_terminal_of_pos

-- Layer B stage 3: sections of an explicit injective resolution compute the local `H'`
-- groups, and a fixed Cech column is their product over finite intersections. Local
-- acyclicity therefore kills every positive-resolution-degree column homology object.
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaPresheafHomAddEquiv
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheafHomAddEquiv
#print axioms CategoryTheory.Sheaf.sectionsAtFunctor
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsComplex
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaHomComplexIsoSections
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsCohomologyAddEquivHPrime
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexColumnXIso
#print axioms CategoryTheory.Sheaf.cechColumnSectionsComplex
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexColumnIsoSectionsComplex
#print axioms CategoryTheory.Sheaf.cechColumnSectionsComplex_exactAt
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexColumn_exactAt_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.subsingleton_cechInjectiveBicomplexColumnHomology_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.isZero_cechInjectiveInitialPage_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.subsingleton_cechInjectiveInitialPage_of_isCechAcyclicFor

-- Layer B stage 3: the same results reached from the `X.Modules` wrapper, which instance
-- search does not see through on its own. `Scheme.Modules.toSheaf` is the retyped functor
-- downstream work should use; the two transfer instances cover the goals that still arrive
-- on the wrong side.
#print axioms Scheme.Modules.epi_sheafOfModules
#print axioms Scheme.Modules.mono_sheafOfModules
#print axioms Scheme.Modules.toSheaf
#print axioms Scheme.Modules.additive_toSheaf
#print axioms Scheme.Modules.preservesFiniteLimits_toSheaf
#print axioms Scheme.Modules.preservesFiniteColimits_toSheaf
#print axioms Scheme.Modules.preservesEpimorphisms_toSheaf
#print axioms Scheme.Modules.shortExact_map_toSheaf

-- Layer B stage 2: invertible sheaves and the raw sheafified tensor product. The final
-- Picard group law waits on tensor/sheafification coherence; these declarations expose the
-- complete foundation without postulating that missing theorem.
#print axioms SheafOfModules.freePUnitIsoUnit
#print axioms SheafOfModules.LocalGeneratorsData.isRankOne_ofIso
#print axioms SheafOfModules.IsInvertible.ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitLeftIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitRightIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_id_comp
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_id_comp_assoc

/-! ## What the sheafified tensor does to a SECTION (#585 step P1)

Before this the tree had no element-level rule for the sheafified tensor at all: not for tensorObj,
not for tensorHom, not for either unitor. Every consumer used them at the morphism level only, and
nothing anywhere said what one does to a section. That is what blocked #585's glue, which has to
meet the chart-extension half -- and that half speaks in scalars acting on sections.

unitorConj is M = M (x) 1 --(1 (x) phi)--> M (x) 1 = M, the way a map out of the structure sheaf
acts on an arbitrary module sheaf when no linearity of the tensor is available. unitorConj_app says
it multiplies by phi's value on 1.

The route never computes sheafification on sections. unitorConjPre is the same conjugation one
level down, on presheaves of modules, where Mathlib's Presheaf/Monoidal.lean gives the unitors and
tensorHom openwise by rfl and the whole chain t |-> t (x) 1 |-> t (x) phi(1) |-> phi(1) . t is
definitional. unitorConj_eq carries it across: toPresheafOfModules is fully faithful, so the
presheaf endomorphism is the image of a unique sheaf endomorphism, and counit naturality collapses
counit.inv followed by associatedSheaf.map followed by counit.hom onto exactly that. Given it,
unitorConj_app is rfl.

These live in Picard.lean and cannot move: associatedSheaf is a private abbrev there and the
monoidal structure on X.PresheafOfModules is a local instance, so neither is nameable outside.

Two steps use congrArg/exact rather than rw. Goals mentioning associatedSheaf are not type-correct
under the instances transparency level, which stops rw matching patterns that ARE syntactically
present. Same failure mode recorded for restrict_smul_eq and for chartTwistBy_eq. -/

#print axioms AlgebraicGeometry.Scheme.Modules.unitorConj
#print axioms AlgebraicGeometry.Scheme.Modules.unitorConjPre
#print axioms AlgebraicGeometry.Scheme.Modules.unitorConj_eq
#print axioms AlgebraicGeometry.Scheme.Modules.unitorConj_app

/-! ## A pure tensor of SECTIONS, and what the twistBy shape does to one (#585 step D prerequisite)

tmulSection is the exportable handle on the sheafified tensor at section level. tensorObj is built
from toPresheafOfModules and the monoidal structure on X.PresheafOfModules; the first is reached
through a private abbrev here and the second is a local instance, so a consumer OUTSIDE this file
cannot write a pure tensor at all. Any section-level statement about the tensor has to go through a
named constructor, and this is it.

It is the image of the honest pure tensor under the sheafification adjunction's unit. Sections of a
sheafification are not in general sums of pure tensors, so this maps INTO the sections rather than
describing them -- which is all the twist API needs.

tensorUnitRight_inv_tensorHom_app is the payoff: (rho.inv followed by tensorHom (1 F) psi) is
exactly the shape of Proj.twistBy and Proj.chartTwistBy, and this says what it does to a section.
With smul_tmulSection it lets #585's glue compare the two charts WITHOUT restriction commuting with
the tensor product -- which nothing in this repository or in Mathlib provides.

Proved like unitorConj_eq, and again sheafification is never computed on sections: the counit's
inverse IS the adjunction unit (right triangle identity, assembled mono-free because Mono does not
synthesize on a .val), and naturality of that unit carries a presheaf-level computation across
where it is rfl.

Every step is congrArg/exact -- goals mentioning associatedSheaf are not type-correct under the
instances transparency level, so rw will not match patterns that ARE syntactically present. The
naturality step needs DFunLike.congr_fun and not congrFun: the components are bundled LinearMaps,
not functions. -/

#print axioms AlgebraicGeometry.Scheme.Modules.tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.smul_tmulSection

-- The CONVERSE of tmulSection, for #586. tmulSection's docstring warns it is "a map INTO the
-- sections, not a description of them", and globally that is right. Locally it is a description:
-- exists_eq_sum_tmulSection says a section of the sheafified tensor is, near every point, a finite
-- sum of pure tensors.
--
-- It can only live in Picard.lean, and that is the point. The monoidal structure on
-- X.PresheafOfModules is a local instance there and associatedSheaf is a private abbrev, so no
-- consumer can write t (x)t y, name M' (x) N', or say "this section comes from the presheaf tensor"
-- at all -- confirmed by compiling the attempt outside, where the tensor notation does not even
-- parse. Anything that has to take a section of M (x) N apart must be handed this from inside.
--
-- Three facts, none of them reachable from outside: the sheafification unit is locally surjective,
-- so the section has a preimage in the presheaf tensor near the point; TensorProduct.exists_finset
-- writes that preimage as a finite sum of pure tensors; and the unit's component is additive, which
-- turns the sum into a sum of tmulSections by the definition of tmulSection.
--
-- isLocallySurjective_sheafificationUnit is stated separately because instance search does not find
-- it. All three of HasWeakSheafify, HasSheafCompose and PreservesSheafification synthesize for this
-- site, and the composite goal still does not; rewriting the unit to toSheafify (which it IS, by
-- rfl) and applying Mathlib's instance explicitly is what closes it. An instance-search failure is
-- not evidence that a fact is missing.
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallySurjective_sheafificationUnit
#print axioms AlgebraicGeometry.Scheme.Modules.exists_eq_sum_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitRight_inv_tensorHom_app
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorTripleAssocIso
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.mk_eq_mk_iff

-- Layer B stage 2: tensor/sheafification descent for invertible sheaves. Local rank-one
-- trivializations make tensor preserve locally bijective maps; this supplies both comparison
-- orientations, restriction compatibility, tensor closure, and the sheafified associator.
#print axioms CategoryTheory.Presheaf.isLocallyInjective_of_coversTop
-- Its companion, and the two packaged together. isLocallySurjective_of_coversTop was private in
-- Divisors/AssociatedSheaf/Construction.lean and hardcoded to Opens X, though its proof uses only
-- Sieve.ofObjects, J.transitive and Sieve.overEquiv -- all general. W_of_coversTop is the recipe
-- that file ran by hand at three sites: local injectivity and local surjectivity each descend
-- along a covering family, and together they are membership in J.W, which sheafification inverts.
-- That is the practical route to "isomorphism on a cover implies isomorphism after sheafification",
-- for which no direct lemma exists on SheafOfModules morphisms.
#print axioms CategoryTheory.Presheaf.isLocallySurjective_of_coversTop
#print axioms CategoryTheory.Presheaf.W_of_coversTop
#print axioms SheafOfModules.LocalGeneratorsData.rankOneTrivialization
#print axioms SheafOfModules.isLocallySurjective_whiskerLeft
#print axioms SheafOfModules.isLocallyInjective_whiskerLeft_of_isoUnit
#print axioms SheafOfModules.isLocallyInjective_whiskerLeft_of_rankOneData
#print axioms SheafOfModules.W_whiskerLeft_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerLeft_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerRight_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerLeft_unit_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerRight_unit_of_rankOneData
#print axioms SheafOfModules.LocalGeneratorsData.rankOneTrivializationOver
#print axioms SheafOfModules.IsInvertible.of_trivializations
#print axioms AlgebraicGeometry.Scheme.Modules.overSheafificationComparison
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_overSheafificationComparison
#print axioms AlgebraicGeometry.Scheme.Modules.overTensorPresheafIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorOverIsoOfTrivializations
#print axioms AlgebraicGeometry.Scheme.Modules.tensorOverIsoOfTrivializationRight
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_tensorObj
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonLeft
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonRight
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_tensorSheafificationComparisonLeft
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_tensorSheafificationComparisonRight
#print axioms AlgebraicGeometry.Scheme.Modules.tensorAssocIso

-- Layer B stage 2: the descended tensor product is coherently symmetric monoidal on
-- invertible sheaves, and its skeleton yields the Picard group. Pentagon and both hexagons
-- reduce to the corresponding presheaf identities; no coherence law is postulated.
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonRight_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonLeft_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorAssocIso_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_id_id
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_comp_tensorHom
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonRight_comp_tensorAssocIso
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafMonoidalCategoryStruct
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafMonoidalCategory
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso_symmetry
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso_inv
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafBraidedCategory
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafSymmetricCategory
#print axioms AlgebraicGeometry.Scheme.Modules.picardClassCommMonoid
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.one_eq_one
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.mk_mul_mk
#print axioms AlgebraicGeometry.Scheme.Modules.Pic.mkOfTensorInverse
#print axioms AlgebraicGeometry.Scheme.Modules.Pic.coe_mkOfTensorInverse
#print axioms AlgebraicGeometry.Scheme.Modules.Pic.coe_one

-- Layer B stage 2: the fractional presheaf and associated invertible sheaf of a Cartier
-- divisor. Local equations give the trivializations; multiplication of rational functions
-- is a locally bijective map and therefore an isomorphism after module sheafification.
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.IsEquationOn
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.IsEquationOn.mono
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.fractionalPresheaf
#print axioms AlgebraicGeometry.Scheme.RationalSections
#print axioms AlgebraicGeometry.Scheme.rationalSectionsRes
#print axioms AlgebraicGeometry.Scheme.germToFunctionField_res
#print axioms AlgebraicGeometry.Scheme.rationalSectionsRes_smul
#print axioms AlgebraicGeometry.Scheme.rationalPresheaf
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheaf
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.equationIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.equationTransitionIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.equationTransitionIso_trans
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheaf_isInvertible
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.multiplicationHom
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.fractionalTensorAddIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedTensorAddIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.globalEquationIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheafZeroIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheafPrincipalIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedTensorInverseIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.toPic
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.coe_toPic
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.divisorToPicAdd
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.divisorToPicAdd_apply
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.divisorToPicAdd_principal
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.classToPicAdd
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.classToPic
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.classToPic_toClass

-- Layer B stage 2: effective Cartier divisors and their fundamental exact sequences.
-- Tensoring by an invertible sheaf is exact, so the normalized twist is directly reusable
-- as `O_X(E-D) → O_X(E) → O_X(E) ⊗ i_* O_D`; both sequences lift to `Coh X`
-- under explicit coherence hypotheses.
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientMap
#print axioms AlgebraicGeometry.Scheme.Modules.tensorLeftFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.mono_tensorHom_id_of_invertible
#print axioms AlgebraicGeometry.Scheme.Modules.shortExact_map_tensorLeft_of_invertible
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.structureSheaf
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.quotient
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.idealInclusion
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.fundamentalSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.fundamentalSequence_shortExact
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cokernelIsoStructureSheaf
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedStructureSheaf
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistSourceIso
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistMiddleIso
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedIdealInclusion
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedQuotient
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistSequence_shortExact
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistCokernelIso
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.structureSheaf_isCoherent
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohFundamentalSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohFundamentalSequence_shortExact
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedStructureSheaf_isCoherent
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohTwistSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohTwistSequence_shortExact

-- Layer B stage 2: determinant lines and first Chern classes. DerivedAlgGeo constructs sheaf
-- exterior powers; invertibility of a top exterior power and exact-sequence comparison remain
-- explicit certificates. The coherent extension requires either finite locally free determinant
-- data or a visible two-term finite locally free resolution.
#print axioms Module.finrank_topExteriorPower
#print axioms AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeData
#print axioms AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeData.isLocallyFree
#print axioms AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeData.ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.coe_toPic
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_eq_of_iso
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.dual
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.tensor
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_dual
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_tensor
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.ExteriorDeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.ExteriorDeterminantData.determinantData
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.isLocallyFree
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClass
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClassAdd
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClass_ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClassAdd_ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClass_eq_of_lineIso
#print axioms AlgebraicGeometry.Scheme.Modules.DirectSumDeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.DirectSumDeterminantData.firstChernClass_eq_mul
#print axioms AlgebraicGeometry.Scheme.Modules.DirectSumDeterminantData.firstChernClassAdd_eq_add
#print axioms AlgebraicGeometry.Scheme.Modules.ShortExactDeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.ShortExactDeterminantData.firstChernClass_eq_mul
#print axioms AlgebraicGeometry.Scheme.Modules.ShortExactDeterminantData.firstChernClassAdd_eq_add
#print axioms AlgebraicGeometry.Coh.ShortExactDeterminantData
#print axioms AlgebraicGeometry.Coh.ShortExactDeterminantData.toModules
#print axioms AlgebraicGeometry.Coh.ShortExactDeterminantData.firstChernClassAdd_eq_add
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.determinantLine
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClass
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClassAdd
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClass_eq
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.ofIso
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClass_ofIso
#print axioms AlgebraicGeometry.Coh.PerfectShortExactDeterminantData
#print axioms AlgebraicGeometry.Coh.PerfectShortExactDeterminantData.firstChernClassAdd_eq_add

-- Layer B stage 4: dimension-general numerical-polynomial algebra and its geometric Snapper
-- bridge. The geometric induction and missing closure theorem are visible structure fields,
-- never hidden axioms.
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.difference
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.difference_comm
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.difference_add_direction
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coordinateDifference
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.mixedDifference
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.mixedDifference_difference
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.mixedDifference_eq_of_perm
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.DegreeLE
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.degreeLE_iff_fin
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.DegreeLE.add
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.DegreeLE.succ
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.DegreeLE.mono
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.DegreeLE.difference
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficient
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficient_eq_of_perm
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.topCoefficient
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.topCoefficient_comp_perm
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coordinateDirections
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.newtonCoefficient
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.mixedDifference_eq_coefficient_of_degreeLE
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficient_cons_add
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficient_middle_add
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficientAddHom
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficient_middle_zsmul
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.mixedDifference_oneVariable
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.oneVariable_fwdDiff_vanishes
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.coefficient_oneVariable
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.surfacePairing
#print axioms AlgebraicGeometry.IntersectionTheory.NumericalPolynomial.surfacePairing_symm
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.picardPower
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.linePower
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.linePower_picardClass
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.twistModules
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.CoherentTwistFamily
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.eulerFunction
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.GeometricInduction
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.GeometricInduction.difference_descendedEuler
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.GeometricInduction.mixedDifference_eulerFunction
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.eulerCharacteristic_isZero
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.snapper
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.mixedDifference_eq_euler_descended
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.coefficient_eq_euler_descended
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.eulerFunction_eq_of_coherentSheafIso
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.eulerFunction_eq_of_lineBundleIso
#print axioms AlgebraicGeometry.IntersectionTheory.Snapper.oneVariable_fwdDiff_euler_vanishes
#print axioms AlgebraicGeometry.IntersectionTheory.Number.picardDifference
#print axioms AlgebraicGeometry.IntersectionTheory.Number.picardMixedDifference
#print axioms AlgebraicGeometry.IntersectionTheory.Number.picardCoefficient
#print axioms AlgebraicGeometry.IntersectionTheory.Number.PicardDegreeLE
#print axioms AlgebraicGeometry.IntersectionTheory.Number.picardCoefficient_middle_mul
#print axioms AlgebraicGeometry.IntersectionTheory.Number.picardCoefficientAddHom
#print axioms AlgebraicGeometry.IntersectionTheory.Number.picardMonomial
#print axioms AlgebraicGeometry.IntersectionTheory.Number.mixedDifference_picardPolynomial
#print axioms AlgebraicGeometry.IntersectionTheory.Number.TwistContext
#print axioms AlgebraicGeometry.IntersectionTheory.Number.TwistContext.picardDegreeLE
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.picardIntersectionNumber
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.picardIntersectionNumber_eq_coefficient
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.picardIntersectionNumber_comp_perm
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.picardIntersectionList_middle_mul
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.cartierClassIntersectionNumber
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.cartierDivisorIntersectionNumber_eq_picard
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.surfaceIntersectionPairing
#print axioms AlgebraicGeometry.IntersectionTheory.Number.IntersectionContext.surfaceIntersectionPairing_symm

-- Layer B stage 5: geometric surface divisor Riemann--Roch. These declarations use Serre
-- symmetry, Snapper intersections, and #25's effective sequence, never Layer A's HRR field.
#print axioms AlgebraicGeometry.RiemannRoch.Surface.correctionNumerator
#print axioms AlgebraicGeometry.RiemannRoch.Surface.twice_eulerPic_sub
#print axioms AlgebraicGeometry.RiemannRoch.Surface.correctionNumerator_even
#print axioms AlgebraicGeometry.RiemannRoch.Surface.eulerPic_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.cartierEulerCharacteristic
#print axioms AlgebraicGeometry.RiemannRoch.Surface.cartierCorrectionNumerator
#print axioms AlgebraicGeometry.RiemannRoch.Surface.cartier_eulerCharacteristic_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.cartierCorrectionNumerator_even
#print axioms AlgebraicGeometry.RiemannRoch.Surface.cartierEulerCharacteristic_eq_of_principalEquivalent
#print axioms AlgebraicGeometry.RiemannRoch.Surface.cartier_formula_eq_of_principalEquivalent
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization.euler_additivity
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization.effective_euler_additivity
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization.QuotientIntersectionComparison
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization.effective_divisor_formula_from_sequence
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization.effective_divisor_formula
#print axioms AlgebraicGeometry.RiemannRoch.Surface.EffectiveSequenceRealization.quotient_eulerCharacteristic_eq_half_correction
#print axioms AlgebraicGeometry.RiemannRoch.Surface.eulerPic_one
#print axioms AlgebraicGeometry.RiemannRoch.Surface.eulerPic_canonical
#print axioms AlgebraicGeometry.RiemannRoch.Surface.k3_eulerPic_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.k3_eulerPic_eq_two

-- Layer B stage 5: surface Todd reconstruction. The top representative comes from the
-- structure-sheaf twist polynomial, and the first component is the explicit class -K/2.
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.Data
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.numericalCanonicalClass
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.homogeneousPicardCoefficient_nil
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.homogeneousPicardCoefficient_singleton
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.toddComponent
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.toddComponent_mem
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.degree_toddTwo_eq_eulerPic_one
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.degree_toddTwo_eq_structureSheafEulerCharacteristic
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.degree_toddOne_mul_divisorClass
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.structureToddOne_eq_toddOne
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.toddOne_eq_zero
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.degree_toddTwo_eq_two
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.NumericalVarietyComparison.ring_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.ToddData.NumericalVarietyComparison.toIsK3

-- Layer B stage 5: finite locally free and explicitly perfect surface dévissage. Arbitrary
-- coherent sheaves receive no hidden resolution instance.
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.locallyFreeCh2Degree
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.locallyFreeC2Degree
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.locallyFree_eulerCharacteristic_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.locallyFreeCh2Degree_shortExact
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.locallyFreeC2Degree_shortExact
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.eulerCharacteristic_eq_middle_sub_left
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.chernCharacterTwoDegree_eq_middle_sub_left
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.perfectC2Degree
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.perfect_eulerCharacteristic_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.discriminantDegree_eq_c2
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.grothendieckEulerHom_class_eq_perfect_formula
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.NumericalVarietyComparison.chi_eq_geometric_terms
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Devissage.NumericalVarietyComparison.chi_eq_classical

-- Layer B stage 5: final geometric assembly. Reconstruction proves HRR for every coherent
-- sheaf; the classical rank/c₁/c₂ interpretation remains conditional on an explicitly
-- supplied two-term finite locally free resolution.
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.reconstruction_eulerPic_one
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.degree_tauComponent_two_eq_eulerCharacteristic
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.sheaf_hirzebruch_riemannRoch
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.toGeometricData
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.toGeometricData_satisfiesSheafHRR
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.toNumericalVariety
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.toNumericalVariety_satisfiesHRR
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.PerfectReconstructionComparison
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.perfect_rank_eq
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.perfect_toddTwo_degree
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.perfect_toddOne_degree
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.perfect_chTwo_degree
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.perfect_surface_expansion
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.perfect_chi_eq_classical
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.toIsK3
#print axioms AlgebraicGeometry.RiemannRoch.Surface.Assembly.k3_eulerCharacteristic_eq

-- Layer B stage 5: numerical HRR in positive dimensions through four. Representability and
-- divisor-pairing separation remain visible in `PairingContext`; no cycle-valued GRR theorem is
-- assumed. The dimension-three and dimension-four constructors expose a separate HRR witness.
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.reconstruction_eulerPic_one
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.degree_tauComponent_top_eq_eulerCharacteristic
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.mk.inj
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.mk.sizeOf_spec
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.eulerPic_iso
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.eulerPic_shortExact
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.rank_iso
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.rank_shortExact
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.reconstruction
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.chernCharacterHom_mem
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.chernCharacterHom_add
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.rankHom_class
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.chernCharacterHom_class
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.intAlgebraMap
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.rankInvariant
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.chernCharacterInvariant
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.rankHom
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.chernCharacterHom
#print axioms AlgebraicGeometry.RiemannRoch.ReconstructionSystem.chernCharacterHom_zero
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.reconstructedToddComponent
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.reconstructedToddComponent_mem
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.sheaf_hirzebruch_riemannRoch
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.hirzebruch_riemannRoch
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.toNumericalVariety
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.toNumericalVariety_satisfiesHRR
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.numericalClass
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.toThreefoldNumericalVariety
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.toFourfoldNumericalVariety
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.threefold_eulerCharacteristic_eq
#print axioms AlgebraicGeometry.RiemannRoch.HigherDimension.fourfold_eulerCharacteristic_eq

-- Layer B stage 4: degree-level surface Chern data. The construction uses determinants,
-- Picard intersections, and Euler characteristics; it does not postulate a Chow-valued class
-- or a perfect numerical pairing.
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.virtualRank
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.picardFirstChernClass
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.numericalFirstChernClass
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.toddOnePairing
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.toddTwoDegree
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.chernCharacterTwoDegree
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.surfaceChernCharacter
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.eulerCharacteristic_eq_rank_mul_toddTwo_add_toddOne_add_chernCharacterTwo
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.chernCharacterTwoDegree_ofIso
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.picardFirstChernClass_shortExact
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.numericalFirstChernClass_shortExact
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.chernCharacterTwoDegree_shortExact
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.chernCharacterTwoDegree_structureSheaf
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.eulerPic_one_eq_eulerCharacteristic_structureSheaf
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.toddTwoDegree_eq_eulerPic_one
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.chernCharacterTwoDegree_lineBundle
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.discriminantDegree
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface.discriminantDegree_eq_numericalVariety

-- Layer B stage 4: bounded numerical-ring reconstruction. Existence of representatives and
-- separation by divisor products are fields of the input structures, not hidden axioms.
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.homogeneousPicardCoefficient
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.picardMixedDifference_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.picardCoefficient_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.scaledPicardCoefficient_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.interpolatingPolynomial_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.homogeneousPicardCoefficient_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.scaledPicardCoefficient_eq_of_perm
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.homogeneousPicardCoefficient_eq_of_perm
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.divisorProduct_nil
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData.tauComponent
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData.tauComponent_mem
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData.degree_tauComponent_mul_divisorProduct
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData.tauComponent_eq_of_twistPairing_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData.tauComponent_eq_of_eulerPic_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.PairingContext.ReconstructionData.tauComponent_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.toddComponent
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_zero
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_one
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_two
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_three
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_four
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_of_five_le
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_mem
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_eq_zero_of_dimension_lt
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.tauComponent_one_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.tauComponent_two_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.tauComponent_three_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.tauComponent_four_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_eq_of_eulerPic_eq
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_iso
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_add
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.LineBundleComparison
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.tauComponent_eq_lineTauCandidate
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.chernCharacterComponent_lineBundle
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.degree_chernCharacterComponent_two_eq_surface
#print axioms AlgebraicGeometry.IntersectionTheory.ChernCharacter.toChernClassData

-- Cohomology strategy: `DerivedAlgGeo/Development/Cohomology/Strategy.lean` contributes nothing here on
-- purpose. It is the compile-only API map for the B3 route decision and declares only
-- `example`s, which are anonymous and cannot be audited. Its guarantee is that it builds:
-- if an upstream declaration it names moves, `lake build` fails. The first real B3
-- theorem goes below this line.
#print axioms CategoryTheory.Sheaf.isFlasque_of_injective
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheafMap_stalk_isIso
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheaf_stalk_isZero_of_not_mem
#print axioms CategoryTheory.Sheaf.cechComplex_exactAt_succ_of_injective

-- Mukai vector: the identification of the abstract Mukai extension with the
-- numerical Mukai pairing. Every field of `IntegralMukaiData` is supplied
-- geometric data, so a clean axiom list here says the identification follows
-- from that data -- not that any K3 satisfies it.
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.mk.inj
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.c₁
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.b
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.b_spec
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.b_comm_on_realized
#print axioms AlgebraicGeometry.Numerical.K3.mukaiSInt
#print axioms AlgebraicGeometry.Numerical.K3.mukaiSInt_spec
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.mukaiVector
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.mukaiVector_fst
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.mukaiVector_snd_fst
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.mukaiVector_snd_snd
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.pairing_mukaiVector
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.selfPairing_mukaiVector
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.chi₂_eq_neg_pairing
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.selfPairing_mukaiVector_eq_neg_chi₂
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.neg_two_le_selfPairing_mukaiVector_iff
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.isSpherical_mukaiVector_iff
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.isIsotropic_mukaiVector_iff
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.expectedDim_mukaiVector
#print axioms AlgebraicGeometry.Numerical.K3.IntegralMukaiData.b_c₁_add

-- Additive `c₁`. ONE new supplied field on top of `IntegralMukaiData`, and it
-- is genuinely supplied: `b_c₁_add` above proves everything the weaker
-- structure implies, which is additivity of `c₁` AGAINST THE FORM, and `b` is
-- nowhere assumed nondegenerate, so that stops short of additivity. With the
-- field, the Mukai vector is an `AddMonoidHom` and the Mukai form is a real
-- `LinearMap.BilinForm`, which is what lets the word "isometry" be used below
-- in Mathlib's sense.
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mk.inj
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.toIntegralMukaiData
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.c₁_add
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.c₁Hom
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.c₁Hom_apply
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiVectorHom
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiVectorHom_apply
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiForm
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiForm_apply
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiForm_comm
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiForm_eq_neg_chi₂
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiVectorIsometry
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiVectorIsometry_apply

-- The K₀ bridge: realizing a triangulated Grothendieck group numerically.
-- `NumericalRealization`, `Descends` and `PreservesEuler` are all SUPPLIED
-- geometric input, none of it constructed here, so a clean axiom list on the
-- isometry theorems says they follow from that input -- not that any variety
-- or any Fourier-Mukai transform provides it.
#print axioms AlgebraicGeometry.Numerical.NumericalRealization
#print axioms AlgebraicGeometry.Numerical.NumericalRealization.mk.inj
#print axioms AlgebraicGeometry.Numerical.NumericalRealization.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.NumericalRealization.cl
#print axioms AlgebraicGeometry.Numerical.Descends
#print axioms AlgebraicGeometry.Numerical.Descends.apply_of
#print axioms AlgebraicGeometry.Numerical.Descends.of_natIso
#print axioms AlgebraicGeometry.Numerical.PreservesEuler
#print axioms AlgebraicGeometry.Numerical.pairing_mukaiVector_eq_of_preservesEuler
#print axioms AlgebraicGeometry.Numerical.selfPairing_mukaiVector_eq_of_preservesEuler
#print axioms AlgebraicGeometry.Numerical.isSpherical_mukaiVector_iff_of_preservesEuler
#print axioms AlgebraicGeometry.Numerical.pairing_mukaiVector_eq_on_realized

-- The isometry itself, in Mathlib's sense of the word: a `ℤ`-linear map under
-- which the two Mukai forms agree. It is an isometry of the forms on the
-- NUMERICAL GROTHENDIECK GROUPS, not of the Mukai extensions, and no map
-- between those is built. The proof fields are the pairing theorems above
-- unchanged -- what a clean axiom list says here is that naming the structure
-- adds no assumption.
#print axioms AlgebraicGeometry.Numerical.isometryOfPreservesEuler
#print axioms AlgebraicGeometry.Numerical.isometryOfPreservesEuler_apply
#print axioms AlgebraicGeometry.Numerical.isometryEquivOfPreservesEuler
#print axioms AlgebraicGeometry.Numerical.mukaiForm_eq_on_realized

-- Transferring Euler-form preservation across a realization. `IsRiemannRoch`
-- is bilinear HRR and `PreservesCategoricalEuler` is what full faithfulness
-- would give; both are supplied, and `CategoricalEulerForm` is supplied rather
-- than built from Hom. A clean axiom list here is a statement about the
-- bookkeeping, not about any variety or any functor.
#print axioms AlgebraicGeometry.Numerical.CategoricalEulerForm
-- The Hom-built form, packaged. `ofLinear` is what retires the "nothing
-- constructs a CategoricalEulerForm" claim; the obligation moves to
-- HomFiniteBounded rather than disappearing.
#print axioms AlgebraicGeometry.Numerical.CategoricalEulerForm.ofLinear
#print axioms AlgebraicGeometry.Numerical.CategoricalEulerForm.ofLinear_chi
-- Step 6: the second of EulerTransfer's three obligations, discharged for
-- Hom-built forms. IsRiemannRoch remains supplied.
#print axioms AlgebraicGeometry.Numerical.ofLinear_preservesCategoricalEuler
#print axioms AlgebraicGeometry.Numerical.CategoricalEulerForm.mk.inj
#print axioms AlgebraicGeometry.Numerical.CategoricalEulerForm.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.CategoricalEulerForm.chi
#print axioms AlgebraicGeometry.Numerical.IsRiemannRoch
#print axioms AlgebraicGeometry.Numerical.PreservesCategoricalEuler
#print axioms AlgebraicGeometry.Numerical.preservesEuler_of_descends
#print axioms AlgebraicGeometry.Numerical.pairing_mukaiVector_eq_on_realized_of_categorical

/-! ## The structure sheaf as a coherent sheaf, and Picard triviality -/

#print axioms AlgebraicGeometry.Scheme.structureSheafCoh
#print axioms AlgebraicGeometry.Scheme.structureSheafCoh_obj
#print axioms AlgebraicGeometry.Scheme.structureSheafCoh_obj_eq_unit
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_eq_iff
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.unit_toPic

/-! ## K3 surfaces

A smooth projective surface with `ω_X` trivial in `Pic` and `H¹(X, O_X) = 0`.
Nothing here constructs such a surface, and nothing here connects the geometric
definition to the numerical `AlgebraicGeometry.Numerical.K3.IsK3` — that bridge
is Hirzebruch--Riemann--Roch and does not exist at the pin. See the module
docstring in `DerivedAlgGeo/AlgebraicGeometry/Surface/K3.lean`. -/

#print axioms AlgebraicGeometry.SmoothProperVariety.CanonicalSheafData.canonicalClass_eq_one_iff
#print axioms AlgebraicGeometry.SmoothProperVariety.IsK3Surface
#print axioms AlgebraicGeometry.SmoothProperVariety.IsK3Surface.projective
#print axioms AlgebraicGeometry.SmoothProperVariety.IsK3Surface.canonicalClass_eq_one
#print axioms AlgebraicGeometry.SmoothProperVariety.IsK3Surface.h1_vanishing
#print axioms AlgebraicGeometry.SmoothProperVariety.IsK3Surface.canonicalSheaf_iso
#print axioms AlgebraicGeometry.SmoothProperVariety.IsK3Surface.antiCanonicalClass_eq_one
#print axioms AlgebraicGeometry.K3Surface
#print axioms AlgebraicGeometry.K3Surface.toSmoothProperVariety
#print axioms AlgebraicGeometry.K3Surface.canonical
#print axioms AlgebraicGeometry.K3Surface.isK3
#print axioms AlgebraicGeometry.K3Surface.mk.inj
#print axioms AlgebraicGeometry.K3Surface.mk.sizeOf_spec
#print axioms AlgebraicGeometry.K3Surface.toVariety
#print axioms AlgebraicGeometry.K3Surface.toScheme
#print axioms AlgebraicGeometry.K3Surface.instIsProjective
#print axioms AlgebraicGeometry.K3Surface.canonicalSheaf_iso
#print axioms AlgebraicGeometry.K3Surface.h1_vanishing

/-! ## The base field acts: module sheaves and `Coh` are `k`-linear

Multiplication by a global function, composed with `k → Γ(X, O_X)`, makes the
categories `k`-linear rather than merely preadditive. Mathlib then supplies
`Linear k (DerivedCategory (Coh X))`, which is what makes `Hom(E, F⟦i⟧)` a
`k`-vector space and hence what makes sphericity of an object expressible at
all. It does NOT supply finite-dimensionality; see issue #332. -/

#print axioms AlgebraicGeometry.Scheme.homModuleGlobal
#print axioms AlgebraicGeometry.Scheme.modulesLinearGlobal
#print axioms AlgebraicGeometry.Variety.homModule
#print axioms AlgebraicGeometry.Variety.modulesLinear
#print axioms AlgebraicGeometry.Variety.smul_eq_action_comp
#print axioms AlgebraicGeometry.Variety.cohLinear
#print axioms AlgebraicGeometry.Variety.derivedLinear

/-! ## Spherical objects on a K3 surface

Huybrechts Definition 8.1, with its `E ⊗ ω_X ≅ E` clause discharged by
triviality of the canonical class, so no derived tensor product is needed.
`end_one` and `ext_two` are hypotheses: finite-dimensionality of `Hom` in
`Dᵇ(Coh X)` is #332. Nothing here exhibits a spherical object, and nothing
connects the definition to `Mukai.IsSpherical`. -/

#print axioms AlgebraicGeometry.K3Surface.DerivedCat
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.vanishing
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.end_one
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.ext_two
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.not_isZero
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.finrank_end
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.finrank_ext_two
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.of_iso

/-! ## The numerical shadow of sphericity

`selfEuler_eq_two` computes `χ(E,E) = 1 - 0 + 1 = 2` from the definition of a
spherical object. `EulerRealization` supplies Hirzebruch--Riemann--Roch — the
agreement between the categorical Euler characteristic and the numerical one —
and nothing here constructs one. `isSpherical_mukaiVector` is the forward
direction only; the converse needs simplicity and Serre duality, as
`MukaiVector.lean` records. -/

#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.finrank_hom_eq_zero
#print axioms AlgebraicGeometry.K3Surface.selfEuler
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.selfEuler_eq_two
#print axioms AlgebraicGeometry.K3Surface.EulerRealization
#print axioms AlgebraicGeometry.K3Surface.EulerRealization.cls
#print axioms AlgebraicGeometry.K3Surface.EulerRealization.chi₂_eq
#print axioms AlgebraicGeometry.K3Surface.EulerRealization.mk.inj
#print axioms AlgebraicGeometry.K3Surface.EulerRealization.mk.sizeOf_spec
#print axioms AlgebraicGeometry.K3Surface.IsSphericalObject.isSpherical_mukaiVector

/-! ## `H⁰(Pⁿ, O(d)) = 0` for `d < 0` (#665, S1a)

The arithmetic and homological steps first, then the two-chart step that produces the cross
equation from a Čech cocycle, then the statement itself. `polynomialIntTwisting_H_zero_subsingleton`
is the acceptance criterion of #665, as an abelian group: the `k`-vector-space structure
`FiniteDimensionalCohomology.finite` asks for is a separate matter and the comparison `AddEquiv` is
not assumed `k`-linear. `Nontrivial ι` is the only hypothesis on the variable set — at one variable
the statement is false, and no finiteness is used. -/

#print axioms AlgebraicGeometry.Proj.intShiftPiece_eq_bot_of_neg
#print axioms AlgebraicGeometry.Proj.eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt
#print axioms AlgebraicGeometry.Proj.num_eq_zero_of_cross_of_neg
#print axioms AlgebraicGeometry.Proj.intCechComplex_homology_zero_isZero_of_ker
#print axioms AlgebraicGeometry.Proj.num_eq_zero_of_intCechFace_eq_of_neg
#print axioms AlgebraicGeometry.Proj.intCechTerm_eq_zero_of_face_eq_of_neg
#print axioms AlgebraicGeometry.Proj.intCechComplex_ker_zero_eq_zero_of_neg
#print axioms AlgebraicGeometry.Proj.polynomialVariableIntCechComplex_homology_zero_isZero
#print axioms AlgebraicGeometry.Proj.polynomialIntTwisting_H_zero_subsingleton

/-! ## The top degree keeps one block (#666, S1b — in progress)

Below the top degree `cechPrimitive` contracts every block, because a tuple too short to meet
every variable cannot carry the full one. At the top it can, so the full block is what survives —
and `cechPrimitive_isPrimitive`'s block hypothesis was weakened to constrain only the cochain
handed to it, which is what makes it usable there.

`exists_fullBlock_add_coboundary` is the block half of #666: every class is carried by the full
block. The finiteness half — that the full block is a finite-dimensional `k`-space, via
`finite_setOf_degree_eq_of_neg` — is NOT here, so #666's acceptance criterion is not met by these
declarations. -/

#print axioms AlgebraicGeometry.Proj.cechBlockProj_cechBlockProj_self
#print axioms AlgebraicGeometry.Proj.intCechFullBlock
#print axioms AlgebraicGeometry.Proj.intCechFullBlock_cocycle
#print axioms AlgebraicGeometry.Proj.exists_fullBlock_add_coboundary

/-! ## The base field on a localization, and a finite block (#666, S1b — in progress)

`finite_setOf_degree_eq_of_neg` counts the exponents of the full block; these declarations turn
that count into finite generation. The `k`-action is not extra data — a constant is a degree-zero
homogeneous element — and `awayMk_smul` is what makes it computable on fractions.

`IsPolynomialTwist.smul_mem` and the generalized `awayMk_eq_sum_monomial`,
`exists_sum_awayMk_monomial`, `awayMk_monomial_eq_iff` and `awayMk_monomial_eq_iff_laurentExponent`
are the same statements as before at either sign of the twist; the nonnegative-only forms could
not reach a negative twist at all.

`fg_blockSpan` is one localization. Assembling the blocks of a Čech cochain and matching this
action against `cechScalarAction` are not here, so #666's acceptance criterion is not met. -/

#print axioms AlgebraicGeometry.Proj.IsPolynomialTwist.smul_mem
#print axioms AlgebraicGeometry.Proj.polynomialToHomogeneousLocalization
#print axioms AlgebraicGeometry.Proj.degreeZeroLocalizationModule
#print axioms AlgebraicGeometry.Proj.awayMk_smul
#print axioms AlgebraicGeometry.Proj.awayMk_congr
#print axioms AlgebraicGeometry.Proj.monomial_one_mem_of_mem_support
#print axioms AlgebraicGeometry.Proj.intNegSupport_of_mem_support_laurentFilter
#print axioms AlgebraicGeometry.Proj.blockRep
#print axioms AlgebraicGeometry.Proj.awayMk_eq_blockRep
#print axioms AlgebraicGeometry.Proj.blockProj_univ_mem_span
#print axioms AlgebraicGeometry.Proj.fg_blockSpan

/-! ## The full blocks of a Čech degree, assembled (#666, S1b — in progress)

`fg_cechBlockSpan` carries one block across the denominator comparison; `powersCongrLinear` is
that transport, `k`-linear because it moves nothing but the name of the type.
`module_finite_pi_cechBlockSpan` is the second, independent finiteness: a Čech index has fixed
length over a finite `ι`, so there are finitely many tuples.

Still the cochain side only — no differential, no cocycles, no cohomology, and the `k`-action is
`degreeZeroLocalizationModule` rather than the `cechScalarAction` the finiteness interface
consumes. #666's acceptance criterion is not met. -/

#print axioms AlgebraicGeometry.Proj.powersCongrLinear
#print axioms AlgebraicGeometry.Proj.powersCongrLinear_apply
#print axioms AlgebraicGeometry.Proj.powersCongrLinear_symm_apply
#print axioms AlgebraicGeometry.Proj.cechBlockSpan
#print axioms AlgebraicGeometry.Proj.cechBlockProj_mem_cechBlockSpan
#print axioms AlgebraicGeometry.Proj.fg_cechBlockSpan
#print axioms AlgebraicGeometry.Proj.module_finite_pi_cechBlockSpan

/-! ## A degree-zero element is the constant function (#666, S1b — the bridge)

`Proj.toSpecZero` makes every degree-zero element a global function;
`openToLocalization_toSpecZero_appTop` computes it, and the answer is `a / 1` at every point.

This is the sheaf-theoretic half of #666's remaining step. The base-field action on cohomology is
multiplication by such a function and acts on associated-sheaf sections pointwise on fibers, so
identifying it with scalar multiplication on the graded localizations rests here. Wiring it
through the five steps of `intCechTermSectionAddEquiv` is still outstanding, so #666's acceptance
criterion is not met. -/

#print axioms AlgebraicGeometry.Proj.toSpecZero_appTop_eq
#print axioms AlgebraicGeometry.Proj.toSpecZero_transport_eq
#print axioms AlgebraicGeometry.Proj.openToLocalization_presheaf_map
#print axioms AlgebraicGeometry.Proj.openToLocalization_toSpecZero_appTop

/-! ## The base field acting on sections of a twist (#666, S1b — the bridge, section level)

`FiniteDimensionalCohomology` means `coherentScalarAction` by `Module.Finite k`; the Čech lane
computes with `k` acting through the constants. These say the two agree on sections: the global
function a scalar becomes has value `r / 1` everywhere, so the action on an associated sheaf is
plain scalar multiplication in each fiber.

The five steps of `intCechTermSectionAddEquiv` have NOT been shown `k`-linear, so
`module_finite_linearCoherentH_of_cech` still cannot be fed and #666 is not closed. -/

#print axioms AlgebraicGeometry.Proj.openToLocalization_baseFieldToGlobalSections
#print axioms AlgebraicGeometry.Proj.varietyScalarAction_apply_fiber

/-! ## The Čech comparison is `k`-linear (#666, S1b — the bridge, closed)

`intCechTermSectionAddEquiv_smul` says the comparison between a Čech term and its sections
respects the base-field action: the one the Čech lane computes with (scaling a numerator) and the
one `FiniteDimensionalCohomology` means (multiplying by the global function a scalar becomes).

The five-step composite is never taken apart. `intCechTermSectionAddEquiv_apply_mk` already
identifies it with `moduleAwayToSection` on every `mk`, and `mk` is surjective, so the whole chain
inherits the linearity of one pointwise `mapOfLE`.

Still outstanding for #666: carrying this up from a single term to the Čech complex, and the
`module_finite_linearCoherentH_of_cech` wiring. -/

#print axioms AlgebraicGeometry.Proj.smul_mk
#print axioms AlgebraicGeometry.Proj.mapOfLE_smul
#print axioms AlgebraicGeometry.Proj.constSectionOn
#print axioms AlgebraicGeometry.Proj.constSectionOn_basicOpen
#print axioms AlgebraicGeometry.Proj.constSection
#print axioms AlgebraicGeometry.Proj.varietyScalarAction_app_eq
#print axioms AlgebraicGeometry.Proj.moduleAwayToSection_smul
#print axioms AlgebraicGeometry.Proj.intCechTermSectionAddEquiv_smul

/-! ## The per-index Čech comparison is `k`-linear (#666, step 5)

`intCechIndexEquiv` is the term comparison plus one transport, because a Čech index names sections
over a categorical product of charts while the term comparison is stated over a basic open. The
transport is `subst`; it is stated against the sheaf endomorphism rather than `•` because a `•`
over `Γ(Proj 𝒜, W)` leaves instance search stuck.

Degreewise linearity and the homology statement are NOT here, so #666 is not closed. -/

#print axioms AlgebraicGeometry.Proj.eqToIso_transport_varietyScalarAction
#print axioms AlgebraicGeometry.Proj.intCechTermSectionAddEquiv_symm_varietyScalarAction
#print axioms AlgebraicGeometry.Proj.intCechIndexEquiv_smul

/-! ## The degreewise Cech comparison is `k`-linear (#666, step 5b)

Degree `n` is the product of the indices over tuples, so this is `intCechIndexEquiv_smul` read one
projection at a time. `intTwistScalarHom` names the endomorphism of the twist presheaf that
`cechScalarAction` induces, and the fact that it elaborates with `intTwistPresheaf` on both sides is
the reconciliation between the sheaf-side complex and the explicit algebraic one.

The homology statement, the surjection from the full blocks, and the
`module_finite_linearCoherentH_of_cech` wiring are NOT here, so #666 is not closed. -/

#print axioms AlgebraicGeometry.Proj.intTwistScalarHom
#print axioms AlgebraicGeometry.Proj.intCechScalar_proj
#print axioms AlgebraicGeometry.Proj.intCechCochainsDegreewiseAddEquiv_smul

/-! ## `Hⁱ(Pⁿ, O(d))` is finite-dimensional in every positive degree (#666, steps 5c-7)

The two halves of the argument are `intCechBlockSmul_comp_class` -- the class map is `k`-linear,
which is `homologyPi` naturality once the cycle map is known to intertwine the actions -- and
`intCechBlockClass_surjective` -- every class is the class of a full-block cocycle, which is
`exists_fullBlock_add_coboundary` with the coboundary killed by `toCycles_comp_homologyPi`.
`Module.Finite.of_surjective` then gives finiteness on the Cech side, and
`module_finite_linearCoherentH_of_cech` carries it to the interface group.

`intChart` and `intTwistModules` present the chart family and the twist at the variety rather than
at `Proj`, because `cechCohomologyFunctor` takes its space implicitly and `cechCohomologyModule`
supplies its instance at whatever spelling it was elaborated with. The instances on
`intCechBlockCocycles` are named for the same reason: it is a submodule of a product of submodules
and instance search will not assemble that on its own.

Positive degrees only. Degree 0 has no coboundaries to absorb the remainder, and `H0` is the module
of global sections outright rather than a subquotient; its finiteness is a separate argument. So
`Hn(Pn, O(d))` is covered for every `n >= 1`, at either sign of `d`, and `P0` is not. -/

/-! ## The twisting sheaf is invertible (#584, step 1)

`Divisors/Tensor.lean` is stated for a locally free rank-one factor, so `F(d) = F (x) O(d)` cannot
be built at all until `O(d)` is known invertible. The local triviality was already there --
`TwistCoherence.lean` needed the same degree-one charts to prove `O(d)` coherent -- so this is
`intShiftOverSelfIso` composed with `associatedSheafSelfIso` and handed to `of_trivializations`.

Route recorded: invertibility first, rather than avoiding the tensor via the graded shift. The
graded shift describes the twist of an *associated* sheaf only, and #570 needs an arbitrary
coherent F; it is kept as the computational special case.

The twist F(d) itself, its two coherence isomorphisms, and coherence-preservation are NOT here, so
#584 is not closed. -/

#print axioms AlgebraicGeometry.Proj.twistingSheafOverUnitIso
#print axioms AlgebraicGeometry.Proj.tensorTwistOverChartIso
#print axioms AlgebraicGeometry.Proj.twistingSheaf_isInvertible

/-! ## The twist F(d) = F (x) O(d) (#584, deliverables 1, 2a and 4)

The three deliverables that need nothing beyond the tensor product twistingSheaf_isInvertible made
applicable. tensorObjIso is the general half: tensorObj is not a bifunctor in this tree -- the
monoidal structure exists only on the invertible sheaves -- but tensorHom_id_id and
tensorHom_comp_tensorHom are exactly the functoriality an isomorphism needs.

F(d)(e) = F(d+e) is NOT here and cannot be got this way: tensorAssocIso requires BOTH outer factors
invertible, and no rearrangement of (F (x) O(d)) (x) O(e) through tensorCommIso avoids leaving a
non-invertible factor outermost. It needs the comparison with the graded shift, after which
sheafTwistAddIso finishes it with no associator at all. Coherence preservation waits on the same
comparison. Both land in the next section, on TwistComparison.lean. -/

#print axioms AlgebraicGeometry.Scheme.Modules.tensorObjIso
#print axioms AlgebraicGeometry.Proj.tensorTwist
#print axioms AlgebraicGeometry.Proj.tensorTwistZeroIso
#print axioms AlgebraicGeometry.Proj.associatedSelfTensorTwistIso

/-! ## The comparison F (x) O(d) = F(d), and deliverables 2b and 3 (#584)

The generator route Divisors/AssociatedSheaf/Construction.lean runs for the Cartier statement is
unavailable here: it needs BOTH tensor factors invertible so that the unit generates the tensor,
and F is arbitrary. What replaces it is stronger. Over an open inside a degree-one chart A(d) IS
the structure sheaf, so the twisted multiplication is already BIJECTIVE on sections, not merely a
local weak equivalence -- twistMultiplicationHom_app_eq factors it as (1 (x) psi), the right
unitor, and phi inverse, for the two chart trivializations. So the local input to W_of_coversTop
is an isomorphism and no local injectivity or surjectivity is proved by hand.

The content of that factorization is one identity on sections, and it is four lines on top of
intShiftZeroModuleLinearEquiv_twistMul: both trivializations are multiplication by the same
scalar, so what is left is associativity of that action.

sectionLinearEquivOfMemIff is the section-level counterpart of linearEquivOfMemIff -- both
trivializations land at the (0)-twist rather than at the module, and intShift 0 has the same
members, so the underlying element never moves and only the certificate is rebuilt.

With the comparison, F(d)(e) = F(d+e) is sheafTwistAddIso and needs no associator, and coherence
preservation goes through the graded side, where intShiftModuleOverSelfIso trivializes the twist
on a chart -- it is not visible through the tensor, which is why it waited.

SCOPE: F is an ASSOCIATED sheaf. Identifying an arbitrary coherent sheaf on Proj with an
associated one is Serre's theorem, which is downstream; TwistInvertible.lean records the same
boundary. -/

#print axioms AlgebraicGeometry.Proj.sectionLinearEquivOfMemIff
#print axioms AlgebraicGeometry.Proj.twistMul_zero_eq_smul
#print axioms AlgebraicGeometry.Proj.chartRingTwistSectionEquiv
#print axioms AlgebraicGeometry.Proj.chartModuleTwistSectionEquiv
#print axioms AlgebraicGeometry.Proj.chartModuleTwistSectionEquiv_sectionTwistMul
#print axioms AlgebraicGeometry.Proj.chartTensorEquiv
#print axioms AlgebraicGeometry.Proj.twistMultiplicationHom_app_eq
#print axioms AlgebraicGeometry.Proj.isIso_twistMultiplicationHom_app
#print axioms AlgebraicGeometry.Proj.isIso_toPresheaf_map_twistMultiplicationHom_app
#print axioms AlgebraicGeometry.Proj.twistMultiplicationHom_mem_W
#print axioms AlgebraicGeometry.Proj.isIso_sheafification_map_twistMultiplicationHom
#print axioms AlgebraicGeometry.Proj.tensorTwistIso
#print axioms AlgebraicGeometry.Proj.tensorTwistAddIso
#print axioms AlgebraicGeometry.Proj.intShiftModule_isCoherent
#print axioms AlgebraicGeometry.Proj.tensorObj_twistingSheaf_isCoherent
#print axioms AlgebraicGeometry.Proj.associatedTensorTwistIso
#print axioms AlgebraicGeometry.Proj.associatedTensorTwistAddIso
#print axioms AlgebraicGeometry.Proj.tensorTwist_isCoherent
#print axioms AlgebraicGeometry.Proj.twistingSheafTensorAddIso

/-! ## Homogeneous elements as sections of the twist (#585 prerequisite)

#585 asks that f^n . s extend to a global section of F(n). That statement could not be WRITTEN
against the tree: multiplying a section of an arbitrary F by a homogeneous element needs a map
F -> F(n) and none existed. #584 gave the twist; these give the multiplication into it.

A degree-n element of the module is a GLOBAL section of M(n)~, not one over a basic open: the
fraction is m/1, the denominator 1 has degree 0, and a degree-n element lies in degree 0 of the
shifted grading. Nothing is inverted, so the fraction is valid everywhere and restriction does not
move it -- which is why the compatibility is rfl and no basicOpen_one transport appears.

unitToTwist reads that family through unitHomEquiv (a global section IS a map out of the unit) and
twistBy tensors with F and cancels the unit. F is ARBITRARY -- not an associated sheaf. #584's
comparison stops at associated sheaves and #585 may not inherit that limit; its acceptance criteria
forbid the hypothesis outright, and nothing here uses the comparison.

unitToTwist_app_one is load-bearing, not decoration: unitHomEquiv.symm is an equivalence's inverse,
so a wrong sectionsOfMem would typecheck and go unnoticed at every use site. It pins 1 |-> m/1.

The extension theorem itself is NOT here. It needs the degree-one chart cover and quasi-coherence
on each chart; it is Proj/Modules/Glue.lean's exists_globalSection_twistBy, which closed #585.
Note it does NOT need exists_pow_smul_mem_of_isLocalized_radical, which the plan expected. -/

#print axioms AlgebraicGeometry.Proj.mem_intShift_zero_of_mem
#print axioms AlgebraicGeometry.Proj.sectionOfMem
#print axioms AlgebraicGeometry.Proj.fracPow
#print axioms AlgebraicGeometry.Proj.fracPow_smul_sectionOfMem
#print axioms AlgebraicGeometry.Proj.sectionOfMem_apply
#print axioms AlgebraicGeometry.Proj.sectionsOfMem
#print axioms AlgebraicGeometry.Proj.unitToTwist
#print axioms AlgebraicGeometry.Proj.unitToTwist_app_one
#print axioms AlgebraicGeometry.Proj.twistBy

/-! ## The two charts' multiplications differ by a MORPHISM (#585 glue)

The comparison #585 needs between charts: over D+(g), multiplying by f^n is multiplying by f^n/g^n
and then by g^n. The correction is carried as a morphism out of the unit, NOT as a scalar.

That is forced, not stylistic. The scalar form needs the scalar to cross tensorHom at the next
step and it cannot: Linear Gamma(X, top) X.PresheafOfModules does not synthesize, and supplying it
would mean a Gamma-linear structure on presheaves, linearity of toPresheafOfModules and of
associatedSheaf, and a MonoidalLinear instance -- none of which exist. As a morphism the next step
only needs tensorHom (1 F) - to be FUNCTORIAL (tensorHom_id_comp), which it is.

D+(g) is used as an OPEN SUBSCHEME, not through degreeOneChart: by ι_image_top its sections over
top are definitionally sections of the structure sheaf over D+(g), so no GammaSpecIso and no
degree-zero away ring appear here at all.

chartUnitToTwist_app_one is load-bearing for the same reason unitToTwist_app_one is one level
down -- restrictUnitIso and the restriction functor are both crossed before anything is applied.

One step changes shape rather than content: Scheme.Modules.restrict_smul_eq moves the equation from
the restricted sheaf's scalar action to the Proj one, which is where step A's pointwise lemma
lives. That lemma is rfl -- the two actions ARE definitionally equal, and it is recorded here
because an earlier draft of this file claimed the opposite. What is true, and much narrower, is
only that ι_appIso is proved by ofRestrict_appIso (ext1 then simp only), not by rfl; that says
nothing about the actions being defeq. The lemma earns its place by shape alone: Mathlib's
smul_restrictAppIso_hom_apply wraps the same fact in two restrictAppIso.hom applications, and the
bare form is what matches a goal written the obvious way. -/

#print axioms AlgebraicGeometry.Scheme.Modules.restrict_smul_eq
#print axioms AlgebraicGeometry.Proj.fracPowSection
#print axioms AlgebraicGeometry.Proj.pow_mem_deg
#print axioms AlgebraicGeometry.Proj.chartOpen
#print axioms AlgebraicGeometry.Proj.chartRestrictFunctor
#print axioms AlgebraicGeometry.Proj.chartUnitToTwist
#print axioms AlgebraicGeometry.Proj.chartOpen_image_le
#print axioms AlgebraicGeometry.Proj.chartFracPowAt
#print axioms AlgebraicGeometry.Proj.chartFracPowSections
#print axioms AlgebraicGeometry.Proj.chartUnitToTwist_app_one
#print axioms AlgebraicGeometry.Proj.chartFracPowMul
#print axioms AlgebraicGeometry.Proj.chartUnitToTwist_eq

/-! ## The same factorisation on an arbitrary F over the chart (#585 glue, step C)

chartTwistBy is twistBy for a module sheaf on D+(g); chartTwistBy_eq is chartUnitToTwist_eq
tensored with F. The ONLY input beyond it is that tensorHom (1 F) - preserves composition
(tensorHom_id_comp) -- never that it is linear, which it is not. That is the payoff of carrying
the correction as a morphism rather than a scalar.

The correction is conjugated by the right unitor, not left in front. tensorHom lands in F (x) 1,
so rho.inv followed by tensorHom (1 F) - cannot be pulled out of chartTwistBy's composite as it
stands; chartFracPowOn conjugates it back onto F and the two unitors cancel mid-proof.

The final step is congrArg, not rw. The pattern IS syntactically present, but the goal mentions
(D+(g) as a scheme).ringCatSheaf and so is not type-correct under the instances transparency
level, which stops rw and simp only matching inside it. congrArg works by defeq. Same failure mode
as the one recorded for restrict_smul_eq; it is a property of these goals, not of either lemma.

NOT here: identifying chartFracPowOn with multiplication by the section f^n/g^n on F (needs the
right unitor on sections), and comparing chartTwistBy (F.restrict) with the restriction of
twistBy F (needs restriction to commute with tensor). This whole route was abandoned: Glue.lean
reaches #585 on sections instead, and these three have no consumer. -/

#print axioms AlgebraicGeometry.Proj.chartTwistBy
#print axioms AlgebraicGeometry.Proj.chartFracPowOn
#print axioms AlgebraicGeometry.Proj.chartTwistBy_eq

/-! ## The overlap comparison, on SECTIONS and on Proj itself (#585 step D core)

twistBy_app is what twistBy does to a section -- the section-level counterpart of
unitToTwist_app_one, one tensor up. Until tensorUnitRight_inv_tensorHom_app existed, nothing in the
tree said what any part of twistBy does to a section, and twistBy was opaque at every use site.

twistBy_app_eq_smul is the agreement #585's glue needs: over an open inside D+(g), twisting a
section by f^n is twisting by g^n and scaling by f^n/g^n. It is stated on Proj DIRECTLY -- no
restriction functor and no chart appear.

That is the point of stating it here rather than deriving it from chartTwistBy_eq. The
morphism-level route lives on the open subscheme, and turning its conclusion back into a statement
about sections of F(n) on Proj would need restriction to commute with the sheafified tensor
product. No such compatibility exists in this repository or in Mathlib. Carrying the comparison on
sections from the start avoids needing it.

The proof is three rewrites and no geometry: twistBy_app twice, smul_tmulSection to push the scalar
onto the twist factor, and step A lifted to sections. The geometry was spent in #751.

NOT here: the cover, the single exponent across it, and the gluing; those are Glue.lean, which
closed #585. twistBy_app_eq_smul is superseded there by FracSection's twistBy_app_eq_smul', the
same comparison for two homogeneous elements of the same degree. -/

#print axioms AlgebraicGeometry.Proj.twistBy_app
#print axioms AlgebraicGeometry.Proj.fracPowSection_smul_sectionOfMem
#print axioms AlgebraicGeometry.Proj.twistBy_app_eq_smul

/-! ## Clearing a denominator on an affine (#585 chart-local engine)

A section of a quasi-coherent sheaf over D(r), times a high enough power of r, is the restriction
of a GLOBAL section. On Proj a degree-one chart is Spec of the degree-zero away ring, D+(f) meets
it in the basic open of f/g, and this clears that denominator.

Six lines, by an instance rather than an argument: Mathlib carries IsLocalizedModule.Away f on
tilde.toOpen, so sections over D(r) ARE the localization M_r and clearing the denominator is
IsLocalizedModule.surj -- a section is m/r^n by the definition of the localization, not by a
theorem about it. The passage to a global section is toOpen_res, which is rfl.

Recorded against the plan #585 was written to: exists_pow_smul_mem_of_isLocalized_radical, which
was extracted into Algebra/Module/LocalizedRadical.lean for this issue, is NOT needed here -- and
in the end #585 did not use it anywhere. The plan expected it to reconcile two charts on their
overlap; separatedness on the degree-two chart of g_i g_j did that instead.

The isQuasicoherent form drops the tilde hypothesis by transporting across fromTildeGamma, which
quasi-coherence makes an isomorphism. Four of its six lines are spelling: modulesSpecToSheaf lands
in an INDUCED category so .val does not project; presheaf.map has two syntactic spellings and rw
matches syntactically; and map_smul inside the Scheme.Modules namespace resolves to a different
lemma, needing _root_.map_smul.

The Proj chart application, one n across a finite cover, and the passage to multiplication into
F(n) are NOT here; they are ChartExtension.lean and Glue.lean, where #585 is closed. -/

#print axioms AlgebraicGeometry.tilde.exists_pow_smul_eq_toOpen
#print axioms AlgebraicGeometry.tilde.exists_pow_smul_eq_res_of_top
#print axioms AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_res_of_top_of_isQuasicoherent
-- The injectivity companion, and the transport factored once. Extension makes a local section
-- global; exists_pow_smul_res_eq_zero says a global section restricting to 0 on D(r) is killed by
-- a power of r. Together they are what a gluing argument over a cover needs. The second rests on
-- Mathlib's isIso_toOpen_top, so every section over top is toOpen m and the elementwise statement
-- applies.
--
-- tildeGammaSectionEquiv names the quasi-coherence isomorphism on sections as a LinearEquiv, with
-- its two restriction laws, so the transport is proved once rather than per statement. Written by
-- hand the second transport does NOT go through: rw fails on patterns that print
-- character-identical to the goal, because the difference is inside the elided le_top proof terms
-- and rw does not see proof irrelevance; simp only does not match either. congrArg .trans does,
-- since exact unifies up to defeq. Separately, inside these namespaces the bare names map_smul and
-- map_zero resolve to OTHER lemmas and must be written _root_-qualified.
#print axioms AlgebraicGeometry.tilde.exists_pow_smul_eq_zero
#print axioms AlgebraicGeometry.tilde.exists_pow_smul_res_eq_zero
#print axioms AlgebraicGeometry.Scheme.Modules.tildeΓSectionEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.tildeΓSectionEquiv_res
#print axioms AlgebraicGeometry.Scheme.Modules.tildeΓSectionEquiv_symm_res
#print axioms AlgebraicGeometry.Scheme.Modules.exists_pow_smul_res_eq_zero_of_isQuasicoherent
#print axioms AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_of_res_eq_of_isQuasicoherent

/-! ## The degree-one chart, as seen by the affine extension lemma (#585 chart step)

A section of a quasi-coherent F over D+(g) inf D+(f) extends to D+(g) after clearing a power of
f/g. The algebra is the affine lemma above; here is the geometry that lets it be applied, and the
naming that lets it elaborate.

The geometry is two rewrites: the chart covers exactly D+(g), and meets D+(f) in D+(g) inf D+(f).
Both fall out of image_preimage_eq_opensRange_inf and opensRange_awayi, with
awayi_preimage_basicOpen naming the element -- for f and g both of degree one it is exactly f/g.
Translating sections across the chart is free, because restrictAppIso is Iso.refl.

The naming is NOT cosmetic. Stated inline, IsIso (F.restrict (degreeOneChart)).fromTildeGamma does
not elaborate: isDefEq runs past 1.6M heartbeats and gives up, and pinning arguments explicitly
(instance-transparency technique 7) does not rescue it. Technique 5 fixes it in two steps, and the
second is easy to miss: chartRestrict names the restriction at an explicit result type, which by
itself converts the timeout into a fast precise mismatch -- fromTildeGamma quantifies over
Spec (.of (coe R)) with R : CommRingCat and Lean cannot invert the coercion -- and the result type
is then written through chartRing, a reducible abbrev for the bundled ring, so R matches
syntactically. That diagnostic shift is the real argument for the technique.

Choosing one n across a finite cover, and the passage to multiplication into F(n), are NOT here;
they are ChartExtension.lean's uniform trio and Glue.lean, where #585 is closed. -/

#print axioms AlgebraicGeometry.Proj.chartRing
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_res_chart
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_res_chart_of_le
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_res_chart_uniform

/-! ## The same three, for AGREEMENT rather than extension (#585 glue)

Two charts' twisted sections are only visibly equal where D+(f) reaches: there each restricts to
the same twistBy f^n of s. But TopCat.Sheaf.IsCompatible demands agreement on the whole pairwise
overlap D+(g_i) inf D+(g_j), which is NOT contained in D+(f). The standing plan for #585 says
agreement is "immediate"; it is immediate only on the overlap WITH D+(f), and closing that distance
costs a second exponent.

These three mirror the extension trio with exists_pow_smul_eq_of_res_eq_of_isQuasicoherent in place
of the extension lemma: one gets an exponent per pair, one raises it, one unifies over a finite
family. The uniform version's index is deliberately arbitrary rather than the chart index, because
agreement must be forced on every PAIR at once and a pair type is what gets passed.

The first is six lines for the same reason its extension sibling is: on a degree-one chart the
sections over D(f/g) are a localization of the sections over the whole chart. -/


/-! ## Fractions with an arbitrary numerator, and the twist comparison they give (#585)

TwistBridge and TwistApp carry f^n/g^n for f and g of degree one. #585's glue needs the same
statements for an arbitrary pair of homogeneous elements of the SAME degree, because the extension
exponent n and the agreement exponent m are independent: the section that finally glues is
twistBy (f^m * g_i^n) of the chart extension, and comparing two of those across an overlap needs
the fraction f^m g_j^n / g_i^(n+m). No power of a single element has that shape.

frac and fracSection are a/b at a point of D+(b) and as a section over any open inside D+(b);
fracPow and fracPowSection are the special case a = f^n, b = g^n, and the bridging lemma is rfl.

frac_eq is the workhorse for the bookkeeping: two fractions with the same VALUE are the same
element whatever degrees they are written in, so (f^d)^n from a chart's distinguished element and
f^(d*n) from a twist need no transport between them.

twistBy_app_eq_smul' is twistBy_app_eq_smul for two homogeneous elements of the same degree; the
older lemma is its a = f^n, b = g^n case. -/

#print axioms AlgebraicGeometry.Proj.frac
#print axioms AlgebraicGeometry.Proj.basicOpen_le_basicOpen_pow
#print axioms AlgebraicGeometry.Proj.fracSection
#print axioms AlgebraicGeometry.Proj.fracPowSection_eq_fracSection
#print axioms AlgebraicGeometry.Proj.pow_mem_smul
#print axioms AlgebraicGeometry.Proj.frac_eq
#print axioms AlgebraicGeometry.Proj.fracSection_eq
#print axioms AlgebraicGeometry.Proj.frac_pow
#print axioms AlgebraicGeometry.Proj.fracSection_mul
#print axioms AlgebraicGeometry.Proj.frac_smul_sectionOfMem
#print axioms AlgebraicGeometry.Proj.fracSection_smul_sectionOfMem
#print axioms AlgebraicGeometry.Proj.twistBy_app_eq_smul'

/-! ## The chart of an element of any positive degree (#585 overlaps)

ChartExtension works with degree-one charts, which is what #585's cover is made of. Its PAIRWISE
OVERLAPS are not: D+(g_i) inf D+(g_j) = D+(g_i g_j) and g_i g_j has degree two. Forcing two chart
extensions to agree on an overlap is an affine statement over that chart, so the same restriction
has to exist one degree up.

awayRestrict is chartRestrict for g in A_d with 0 < d, with the same instance-transparency
discipline and for the same reason; chartRestrict is its d = 1 case by definition. The extension
half is not repeated -- #585 extends only across degree-one charts. -/

#print axioms AlgebraicGeometry.Proj.awayRestrict
#print axioms AlgebraicGeometry.Proj.awayRestrict_isQuasicoherent
#print axioms AlgebraicGeometry.Proj.isIso_fromTildeΓ_awayRestrict
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_away
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_away_of_le
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_away_uniform

/-! ## The chart's scalar, read on Proj (#585 dictionary)

#585's two halves speak different languages. ChartExtension produces sections of a chart and clears
the chart ring's element isLocalizationElem; TwistApp compares twists of sections of F on Proj and
scales by a structure-sheaf section. This is the dictionary, and it was the last genuinely open
step of the issue.

Nothing moves on the module side: restrictAppIso is Iso.refl, so the chart's sections ARE sections
of F over the chart's image. What differs is the ring acting, and the comparison map is Mathlib's
awayToSection.

Two independent facts. awayToSection_isLocalizationElem_pow is elementary once the shapes line up:
the base case is rfl, awayToSection is a ring hom, and the structure sheaf's ring operations are
pointwise. GammaSpecIso_inv_appIso_inv is the one that costs something -- the scalar action reaches
Gamma(Proj, D+(g)) through Scheme.GammaSpecIso and the open immersion's appIso, and nothing in
Mathlib says that composite is awayToSection. It is proved by unfolding awayiota into
basicOpenIsoSpec.inv followed by the open inclusion and quoting basicOpenToSpec_app_top, the single
place Mathlib pins awayToSection against the scheme structure.

It needs backward.isDefEq.respectTransparency false, as Mathlib's own basicOpenIsoAway does:
without it the goal is reported as not type-correct under instances transparency after the first
rewrite and every later rw, Category.assoc included, silently fails to match.

The cover, the single exponent across it, and the gluing are NOT here; they are Glue.lean, which
closed #585. -/

#print axioms AlgebraicGeometry.Proj.structureSheaf_pow_apply
#print axioms AlgebraicGeometry.Proj.isLocalizationFrac
#print axioms AlgebraicGeometry.Proj.awayToSection_isLocalizationElem_apply
#print axioms AlgebraicGeometry.Proj.awayToSection_isLocalizationElem_pow
#print axioms AlgebraicGeometry.Proj.awayι_image_top
#print axioms AlgebraicGeometry.Proj.awayι_image_le
#print axioms AlgebraicGeometry.Proj.awayι_image_basicOpen
#print axioms AlgebraicGeometry.Proj.ΓSpecIso_inv_appIso_inv
#print axioms AlgebraicGeometry.Proj.ΓSpecIso_inv_res_appIso_inv
#print axioms AlgebraicGeometry.Proj.chart_smul_eq
#print axioms AlgebraicGeometry.Proj.isLocalizationElem_pow_smul_eq

/-! ## The chart lemmas, restated on Proj (#585)

ChartExtension and AwayChart state extension and agreement in the chart's own coordinates; the glue
consumes them on Proj -- sections of F over opens of Proj, scaled by a structure-sheaf section.

The transport is a SUBSTITUTION, not a transport. restrictAppIso is Iso.refl, so the chart's
sections already ARE sections of F over the chart's image; what is left is that the glue wants the
opens spelled D+(g) and D+(g) inf D+(f) rather than as chart images, and those are equal only
propositionally. Each statement here therefore takes the opens as VARIABLES with an equation
pinning them to the chart's images; subst turns the statement into the chart's own, and the caller
instantiates at whatever spelling it wants. Restriction maps and inequality proofs come along for
free, because morphisms of Opens are proof-carrying data in a poset.

The hypotheses are oriented "chart image = W" and not "W = chart image" because subst eliminates
the variable, and the variable has to be the one that disappears.

The cover, the twist that puts the family into one sheaf, and the gluing are NOT here. -/

#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_res_image
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_res_image_uniform
#print axioms AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_image_uniform

/-! ## #585: a section over D+(f), twisted, extends to Proj

exists_globalSection_twistBy is the deliverable of #585 and the thing six earlier PRs built the
ingredients for: for F quasi-coherent, f of degree one and a finite family of degree-one elements
generating A over A_0, every section over D+(f) has an N with twistBy (f^N) of it the restriction
of a GLOBAL section of F(N).

The two exponents are independent and both are needed. n extends s across each chart; that is all
the geometry there is, and it is not enough, because IsCompatible wants the extensions to agree on
the WHOLE overlap D+(g_i) inf D+(g_j) and D+(f) is not contained in it. The second exponent closes
that: t_i and (g_j/g_i)^n t_j DO agree on the overlap intersected with D+(f) -- the computation
where the two charts' different denominators cancel -- so separatedness on the overlap, which is
the chart of g_i g_j and therefore of degree two, gives m.

The section that glues is twistBy (f^(2m) * g_i^n) of the chart extension, NOT twistBy (g_i^N).
That choice keeps the whole comparison inside F(N): over an overlap the fraction
f^(2m) g_i^n / (g_i g_j)^m g_i^n is exactly the scalar the agreement supplies, and over
D+(g_i) inf D+(f) the fraction f^N / f^(2m) g_i^n is exactly (f/g_i)^n. Twisting by g_i^N instead
would put the comparison in F(n) and force a passage from F(n)(2m) to F(N), which nothing in this
repository or in Mathlib provides.

The five restriction lemmas below are named because the proof composes restrictions constantly and
rw cannot be used on goals carrying show-ascription residue. -/

#print axioms AlgebraicGeometry.Proj.resSection_trans
#print axioms AlgebraicGeometry.Proj.resSection_smul
#print axioms AlgebraicGeometry.Proj.resΓ_fracSection
#print axioms AlgebraicGeometry.Proj.homApp_res
#print axioms AlgebraicGeometry.Proj.le_basicOpen_mul
#print axioms AlgebraicGeometry.Proj.exists_globalSection_twistBy_of_data
#print axioms AlgebraicGeometry.Proj.exists_overlap_exponent
#print axioms AlgebraicGeometry.Proj.exists_globalSection_twistBy

/-! ## #586: one twist exponent for a whole finite family

exists_globalSection_twistBy produces AN exponent, one per section. Serre's global generation needs
a SINGLE exponent serving every generator of every chart at once, because the surjection it builds,
free I -> F(N), has one target sheaf. exists_globalSection_twistBy_forall_ge upgrades the
existential to "every sufficiently large N works" and exists_globalSection_twistBy_uniform takes
the maximum over a finite family.

Raising is done on the CHART EXTENSIONS, not at the sheaf level, and that is the whole content. The
sheaf-level route -- multiply the global section of F(N) by f^(N'-N) and transport along
F(N)(N'-N) = F(N') -- is not available, and TensorTwist.lean already records why: tensorAssocIso
requires both OUTER tensor factors invertible, and no rearrangement of (F (x) O(d)) (x) O(e) under
tensorCommIso gets the non-invertible F off an outer slot. tensorTwistAddIso supplies the
composition for F an ASSOCIATED sheaf only, which is not the hypothesis here. Even granting the
isomorphism the argument would have to compute what it does to a section, which is what #585
established these witnesses cannot do.

This is the same move as ChartExtension.lean's exists_pow_smul_eq_res_chart_of_le, which raises the
extension exponent in the chart's own coordinates. Its existential form cannot be reused here: it
returns SOME extension at the larger exponent, and holding one overlap exponent m fixed needs the
raised family to be the original one times a KNOWN unit. Discard that relation and m has to be
re-derived at each n, which puts N = 2m(n) + n back out of reach.

One level down it is plain algebra in Gamma(F, -) on Proj. The extension at exponent n + k is the
extension at exponent n multiplied by (f/g_i)^k, a section of the structure sheaf over the WHOLE of
D+(g_i) because f and g_i both have degree one; the overlap discrepancy is therefore scaled by that
same unit, so ONE overlap exponent m serves every larger n. Hence N = 2m + n' is reachable for
every n' >= n, which is every N >= 2m + n.

The multiplier is (f/g_i)^k and not a fixed monomial. g_i is inverted on D+(g_i) and nowhere else,
and D+(g_i) is the only open where t_i is asked to say anything. A fraction with a different
denominator is still a legitimate section wherever ITS denominator is invertible, so the raised
statement would typecheck -- and be false, because that fraction vanishes somewhere on D+(g_i) and
the raised family would no longer extend s. The denominator is fixed by the chart, not chosen.

The two fraction identities are named because the degree bookkeeping is unreadable inline and
because each is used under a scalar action, where the ascription at Gamma(Proj A, U) is mandatory.

Generation, local surjectivity and free I are NOT here; the chart-local half of Serre's theorem is
below. -/

#print axioms AlgebraicGeometry.Proj.fracSection_pow_mul_isLocalizationFrac
#print axioms AlgebraicGeometry.Proj.fracSection_pow_mul_comm
#print axioms AlgebraicGeometry.Proj.exists_globalSection_twistBy_forall_ge
#print axioms AlgebraicGeometry.Proj.exists_globalSection_twistBy_uniform

/-! ## #586: epimorphisms from local preimages, and O(N) generated by g^N on D+(g)

Two independent pieces of the chart-local half of Serre's global generation.

epi_of_pointwise_preimages packages a four-link chain -- isLocallySurjective_iff, the sheaf-level
class, epi_of_isLocallySurjective, and epi_of_epi_map along toSheaf -- into the one criterion a
chart-by-chart argument actually wants. Its hypothesis is POINTWISE, not indexed by a cover, and
that is the point: no GrothendieckTopology.over appears anywhere, because a caller arguing chart by
chart is handed the point first and picks the chart around it. The reconnaissance for #586 recorded
the over-plumbing as a gap; it is not a gap, it is unnecessary, and Opens.mem_grothendieckTopology
being rfl is why.

Divisors/Effective.lean runs exactly this chain inline for one quotient map and hand-rolls the
faithfulness of the forgetful functor while doing it -- Mathlib's toSheaf Faithful instance plus
reflectsEpimorphisms_of_faithful already give it. That file is left alone here; folding it onto
this lemma is a separate cleanup.

exists_smul_sectionOfMem_eq exhibits the generator. O(N) is invertible and trivial on a degree-one
chart, so it is tempting to read this off twistingSheafOverUnitIso -- and that does not work, for
#585's reason: those isomorphisms are PROPERTY WITNESSES, NOT COMPUTATIONS. They say a
trivialization exists; they do not say that this section, g^N/1, is one. So the generator is
exhibited and the argument is made on fractions: isLocallyFraction gives w = r/s near the point, the
shift is a natural number so r sits in 𝒜 (i + N) honestly (mem_intShift_ofNat_iff), and the scalar
is r / (s * g^N) -- degree zero because s * g^N matches r's degree, and a section because both s and
g are invertible after shrinking to V' ⊓ D+(g). Cancelling g^N is one LocalizedModule.mk_eq with
witness 1, the same last step as frac_smul_sectionOfMem.

The shrinking is forced twice and neither cut is cosmetic: isLocallyFraction offers a fraction only
on SOME neighbourhood, and the denominator is invertible only where g is. Hence the conclusion
carries W and W ≤ V rather than asserting anything on V.

The tensor step -- passing from the O(N) factor to F(N) -- is NOT here. -/

#print axioms AlgebraicGeometry.Scheme.Modules.epi_of_pointwise_preimages
#print axioms AlgebraicGeometry.Proj.exists_smul_sectionOfMem_eq

/-! ## f^n on a degree-one chart is (f/g)^n (#585 bridge)

The bridge between #585's two halves. The chart step clears a power of f/g on the chart through g;
TwistSection multiplies by the global section f^n of O(n). These are the same thing, so the halves
meet with NO correction factor.

This comes BEFORE the glue, not after, which is the opposite of the obvious reading of #585. The
chart step produces, per chart, a section obtained by clearing a DIFFERENT scalar (f/g_i)^n. Those
are not sections of any one sheaf, so there is nothing to glue yet; twisting is what makes them
comparable, since each becomes a section of the single sheaf F(n).

The computation: intShiftZeroLinearEquiv_apply_mk on the constant fraction f^n/1 at d = n gives
d.toNat = n and (-d).toNat = 0, hence f^n * g^0 over 1 * g^n; ext and simp clean it to f^n/g^n. The
deg fields differ (0 + n against n) and it does not matter, because the embedding reads only
numerator and denominator. f^n/g^n is isLocalizationElem hg hf ^ n, exactly the scalar
exists_pow_smul_eq_res_chart clears.

The section level is a one-liner: both sides are pointwise, so it is the fibre statement applied at
the point. Same as #584's chartModuleTwistSectionEquiv_sectionTwistMul -- in this construction
lifting from fibres to sections is free and the cost is in the fraction identity underneath.

The glue is NOT here; it is Glue.lean and GlueUniform.lean, where #585 is closed. -/

#print axioms AlgebraicGeometry.Proj.intShiftZeroLinearEquiv_constFraction
#print axioms AlgebraicGeometry.Proj.intShiftSectionLinearEquivOn_sectionOfMem

#print axioms AlgebraicGeometry.Proj.intCechCochainsDegreewiseAddEquiv_symm_smul
#print axioms AlgebraicGeometry.Proj.intCech_d_apply_eq_zero_iff
#print axioms AlgebraicGeometry.Proj.intCechBlockIncl
#print axioms AlgebraicGeometry.Proj.intCechBlockD
#print axioms AlgebraicGeometry.Proj.intCechBlockCocycles
#print axioms AlgebraicGeometry.Proj.addCommGroupIntCechBlockCocycles
#print axioms AlgebraicGeometry.Proj.moduleIntCechBlockCocycles
#print axioms AlgebraicGeometry.Proj.module_finite_intCechBlockCocycles
#print axioms AlgebraicGeometry.Proj.intCechBlockCocycleHom
#print axioms AlgebraicGeometry.Proj.intCechBlockCocycleHom_apply
#print axioms AlgebraicGeometry.Proj.intCechBlockCocycleHom_comp_d
#print axioms AlgebraicGeometry.Proj.intCechBlockCycle
#print axioms AlgebraicGeometry.Proj.intCechBlockCycle_i
#print axioms AlgebraicGeometry.Proj.intCechBlockClass
#print axioms AlgebraicGeometry.Proj.intCechBlockSmul
#print axioms AlgebraicGeometry.Proj.intCechBlockSmul_comp_cocycleHom
#print axioms AlgebraicGeometry.Proj.intCechBlockSmul_comp_cycle
#print axioms AlgebraicGeometry.Proj.intCechBlockSmul_comp_class
#print axioms AlgebraicGeometry.Proj.intCechBlockClass_surjective
#print axioms AlgebraicGeometry.Proj.intTwistModules
#print axioms AlgebraicGeometry.Proj.intChart
#print axioms AlgebraicGeometry.Proj.intCechBlockClassLinear
#print axioms AlgebraicGeometry.Proj.module_finite_cechCohomology_intTwist
#print axioms AlgebraicGeometry.Proj.module_finite_linearCoherentH_projectiveSpaceTwist

/-! ### `Z(β,ω)` on a numerical class

The central charge composed with the Mukai vector, so route (A)'s conclusions —
the support property above all — become statements about classes rather than
about a quadratic space. -/

#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalCharge
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalCharge_apply
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalCharge_add
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.realForm_extendMap_mukaiVector
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiForm_neg_of_numericalCharge_eq_zero
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalCharge_ne_zero_of_nonneg
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mem_wall_iff_numericalCharge_eq_zero

-- #720 groundwork: the functor-level exactness the quasi-coherent extension
-- argument consumes. `tilde` exact is the kernel closure above, packaged.
#print axioms AlgebraicGeometry.quasicoherentι_preservesFiniteLimits
#print axioms AlgebraicGeometry.tilde_preservesFiniteLimits
#print axioms AlgebraicGeometry.qcι_preservesKernel
#print axioms AlgebraicGeometry.qcHasFiniteProducts
#print axioms AlgebraicGeometry.qcHasBinaryBiproducts
#print axioms AlgebraicGeometry.qcAbelian
#print axioms AlgebraicGeometry.moduleSpecSectionsFunctor
#print axioms AlgebraicGeometry.moduleSpecSectionsFunctor_preservesFiniteLimits
#print axioms AlgebraicGeometry.moduleSpecSectionsFunctor_preservesZeroMorphisms
#print axioms AlgebraicGeometry.affineΓ
#print axioms AlgebraicGeometry.shortExact_map_affineΓ
#print axioms AlgebraicGeometry.fromTildeΓShortComplexHom
#print axioms AlgebraicGeometry.fromTildeΓShortComplexHom_τ₁
#print axioms AlgebraicGeometry.fromTildeΓShortComplexHom_τ₂
#print axioms AlgebraicGeometry.fromTildeΓShortComplexHom_τ₃
#print axioms AlgebraicGeometry.isQuasicoherent_middle_affine
#print axioms AlgebraicGeometry.isQuasicoherent_middle
#print axioms AlgebraicGeometry.quasicoherent_isClosedUnderExtensions
#print axioms AlgebraicGeometry.quasicoherent_containsZero
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma_affine
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma
#print axioms AlgebraicGeometry.quasicoherent_isClosedUnderCoproducts

/-! ## The numerical charge, bundled, and its bridge to the categorical side

`numericalCharge` was proved additive and left unbundled, which is what kept the numerical
lane from meeting the stability-function side — every charge there is an `AddMonoidHom`, and
an equation is not one. `numericalCharge_zero` did not exist at all and is free once the hom
does.

`toMukaiChargeData` builds the categorical class map as a composition of homs, so
`charge_toMukaiChargeData` is definitional: the categorical charge of an object IS the
numerical charge of its class. That is the lemma that makes the numerical support-property
theorems reachable from an object of an abelian category.
-/

#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalChargeHom
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalChargeHom_apply
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.numericalCharge_zero
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.toMukaiChargeData
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.toMukaiChargeData_mukai
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.charge_toMukaiChargeData

/-! ## The Euler radical against the kernel of the Mukai vector

`CategoricalCharge` records the numerical quotient as bypassed: the geometric class map lands
in `N ⧸ leftRadical` while `numericalCharge` is defined on `N`. This settles what closing that
costs. One inclusion is free — `ker_le_leftRadical` follows from `mukaiForm_eq_neg_chi₂` with
no nondegeneracy anywhere. The other is not, and is not true as stated: membership in
`leftRadical` only says the Mukai vector pairs to zero against the **image** of the Mukai
vector, so `DetectsRadical` carries the missing nondegeneracy as a named hypothesis rather
than a pretended theorem — and `detectsRadical_of` reduces it to a point class, a rank-one
class with vanishing `c₁`, and nondegeneracy of `b` against realized Chern classes, so it is
not the conclusion renamed. `mukaiVectorQuotient` is what it buys.
-/

#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiForm_eq_zero_iff_chi₂_eq_zero
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.ker_le_leftRadical
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.DetectsRadical
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.detectsRadical_of
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.leftRadical_le_ker
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.leftRadical_eq_ker
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiVectorQuotient
#print axioms AlgebraicGeometry.Numerical.K3.AdditiveMukaiData.mukaiVectorQuotient_mk
#print axioms AlgebraicGeometry.moduleFinite_sections_restrict_of_isCoherent
#print axioms SheafOfModules.GeneratingSections.ofFreeEpi
#print axioms SheafOfModules.GeneratingSections.isFiniteType_ofFreeEpi
#print axioms SheafOfModules.GeneratingSections.ofFreeEpi_π
