/-
Tilting slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## Tilting lane — torsion pairs in an abelian category

Mathlib has no torsion pair for abelian categories at the pin, so this is built
from scratch. Pure abelian-category theory: no foundational library import, no geometry. The
Happel-Reiten-Smalo tilt itself is NOT here; see the module docstring. -/

#print axioms Tilting.TorsionPair
#print axioms Tilting.TorsionPair.isZero_of_tors_of_free
#print axioms Tilting.TorsionPair.tors_iff
#print axioms Tilting.TorsionPair.free_iff
#print axioms Tilting.TorsionPair.free_of_mono
#print axioms Tilting.TorsionPair.tors_of_epi
#print axioms Tilting.TorsionPair.tors_of_shortExact
#print axioms Tilting.TorsionPair.free_of_shortExact
#print axioms Tilting.TorsionPair.exists_factor_of_tors
#print axioms Tilting.TorsionPair.allTors
#print axioms Tilting.TorsionPair.allFree

/-! ## Tilting lane — torsion pairs on a heart, and the tilted aisles

The aisles are defined by HOM-ORTHOGONALITY, not with a cohomology functor.
Mathlib has no bundled `H^n` functor into the heart at the pin. This project
now constructs one and proves it homological, but that later result does not
change the original aisle definition. `zero'` is proved here;
`exists_triangle_zero_one` is NOT, and is not declared with `sorry`. -/

#print axioms Tilting.HeartTorsionPair
#print axioms Tilting.HeartTorsionPair.tiltLE
#print axioms Tilting.HeartTorsionPair.tiltGE
#print axioms Tilting.HeartTorsionPair.tiltLE_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.tiltGE_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.exists_factor_truncGE
#print axioms Tilting.HeartTorsionPair.factor_truncGE_unique
#print axioms Tilting.HeartTorsionPair.tors_of_orthogonal
#print axioms Tilting.HeartTorsionPair.hom_eq_zero_of_tiltLE_of_tiltGE

/-! ## Tilting lane — the indexed aisle families

The shift and inclusion fields of the tilted t-structure. Note
`tiltAt_zero'` ends in an apostrophe: `scripts/check_audit.py` has a regression
test for exactly that parse hazard. -/

#print axioms Tilting.HeartTorsionPair.torsOrth
#print axioms Tilting.HeartTorsionPair.freeOrth
#print axioms Tilting.HeartTorsionPair.torsOrth_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.freeOrth_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.tiltLEAt
#print axioms Tilting.HeartTorsionPair.tiltGEAt
#print axioms Tilting.HeartTorsionPair.tiltLEAt_zero_iff
#print axioms Tilting.HeartTorsionPair.tiltGEAt_one_iff
#print axioms Tilting.HeartTorsionPair.tiltLEAt_shift
#print axioms Tilting.HeartTorsionPair.tiltGEAt_shift
#print axioms Tilting.HeartTorsionPair.tiltLEAt_zero_le
#print axioms Tilting.HeartTorsionPair.tiltGEAt_one_le
#print axioms Tilting.HeartTorsionPair.tiltAt_zero'

/-! ## Tilting lane — recognising the two aisles from a triangle

The two halves of `exists_triangle_zero_one`. Neither needs a cohomology
functor; the module docstring records why the textbook construction appeared to
and this one does not. -/

#print axioms Tilting.HeartTorsionPair.tiltLE_of_triangle
#print axioms Tilting.HeartTorsionPair.tiltGE_of_triangle
#print axioms Tilting.HeartTorsionPair.tiltLEAt_zero_of_triangle
#print axioms Tilting.HeartTorsionPair.tiltGEAt_one_of_triangle

/-! ## Tilting lane — the Happel-Reiten-Smalo tilt

`tilt` is a genuine Triangulated.TStructure: every field is proved, none is
sorry-backed, and no cohomology functor appears in the construction. Note
`tilt` is a `def`, so its clean axiom line reports the axiom closure of a
CONSTRUCTION -- the theorems it is built from are the six field lemmas above
and below. -/

#print axioms Tilting.HeartTorsionPair.tiltLEAt_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.tiltGEAt_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.exists_tilt_triangle_of_data
#print axioms Tilting.HeartTorsionPair.exists_tilt_triangle
#print axioms Tilting.HeartTorsionPair.tilt
#print axioms Tilting.HeartTorsionPair.tilt_le
#print axioms Tilting.HeartTorsionPair.tilt_ge
#print axioms Tilting.HeartTorsionPair.tilt_le_zero_iff

/-! ## Tilting lane — textbook agreement for the tilted aisles

The dual factorisation pair and `free_of_orthogonal` complete the counit
substitutes on both sides, and the four agreement theorems tie the
Hom-orthogonal aisles to the textbook `H⁰` formulation, with `τ^{≥0}` and
`τ^{≤0}` in the role of `H⁰`. Closes the review finding F1 of #86 (#94). -/

#print axioms Tilting.HeartTorsionPair.exists_factor_truncLE
#print axioms Tilting.HeartTorsionPair.factor_truncLE_unique
#print axioms Tilting.HeartTorsionPair.free_of_orthogonal
#print axioms Tilting.HeartTorsionPair.torsOrth_iff_tors_truncGE
#print axioms Tilting.HeartTorsionPair.freeOrth_iff_free_truncLE
#print axioms Tilting.HeartTorsionPair.tiltLE_iff_tors_truncGE
#print axioms Tilting.HeartTorsionPair.tiltGE_iff_free_truncLE

/-! ## Tilting lane — the tilted heart identified

`tilt_heart_iff` is the textbook `A† = ⟨F⟦1⟧, T⟩` in the single-step form
exact for a torsion pair: membership in the tilted heart is exactly being an
extension of a torsion object by a shifted torsion-free one. Closes #106
under the #81 weak-stability epic; abstract, bound to no source coordinate. -/

#print axioms Tilting.HeartTorsionPair.tilt_heart_of_triangle
#print axioms Tilting.HeartTorsionPair.exists_triangle_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.tilt_heart_iff

/-! ## Tilting lane — original and tilted heart cohomology bridge

The t-structure-only cohomology functor applies to both hearts.  A tilted-heart
object has the canonical torsion-free `H⁻¹` and torsion `H⁰` factors, whose
truncation triangle is a short exact sequence in the tilted heart; its maps
are exposed as a kernel and a cokernel.  The arbitrary-short-exact six-term
cohomology sequence remains deliberately undeclared. -/

#print axioms Tilting.originalHeartCohFunctor
#print axioms Tilting.originalHeartCohFunctor_additive
#print axioms Tilting.originalHeartCoh
#print axioms Tilting.originalHeartCohIsoOfHeart
#print axioms Tilting.HeartTorsionPair.tiltedHeartCohFunctor
#print axioms Tilting.HeartTorsionPair.tors_zero
#print axioms Tilting.HeartTorsionPair.free_zero
#print axioms Tilting.HeartTorsionPair.isLE_zero_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.isGE_neg_one_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.tors_truncGE_zero_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.free_truncLT_zero_shift_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.originalHMinusOne
#print axioms Tilting.HeartTorsionPair.originalHZero
#print axioms Tilting.HeartTorsionPair.originalHMinusOne_free
#print axioms Tilting.HeartTorsionPair.originalHZero_tors
#print axioms Tilting.HeartTorsionPair.originalHeartCohIsoHMinusOne
#print axioms Tilting.HeartTorsionPair.originalHeartCohIsoHZero
#print axioms Tilting.originalCohomologyShiftIso
#print axioms Tilting.originalCohomologyTriangle
#print axioms Tilting.originalCohomologyTriangle_distinguished
#print axioms Tilting.HeartTorsionPair.free_shift_mem_tilt_heart
#print axioms Tilting.HeartTorsionPair.tors_mem_tilt_heart
#print axioms Tilting.HeartTorsionPair.originalHMinusOneShiftInTiltHeart
#print axioms Tilting.HeartTorsionPair.objectInTiltHeart
#print axioms Tilting.HeartTorsionPair.originalHZeroInTiltHeart
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex_shortExact
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex_f_isKernel
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex_g_isCokernel

/-! ## TStructure lane — truncation functors commute with the shift -/

#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGE
#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGE_distinguished
#print axioms CategoryTheory.Triangulated.TStructure.isLE_shiftedTriangleLTGE_obj₁
#print axioms CategoryTheory.Triangulated.TStructure.isGE_shiftedTriangleLTGE_obj₃
#print axioms CategoryTheory.Triangulated.TStructure.exists_shiftedTriangleLTGE_iso
#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGEIso
#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGEIso_hom₂
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftIso
#print axioms CategoryTheory.Triangulated.TStructure.truncGEShiftIso
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftIso_hom_comp_truncLTι
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftIso_hom_comp_truncLTι_assoc
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_hom
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_hom_assoc
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_inv
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_inv_assoc
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftNatIso
#print axioms CategoryTheory.Triangulated.TStructure.truncGEShiftNatIso
#print axioms CategoryTheory.Triangulated.TStructure.truncLEShiftNatIso
#print axioms CategoryTheory.Triangulated.TStructure.truncGELEShiftNatIso
#print axioms Tilting.originalHeartCohUnderlyingShiftNatIso
#print axioms Tilting.originalHeartCohShiftNatIso

/-! ## Tilting lane — six-term original-heart cohomology sequence

Degree-zero cohomology of an arbitrary t-structure is proved homological.
The six-term sequence is then constructed for any triangle and specialized
to a short exact sequence in the tilted heart, with canonical identifications
of all six terms and unconditional exactness plus endpoint mono/epi. -/

#print axioms Tilting.OriginalHeartCohomologyIsHomological
#print axioms Tilting.originalHeartCohFunctor_isHomological
#print axioms Tilting.originalHeartCohFunctor_zero_shiftSequence
#print axioms Tilting.originalHeartCohShiftIso
#print axioms Tilting.originalHeartCoh_isZero_of_isGE
#print axioms Tilting.originalHeartCoh_isZero_of_isLE
#print axioms Tilting.originalHeartCohFunctor_shift_isZero_of_isGE
#print axioms Tilting.originalHeartCohFunctor_shift_isZero_of_isLE
#print axioms Tilting.originalHeartCohomologySixTermSequence
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₀Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₁Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₂Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₃Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₄Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₅Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_exact
#print axioms Tilting.originalHeartCohomologySixTermSequence_mono_first
#print axioms Tilting.originalHeartCohomologySixTermSequence_epi_last
#print axioms Tilting.HeartTorsionPair.exists_distinguished_triangle_of_shortExact
#print axioms Tilting.HeartTorsionPair.triangleOfShortExact
#print axioms Tilting.HeartTorsionPair.triangleOfShortExact_distinguished
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₀Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₁Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₂Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₃Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₄Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₅Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_exact
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_mono_first
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_epi_last
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_exact_with_endpoints
#print axioms Tilting.HeartTorsionPair.originalHMinusOne_isZero_of_tors
#print axioms Tilting.HeartTorsionPair.originalHZeroIsoOfTors
#print axioms Tilting.HeartTorsionPair.originalHZero_isZero_of_free_shift
#print axioms Tilting.HeartTorsionPair.originalHMinusOneShiftIsoOfHZeroIsZero
#print axioms Tilting.HeartTorsionPair.originalHMinusOneIsoOfFreeShift
#print axioms Tilting.HeartTorsionPair.exists_original_triangle_of_torsion_subobject_free_shift

/-! ## The abelian torsion pair of a stability function

`T β` and `F β` of `Foundation/StabilityFunction/Cutoff.lean` satisfy both
torsion-pair axioms: Hom-vanishing from `PhaseMonotone.lean`, and the splitting
from `Splitting.lean`. This is the abelian counterpart of the slicing pair in
`TorsionPair/Slope.lean`, and the form Bridgeland's §6 uses on `Coh X`. -/

#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTorsProperty
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnFreeProperty
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTorsProperty_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnFreeProperty_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTorsionPair
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTorsionPair_tors
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTorsionPair_free

/-! ## From the abelian torsion pair to the HRS input

`TorsionPair/Basic.lean` and `TorsionPair/Heart.lean` state the same notion in
the heart and in the ambient category, and each says the other is not derived
from it. `ofTorsionPair` derives the second from the first: the classes travel
by `ambientProperty` and the decomposition by
`heartFullSubcategory_shortExact_triangle`. `hnTilt` is the whole chain — a
stability function on the heart, a cutoff, and a t-structure out. -/

#print axioms CategoryTheory.Triangulated.Tilting.ambientProperty
#print axioms CategoryTheory.Triangulated.Tilting.ambientProperty_of_obj
#print axioms CategoryTheory.Triangulated.Tilting.heart_of_ambientProperty
#print axioms CategoryTheory.Triangulated.Tilting.isLE_of_ambientProperty
#print axioms CategoryTheory.Triangulated.Tilting.isGE_of_ambientProperty
#print axioms CategoryTheory.Triangulated.Tilting.ambientProperty_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Tilting.HeartTorsionPair.ofTorsionPair
#print axioms CategoryTheory.Triangulated.Tilting.HeartTorsionPair.ofTorsionPair_tors
#print axioms CategoryTheory.Triangulated.Tilting.HeartTorsionPair.ofTorsionPair_free
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnHeartTorsionPair
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnHeartTorsionPair_tors
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnHeartTorsionPair_free
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTilt

/-! ## What the tilted heart of a stability function is

The Happel--Reiten--Smalo description specialised to `hnTilt`: the tilted heart
is the extensions of `T β` by `F β ⟦1⟧`, with the two generating families as the
ends of that triangle. -/

#print axioms CategoryTheory.Triangulated.StabilityFunction.hnTilt_heart_iff
#print axioms CategoryTheory.Triangulated.StabilityFunction.mem_hnTilt_heart_of_hnTors
#print axioms CategoryTheory.Triangulated.StabilityFunction.shift_mem_hnTilt_heart_of_hnFree

/-! ## The cutoff bounds the object's own phase

`hnTors`/`hnFree` are defined by the HN extrema `φ⁻`/`φ⁺`, but every consumer that reads a
cutoff against a charge needs the object's own phase. `HNPolygon.lean` already proved the
bracketing, as `phase_le_first` and `last_le_phase`, with the extremal indices written out
rather than as `φ±` -- which is why grepping `HarderNarasimhan.lean` for a bound on
`Z.phase E` does not find it. These name it and draw the two cutoff corollaries;
`lt_phase_of_mem_hnTors` is the categorical step cases 1--3 of #740 begin with.
-/

#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phiMinus_le_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_le_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityFunction.lt_phase_of_mem_hnTors
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_le_of_mem_hnFree

/-! ## From the torsion class to a slope bound

The composite of `lt_phase_of_mem_hnTors` with `lt_phase_iff_slopeOfPhase_lt`, and the statement
cases 1--3 of Lemma 6.2 actually consume: an object of the torsion class, of positive rank, has
slope strictly above the cutoff's slope. `Mukai.im_expCharge_pos` takes it from there. Rank zero
is excluded and handled by `mem_hnTors_of_rank_zero`, which is arithmetic rather than comparison.
-/

#print axioms CategoryTheory.Triangulated.SlopeData.slopeOfPhase_lt_of_mem_hnTors
#print axioms CategoryTheory.Triangulated.SlopeData.slope_le_slopeOfPhase_of_mem_hnFree

/-! ## The weak torsion pair, at a slope cutoff

The strict pair above is cut by a phase in `ℝ`. This one is cut by a slope in `WithTop ℝ`,
which is what lets a rank-zero object -- slope `⊤`, no phase at all -- sit in `T μ₀` at every
finite cutoff.

Its splitting axiom was blocked from #789 until `tailAt` could be ported, which needed the
subobject correspondence proved without a charge (`CategoryTheory/SubobjectCorrespondence.lean`,
#815). `WeakTail.lean` and `WeakSplitting.lean` are that port and its consequence. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.slope_cokernel_pullback_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.isSemistable_cokernel_pullback_iff
#print axioms CategoryTheory.Triangulated.AbelianWeakHNFiltration.tailAt
#print axioms CategoryTheory.Triangulated.AbelianWeakHNFiltration.tailAt_n
#print axioms CategoryTheory.Triangulated.AbelianWeakHNFiltration.tailAt_μ
#print axioms CategoryTheory.Triangulated.AbelianWeakHNFiltration.tailAt_μPlus
#print axioms CategoryTheory.Triangulated.AbelianWeakHNFiltration.tailAt_μMinus
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.exists_subobject_hnTors_cokernel_hnFree
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.exists_shortExact_hnTors_hnFree
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnTorsProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnFreeProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnTorsProperty_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnFreeProperty_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnTorsionPair
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnTorsionPair_tors
#print axioms CategoryTheory.Triangulated.WeakStabilityFunctionOn.hnTorsionPair_free
