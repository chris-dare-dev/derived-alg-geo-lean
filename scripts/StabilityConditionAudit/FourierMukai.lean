/-
FourierMukai slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HomFiniteWitness
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## Fourier--Mukai lane -- the abstract kernel-functor interface

Every record here is hypothesis-only. `Correspondence` asks for three functors
and assumes nothing about them, so a clean axiom list for these declarations
says that the interface is consistent, not that any functor is of kernel type.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.pull
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.tensor
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.push
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transform
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transform_obj
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transform_map
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transformMapIso
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transformMapIso_refl
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.IsKernelFunctor
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.isKernelFunctor_transform
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.IsKernelFunctor.of_natIso
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.IsKernelFunctor.kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.IsKernelFunctor.iso
#print axioms CategoryTheory.Triangulated.FourierMukai.transform_isTriangulated
#print axioms CategoryTheory.Triangulated.FourierMukai.transform_additive

/-! ## Fourier--Mukai lane -- convolution of kernels

`ConvolutionData` supplies Huybrechts' Prop. 5.10 rather than proving it, so a
clean axiom list here says the supplied-data interface is consistent and that
its consequences follow from it -- not that any convolution exists.

`CoherentConvolutionData` is the stronger endocorrespondence root. It carries
an explicit monoidal presentation, so associator, unitors, pentagon, and
triangle cannot be chosen independently; it forgets one-way to the legacy
interface. Nothing constructs this root either.

Associativity splits: `convolutionTransformAssoc` is a THEOREM (transform
level, derived from four compIso families alone), while
`ConvolutionAssocData` is SUPPLIED (kernel level; deriving it would need
Orlov uniqueness). Nothing constructs the latter.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.conv
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.compIso
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.monoidal
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.compIso
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.conv
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.unit
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.assocIso
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.leftUnitIso
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.rightUnitIso
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.Pentagon
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.pentagon
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.Triangle
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.triangle
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.toConvolutionData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.isKernelFunctor_transform_comp
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.isKernelFunctor_comp
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.transformMapConvIso
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.transformMapConvIso_refl
#print axioms CategoryTheory.Triangulated.FourierMukai.convolutionTransformAssoc
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionAssocData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionAssocData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionAssocData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionAssocData.assocIso
#print axioms CategoryTheory.Triangulated.FourierMukai.convolutionTransformUnitLeft
#print axioms CategoryTheory.Triangulated.FourierMukai.convolutionTransformUnitRight
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionLeftUnitData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionLeftUnitData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionLeftUnitData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionLeftUnitData.leftUnitIso
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionRightUnitData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionRightUnitData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionRightUnitData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionRightUnitData.rightUnitIso
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.toConvolutionAssocData
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.toConvolutionLeftUnitData
#print axioms CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.toConvolutionRightUnitData

/-! ## Fourier--Mukai lane -- the induced maps on K₀

The only FourierMukai module that reaches into this subsystem's own
`Foundation`, for `Triangulated.K₀`. `transformK₀_conv` turns the supplied
Prop. 5.10 isomorphism into an equality of homomorphisms, so its axiom list is
the one to read if the supplied-data interface is ever suspected of hiding a
proof hole.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transformK₀
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transformK₀_eq
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.transformK₀_of
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.K₀_map_eq_transformK₀
#print axioms CategoryTheory.Triangulated.FourierMukai.Correspondence.K₀_map_eq_transformK₀_kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.ConvolutionData.transformK₀_conv

/-! ## K₀ of an exact equivalence -/

#print axioms CategoryTheory.Triangulated.K₀.map_comp_map_eq_id
#print axioms CategoryTheory.Triangulated.K₀.mapAddEquiv
#print axioms CategoryTheory.Triangulated.K₀.mapAddEquiv_apply

/-! ## The alternating sum along a bounded exact sequence

Pure linear algebra: rank-nullity plus an induction. Mathlib's
`Algebra.Homology.EulerCharacteristic` defines `eulerChar` but proves no
relation to homology and nothing about exact complexes, so this is the
arithmetic engine a Hom-built Euler form would run on. It is NOT that form,
and nothing here mentions a category.
-/

#print axioms DerivedAlgGeo.LinearAlgebra.diffRank
#print axioms DerivedAlgGeo.LinearAlgebra.finrank_eq_finrank_ker_add_diffRank
#print axioms DerivedAlgGeo.LinearAlgebra.finrank_eq_diffRank_add_diffRank
#print axioms DerivedAlgGeo.LinearAlgebra.sum_range_succ_smul_finrank
#print axioms DerivedAlgGeo.LinearAlgebra.sum_range_succ_smul_finrank_eq_zero
#print axioms DerivedAlgGeo.LinearAlgebra.diffRank_eq_zero_of_subsingleton

/-! ## Kernel functors acting on stability conditions

The join between the Fourier--Mukai lane and the autoequivalence action. Every
field of `KernelAutoequivalence` is supplied -- nothing proves a transform is an
equivalence -- so a clean axiom list here says the transport follows from that
datum, not that any kernel provides it.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.corr
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.equiv
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.iso
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.map_eq_transformK₀
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.of_obj_eq
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStab
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStab_slicing
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStab_Z

/-! ## The dual kernel

`DualKernel` is supplied: that the quasi-inverse of a Fourier--Mukai
equivalence is again one, with the derived-dual kernel, is classical geometry.
What is proved from it is that both directions become kernel-computable, and
that the two class maps are mutually inverse.

Since #559 there is also an abstract constructor from adjunction data --
see the adjoint-kernel section at the end of this file. It does not change
the status of `DualKernel` as a supplied datum; it moves the supply point.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.invIso
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.map_inverse_eq_transformK₀
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.transformK₀_dual_comp
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.transformK₀_comp_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.transformK₀AddEquiv
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.transformK₀AddEquiv_apply
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.transformK₀AddEquiv_symm_apply
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStabOfDual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStabOfDual_slicing
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStabOfDual_Z

/-! ## Kernel autoequivalences as elements of the acting group

The bridge into `GroupAction.AutPairQuot`. `toAutPair` needs a `DualKernel`
and a supplied *invertible* `lam`; `mk_toAutPair_smul` says the group element's
action is the transport `actStabOfDual` already gave. A clean axiom list here
says the group membership follows from those two supplied data, not that any
kernel provides either. This is a map on elements only -- it is NOT a monoid
homomorphism, and the module docstring says why.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.toTriEquiv
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.toAutPair
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.toAutPair_lam
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.toAutPair_act
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.mk_toAutPair_smul

/-! ## Composing two transports

The associativity clause of an action, without a group. The six
`Equivalence.trans` instances are `inferInstanceAs` wrappers that instance
search cannot reach on its own; `KernelAutoequivalence.trans` is the kernel-level
composite, whose kernel is the convolution.
-/

#print axioms CategoryTheory.Triangulated.transFunctorAdditive
#print axioms CategoryTheory.Triangulated.transInverseAdditive
#print axioms CategoryTheory.Triangulated.transFunctorCommShift
#print axioms CategoryTheory.Triangulated.transInverseCommShift
#print axioms CategoryTheory.Triangulated.transFunctorIsTriangulated
#print axioms CategoryTheory.Triangulated.transInverseIsTriangulated
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_trans
#print axioms CategoryTheory.Triangulated.hlam_trans
#print axioms CategoryTheory.Triangulated.actStabAut_trans
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.trans
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.trans_kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.trans_equiv
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.actStab_trans

/-! ## The unit kernel

The unit *object* of the composition story, and only the object: `𝒪_Δ`
presenting `𝟭` as a transform is supplied, exactly as `ConvolutionData` is. No
identity law is proved, because a law would need convolution data comparing a
correspondence with itself. What the unit kernel does buy for free is its own
dual kernel -- `Equivalence.refl.inverse` is `𝟭 C` -- so every `DualKernel`
consequence applies to `KernelAutoequivalence.id`.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.unitKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.unitIso
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.id
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.id_kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.id_equiv
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.id_corr
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.toDualKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.toDualKernel_dual

/-! ## The k-linear Yoneda functor is homological, and its shift sequence

The `ModuleCat k` counterpart of Mathlib's `preadditiveYoneda` instance, and the
one a `k`-dimension count can use — `finrank` is not statable in `AddCommGrpCat`.

`ShiftSequence ℤ` is here as of #469, so the long exact Hom sequence is
available. A clean axiom list on the three `homologySequence_exact` lemmas says
they follow from Mathlib's generic homology-sequence API once the two instances
are supplied — it does NOT say any Euler form exists. That still needs
finiteness data nothing here provides.
-/

#print axioms CategoryTheory.Triangulated.linearYoneda_isHomological
#print axioms CategoryTheory.Triangulated.linearYoneda_map_distinguished
#print axioms CategoryTheory.Triangulated.linearYonedaShiftSequence
#print axioms CategoryTheory.Triangulated.linearYoneda_homologySequence_exact₁
#print axioms CategoryTheory.Triangulated.linearYoneda_homologySequence_exact₂
#print axioms CategoryTheory.Triangulated.linearYoneda_homologySequence_exact₃

/-! ## The alternating sum along a `ℤ`-indexed long exact sequence

The arithmetic under a Hom-built Euler form. Indexed by `ℤ` and carrying NO
boundary hypotheses -- no injectivity, no surjectivity, no `Subsingleton` --
because the three-family statement telescopes by a translation of the summation
index rather than by induction. `k` is a `DivisionRing`: rank-nullity is what
forces it and commutativity is used nowhere.
-/

#print axioms DerivedAlgGeo.LinearAlgebra.finrank_eq_range_add_range
#print axioms DerivedAlgGeo.LinearAlgebra.altDim
#print axioms DerivedAlgGeo.LinearAlgebra.support_altDim
#print axioms DerivedAlgGeo.LinearAlgebra.support_range_subset
#print axioms DerivedAlgGeo.LinearAlgebra.finsum_altDim_middle

/-! ## The k-linear coyoneda functor is homological

The second-variable companion of `linearYoneda`. Its shift sequence is
tautological -- the functor is covariant with source `C` -- so unlike the
Yoneda side it needs NO opposite-category linearity and NO
`(shiftFunctor C n).Linear k` hypothesis.
-/

#print axioms CategoryTheory.Triangulated.linearCoyoneda_isHomological
#print axioms CategoryTheory.Triangulated.linearCoyonedaShiftSequence
#print axioms CategoryTheory.Triangulated.linearCoyoneda_homologySequence_exact₁
#print axioms CategoryTheory.Triangulated.linearCoyoneda_homologySequence_exact₂
#print axioms CategoryTheory.Triangulated.linearCoyoneda_homologySequence_exact₃

/-! ## The Hom-built Euler form

`chi(X,Y) = SUM (-1)^i dim_k Hom(X, Y[i])`, biadditive, descended to `K0`.
`HomFiniteBounded` is the one supplied datum and every other declaration here is
constructed from it plus the two long exact sequences. A clean axiom list is the
claim that constructing the Euler form needs no assumption beyond Hom-finiteness
-- in particular no Serre duality and no geometry.

`chiHom` itself is junk-total: `finrank` is 0 on a non-finite module and `finsum`
is 0 on infinite support, so it is defined everywhere and only the additivity
results require `HomFiniteBounded`.
-/

#print axioms CategoryTheory.Triangulated.HomFiniteBounded
#print axioms CategoryTheory.Triangulated.HomFiniteBounded.finite
#print axioms CategoryTheory.Triangulated.HomFiniteBounded.support_finite
#print axioms CategoryTheory.Triangulated.chiHom
#print axioms CategoryTheory.Triangulated.chiHom_eq_finsum_altDim
#print axioms CategoryTheory.Triangulated.exact_hom_of_shortComplex_exact
#print axioms CategoryTheory.Triangulated.chiHom_additive_right
#print axioms CategoryTheory.Triangulated.chiHom_additive_left
#print axioms CategoryTheory.Triangulated.isTriangleAdditive_chiHom
#print axioms CategoryTheory.Triangulated.chiRight
#print axioms CategoryTheory.Triangulated.chiRight.congr_simp
#print axioms CategoryTheory.Triangulated.chiRight_of
#print axioms CategoryTheory.Triangulated.isTriangleAdditive_chiRight
#print axioms CategoryTheory.Triangulated.chiK₀
#print axioms CategoryTheory.Triangulated.chiK₀_of
#print axioms CategoryTheory.Triangulated.chiK₀_of_of
#print axioms CategoryTheory.Triangulated.chiK₀.congr_simp

/-! ## A fully faithful k-linear functor preserves the Euler form

Step 6 of the Hom-built Euler form. The content is the term-by-term match of
`Hom(X, Y[i])` with `Hom(PhiX, PhiY[i])`; `k`-linearity is what makes the
matched summands equal as k-DIMENSIONS, which additivity alone would not give.
A clean axiom list says preservation follows from full faithfulness plus
k-linearity plus shift-compatibility, and from nothing else -- no Serre duality
and no geometry.
-/

#print axioms CategoryTheory.Triangulated.homLinearEquivOfFullyFaithful
#print axioms CategoryTheory.Triangulated.homShiftLinearEquiv
#print axioms CategoryTheory.Triangulated.finrank_hom_shift_map
#print axioms CategoryTheory.Triangulated.homShiftLinearEquivOfEssSurj
#print axioms CategoryTheory.Triangulated.HomFiniteBounded.of_essSurj
#print axioms CategoryTheory.Triangulated.chiHom_map
#print axioms CategoryTheory.Triangulated.chiK₀_map

/-! ## A concrete HomFiniteBounded model (#543)

The bounded homotopy category of a Hom-finite k-linear category satisfies
`HomFiniteBounded`; `Kᵇ(FGModuleCat k)` is the named witness. Satisfiability
only: nothing relates `chiHom` on it to homology, and nothing about `Dᵇ` is
claimed or used. -/

#print axioms CategoryTheory.Triangulated.HomFiniteWitness.homRestrict
#print axioms CategoryTheory.Triangulated.HomFiniteWitness.module_finite_hom
#print axioms CategoryTheory.Triangulated.HomFiniteWitness.subsingleton_hom_of_le_lt_ge
#print axioms CategoryTheory.Triangulated.HomFiniteWitness.subsingleton_hom_of_ge_lt_le
#print axioms CategoryTheory.Triangulated.HomFiniteWitness.boundedHomEquiv
#print axioms CategoryTheory.Triangulated.instHomFiniteBoundedBounded
#print axioms CategoryTheory.Triangulated.fgModuleCat_hom_finite
#print axioms CategoryTheory.Triangulated.homFiniteBounded_fgModuleCat
#print axioms FGModuleCat.instProjective
#print axioms CategoryTheory.Triangulated.isKProjective_of_isStrictlyLE
#print axioms CategoryTheory.Triangulated.isKProjective_bounded
#print axioms CategoryTheory.Triangulated.boundedQh
#print axioms CategoryTheory.Triangulated.boundedQh_full
#print axioms CategoryTheory.Triangulated.boundedQh_faithful
#print axioms CategoryTheory.Triangulated.boundedLift
#print axioms CategoryTheory.Triangulated.boundedLift_linear
#print axioms CategoryTheory.Triangulated.boundedLift_essSurj
#print axioms CategoryTheory.Triangulated.homFiniteBounded_boundedDerived


/-! ## Kernel-presented adjoints (#559)

`LeftAdjointKernelData` and `RightAdjointKernelData` are supplied, and are the
lane's newest trust boundary: that a Fourier--Mukai transform has adjoints, let
alone kernel-presented ones, is Grothendieck duality on smooth projective
varieties. An abstract `Correspondence` assumes no adjunction between `pull`
and `push`, so nothing here could produce one.

A clean axiom list on these records says the interface is consistent and that
its consequences follow from it. In particular it does NOT say that any
transform has an adjoint. What follows from the supplied adjunction, with no
further input, is uniqueness: `isoOfAdj` identifies any adjoint of the
transform with the adjoint kernel's transform, and `isKernelFunctor_of_adj`
turns that into membership of `IsKernelFunctor` for the opposite
correspondence.

No triangulated structure is used. The `transformIso` families are uniqueness
of the adjoint *transform*, never of the adjoint *kernel* -- the converse is
Orlov uniqueness, which this repository does not state.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.adj
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.isKernelFunctor_of_adj
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.isLeftAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.isRightAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.isoOfAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.mapAdjKernelIso
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.mapAdjKernelIso_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.ofKernelIso
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.ofKernelIso_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.toRightAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.toRightAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.LeftAdjointKernelData.transformIso
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.adj
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.isKernelFunctor_of_adj
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.isLeftAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.isRightAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.isoOfAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.mapAdjKernelIso
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.mapAdjKernelIso_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.ofKernelIso
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.ofKernelIso_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.toLeftAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.toLeftAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.RightAdjointKernelData.transformIso

/-! ## Dual kernels derived from adjunction data (#559)

The consumer of the adjoint-kernel layer, and the first constructor of a
`DualKernel` from anything other than a directly supplied `invIso`.
`ofLeftAdjointKernel` and `ofRightAdjointKernel` build one by uniqueness of
adjoints; `toLeftAdjointKernelData` and `toRightAdjointKernelData` go back, so
for a kernel autoequivalence the data are interderivable and the derivation
weakens no hypothesis. A clean axiom list here says exactly that -- the
geometric content has moved into `LeftAdjointKernelData`, not disappeared.

`UnitKernelData.toLeftAdjointKernelData` is the only production of adjoint
kernel data in the repository, and it is the trivial one: `𝟭 C` is its own
adjoint. `UnitKernelData.ofLeftAdjointKernel_dual` checks that running it
through the derived constructor lands on the same kernel object as
`toDualKernel` supplies -- on the kernel only; the two `invIso` fields are not
claimed equal.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.ofLeftAdjointKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.ofLeftAdjointKernel_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.ofLeftAdjointKernel_toLeftAdjointKernelData_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.ofRightAdjointKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.ofRightAdjointKernel_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.ofRightAdjointKernel_toRightAdjointKernelData_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.toLeftAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.toLeftAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.toRightAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.DualKernel.toRightAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.ofLeftAdjointKernel_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.toLeftAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.UnitKernelData.toLeftAdjointKernelData_adjKernel


/-! ## The adjoint-kernel ledger: constituents plus a projection formula

`ConstituentRightAdjoints` and `ConstituentLeftAdjoints` split the single
opaque adjoint-kernel obligation into the three adjunctions a transform's
constituents classically have -- pullback/pushforward, rigidity of the kernel,
and Grothendieck duality -- and nothing constructs either structure.

The composition is the FREE half: `adj` is `Adjunction.comp` applied twice, so
a clean axiom list on it says the transform is adjoint to the composite as soon
as its three constituents are adjoint, and says nothing else.

The remaining half is an ARGUMENT, not a field. `toRightAdjointKernelData`
takes an isomorphism `rightAdjoint = C'.transform Q` from the caller; that is
the projection formula plus the identification of the shriek functor as a
twisted pullback, and it is where a dualizing object would eventually appear.
Keeping it out of the structure is deliberate -- the three adjunctions do not
imply it, and a field would read as though they did.

Direction of strength: this ledger is stronger input than the
`LeftAdjointKernelData` / `RightAdjointKernelData` it produces, and nothing
converts back. It does not lower the bar for an adjoint kernel; it replaces one
compound obligation with four separately-classical ones.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.adj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.isKernelFunctor_rightAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.isLeftAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.pullAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.pullRight
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.pushAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.pushRight
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.rightAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.toRightAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.toRightAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.twistAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentRightAdjoints.twistRight

#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.adj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.isKernelFunctor_leftAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.isRightAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.leftAdjoint
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.mk.inj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.pullAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.pullLeft
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.pushAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.pushLeft
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.toLeftAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.toLeftAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.twistAdj
#print axioms CategoryTheory.Triangulated.FourierMukai.ConstituentLeftAdjoints.twistLeft


/-! ## The equivalence, derived rather than supplied (#795 half one)

`KernelAutoequivalence` took its equivalence and comparison isomorphism as
supplied fields. `ofRightAdjointKernel` derives both: an adjunction with
invertible unit and counit IS an equivalence by `Adjunction.toEquivalence`, and
its functor is the transform DEFINITIONALLY, so `iso` is `Iso.refl` and nothing
is transported. `dualKernelOfRightAdjointKernel` is the same datum's dual
kernel, also at `Iso.refl` -- `toEquivalence`'s inverse is the right adjoint on
the nose, so no trip through `rightAdjointUniq` is needed.

`ofFullyFaithful` splits the hypothesis the way a criterion would deliver it:
full faithfulness gives the unit through Mathlib's
`unit_isIso_of_L_fully_faithful`, and the counit is the remaining
essential-surjectivity half.

`transform_isEquivalence`, `isIso_unit` and `isIso_counit` are the CONVERSE, and
they are the honesty check: given a kernel autoequivalence and a right adjoint
kernel, the unit and counit are already invertible. So none of the above lowers
the bar -- it restates it pointwise, in the shape a geometric criterion
(Bondal--Orlov) actually has. Nothing here supplies that invertibility.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.dualKernelOfRightAdjointKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.dualKernelOfRightAdjointKernel_dual
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.isIso_counit
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.isIso_unit
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.ofFullyFaithful
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.ofFullyFaithful_kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.ofRightAdjointKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.ofRightAdjointKernel_corr
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.ofRightAdjointKernel_kernel
#print axioms CategoryTheory.Triangulated.FourierMukai.KernelAutoequivalence.transform_isEquivalence


/-! ## Satisfiability witnesses

`Correspondence`, `ConstituentRightAdjoints` and `ConstituentLeftAdjoints` had
NO inhabitant at all, and neither did `UnitKernelData`. An interface nobody has
inhabited is one nobody has checked for consistency -- a structure whose fields
cannot be met simultaneously looks exactly like a structure nobody has tried.

`trivialCorrespondence` takes pull, push and every twist to be the identity. Its
transform is then the identity DEFINITIONALLY (`trivialCorrespondence_transform`
is `rfl`), so `Adjunction.id` discharges every adjunction field with no
transport at all.

A clean axiom list here says the interfaces are CONSISTENT. It says nothing
else: not that any geometric Fourier--Mukai transform exists, not that any
transform is an equivalence, and not that any contract in
`AlgebraicGeometry/DerivedCategory/FourierMukai/` is dischargeable. The
geometric ledger remains entirely uninhabited.

Nothing here is an `instance`, deliberately: a global `Correspondence` instance
would put the trivial one in front of every instance search mentioning the
structure.
-/

#print axioms CategoryTheory.Triangulated.FourierMukai.trivialConstituentLeftAdjoints
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialConstituentRightAdjoints
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialCorrespondence
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialCorrespondence_transform
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialLeftAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialLeftAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialRightAdjointKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialRightAdjointKernelData_adjKernel
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialUnitKernelData
#print axioms CategoryTheory.Triangulated.FourierMukai.trivialUnitKernelData_unitKernel
