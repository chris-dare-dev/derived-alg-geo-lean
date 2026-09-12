/-
Axiom + sorry audit over a HAND-MAINTAINED LIST of this library's declarations.

Run: `lake env lean scripts/DGCategoryAudit.lean` (to read the output), or
`lake build DGCategoryAudit` (to check it still elaborates).

The same shape as `scripts/StabilityConditionAudit.lean`, and gated the same way:

    lake env lean scripts/DGCategoryAudit.lean > dg-audit.txt 2>&1
    python3 scripts/check_audit.py dg-audit.txt scripts/DGCategoryAudit.lean

`#print axioms` prints `[sorryAx]` and exits 0, so being in the build is not
being a gate -- `check_audit.py` is what fails on an axiom outside the trusted
three, on `sorryAx`, on an empty sweep, and on this file falling behind the
source tree.

The dg-category subsystem was gated from its first commit rather than
retrofitted. The algebraic-geometry subsystem needed a linter ratchet to catch
up; this list starts complete and should stay that way.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement

#print axioms CategoryTheory.Cdg
#print axioms CategoryTheory.Cdg.coboundariesIn_le_comap
#print axioms CategoryTheory.Cdg.coboundaries_le_comap
#print axioms CategoryTheory.Cdg.cochain_ofHom_coneHom
#print axioms CategoryTheory.Cdg.cocycleAddEquiv
#print axioms CategoryTheory.Cdg.cocycles_eq
#print axioms CategoryTheory.Cdg.comp_fst_of_split
#print axioms CategoryTheory.Cdg.comp_snd_of_split
#print axioms CategoryTheory.Cdg.coneCocycle
#print axioms CategoryTheory.Cdg.coneHom
#print axioms CategoryTheory.Cdg.coneObj
#print axioms CategoryTheory.Cdg.delta_shift_sign_agrees
#print axioms CategoryTheory.Cdg.dgComp_eq
#print axioms CategoryTheory.Cdg.dgHom_eq
#print axioms CategoryTheory.Cdg.dgId_eq
#print axioms CategoryTheory.Cdg.homModule
#print axioms CategoryTheory.Cdg.linear
#print axioms CategoryTheory.Cdg.enhancement
#print axioms CategoryTheory.Cdg.h0Functor
#print axioms CategoryTheory.Cdg.homEquivCohomologyClass
#print axioms CategoryTheory.Cdg.homOf_comp
#print axioms CategoryTheory.Cdg.homOf_dgComp
#print axioms CategoryTheory.Cdg.homSeam
#print axioms CategoryTheory.Cdg.instDGCategory
#print axioms CategoryTheory.Cdg.instEssSurjH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.instFaithfulH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.instFullH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.instIsEquivalenceH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.isConeOf
#print axioms CategoryTheory.Cdg.isPretriangulated
#print axioms CategoryTheory.Cdg.isShiftBy
#print axioms CategoryTheory.Cdg.mem_coboundaries_iff'
#print axioms CategoryTheory.Cdg.of
#print axioms CategoryTheory.Cdg.ofCocycle
#print axioms CategoryTheory.Cdg.ofCocycle_toCocycle
#print axioms CategoryTheory.Cdg.ofCocycle_val
#print axioms CategoryTheory.Cdg.of_shiftObj
#print axioms CategoryTheory.Cdg.postcompAddEquiv
#print axioms CategoryTheory.Cdg.quotient_map_homOf_eq
#print axioms CategoryTheory.Cdg.rightUnshift_shiftCocycle
#print axioms CategoryTheory.Cdg.seam
#print axioms CategoryTheory.Cdg.shiftCocycle
#print axioms CategoryTheory.Cdg.shiftComp_eq
#print axioms CategoryTheory.Cdg.shiftD_eq
#print axioms CategoryTheory.Cdg.shiftObj
#print axioms CategoryTheory.Cdg.struct
#print axioms CategoryTheory.Cdg.toCocycle
#print axioms CategoryTheory.Cdg.toCocycle_ofCocycle
#print axioms CategoryTheory.Cdg.toCocycle_val
#print axioms CategoryTheory.Const
#print axioms CategoryTheory.Const.dgCategory
#print axioms CategoryTheory.DGCategory
#print axioms CategoryTheory.DGCategory.dgComp_assoc
#print axioms CategoryTheory.DGCategory.dgComp_id
#print axioms CategoryTheory.DGCategory.dgComp_leibniz
#print axioms CategoryTheory.DGCategory.dgComp_units_smul_left
#print axioms CategoryTheory.DGCategory.dgComp_units_smul_right
#print axioms CategoryTheory.DGCategory.dgId_cocycle
#print axioms CategoryTheory.DGCategory.dgId_comp
#print axioms CategoryTheory.DGCategory.dgProd_fst_add
#print axioms CategoryTheory.DGCategory.dgProd_fst_units_smul
#print axioms CategoryTheory.DGCategory.dgProd_snd_add
#print axioms CategoryTheory.DGCategory.dgProd_snd_units_smul
#print axioms CategoryTheory.DGCategory.hom_units_smul
#print axioms CategoryTheory.DGCategory.op
#print axioms CategoryTheory.DGCategory.opStruct
#print axioms CategoryTheory.DGCategory.op_dgComp_apply
#print axioms CategoryTheory.DGCategory.op_dgHom
#print axioms CategoryTheory.DGCategory.op_dgId
#print axioms CategoryTheory.DGCategory.prod
#print axioms CategoryTheory.DGCategory.prodStruct
#print axioms CategoryTheory.DGCategory.prod_d_apply
#print axioms CategoryTheory.DGCategory.prod_dgComp_apply
#print axioms CategoryTheory.DGCategory.prod_dgId
#print axioms CategoryTheory.DGCategory.shiftComp
#print axioms CategoryTheory.DGCategory.shiftComp.congr_simp
#print axioms CategoryTheory.DGCategory.shiftComp_apply
#print axioms CategoryTheory.DGCategory.shiftComp_assoc
#print axioms CategoryTheory.DGCategory.shiftComp_dgId_left
#print axioms CategoryTheory.DGCategory.shiftComp_dgId_right
#print axioms CategoryTheory.DGCategory.shiftComp_leibniz
#print axioms CategoryTheory.DGCategory.shiftComp_zero_zero
#print axioms CategoryTheory.DGCategory.shiftD
#print axioms CategoryTheory.DGCategory.shiftD_apply
#print axioms CategoryTheory.DGCategory.shiftD_shiftD
#print axioms CategoryTheory.DGCategory.shiftD_zero
#print axioms CategoryTheory.DGCategory.shiftFunctor_dgHom_X
#print axioms CategoryTheory.DGCategory.shiftFunctor_dgHom_d
#print axioms CategoryTheory.DGCategory.toDGCategoryStruct
#print axioms CategoryTheory.DGCategoryStruct
#print axioms CategoryTheory.DGCategoryStruct.dgComp
#print axioms CategoryTheory.DGCategoryStruct.dgComp.congr_simp
#print axioms CategoryTheory.DGCategoryStruct.dgHom
#print axioms CategoryTheory.DGCategoryStruct.dgId
#print axioms CategoryTheory.DGFunctor
#print axioms CategoryTheory.DGFunctor.IsQuasiEquivalence
#print axioms CategoryTheory.DGFunctor.IsQuasiEquivalence.essSurj
#print axioms CategoryTheory.DGFunctor.IsQuasiEquivalence.quasiIso
#print axioms CategoryTheory.DGFunctor.comp
#print axioms CategoryTheory.DGFunctor.comp_map
#print axioms CategoryTheory.DGFunctor.comp_obj
#print axioms CategoryTheory.DGFunctor.h0
#print axioms CategoryTheory.DGFunctor.h0CompIso
#print axioms CategoryTheory.DGFunctor.h0IdIso
#print axioms CategoryTheory.DGFunctor.h0_map_mk
#print axioms CategoryTheory.DGFunctor.h0_obj
#print axioms CategoryTheory.DGFunctor.id
#print axioms CategoryTheory.DGFunctor.id_map
#print axioms CategoryTheory.DGFunctor.id_obj
#print axioms CategoryTheory.DGFunctor.map
#print axioms CategoryTheory.DGFunctor.mapComplex
#print axioms CategoryTheory.DGFunctor.map_comp
#print axioms CategoryTheory.DGFunctor.map_d
#print axioms CategoryTheory.DGFunctor.map_id
#print axioms CategoryTheory.DGFunctor.map_mem_coboundaries
#print axioms CategoryTheory.DGFunctor.map_mem_cocycles
#print axioms CategoryTheory.DGFunctor.mk.inj
#print axioms CategoryTheory.DGFunctor.mk.sizeOf_spec
#print axioms CategoryTheory.DGFunctor.obj
#print axioms CategoryTheory.DGLinear
#print axioms CategoryTheory.DGLinear.comp_smul_left
#print axioms CategoryTheory.DGLinear.comp_smul_right
#print axioms CategoryTheory.DGLinear.d_smul
#print axioms CategoryTheory.DGLinear.homComplex
#print axioms CategoryTheory.DGLinear.homComplex_X
#print axioms CategoryTheory.DGLinear.homComplex_d_apply
#print axioms CategoryTheory.DGLinear.postcompCochain
#print axioms CategoryTheory.DGLinear.postcompCochain_apply
#print axioms CategoryTheory.DGLinear.postcompCochain_d
#print axioms CategoryTheory.DGFunctor.Linear
#print axioms CategoryTheory.DGFunctor.Linear.map_smul
#print axioms CategoryTheory.DGFunctor.compLinear
#print axioms CategoryTheory.DGFunctor.h0Linear
#print axioms CategoryTheory.DGFunctor.idLinear
#print axioms CategoryTheory.DGFunctor.map_smul
#print axioms CategoryTheory.H0.coboundariesSubmodule
#print axioms CategoryTheory.H0.cocyclesModule
#print axioms CategoryTheory.H0.cocyclesSubmodule
#print axioms CategoryTheory.H0.homModule
#print axioms CategoryTheory.H0.linear
#print axioms CategoryTheory.Enhancement
#print axioms CategoryTheory.Enhancement.dgCat
#print axioms CategoryTheory.Enhancement.equiv
#print axioms CategoryTheory.Enhancement.hasZeroObject
#print axioms CategoryTheory.Enhancement.isDGCategory
#print axioms CategoryTheory.Enhancement.isPretriangulated
#print axioms CategoryTheory.Enhancement.mk.inj
#print axioms CategoryTheory.Enhancement.mk.sizeOf_spec
#print axioms CategoryTheory.H0
#print axioms CategoryTheory.H0.category
#print axioms CategoryTheory.H0.coboundariesIn
#print axioms CategoryTheory.H0.hasZeroObject
#print axioms CategoryTheory.H0.isZero_of_dgId_eq_zero
#print axioms CategoryTheory.H0.of
#print axioms CategoryTheory.H0.of_self
#print axioms CategoryTheory.H0.preadditive
#print axioms CategoryTheory.IsConeOf
#print axioms CategoryTheory.IsConeOf.bijective
#print axioms CategoryTheory.IsConeOf.comp_inr_mem_coboundaries
#print axioms CategoryTheory.IsConeOf.inl
#print axioms CategoryTheory.IsConeOf.inr
#print axioms CategoryTheory.IsConeOf.inr_closed
#print axioms CategoryTheory.IsConeOf.inr_mem_cocycles
#print axioms CategoryTheory.IsConeOf.mk.inj
#print axioms CategoryTheory.IsConeOf.mk.sizeOf_spec
#print axioms CategoryTheory.IsConeOf.δ_inl
#print axioms CategoryTheory.IsPretriangulated
#print axioms CategoryTheory.IsPretriangulated.exists_cone
#print axioms CategoryTheory.IsPretriangulated.exists_shift
#print axioms CategoryTheory.IsPretriangulated.exists_zero
#print axioms CategoryTheory.IsShiftBy
#print axioms CategoryTheory.IsShiftBy.bijective
#print axioms CategoryTheory.IsShiftBy.bijective_homMap
#print axioms CategoryTheory.IsShiftBy.comp
#print axioms CategoryTheory.IsShiftBy.compare
#print axioms CategoryTheory.IsShiftBy.compare_comp_compare
#print axioms CategoryTheory.IsShiftBy.compare_eq_mapShift
#print axioms CategoryTheory.IsShiftBy.compare_mem_cocycles
#print axioms CategoryTheory.IsShiftBy.hom
#print axioms CategoryTheory.IsShiftBy.homMap
#print axioms CategoryTheory.IsShiftBy.hom_closed
#print axioms CategoryTheory.IsShiftBy.hom_inv
#print axioms CategoryTheory.IsShiftBy.inv
#print axioms CategoryTheory.IsShiftBy.inv_closed
#print axioms CategoryTheory.IsShiftBy.inv_hom
#print axioms CategoryTheory.IsShiftBy.mapShift
#print axioms CategoryTheory.IsShiftBy.mapShift_comp
#print axioms CategoryTheory.IsShiftBy.mapShift_id
#print axioms CategoryTheory.IsShiftBy.mapShift_mem_cocycles
#print axioms CategoryTheory.IsShiftBy.mk.inj
#print axioms CategoryTheory.IsShiftBy.mk.sizeOf_spec
#print axioms CategoryTheory.IsShiftBy.self
#print axioms CategoryTheory.Z0
#print axioms CategoryTheory.Z0.category
#print axioms CategoryTheory.Z0.comp_mem
#print axioms CategoryTheory.Z0.comp_val
#print axioms CategoryTheory.Z0.id_val
#print axioms CategoryTheory.Z0.of
#print axioms CategoryTheory.Z0.toH0
#print axioms CategoryTheory.Z0.toH0_full
#print axioms CategoryTheory.coboundaries
#print axioms CategoryTheory.coboundaries_le_cocycles
#print axioms CategoryTheory.coboundary_comp_mem
#print axioms CategoryTheory.cocycles
#print axioms CategoryTheory.compRight
#print axioms CategoryTheory.compRight.congr_simp
#print axioms CategoryTheory.compRight_apply
#print axioms CategoryTheory.compRight_comm
#print axioms CategoryTheory.comp_coboundary_mem
#print axioms CategoryTheory.comp_sub_mem
#print axioms CategoryTheory.constComplex
#print axioms CategoryTheory.constComplex_X_coe
#print axioms CategoryTheory.constComplex_d
#print axioms CategoryTheory.dgComp_closed
#print axioms CategoryTheory.mem_coboundaries_iff
#print axioms CategoryTheory.mem_cocycles_iff
#print axioms CategoryTheory.prodComp
#print axioms CategoryTheory.prodComp_apply
#print axioms CategoryTheory.prodComplex
#print axioms CategoryTheory.prodComplex_X_coe
#print axioms CategoryTheory.prodComplex_d
#print axioms CategoryTheory.prodD

-- dg-enhancements-e6: the shift functor on H0, its zero and add comparison
-- isomorphisms, all three ShiftMkCore coherence identities, and the resulting
-- HasShift (H0 C) instance.
#print axioms CategoryTheory.H0.compareIso
#print axioms CategoryTheory.H0.hasShift
#print axioms CategoryTheory.H0.shiftCompWitness
#print axioms CategoryTheory.H0.shiftCompWitness'
#print axioms CategoryTheory.H0.shiftFunctor
#print axioms CategoryTheory.H0.shiftFunctorAddIso
#print axioms CategoryTheory.H0.shiftFunctorAddIso'
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_assoc
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_hom_app_congr
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_hom_app_zero_left
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_hom_app_zero_right
#print axioms CategoryTheory.H0.shiftFunctorZeroIso
#print axioms CategoryTheory.H0.shiftFunctor_additive
#print axioms CategoryTheory.H0.shiftFunctor_map_mk
#print axioms CategoryTheory.H0.shiftMkCore
#print axioms CategoryTheory.IsPretriangulated.shiftObj
#print axioms CategoryTheory.IsPretriangulated.shiftWitness
#print axioms CategoryTheory.IsShiftBy.comp'
#print axioms CategoryTheory.IsShiftBy.comp'.congr_simp
#print axioms CategoryTheory.IsShiftBy.comp'_assoc_hom
#print axioms CategoryTheory.IsShiftBy.comp'_hom
#print axioms CategoryTheory.IsShiftBy.comp'_inv
#print axioms CategoryTheory.IsShiftBy.comp'_self_left_inv
#print axioms CategoryTheory.IsShiftBy.comp'_self_right_inv
#print axioms CategoryTheory.IsShiftBy.comp_eq_comp'
#print axioms CategoryTheory.IsShiftBy.comp_hom
#print axioms CategoryTheory.IsShiftBy.comp_inv
#print axioms CategoryTheory.IsShiftBy.compare_comp'_right
#print axioms CategoryTheory.IsShiftBy.compare_congr
#print axioms CategoryTheory.IsShiftBy.compare_self
#print axioms CategoryTheory.IsShiftBy.compare_trans
#print axioms CategoryTheory.IsShiftBy.inv_unique
#print axioms CategoryTheory.IsShiftBy.mapShiftHom
#print axioms CategoryTheory.IsShiftBy.mapShiftHom_apply
#print axioms CategoryTheory.IsShiftBy.mapShift_add
#print axioms CategoryTheory.IsShiftBy.mapShift_comp'_shift
#print axioms CategoryTheory.IsShiftBy.mapShift_comp_shift
#print axioms CategoryTheory.IsShiftBy.mapShift_compare
#print axioms CategoryTheory.IsShiftBy.mapShift_compare_comp
#print axioms CategoryTheory.IsShiftBy.mapShift_compare_comp'
#print axioms CategoryTheory.IsShiftBy.mapShift_mem_coboundaries
#print axioms CategoryTheory.IsShiftBy.mapShift_self
#print axioms CategoryTheory.IsShiftBy.self_inv

-- The maps *out* of a dg cone (dg-enhancements-e6). `IsConeOf` gives the universal
-- property for maps into the cone; the triangle needs the projections, and the
-- projection to the source is closed for a reason -- uniqueness of the splitting --
-- rather than by assumption.
#print axioms CategoryTheory.IsConeOf.splitId
#print axioms CategoryTheory.IsConeOf.fst
#print axioms CategoryTheory.IsConeOf.snd
#print axioms CategoryTheory.IsConeOf.fst_inl_add_snd_inr
#print axioms CategoryTheory.IsConeOf.delta_splitId_key
#print axioms CategoryTheory.IsConeOf.delta_fst
#print axioms CategoryTheory.IsConeOf.inr_comp_fst_and_snd
#print axioms CategoryTheory.IsConeOf.inr_comp_fst
#print axioms CategoryTheory.IsConeOf.inr_comp_snd
#print axioms CategoryTheory.IsConeOf.toShift
#print axioms CategoryTheory.IsConeOf.toShift_closed
#print axioms CategoryTheory.IsConeOf.toShift_mem_cocycles
#print axioms CategoryTheory.IsConeOf.inr_comp_toShift

-- The cone on an identity is contractible: the primitive is `snd` composed with
-- `inl`, and both of the cone's differential corrections are consumed exactly.
#print axioms CategoryTheory.IsConeOf.delta_fst_and_snd
#print axioms CategoryTheory.IsConeOf.delta_snd
#print axioms CategoryTheory.IsConeOf.dgId_mem_coboundaries_of_dgId

-- The distinguished triangles of H⁰, and three of the six Pretriangulated fields.
#print axioms CategoryTheory.H0.homMk
#print axioms CategoryTheory.H0.shiftFunctor_additive'
#print axioms CategoryTheory.H0.coneTriangle
#print axioms CategoryTheory.H0.distinguishedTriangles
#print axioms CategoryTheory.H0.coneTriangle_mem
#print axioms CategoryTheory.H0.isomorphic_distinguished
#print axioms CategoryTheory.H0.distinguished_cocone_triangle
#print axioms CategoryTheory.H0.isZero_of_dgId_mem_coboundaries
#print axioms CategoryTheory.H0.contractible_distinguished

-- Rotation groundwork (dg-enhancements-e6): the morphism a cone is built on is
-- automatically closed, and the two comparison maps between a cone on `inr` and
-- the shift, each closed for a reason the source records.
#print axioms CategoryTheory.IsConeOf.delta_f
#print axioms CategoryTheory.IsConeOf.rotateFwd
#print axioms CategoryTheory.IsConeOf.rotateFwd_closed
#print axioms CategoryTheory.IsConeOf.rotateBwd
#print axioms CategoryTheory.IsConeOf.delta_shiftInvComp
#print axioms CategoryTheory.IsConeOf.delta_shiftInvComp_inl
#print axioms CategoryTheory.IsConeOf.rotateBwd_closed

-- The comparison is a homotopy equivalence: one composite is the identity on the
-- nose, the other only up to a primitive the source exhibits.
#print axioms CategoryTheory.IsConeOf.inl_comp_fst_and_snd
#print axioms CategoryTheory.IsConeOf.inl_comp_fst
#print axioms CategoryTheory.IsConeOf.inl_comp_snd
#print axioms CategoryTheory.IsConeOf.inl_comp_rotateFwd
#print axioms CategoryTheory.IsConeOf.inr_comp_rotateFwd
#print axioms CategoryTheory.IsConeOf.rotateBwd_comp_rotateFwd
#print axioms CategoryTheory.IsConeOf.rotateFwd_absorb_inl
#print axioms CategoryTheory.IsConeOf.rotateFwd_absorb_inr
#print axioms CategoryTheory.IsConeOf.delta_sndComp
#print axioms CategoryTheory.IsConeOf.rotateFwd_comp_rotateBwd_eq
#print axioms CategoryTheory.IsConeOf.rotateFwd_comp_rotateBwd_sub_dgId

-- The rotation axiom, forward direction (dg-enhancements-e6): the two squares of
-- the rotated triangle -- one strict, one up to an exhibited primitive -- and the
-- comparison assembled as an isomorphism of triangles in H⁰.
#print axioms CategoryTheory.IsConeOf.rotateBwd_comp_toShift
#print axioms CategoryTheory.IsConeOf.toShift_comp_rotateBwd_eq
#print axioms CategoryTheory.IsConeOf.toShift_comp_rotateBwd_sub_inr
#print axioms CategoryTheory.H0.homMk_eq_homMk
#print axioms CategoryTheory.H0.homMk_neg
#print axioms CategoryTheory.H0.homMk_comp
#print axioms CategoryTheory.H0.homMk_id
#print axioms CategoryTheory.H0.coneTriangle_mor₁
#print axioms CategoryTheory.H0.coneTriangle_mor₂
#print axioms CategoryTheory.H0.coneTriangle_mor₃
#print axioms CategoryTheory.H0.rotateIso
#print axioms CategoryTheory.H0.rotateIso_hom
#print axioms CategoryTheory.H0.rotateIso_inv
#print axioms CategoryTheory.H0.rotateConeTriangleIso
#print axioms CategoryTheory.H0.rotate_mem_of_mem

-- The lifting axiom (dg-enhancements-e6): a square commuting in H⁰ extends to the
-- cones. The homotopy is folded into the map -- that is the axiom's content -- and
-- both of the extension's own squares then hold strictly.
#print axioms CategoryTheory.IsConeOf.lift
#print axioms CategoryTheory.IsConeOf.inr_comp_lift
#print axioms CategoryTheory.IsConeOf.lift_closed
#print axioms CategoryTheory.IsConeOf.lift_comp_toShift
#print axioms CategoryTheory.H0.exists_lift_of_comm

-- Functorial dg cones retain the chosen homotopy and the closed cone map.
-- Their category laws are proved before passage to H⁰.
#print axioms CategoryTheory.DGCategory.HomotopySquare
#print axioms CategoryTheory.DGCategory.HomotopySquare.ext
#print axioms CategoryTheory.DGCategory.HomotopySquare.id
#print axioms CategoryTheory.DGCategory.HomotopySquare.comp
#print axioms CategoryTheory.DGCategory.HomotopySquare.strict
#print axioms CategoryTheory.DGCategory.HomotopySquare.strict_homotopy
#print axioms CategoryTheory.IsConeOf.Morphism
#print axioms CategoryTheory.IsConeOf.Morphism.a_closed
#print axioms CategoryTheory.IsConeOf.Morphism.b_closed
#print axioms CategoryTheory.IsConeOf.Morphism.homotopy
#print axioms CategoryTheory.IsConeOf.Morphism.homotopy_boundary
#print axioms CategoryTheory.IsConeOf.Morphism.ext
#print axioms CategoryTheory.IsConeOf.liftMorphism
#print axioms CategoryTheory.IsConeOf.Morphism.id
#print axioms CategoryTheory.IsConeOf.Morphism.comp
#print axioms CategoryTheory.DGCategory.ConePresentation
#print axioms CategoryTheory.DGCategory.ConePresentation.source
#print axioms CategoryTheory.DGCategory.ConePresentation.target
#print axioms CategoryTheory.DGCategory.ConePresentation.arrow
#print axioms CategoryTheory.DGCategory.ConePresentation.cone
#print axioms CategoryTheory.DGCategory.ConePresentation.isCone
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.source
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.target
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.coneMorphism
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.ext
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.id
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.comp
#print axioms CategoryTheory.DGCategory.ConePresentation.id_source
#print axioms CategoryTheory.DGCategory.ConePresentation.id_target
#print axioms CategoryTheory.DGCategory.ConePresentation.comp_source
#print axioms CategoryTheory.DGCategory.ConePresentation.comp_target
#print axioms CategoryTheory.IsConeOf.Morphism.toTriangleMorphism
#print axioms CategoryTheory.IsConeOf.Morphism.toTriangleMorphism_id
#print axioms CategoryTheory.IsConeOf.Morphism.toTriangleMorphism_comp
#print axioms CategoryTheory.H0.coneSourceFunctor
#print axioms CategoryTheory.H0.coneTargetFunctor
#print axioms CategoryTheory.H0.coneObjectFunctor
#print axioms CategoryTheory.H0.coneSourceFunctor_obj
#print axioms CategoryTheory.H0.coneSourceFunctor_map
#print axioms CategoryTheory.H0.coneTargetFunctor_obj
#print axioms CategoryTheory.H0.coneTargetFunctor_map
#print axioms CategoryTheory.H0.coneObjectFunctor_obj
#print axioms CategoryTheory.H0.coneObjectFunctor_map
#print axioms CategoryTheory.H0.coneTriangleFunctor
#print axioms CategoryTheory.H0.coneTriangleFunctor_obj
#print axioms CategoryTheory.H0.coneTriangleFunctor_map
#print axioms CategoryTheory.H0.coneTriangleFunctor_obj_distinguished
#print axioms CategoryTheory.H0.distinguishedConeTriangleFunctor
#print axioms CategoryTheory.H0.distinguishedConeTriangleFunctor_obj_val

-- Shift/cone preservation by dg functors is composable at the dg layer and
-- derives ordinary exactness on H⁰.
#print axioms CategoryTheory.IsShiftBy.compare_congr_left
#print axioms CategoryTheory.DGFunctor.PreservesShifts
#print axioms CategoryTheory.DGFunctor.PreservesShifts.id
#print axioms CategoryTheory.DGFunctor.PreservesShifts.comp

-- Every dg functor preserves shifts.  A shift element is a closed, two-sided
-- invertible element of degree `-n` (`IsShiftBy.inv`, `hom_inv`, `inv_hom`),
-- and a dg functor preserves composition and identities on the nose, so it
-- carries invertible elements to invertible ones.  `PreservesShifts` therefore
-- costs a caller nothing.  `PreservesChosenCones` is not like this and remains
-- a genuine hypothesis: a cone is not an invertible element.
#print axioms CategoryTheory.DGFunctor.preservesShifts
#print axioms CategoryTheory.DGFunctor.mapHomotopySquare
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.id
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.comp
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.ofIso
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mapCone_fst
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mapCone_snd
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mapCone_toShift
#print axioms CategoryTheory.DGFunctor.mapShift_inv_eq
#print axioms CategoryTheory.DGFunctor.map_mapShift
#print axioms CategoryTheory.DGFunctor.map_compare
#print axioms CategoryTheory.DGFunctor.shiftCommIso
#print axioms CategoryTheory.DGFunctor.shiftCommIso_zero_hom_app
#print axioms CategoryTheory.DGFunctor.shiftCommIso_add_hom_app
#print axioms CategoryTheory.DGFunctor.commShift
#print axioms CategoryTheory.DGFunctor.PreservesConeTriangles
#print axioms CategoryTheory.DGFunctor.preservesConeTriangles_of_preservesChosenCones
#print axioms CategoryTheory.DGFunctor.isTriangulated_of_preservesConeTriangles
#print axioms CategoryTheory.DGFunctor.isTriangulated_of_preservesShifts_and_coneTriangles
#print axioms CategoryTheory.DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones

-- The instance itself (dg-enhancements-e6, #377): the completion axiom for
-- arbitrary distinguished triangles, the five axioms H⁰ proves, and the
-- `Pretriangulated (H0 C)` they assemble into.
#print axioms CategoryTheory.H0.complete_distinguished_triangle_morphism
#print axioms CategoryTheory.H0.pretriangulatedAxioms
#print axioms CategoryTheory.H0.pretriangulated
#print axioms CategoryTheory.H0.mem_distTriang_iff

-- Uniqueness handles for the two `Classical.choice` constructions
-- (dg-enhancements-e7). `IsShiftBy.inv` and `IsConeOf.splitId` cannot be
-- unfolded, so every identification of `mapShift`, `compare`, `fst` or `snd`
-- with a concretely given element goes through one of these.
#print axioms CategoryTheory.IsShiftBy.mapShift_unique
#print axioms CategoryTheory.IsShiftBy.compare_unique
#print axioms CategoryTheory.IsConeOf.splitId_unique
#print axioms CategoryTheory.IsConeOf.toShift_comp_compare

-- The sign on the cone triangle's connecting morphism (dg-enhancements-e7).
-- `H0.coneTriangle` negates `IsConeOf.toShift`, so the rotation comparison is
-- negated too; `Cdg.triangle_mor₃_eq` is what forces the sign.
#print axioms CategoryTheory.H0.rotateIsoNeg

-- The ambient shift on H⁰ is the one `H0Shift.lean` built (dg-enhancements-e7).
#print axioms CategoryTheory.H0.shiftFunctorZero_eq
#print axioms CategoryTheory.H0.shiftFunctorAdd_eq

-- The model shift is Mathlib's shift (dg-enhancements-e7). Stated first on plain
-- cochain complexes, where no `Cdg`/`CochainComplex` synonym has to be crossed
-- inside a rewrite, and then read back on `C^dg`.
#print axioms CategoryTheory.Cdg.rightShift_id_zero
#print axioms CategoryTheory.Cdg.rightShift_id_comp
#print axioms CategoryTheory.Cdg.shiftCocycle_v
#print axioms CategoryTheory.Cdg.mapShift_isShiftBy
#print axioms CategoryTheory.Cdg.shiftCocycle_zero
#print axioms CategoryTheory.Cdg.comp_shiftCocycle

-- `Cdg.toH0` and its commutation with the shift (dg-enhancements-e7). This is
-- where the two coherence identities of a `CommShift` structure are discharged;
-- both telescope into a single `IsShiftBy.compare`.
#print axioms CategoryTheory.Cdg.toH0
#print axioms CategoryTheory.Cdg.toH0_map
#print axioms CategoryTheory.Cdg.instFullCochainComplexIntH0ToH0
#print axioms CategoryTheory.Cdg.h0Functor_map_toH0_map
#print axioms CategoryTheory.Cdg.toH0ShiftIso
#print axioms CategoryTheory.Cdg.compare_isShiftBy_zero
#print axioms CategoryTheory.Cdg.compare_isShiftBy_add
#print axioms CategoryTheory.Cdg.toH0ShiftIso_zero_hom
#print axioms CategoryTheory.Cdg.toH0ShiftIso_add_hom
#print axioms CategoryTheory.Cdg.toH0CommShift

-- **The seam commutes with the shift** (dg-enhancements-e7, #378). The issue
-- calls this "the real content of this epic".
#print axioms CategoryTheory.Cdg.seamShiftIso
#print axioms CategoryTheory.Cdg.seamShiftIso_hom
#print axioms CategoryTheory.Cdg.seamCommShiftIso
#print axioms CategoryTheory.Cdg.seamCommShiftIso_hom_app
#print axioms CategoryTheory.Cdg.h0FunctorCommShift
#print axioms CategoryTheory.Cdg.h0Functor_commShiftIso_hom_app

-- The model cone is Mathlib's mapping cone, sign included (dg-enhancements-e7).
#print axioms CategoryTheory.Cdg.isConeOf_fst
#print axioms CategoryTheory.Cdg.comp_shiftCocycle_id
#print axioms CategoryTheory.Cdg.toShift_isShiftBy
#print axioms CategoryTheory.Cdg.triangle_mor₃_eq
#print axioms CategoryTheory.Cdg.mapTriangleConeTriangleIso

-- **The agreement theorem** (dg-enhancements-e7, #378): the transported
-- distinguished triangles are Mathlib's, as an equality of `Set (Triangle _)`,
-- together with the octahedral half the pin supplies.
#print axioms CategoryTheory.Cdg.h0FunctorIsTriangulated
#print axioms CategoryTheory.Cdg.mem_distTriang_iff
#print axioms CategoryTheory.Cdg.distinguishedTriangles_eq
#print axioms CategoryTheory.Cdg.instIsTriangulatedH0
#print axioms CategoryTheory.Cdg.seamFunctorCommShift
#print axioms CategoryTheory.Cdg.seamInverseCommShift
#print axioms CategoryTheory.Cdg.seamCommShift
#print axioms CategoryTheory.Cdg.seamFunctorIsTriangulated
#print axioms CategoryTheory.Cdg.seamIsTriangulated
#print axioms CategoryTheory.Cdg.seam_distinguishedTriangles_eq

-- The Grothendieck group of a pretriangulated dg category: `K₀` at the
-- `Pretriangulated (H0 C)` instance above, not a new construction. The first
-- downstream consumer of `H0.pretriangulated`.
#print axioms CategoryTheory.DGCategory.K₀dg
#print axioms CategoryTheory.DGCategory.K₀dg.of
#print axioms CategoryTheory.DGCategory.K₀dg.of_eq
#print axioms CategoryTheory.DGCategory.K₀dg.of_triangle

-- Homogeneous dg natural transformations of every integer degree, their
-- pointwise differential and vertical composition, and the dg category of dg
-- functors they form.
#print axioms CategoryTheory.DGFunctor.HomogeneousFamily
#print axioms CategoryTheory.DGFunctor.HomogeneousFamily.IsNatural
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.IsClosed
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.IsClosed.app_d
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.add_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.comp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.comp_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.complex
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.complex_X
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.complex_d_apply
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.composition
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.composition_apply_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.differential
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.differentialHom
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.differentialHom_apply
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.differential_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.differential_differential
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ext
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ext_iff
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.id_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.naturality
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.neg_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.units_smul_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.zero_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.zsmul_app
#print axioms CategoryTheory.DGFunctor.dgCategory
#print axioms CategoryTheory.DGFunctor.homogeneousNatTransSubgroup

-- Signed cone lifts of homogeneous squares in every degree: the identity,
-- additivity, composition, differential, and projection formulas that make
-- objectwise cones a strict dg functor.
#print axioms CategoryTheory.DGCategory.HomogeneousSquare
#print axioms CategoryTheory.DGCategory.HomogeneousSquare.homotopy
#print axioms CategoryTheory.DGCategory.HomogeneousSquare.homotopy_boundary
#print axioms CategoryTheory.DGCategory.HomogeneousSquare.mk.inj
#print axioms CategoryTheory.DGCategory.HomogeneousSquare.mk.sizeOf_spec
#print axioms CategoryTheory.DGCategory.HomogeneousSquare.strict
#print axioms CategoryTheory.DGCategory.HomogeneousSquare.strict_homotopy
#print axioms CategoryTheory.IsConeOf.homogeneousLift
#print axioms CategoryTheory.IsConeOf.homogeneousLift_comp_fst
#print axioms CategoryTheory.IsConeOf.homogeneousLift_comp_snd
#print axioms CategoryTheory.IsConeOf.homogeneousLift_id
#print axioms CategoryTheory.IsConeOf.homogeneousLift_strict_add
#print axioms CategoryTheory.IsConeOf.homogeneousLift_strict_comp
#print axioms CategoryTheory.IsConeOf.homogeneousLift_strict_d
#print axioms CategoryTheory.IsConeOf.homogeneousLift_strict_map_d
#print axioms CategoryTheory.IsConeOf.isoOfStrictSquare
#print axioms CategoryTheory.IsConeOf.isoOfStrictSquare_hom_val
#print axioms CategoryTheory.IsConeOf.isoOfStrictSquare_inv_val
#print axioms CategoryTheory.IsConeOf.inr_comp_isoOfStrictSquare_hom
#print axioms CategoryTheory.IsConeOf.isoOfStrictSquare_hom_comp_fst
#print axioms CategoryTheory.IsConeOf.homogeneous_ext
#print axioms CategoryTheory.IsConeOf.inl_comp_homogeneousLift_strict
#print axioms CategoryTheory.IsConeOf.inl_comp_homogeneousLift_strict_general
#print axioms CategoryTheory.IsConeOf.inr_comp_homogeneousLift
#print axioms CategoryTheory.IsConeOf.inr_comp_homogeneousLift_general

-- Objectwise cones of a closed degree-zero dg natural transformation, the
-- assembled cone dg functor, and its canonical inclusion transformations.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.differential_inl
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.functor
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.functor_map
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.functor_obj
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.inl
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.inl_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.inr
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.inr_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.inr_isClosed
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isCone
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.mk.inj
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.mk.sizeOf_spec
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.obj
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.functorK₀Of
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.functorK₀Map
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.IsClosed.app_mem_cocycles
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.chosenConeData

-- Dg adjunctions (closed unit and counit with componentwise triangle
-- identities) and the unshifted cones of their unit and counit.
#print axioms CategoryTheory.DGAdjunction
#print axioms CategoryTheory.DGAdjunction.CounitConeData
#print axioms CategoryTheory.DGAdjunction.CounitConeData.boundary
#print axioms CategoryTheory.DGAdjunction.CounitConeData.differential_boundary
#print axioms CategoryTheory.DGAdjunction.CounitConeData.inclusion
#print axioms CategoryTheory.DGAdjunction.CounitConeData.inclusion_isClosed
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twist
#print axioms CategoryTheory.DGAdjunction.UnitConeData
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitCone
#print axioms CategoryTheory.DGAdjunction.chosenCounitConeData
#print axioms CategoryTheory.DGAdjunction.chosenUnitConeData
#print axioms CategoryTheory.DGAdjunction.counit
#print axioms CategoryTheory.DGAdjunction.counitEndofunctor
#print axioms CategoryTheory.DGAdjunction.counit_isClosed
#print axioms CategoryTheory.DGAdjunction.left_triangle
#print axioms CategoryTheory.DGAdjunction.mk.inj
#print axioms CategoryTheory.DGAdjunction.mk.sizeOf_spec
#print axioms CategoryTheory.DGAdjunction.right_triangle
#print axioms CategoryTheory.DGAdjunction.unit
#print axioms CategoryTheory.DGAdjunction.unitEndofunctor
#print axioms CategoryTheory.DGAdjunction.unit_isClosed

-- Generated projections, injectivity and extensionality lemmas of the new dg
-- structures, plus the cone-category instance and the H⁰ distinguished-triangle
-- object property.
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.ext_iff
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.mk.inj
#print axioms CategoryTheory.DGCategory.ConePresentation.Hom.mk.sizeOf_spec
#print axioms CategoryTheory.DGCategory.ConePresentation.instCategory
#print axioms CategoryTheory.DGCategory.ConePresentation.mk.inj
#print axioms CategoryTheory.DGCategory.ConePresentation.mk.sizeOf_spec
#print axioms CategoryTheory.DGCategory.HomotopySquare.a_closed
#print axioms CategoryTheory.DGCategory.HomotopySquare.b_closed
#print axioms CategoryTheory.DGCategory.HomotopySquare.ext_iff
#print axioms CategoryTheory.DGCategory.HomotopySquare.mk.inj
#print axioms CategoryTheory.DGCategory.HomotopySquare.mk.sizeOf_spec
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mapCone
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mapCone_inl
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mapCone_inr
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mk.inj
#print axioms CategoryTheory.DGFunctor.PreservesChosenCones.mk.sizeOf_spec
#print axioms CategoryTheory.DGFunctor.PreservesConeTriangles.map_cone
#print axioms CategoryTheory.DGFunctor.PreservesShifts.mapShift
#print axioms CategoryTheory.DGFunctor.PreservesShifts.mapShift_hom
#print axioms CategoryTheory.DGFunctor.PreservesShifts.mk.inj
#print axioms CategoryTheory.DGFunctor.PreservesShifts.mk.sizeOf_spec
#print axioms CategoryTheory.H0.distinguishedTriangleProperty
#print axioms CategoryTheory.IsConeOf.Morphism.ext_iff
#print axioms CategoryTheory.IsConeOf.Morphism.hom
#print axioms CategoryTheory.IsConeOf.Morphism.inr_comm
#print axioms CategoryTheory.IsConeOf.Morphism.mk.inj
#print axioms CategoryTheory.IsConeOf.Morphism.mk.sizeOf_spec
#print axioms CategoryTheory.IsConeOf.Morphism.square
#print axioms CategoryTheory.IsConeOf.Morphism.toShift_comm
#print axioms CategoryTheory.IsConeOf.Morphism.fst_comm
#print axioms CategoryTheory.IsConeOf.lift_comp_fst
#print axioms CategoryTheory.IsConeOf.homogeneousLift_d
#print axioms CategoryTheory.IsConeOf.homogeneousLift_zero
#print axioms CategoryTheory.DGCategory.HomotopySquare.toHomogeneousSquare
#print axioms CategoryTheory.DGCategory.HomotopySquare.boundary
#print axioms CategoryTheory.DGCategory.HomotopySquare.ofBoundary
#print axioms CategoryTheory.DGCategory.HomotopySquare.ofBoundary_homotopy
#print axioms CategoryTheory.DGCategory.HomotopySquare.id_homotopy
#print axioms CategoryTheory.DGCategory.HomotopySquare.comp_homotopy
#print axioms CategoryTheory.DGFunctor.mapHomotopySquare_homotopy
#print axioms CategoryTheory.Enhancement.coneTriangleFunctor
#print axioms CategoryTheory.Enhancement.coneTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.Enhancement.coneTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.Enhancement.coneTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.Enhancement.coneTriangleFunctor_obj_distinguished
#print axioms CategoryTheory.Enhancement.conePresentation
#print axioms CategoryTheory.Enhancement.conePresentation_arrow
#print axioms CategoryTheory.Enhancement.conePresentation_source
#print axioms CategoryTheory.Enhancement.conePresentation_target
#print axioms CategoryTheory.Enhancement.counit_conjugate_conePresentation_arrow
#print axioms CategoryTheory.Enhancement.counit_conjugate_liftedCocycle
#print axioms CategoryTheory.Enhancement.homMk_conePresentation_arrow
#print axioms CategoryTheory.Enhancement.homMk_liftedCocycle
#print axioms CategoryTheory.Enhancement.liftedCocycle

-- Closed degree-zero dg natural transformations descend to `H⁰`, and a dg
-- adjunction is an adjunction there.  This is the adapter that makes dg data
-- comparable with the ordinary categorical data the rest of the library uses.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.h0
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.h0_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.h0_id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.isClosed_id
#print axioms CategoryTheory.DGAdjunction.h0Unit
#print axioms CategoryTheory.DGAdjunction.h0Counit
#print axioms CategoryTheory.DGAdjunction.h0Unit_app
#print axioms CategoryTheory.DGAdjunction.h0Counit_app
#print axioms CategoryTheory.DGAdjunction.h0
#print axioms CategoryTheory.DGAdjunction.h0_unit
#print axioms CategoryTheory.DGAdjunction.h0_counit

-- The cone projections are graded-natural, so the objectwise cones of a closed
-- degree-zero dg natural transformation assemble into a cone in the dg category
-- of dg functors.  With the zero object and the shift below, that is all three
-- fields of a pretriangulated structure on `DGFunctor C D`.
#print axioms CategoryTheory.IsConeOf.homogeneousLift_comp_fst_general
#print axioms CategoryTheory.IsConeOf.homogeneousLift_comp_snd_general
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.fst
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.fst_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.snd
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.snd_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isConeOf
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isConeOf_fst
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isConeOf_snd
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare_hom_val
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare_inv_val
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare_hom_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare_inv_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.inr_comp_isoOfStrictSquare_hom
#print axioms CategoryTheory.DGFunctor.constZero
#print axioms CategoryTheory.DGFunctor.constZero_obj
#print axioms CategoryTheory.DGFunctor.constZero_map
#print axioms CategoryTheory.DGFunctor.dgId_constZero_eq_zero
#print axioms CategoryTheory.DGFunctor.exists_zero_dgFunctor
#print axioms CategoryTheory.DGFunctor.exists_cone_dgFunctor

-- Transport of a homogeneous morphism across chosen shifts, and the sign it
-- forces.  `shiftMap_d` is the identity that rules out the naive shift
-- functor: transport anticommutes with the differential by `(-1)^n`, so the
-- shift of a dg functor has to carry `(-1)^(n * p)` in degree `p`.
#print axioms CategoryTheory.dgComp_units_smul_left
#print axioms CategoryTheory.dgComp_units_smul_right
#print axioms CategoryTheory.IsShiftBy.shiftMap
#print axioms CategoryTheory.IsShiftBy.hom_comp_shiftMap
#print axioms CategoryTheory.IsShiftBy.shiftMap_unique
#print axioms CategoryTheory.IsShiftBy.shiftMap_add
#print axioms CategoryTheory.IsShiftBy.shiftMap_zero
#print axioms CategoryTheory.IsShiftBy.shiftMap_id
#print axioms CategoryTheory.IsShiftBy.shiftMap_comp
#print axioms CategoryTheory.IsShiftBy.shiftMap_comp_inv
#print axioms CategoryTheory.IsShiftBy.shiftMap_d
#print axioms CategoryTheory.IsShiftBy.comp_inv_naturality
#print axioms CategoryTheory.IsShiftBy.comp_inv_comp_hom

-- Comparing two chosen shifts, and composing shifts, in every degree.  These
-- are what make the objectwise comparison of `IsShiftBy.compare` natural, and
-- with them the shift of a dg functor is coherent in the degree rather than
-- only defined for each degree separately.
#print axioms CategoryTheory.IsShiftBy.shiftMap_units_smul
#print axioms CategoryTheory.IsShiftBy.hom_comp_compare
#print axioms CategoryTheory.IsShiftBy.shiftMap_compare
#print axioms CategoryTheory.IsShiftBy.comp'_shiftMap
#print axioms CategoryTheory.IsShiftBy.comp'_shiftMap_smul
#print axioms CategoryTheory.IsShiftBy.shiftMap_compare_compOfDegree
#print axioms CategoryTheory.IsShiftBy.compare_compLeftOfDegree
#print axioms CategoryTheory.IsShiftBy.shiftMap_self
#print axioms CategoryTheory.IsShiftBy.shiftMap_zero_eq_mapShift

-- The dg shift of a functor computes the `H⁰` shift, on objects by `rfl` and
-- on morphisms because the Koszul sign is `+1` in degree zero and the two
-- transports agree.  This is what makes "the cotwist is the shift of the cone
-- functor" a statement about the dg functor rather than only about each value.
#print axioms CategoryTheory.DGFunctor.shiftedFunctor_h0_obj
#print axioms CategoryTheory.DGFunctor.shiftedFunctor_h0_map
#print axioms CategoryTheory.DGFunctor.shiftedFunctor_h0_eq
#print axioms CategoryTheory.DGFunctor.shiftedFunctorH0Iso
#print axioms CategoryTheory.DGFunctor.shiftedFunctor_h0_isEquivalence
#print axioms CategoryTheory.DGFunctor.shiftedFunctorH0Equivalence
#print axioms CategoryTheory.DGFunctor.shiftedFunctorH0CommShift
#print axioms CategoryTheory.DGFunctor.shiftedFunctorH0IsTriangulated

-- `dg-enhancements-e10`: a quasi-equivalence of dg categories induces an
-- equivalence on `H⁰`.  The seam between the `H⁰` Hom quotient and Mathlib's
-- homology is crossed with a hand-built `LeftHomologyMapData`, whose `φH` is
-- the map on cocycles modulo coboundaries; `quasiIso_iff` then reads the
-- hypothesis off it directly, and no naturality of `abHomologyIso` is needed.
#print axioms CategoryTheory.homSc
#print axioms CategoryTheory.range_abToCycles
#print axioms CategoryTheory.DGFunctor.mapHomSc
#print axioms CategoryTheory.DGFunctor.mapCocycles
#print axioms CategoryTheory.DGFunctor.mapH0Hom
#print axioms CategoryTheory.DGFunctor.mapHomScData
#print axioms CategoryTheory.DGFunctor.h0_map_eq_mapH0Hom
#print axioms CategoryTheory.DGFunctor.homologyQuotientEquiv
#print axioms CategoryTheory.DGFunctor.mapH0Hom_comp_homologyQuotientEquiv
#print axioms CategoryTheory.DGFunctor.bijective_mapH0Hom
#print axioms CategoryTheory.DGFunctor.faithful_h0
#print axioms CategoryTheory.DGFunctor.full_h0
#print axioms CategoryTheory.DGFunctor.isEquivalence_h0
#print axioms CategoryTheory.DGFunctor.h0Equivalence

-- Shifting twice agrees with shifting once, and shifting by zero changes
-- nothing -- both up to a canonical comparison that is closed and invertible,
-- so these are isomorphisms in the dg category of dg functors and not merely
-- maps.  The signs merge because `n p + m p = r p`.
#print axioms CategoryTheory.DGFunctor.shiftWitnessComp
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAdd
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAddInv
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAdd_app
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAddInv_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.shiftedDegreeZero
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.shiftedDegreeZero_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.shiftedDegreeZero_isClosed
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.shiftedDegreeZero_id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.shiftedDegreeZero_comp
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAddAssocLeft
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAddAssocRight
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAdd_assoc
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZero
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZero_app
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZeroInv
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZeroInv_app
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAdd_isClosed
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAddInv_isClosed
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZero_isClosed
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZeroInv_isClosed
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAdd_comp_inv
#print axioms CategoryTheory.DGFunctor.shiftedFunctorAddInv_comp
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZero_comp_inv
#print axioms CategoryTheory.DGFunctor.shiftedFunctorZeroInv_comp

-- The closed degree-zero category of dg functors carries the pointwise dg
-- shift as an actual Mathlib `HasShift`.  `z0ShiftMkCore` uses the inverse
-- comparison in Mathlib's total-to-iterated direction, reuses the raw
-- associativity theorem through categorical inverses, and supplies both unit
-- coherences rather than introducing a parallel shift interface.
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctor
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctor_obj
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctor_map_val
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorZeroIso
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorZeroIso_hom_app_val
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorZeroIso_inv_app_val
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'_hom_app_val
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'_inv_app_val
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'_hom_app_zero_right
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'_hom_app_zero_left
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'_hom_app_congr
#print axioms CategoryTheory.DGFunctor.z0ShiftFunctorAddIso'_assoc
#print axioms CategoryTheory.DGFunctor.z0ShiftMkCore
#print axioms CategoryTheory.DGFunctor.z0HasShift
#print axioms CategoryTheory.DGFunctor.z0_shiftFunctor_eq
#print axioms CategoryTheory.DGFunctor.z0_shiftFunctor_obj
#print axioms CategoryTheory.DGFunctor.z0_shiftFunctorZero_eq
#print axioms CategoryTheory.DGFunctor.z0_shiftFunctorAdd_eq

-- The shift of a dg functor, and the resulting pretriangulated structure on
-- the dg category of dg functors.  This is what makes the objectwise twist a
-- genuine cone of functors: Anno--Logvinenko's triangle read in `DGFunctor C D`
-- rather than objectwise in `D`.
#print axioms CategoryTheory.DGFunctor.shiftObj
#print axioms CategoryTheory.DGFunctor.shiftWitness
#print axioms CategoryTheory.DGFunctor.shiftedFunctor
#print axioms CategoryTheory.DGFunctor.shiftedFunctor_obj
#print axioms CategoryTheory.DGFunctor.shiftedFunctor_map
#print axioms CategoryTheory.DGFunctor.shiftHom
#print axioms CategoryTheory.DGFunctor.shiftHom_app
#print axioms CategoryTheory.DGFunctor.shiftedFunctorWitness
#print axioms CategoryTheory.DGFunctor.exists_shift_dgFunctor
#print axioms CategoryTheory.DGFunctor.isPretriangulated_dgFunctor

-- Whiskering a homogeneous dg natural transformation by a dg functor on either
-- side.  Neither operation carries a sign, because a dg functor preserves the
-- graded composition on the nose; the Koszul sign of the horizontal composite
-- lives in `interchange`, where it is the naturality sign of the second
-- transformation evaluated at a component of the first.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_zero
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_add
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeftHom
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeftHom_apply
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_composition
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_differential
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.IsClosed.whiskerLeft
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_zero
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_add
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRightHom
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRightHom_apply
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_composition
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_differential
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.IsClosed.whiskerRight
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.interchange_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.interchange

-- Dg functors compose strictly: associativity and both unit laws are `rfl`.
-- These are what let a law about horizontally composed transformations be
-- stated at all, since the two sides then have definitionally equal types.
#print axioms CategoryTheory.DGFunctor.id_comp
#print axioms CategoryTheory.DGFunctor.comp_id
#print axioms CategoryTheory.DGFunctor.comp_assoc
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_whiskerRight
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerLeft_whiskerLeft
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.whiskerRight_whiskerLeft

-- The Godement product of homogeneous dg natural transformations, its graded
-- Leibniz rule, and strict associativity.  `hcomp` fixes one of the two
-- readings of the horizontal composite; `hcomp_eq_smul_swap` is the price of
-- the other, and it is the `(-1)^(m n)` of `interchange`.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_eq_smul_swap
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_app_swap
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_zero_left
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_zero_right
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_add_left
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_add_right
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.horizontalComposition
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.horizontalComposition_apply
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.id_hcomp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.id_hcomp_id
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.differential_hcomp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.IsClosed.hcomp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.hcomp_assoc

-- `H⁰` of the dg category of dg functors, compared with ordinary functors.
-- The comparison is well defined because the differential of the dg functor
-- category is the pointwise one, so a homotopy between transformations is a
-- homotopy at every component.  Nothing here claims it is full, faithful or
-- essentially surjective; none of the three holds in general.
#print axioms CategoryTheory.DGFunctor.isClosed_of_mem_cocycles
#print axioms CategoryTheory.DGFunctor.mem_cocycles_of_isClosed
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.h0_comp
#print axioms CategoryTheory.DGFunctor.h0Comparison
#print axioms CategoryTheory.DGFunctor.h0Comparison_obj
#print axioms CategoryTheory.DGFunctor.h0Comparison_map_mk
#print axioms CategoryTheory.DGFunctor.h0Iso
#print axioms CategoryTheory.DGFunctor.h0Iso_hom
#print axioms CategoryTheory.DGFunctor.h0Iso_inv
#print axioms CategoryTheory.DGFunctor.h0Iso_hom_app
#print axioms CategoryTheory.DGFunctor.h0Iso_inv_app
#print axioms CategoryTheory.DGFunctor.h0Iso_refl
#print axioms CategoryTheory.DGFunctor.h0Iso_trans

-- The objectwise cones of a closed degree-zero dg natural transformation give
-- a functor from `H⁰ C` to triangles of `H⁰ D`, every value distinguished.
-- The third square of each triangle morphism is the connecting-map square,
-- which is why the cone morphism rather than the three component functors is
-- what has to be produced.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.coneMorphism
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleObj
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleObj_mem_distinguishedTriangles
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.coneTriangleMorphism
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleFunctor
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleFunctor_obj
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleFunctor_map_hom₁
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleFunctor_map_hom₂
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleFunctor_map_hom₃
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleFunctor_obj_mem_distinguishedTriangles

-- Naturality of that functor in the transformation.  A strictly commuting
-- square of closed degree-zero dg natural transformations gives a natural
-- transformation of triangle functors, and the cone lifts are natural on the
-- nose rather than up to homotopy -- which is exactly what the square being
-- strict buys.  The homotopy-coherent case is not treated.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.squareAt
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.squareConeMorphism
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.squareTriangleMorphism
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.functor_map_comp_lift
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.squareTriangleMorphism_hom₁
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.squareTriangleMorphism_hom₂
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.squareTriangleMorphism_hom₃
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleNatTrans
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleNatTrans_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare_hom_app
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare_hom_app_hom₁
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare_hom_app_hom₂
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare_hom_app_hom₃

-- Independence of the chosen cones.  Two `ConeData` for one transformation are
-- related by the identity square, so the comparison is the identity case of
-- the naturality above; `compareIso` packages it as an isomorphism of triangle
-- functors, which says the construction does not depend on the choices.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareCone
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareCone_self
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareCone_comp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.id_square
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareNatTrans
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareNatTrans_app_hom₁
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareNatTrans_app_hom₂
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareNatTrans_app_hom₃
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareNatTrans_self
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareNatTrans_comp
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareIso
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareIso_hom
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compareIso_inv

-- A cone functor preserves chosen cones when its two ends do, so the twist
-- candidate of a dg adjunction is exact as soon as the adjoints are.  That
-- argument is the cone splitting rather than a computation: in the coordinates
-- of the splittings the map is block diagonal, with one sign.  The shift
-- versions below take no arguments at all -- `DGFunctor.preservesShifts` holds
-- for every dg functor, so the cone splitting is not needed for them and the
-- specialised proofs were removed.
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.compRight_functor_map
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.preservesShifts
#print axioms CategoryTheory.DGAdjunction.CounitConeData.preservesShifts
#print axioms CategoryTheory.DGAdjunction.UnitConeData.preservesShifts
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.coneSplit_functor_map
#print axioms CategoryTheory.DGFunctor.HomogeneousNatTrans.ConeData.preservesChosenCones
#print axioms CategoryTheory.DGAdjunction.CounitConeData.preservesChosenCones
#print axioms CategoryTheory.DGAdjunction.UnitConeData.preservesChosenCones

-- Anno--Logvinenko's twist triangle, read as a triangle of functors on `H⁰`.
-- The counit's chosen cones give `X ↦ (L R X ⟶ X ⟶ T X ⟶ (L R X)⟦1⟧)`, every
-- value distinguished, with the first two maps the adjunction's own counit and
-- the canonical inclusion rather than new choices.  No sphericality, no
-- autoequivalence, and no relation to the other three triangles is claimed.
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mor₁
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mor₂
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_map_hom₁
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleFunctor_map_hom₃
#print axioms CategoryTheory.DGAdjunction.CounitConeData.twistTriangleIso
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleFunctor
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mor₁
#print axioms CategoryTheory.DGAdjunction.UnitConeData.unitTriangleIso

-- Tensoring a dg object by a complex, stated by its universal property the way
-- `IsShiftBy` states the shift: `IsCopowerOf K X Z` says degree-`p` morphisms
-- out of `Z` are degree-`p` cochains out of `K` into `dgHom X -`.  The
-- `HasCopower` and `HasCopowers` classes package existence without storing a
-- preferred object in the class, following Mathlib's `HasLimit` pattern.
#print axioms CategoryTheory.copowerCochain
#print axioms CategoryTheory.copowerCochain_apply
#print axioms CategoryTheory.IsCopowerOf
#print axioms CategoryTheory.IsCopowerOf.univ
#print axioms CategoryTheory.IsCopowerOf.univ_d
#print axioms CategoryTheory.IsCopowerOf.bijective
#print axioms CategoryTheory.IsCopowerOf.mk.inj
#print axioms CategoryTheory.IsCopowerOf.mk.sizeOf_spec
#print axioms CategoryTheory.IsCopowerOf.lift_unique
#print axioms CategoryTheory.IsCopowerOf.lift
#print axioms CategoryTheory.IsCopowerOf.univ_comp_lift
#print axioms CategoryTheory.IsCopowerOf.compare
#print axioms CategoryTheory.IsCopowerOf.univ_comp_compare
#print axioms CategoryTheory.IsCopowerOf.compare_mem_cocycles
#print axioms CategoryTheory.IsCopowerOf.compare_comp_compare
#print axioms CategoryTheory.IsCopowerOf.compare_trans
#print axioms CategoryTheory.IsCopowerOf.compare_self
#print axioms CategoryTheory.CopowerData
#print axioms CategoryTheory.CopowerData.obj
#print axioms CategoryTheory.CopowerData.isCopower
#print axioms CategoryTheory.CopowerData.mk.inj
#print axioms CategoryTheory.CopowerData.mk.sizeOf_spec
#print axioms CategoryTheory.HasCopower
#print axioms CategoryTheory.HasCopower.exists_copower
#print axioms CategoryTheory.HasCopower.of_isCopower
#print axioms CategoryTheory.copowerData
#print axioms CategoryTheory.copowerObj
#print axioms CategoryTheory.copowerIsCopower
#print axioms CategoryTheory.HasCopowers
#print axioms CategoryTheory.HasCopowers.has_copower
#print axioms CategoryTheory.hasCopowerOfHasCopowers

-- The genuinely `k`-linear counterpart is separate: `DGLinear.homComplex` reuses the
-- existing graded pieces and differential in `ModuleCat k`, while
-- `IsLinearCopowerOf` represents only `k`-linear cochains.  There is no
-- forgetful projection to `IsCopowerOf`, whose universal property ranges over
-- every additive cochain.  Choice, comparison, and existence use the same
-- universal-property pattern without asserting an Euler-class computation.
#print axioms CategoryTheory.linearCopowerCochain
#print axioms CategoryTheory.linearCopowerCochain_apply
#print axioms CategoryTheory.IsLinearCopowerOf
#print axioms CategoryTheory.IsLinearCopowerOf.univ
#print axioms CategoryTheory.IsLinearCopowerOf.bijective
#print axioms CategoryTheory.IsLinearCopowerOf.mk.inj
#print axioms CategoryTheory.IsLinearCopowerOf.mk.sizeOf_spec
#print axioms CategoryTheory.IsLinearCopowerOf.univ_d
#print axioms CategoryTheory.IsLinearCopowerOf.cochainLinearEquiv
#print axioms CategoryTheory.IsLinearCopowerOf.lift_unique
#print axioms CategoryTheory.IsLinearCopowerOf.lift
#print axioms CategoryTheory.IsLinearCopowerOf.lift_zero
#print axioms CategoryTheory.IsLinearCopowerOf.lift_add
#print axioms CategoryTheory.IsLinearCopowerOf.lift_smul
#print axioms CategoryTheory.IsLinearCopowerOf.univ_comp_lift
#print axioms CategoryTheory.IsLinearCopowerOf.compare
#print axioms CategoryTheory.IsLinearCopowerOf.univ_comp_compare
#print axioms CategoryTheory.IsLinearCopowerOf.compare_mem_cocycles
#print axioms CategoryTheory.IsLinearCopowerOf.compare_comp_compare
#print axioms CategoryTheory.IsLinearCopowerOf.compare_trans
#print axioms CategoryTheory.IsLinearCopowerOf.compare_self
#print axioms CategoryTheory.LinearCopowerData
#print axioms CategoryTheory.LinearCopowerData.obj
#print axioms CategoryTheory.LinearCopowerData.isLinearCopower
#print axioms CategoryTheory.LinearCopowerData.mk.inj
#print axioms CategoryTheory.LinearCopowerData.mk.sizeOf_spec
#print axioms CategoryTheory.HasLinearCopower
#print axioms CategoryTheory.HasLinearCopower.exists_linearCopower
#print axioms CategoryTheory.HasLinearCopower.of_isLinearCopower
#print axioms CategoryTheory.linearCopowerData
#print axioms CategoryTheory.linearCopowerObj
#print axioms CategoryTheory.linearCopowerIsLinearCopower
#print axioms CategoryTheory.HasLinearCopowers
#print axioms CategoryTheory.HasLinearCopowers.has_linearCopower
#print axioms CategoryTheory.hasLinearCopowerOfHasLinearCopowers

-- Coefficient-complex functoriality is a single linear dg functor, not a
-- collection of unrelated degree-zero comparisons.  Its Hom-complex
-- isomorphism owns differential compatibility; homotopies descend to equality
-- in `H⁰`, and the selected homotopy-equivalence comparison reuses the existing
-- `H⁰(Cdg) ≃ HomotopyCategory` seam.  No quasi-isomorphism or Euler claim is
-- made.
#print axioms CategoryTheory.IsLinearCopowerOf.linearCopowerCochain_d
#print axioms CategoryTheory.IsLinearCopowerOf.homComplexIso
#print axioms CategoryTheory.IsLinearCopowerOf.homComplexIso_hom_f_apply
#print axioms CategoryTheory.IsLinearCopowerOf.homComplexIso_inv_f_apply
#print axioms CategoryTheory.IsLinearCopowerOf.lift_d
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMap
#print axioms CategoryTheory.IsLinearCopowerOf.univ_comp_coefficientMap
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMap_d
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMap_comp
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMap_id
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMap_id_eq_compare
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMapOfHom
#print axioms CategoryTheory.IsLinearCopowerOf.univ_comp_coefficientMapOfHom
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMapOfHom_mem_cocycles
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMapOfHom_id_eq_compare
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMapOfHom_comp
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientMapOfHom_sub_mem_coboundaries
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientHom
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientHom_eq_of_homotopy
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientHom_id
#print axioms CategoryTheory.IsLinearCopowerOf.coefficientHom_comp
#print axioms CategoryTheory.IsLinearCopowerOf.homotopyEquivIso
#print axioms CategoryTheory.linearCopowerFunctor
#print axioms CategoryTheory.linearCopowerFunctor_linear
#print axioms CategoryTheory.linearCopowerFunctor_obj
#print axioms CategoryTheory.linearCopowerFunctor_map
#print axioms CategoryTheory.linearCopowerObjIsoOfHomotopyEquiv

-- Scalar-linear evaluation data assembles the linear copowers at a fixed
-- object into a `k`-linear dg functor and a closed evaluation transformation.
-- Its existence selector is choice-independent up to a coherent canonical
-- `Z⁰` isomorphism which commutes strictly with evaluation.  This remains
-- separate from additive `EvaluationData` and asserts no Euler computation.
#print axioms CategoryTheory.LinearEvaluationData
#print axioms CategoryTheory.LinearEvaluationData.obj
#print axioms CategoryTheory.LinearEvaluationData.isLinearCopower
#print axioms CategoryTheory.LinearEvaluationData.mk.inj
#print axioms CategoryTheory.LinearEvaluationData.mk.sizeOf_spec
#print axioms CategoryTheory.HasLinearEvaluationData
#print axioms CategoryTheory.HasLinearEvaluationData.exists_linearEvaluationData
#print axioms CategoryTheory.chosenLinearEvaluationData
#print axioms CategoryTheory.LinearEvaluationData.ofHasLinearCopowers
#print axioms CategoryTheory.LinearEvaluationData.hasLinearEvaluationDataOfHasLinearCopowers
#print axioms CategoryTheory.LinearEvaluationData.map
#print axioms CategoryTheory.LinearEvaluationData.univ_comp_map
#print axioms CategoryTheory.LinearEvaluationData.functor
#print axioms CategoryTheory.LinearEvaluationData.functor_obj
#print axioms CategoryTheory.LinearEvaluationData.functor_map
#print axioms CategoryTheory.LinearEvaluationData.functorLinear
#print axioms CategoryTheory.LinearEvaluationData.evalHom
#print axioms CategoryTheory.LinearEvaluationData.univ_comp_evalHom
#print axioms CategoryTheory.LinearEvaluationData.evaluation
#print axioms CategoryTheory.LinearEvaluationData.evaluation_isClosed
#print axioms CategoryTheory.LinearEvaluationData.compare
#print axioms CategoryTheory.LinearEvaluationData.compare_app
#print axioms CategoryTheory.LinearEvaluationData.compare_isClosed
#print axioms CategoryTheory.LinearEvaluationData.compare_comp
#print axioms CategoryTheory.LinearEvaluationData.compare_self
#print axioms CategoryTheory.LinearEvaluationData.compareIso
#print axioms CategoryTheory.LinearEvaluationData.compareIso_hom_val
#print axioms CategoryTheory.LinearEvaluationData.compareIso_inv_val
#print axioms CategoryTheory.LinearEvaluationData.compareIso_self
#print axioms CategoryTheory.LinearEvaluationData.compareIso_trans
#print axioms CategoryTheory.LinearEvaluationData.compare_comp_evaluation

-- The evaluation functor `RHom(E,-) ⊗ E` and its transformation to the
-- identity.  Every one of the functor's four laws is `lift_unique` applied to
-- the cochain each side induces; only `map_d` needs more than associativity,
-- and there it is the Leibniz rule twice, once in `C` and once in the
-- Hom-complex out of `E`.  Mere existence at one object is packaged by
-- `HasEvaluationData`; all copowers supply it.  Any two choices are canonically
-- isomorphic in `Z⁰`, and that isomorphism commutes strictly with evaluation.
#print axioms CategoryTheory.EvaluationData
#print axioms CategoryTheory.EvaluationData.obj
#print axioms CategoryTheory.EvaluationData.isCopower
#print axioms CategoryTheory.EvaluationData.mk.inj
#print axioms CategoryTheory.EvaluationData.mk.sizeOf_spec
#print axioms CategoryTheory.HasEvaluationData
#print axioms CategoryTheory.HasEvaluationData.exists_evaluationData
#print axioms CategoryTheory.chosenEvaluationData
#print axioms CategoryTheory.EvaluationData.ofHasCopowers
#print axioms CategoryTheory.EvaluationData.hasEvaluationDataOfHasCopowers
#print axioms CategoryTheory.EvaluationData.map
#print axioms CategoryTheory.EvaluationData.univ_comp_map
#print axioms CategoryTheory.EvaluationData.map_zero
#print axioms CategoryTheory.EvaluationData.map_add
#print axioms CategoryTheory.EvaluationData.functor
#print axioms CategoryTheory.EvaluationData.functor_obj
#print axioms CategoryTheory.EvaluationData.functor_map
#print axioms CategoryTheory.EvaluationData.evalHom
#print axioms CategoryTheory.EvaluationData.univ_comp_evalHom
#print axioms CategoryTheory.EvaluationData.evaluation
#print axioms CategoryTheory.EvaluationData.compare
#print axioms CategoryTheory.EvaluationData.compare_app
#print axioms CategoryTheory.EvaluationData.compare_isClosed
#print axioms CategoryTheory.EvaluationData.compare_comp
#print axioms CategoryTheory.EvaluationData.compare_self
#print axioms CategoryTheory.EvaluationData.compareIso
#print axioms CategoryTheory.EvaluationData.compareIso_hom_val
#print axioms CategoryTheory.EvaluationData.compareIso_inv_val
#print axioms CategoryTheory.EvaluationData.compareIso_self
#print axioms CategoryTheory.EvaluationData.compareIso_trans
#print axioms CategoryTheory.EvaluationData.compare_comp_evaluation
#print axioms CategoryTheory.EvaluationData.preservesChosenConesOfCompare
#print axioms CategoryTheory.EvaluationData.compare_evaluation_square
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistK₀Of
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistK₀Map
#print axioms CategoryTheory.EvaluationData.IsEulerCopower
#print axioms CategoryTheory.EvaluationData.IsEulerCopower.ofCompare

-- The Seidel--Thomas twist of an *object*: the cone of `RHom(E,-) ⊗ E ⟶ id`.
-- `evaluation_isClosed` is the whole input beyond the generic cone layer, and
-- it is the Leibniz rule against the identity cochain.  This is not the
-- adjunction twist: that one is the cone of an adjunction counit, this one is
-- attached to a single object.  The two agree for a spherical functor out of
-- `Perf(k)`, which the repository cannot state.  No autoequivalence and no
-- sphericality is claimed for either.
#print axioms CategoryTheory.EvaluationData.evaluation_isClosed
#print axioms CategoryTheory.EvaluationData.TwistConeData
#print axioms CategoryTheory.EvaluationData.chosenTwistConeData
#print axioms CategoryTheory.EvaluationData.TwistConeData.twist
#print axioms CategoryTheory.EvaluationData.TwistConeData.inclusion
#print axioms CategoryTheory.EvaluationData.TwistConeData.inclusion_isClosed
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso_hom_val
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso_inv_val
#print axioms CategoryTheory.EvaluationData.TwistConeData.inclusion_comp_compareIso_hom_val
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso_self_hom_val
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso_self
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso_hom_val_comp
#print axioms CategoryTheory.EvaluationData.TwistConeData.compareIso_trans
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_obj_mor₁
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_obj_mor₂
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_map_hom₁
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleFunctor_map_hom₃
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIso
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation_hom_app_hom₁
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation_hom_app_hom₂
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation_hom_app_hom₃
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation_self
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation_trans

-- Exactness of the object twist.  The shift half is free -- every dg functor
-- preserves shifts, `DGFunctor.preservesShifts` -- so only the cone half is a
-- hypothesis, and it is `RHom(E,-) ⊗ E`'s.  That one stays open:
-- `PreservesChosenCones` asks that maps into the cone split, while
-- `IsCopowerOf` is a mapping-out property.  Exact is not autoequivalence; the
-- object twist has no autoequivalence statement.
#print axioms CategoryTheory.EvaluationData.TwistConeData.preservesShifts
#print axioms CategoryTheory.EvaluationData.TwistConeData.preservesChosenCones
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistH0CommShift
#print axioms CategoryTheory.EvaluationData.TwistConeData.twistH0IsTriangulated
