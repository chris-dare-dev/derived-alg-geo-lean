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
import DerivedAlgGeo.CategoryTheory.DGCategory

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
