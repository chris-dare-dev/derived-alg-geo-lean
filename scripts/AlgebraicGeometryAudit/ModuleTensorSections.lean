/-
Section-level calculus for the sheafified tensor product and the stalk of a tensor product of module
sheaves, a slice of the AlgebraicGeometry audit (issue #1664, DQ1.2a).
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Sections
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Stalk

/-! ## Pure-tensor calculus (`Tensor/Sections.lean`)

Morphisms out of `M ⊗ N` and `(M ⊗ N) ⊗ P` are determined by their values on pure tensors, and the
tensor of morphisms, the unitors and the associator are computed on pure tensors. `TensorLiftData`
is the universal property of the sheafified tensor product in terms of sectionwise bilinear data.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.section_ext_of_locally
#print axioms AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext
#print axioms AlgebraicGeometry.Scheme.Modules.tensorObj_tensorObj_hom_ext
#print axioms AlgebraicGeometry.Scheme.Modules.tmulSection_add_right
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitLeftIso_hom_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitRightIso_hom_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.tensorAssocIso_hom_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.mk.inj
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.toFun
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.add_left
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.smul_left
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.add_right
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.smul_right
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.res
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.toPre
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.lift
#print axioms AlgebraicGeometry.Scheme.Modules.TensorLiftData.lift_app_tmulSection

/-! ## Stalks of the sheafified tensor product (`Tensor/Stalk.lean`)

The stalk of `M ⊗ N` at `x` is `Mₓ ⊗[𝒪ₓ] Nₓ`, with the germ of a pure tensor of sections going to the
tensor of the germs.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleGerm_exists
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleGerm_smul
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleGerm_res
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalk_smul_eq
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkBridge
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkTensorEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkTensorEquiv_germ_tmul_germ
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkGerm_exists_pair
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkTensorEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkTensorEquiv_germ_tmul_germ
