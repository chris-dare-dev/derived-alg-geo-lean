/-
Topological stalk-tensor slice of the AlgebraicGeometry audit, split out so concurrent branches
append to different files (#480). `EnumDecls.libraryOf` routes the `Topology` subject through
this audit. See the umbrella file for the contract.
-/
import DerivedAlgGeo.Topology.Sheaves.ModuleTensor.StalkTensor

/-! ## The stalk of a tensor product of presheaves of modules (#833)

`stalkTensorEquiv` is the headline: `Mₓ ⊗[Rₓ] Pₓ ≅ (M ⊗ P)ₓ`. Everything above it is the
two-stage colimit construction of the backward map and the single cocone of the forward one.
-/

#print axioms PresheafOfModules.StalkTensor
#print axioms PresheafOfModules.stalkTensorModuleAt
#print axioms PresheafOfModules.stalkTensorBilin
#print axioms PresheafOfModules.resSec
#print axioms PresheafOfModules.germTmul
#print axioms PresheafOfModules.germTmul_res_left
#print axioms PresheafOfModules.germTmul_res_right
#print axioms PresheafOfModules.germTmul_congr
#print axioms PresheafOfModules.germTmul_self
#print axioms PresheafOfModules.germ_smul_germTmul_self
#print axioms PresheafOfModules.germ_smul_germTmul
#print axioms PresheafOfModules.germTmul_add_left
#print axioms PresheafOfModules.germTmul_add_right
#print axioms PresheafOfModules.germTmulCoconeRight
#print axioms PresheafOfModules.germTmulRight
#print axioms PresheafOfModules.germTmulRight_germ
#print axioms PresheafOfModules.germTmulRight_res_left
#print axioms PresheafOfModules.germTmulRight_add
#print axioms PresheafOfModules.germTmulCoconeLeft
#print axioms PresheafOfModules.germTmulBiadd
#print axioms PresheafOfModules.germTmulBiadd_germ
#print axioms PresheafOfModules.germ_smul_germTmul_self_right
#print axioms PresheafOfModules.germTmulBiadd_smul_left
#print axioms PresheafOfModules.germTmulBiadd_smul_right
#print axioms PresheafOfModules.germTmulBiadd_add_left
#print axioms PresheafOfModules.germTmulBilin
#print axioms PresheafOfModules.stalkTensorBackward
#print axioms PresheafOfModules.stalkTensorBackward_tmul
#print axioms PresheafOfModules.stalkTensorBackward_germ_tmul_germ
#print axioms PresheafOfModules.stalkTensorLeg
#print axioms PresheafOfModules.stalkTensorLeg_tmul
#print axioms PresheafOfModules.stalkTensorLeg_res
#print axioms PresheafOfModules.stalkTensorForwardCocone
#print axioms PresheafOfModules.stalkTensorForward
#print axioms PresheafOfModules.stalkTensorForward_germ
#print axioms PresheafOfModules.stalkTensorForward_germTmul
#print axioms PresheafOfModules.stalkTensorForward_backward
#print axioms PresheafOfModules.stalkTensorBackward_forward
#print axioms PresheafOfModules.stalkTensorEquiv
#print axioms PresheafOfModules.stalkTensorEquiv_germ_tmul_germ
#print axioms PresheafOfModules.stalkTensorEquiv_symm_germ

/-! ## The stalk map of a morphism, and whiskering (#833)

`isIso_stalkMapAdd_whiskerLeft` is the point: tensoring a stalk isomorphism with an arbitrary
`Mₓ` is again an isomorphism, which is what removes the rank-one hypothesis downstream.
-/

#print axioms PresheafOfModules.stalkMapAdd
#print axioms PresheafOfModules.stalkMapAdd_germ
#print axioms PresheafOfModules.stalkMap
#print axioms PresheafOfModules.stalkMap_germ
#print axioms PresheafOfModules.whiskerLeft_app_tmul
#print axioms PresheafOfModules.stalkMapAdd_whiskerLeft
#print axioms PresheafOfModules.isIso_stalkMapAdd_whiskerLeft
