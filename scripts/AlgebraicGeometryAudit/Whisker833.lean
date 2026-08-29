/-
Whiskering slice of the AlgebraicGeometry audit, split out so concurrent branches append to
different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic

/-! ## Sheafification inverts `M ◁ toSheafify` for arbitrary `M` (#833)

The three declarations that take `PresheafOfModules.isIso_stalkMapAdd_whiskerLeft` from a stalk
statement to the tree's comparison morphism. The rank-one variants above them are unchanged and
remain the only route available over a general site.
-/

#print axioms TopCat.Presheaf.W_of_isIso_stalkFunctor_map
#print axioms PresheafOfModules.W_whiskerLeft_of_isIso_stalk
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_sheafification_map_whiskerLeft_unit
