import DerivedAlgGeo.CategoryTheory.Linear.ModuleObject.Basic
import DerivedAlgGeo.CategoryTheory.Linear.ModuleObject.ModuleCat
import DerivedAlgGeo.CategoryTheory.Linear.ModuleObject.Tensor

/-! # Module objects of a linear category

For a `k`-linear category `A` and a `k`-algebra `R`, the category `A_R` of `R`-module objects of
`A` (objects with a `k`-algebra map `R →ₐ[k] End E`): its limits, colimits and abelian
structure, restriction and base change of scalars, the tensor action `M ⊗_k E` of `k`-modules on
`A` and flat objects, the pseudofunctor `R ↦ A_R`, and the equivalence
`(ModuleCat k)_R ≌ ModuleCat R`. -/
