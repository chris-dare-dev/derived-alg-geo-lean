import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Exactness
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.ExteriorPower
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.GeneratingSections
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Invertible
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Over
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Tensor

/-!
# Sheaves of modules on a ringed site

Extensions of Mathlib's `SheafOfModules`, at Mathlib's path
`Algebra/Category/ModuleCat/Sheaf/`: exactness of the forgetful functor,
restriction to over sites, generating sections from free epimorphisms,
intrinsic invertibility and rank-one local trivializations, tensor descent,
exterior powers, and finite presentation with its transport, locality, and
closure properties. Every signature here uses only a sheaf of rings on an
arbitrary site; scheme consumers live under `AlgebraicGeometry/Modules/`.
-/
