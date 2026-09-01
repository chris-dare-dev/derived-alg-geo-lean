import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent
import DerivedAlgGeo.AlgebraicGeometry.Modules.ExteriorPower
import DerivedAlgGeo.AlgebraicGeometry.Modules.LocallySurjective
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor

/-!
# Sheaves of modules on a scheme

Everything stated about Mathlib's `X.Modules`: affine comparisons,
presentations, restriction, pullback, pushforward, tensor products, exterior
powers, and the refinement chain `X.Modules ⊇ QCoh(X) ⊇ Coh(X)` under
`Quasicoherent/` and `Coherent/`. Mathlib defines `X.Modules` in
`AlgebraicGeometry/Modules/Sheaf.lean`, so the subcategories cut out of it live
here, with the object, as `ModuleCat/Abelian.lean` lives with `ModuleCat`.
-/
