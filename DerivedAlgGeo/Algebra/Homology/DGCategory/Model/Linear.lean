/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Linear
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model.Complexes

/-!
# Linearity of the standard dg category of complexes

For a commutative ring `k`, Mathlib's Hom-complexes of complexes of
`k`-modules carry their existing pointwise `k`-module structures.  Mathlib's
linearity lemmas for the Hom differential and cochain composition therefore
supply the `DGLinear k` structure on `Cdg (ModuleCat k)` directly.

No additional module structure is introduced here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v w

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex DGCategoryStruct

namespace Cdg

variable (k : Type w) [CommRing k]

/-- Expose Mathlib's existing pointwise module structure through the opaque
`Cdg`/`dgHom` wrappers.  This is a definitional bridge, not a new action. -/
instance homModule (K L : Cdg (ModuleCat.{v} k)) (p : ℤ) :
    Module k ((dgHom K L).X p) := by
  change Module k (CochainComplex.HomComplex.Cochain
    (of (ModuleCat.{v} k) K) (of (ModuleCat.{v} k) L) p)
  infer_instance

/-- The standard dg category of cochain complexes of `k`-modules is
`k`-linear. -/
instance linear : DGLinear k (Cdg (ModuleCat.{v} k)) where
  d_smul p q c f := by
    change CochainComplex.HomComplex.δ p q (c • f) =
      c • CochainComplex.HomComplex.δ p q f
    exact CochainComplex.HomComplex.δ_smul (R := k) p q c f
  comp_smul_left p q r h c f g := by
    change (c • f).comp g h = c • f.comp g h
    exact CochainComplex.HomComplex.Cochain.smul_comp c f g h
  comp_smul_right p q r h c f g := by
    change f.comp (c • g) h = c • f.comp g h
    exact CochainComplex.HomComplex.Cochain.comp_smul f c g h

end Cdg

end CategoryTheory
