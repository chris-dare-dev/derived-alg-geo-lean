/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Pullback and restriction of scheme-module sheaves

For a scheme morphism `f : X ⟶ Y` and an open `U ⊆ Y`, restriction of `f⁺ M` to
`f⁻¹ U` agrees with pullback of `M|_U` along the restricted morphism
`f|_U : X|_{f⁻¹ U} ⟶ Y|_U`.

The statement is expressed in Mathlib's slice-site category, because this is the common root used
by local generators, finite presentations, and intrinsic local freeness. The proof is assembled
only from the scheme-module pullback pseudofunctor and the equivalence between slice-site modules
and modules on an open subscheme.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable section

/-- Restricting a pulled-back module to an inverse-image open agrees with pulling back the
restriction along the restricted scheme morphism. -/
noncomputable def pullbackOverIso (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    ((pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      (overEquiv (f ⁻¹ᵁ U)).inverse.obj
        ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (M.over U))) := by
  let V : X.Opens := f ⁻¹ᵁ U
  let N : V.toScheme.Modules :=
    (pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (M.over U))
  let eU : (overEquiv U).functor.obj (M.over U) ≅ (pullback U.ι).obj M :=
    (overFunctorEquiv U).app M ≪≫ (restrictFunctorIsoPullback U.ι).app M
  let e : (overEquiv V).functor.obj (((pullback f).obj M).over V) ≅ N :=
    (overFunctorEquiv V).app ((pullback f).obj M) ≪≫
      (restrictFunctorIsoPullback V.ι).app ((pullback f).obj M) ≪≫
      (pullbackComp V.ι f).app M ≪≫
      (pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
      (pullbackComp (f ∣_ U) U.ι).symm.app M ≪≫
      (pullback (f ∣_ U)).mapIso eU.symm
  exact (overEquiv V).fullyFaithfulFunctor.preimageIso
    (e ≪≫ ((overEquiv V).counitIso.app N).symm)

end

end AlgebraicGeometry.Scheme.Modules
