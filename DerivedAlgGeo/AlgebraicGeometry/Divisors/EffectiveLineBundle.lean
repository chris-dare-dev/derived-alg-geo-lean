/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.CartierLineBundle
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Effective

/-!
# Effective Cartier-divisor sequences twisted by a line bundle

The normalized Cartier sequence for `D` and `E` has line terms
`O_X(E-D)` and `O_X(E)`. This leaf tensors that sequence by arbitrary
`LineBundleData L`, obtaining line terms
`L ⊗ O_X(E-D)` and `L ⊗ O_X(E)`. Exactness comes from the generic exact
tensor functor; coherence of the quotient is then inherited from its
cokernel presentation.

This is the reusable geometric root needed by divisor-chain applications.
It keeps arbitrary base line bundles out of the Enriques paper adapter.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

/-- The normalized Cartier-divisor sequence, tensored on the left by an
arbitrary line bundle. -/
noncomputable def lineBundleTwistSequence
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) : ShortComplex X.Modules :=
  (D.twistSequence E).map (Modules.tensorLeftFunctor L.line)

@[simp]
theorem lineBundleTwistSequence_X₁
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) :
    (D.lineBundleTwistSequence L E).X₁ =
      (L.tensor (CartierDivisor.lineBundleData (E - D.divisor))).line :=
  rfl

@[simp]
theorem lineBundleTwistSequence_X₂
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) :
    (D.lineBundleTwistSequence L E).X₂ =
      (L.tensor (CartierDivisor.lineBundleData E)).line :=
  rfl

/-- The source line of the tensor-twisted sequence is coherent. -/
theorem lineBundleTwistSource_isCoherent
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) :
    Scheme.coherent X (D.lineBundleTwistSequence L E).X₁ := by
  rw [lineBundleTwistSequence_X₁]
  exact (L.tensor
    (CartierDivisor.lineBundleData (E - D.divisor))).isCoherent

/-- The middle line of the tensor-twisted sequence is coherent. -/
theorem lineBundleTwistMiddle_isCoherent
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) :
    Scheme.coherent X (D.lineBundleTwistSequence L E).X₂ := by
  rw [lineBundleTwistSequence_X₂]
  exact (L.tensor (CartierDivisor.lineBundleData E)).isCoherent

/-- Tensoring by a line bundle preserves the short exact Cartier sequence. -/
theorem lineBundleTwistSequence_shortExact
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) :
    (D.lineBundleTwistSequence L E).ShortExact :=
  Modules.shortExact_map_tensorLeft_of_invertible L.line
    (D.twistSequence E) (D.twistSequence_shortExact E)

/-- The target of the line-bundle-twisted sequence is the cokernel of its
first map. -/
noncomputable def lineBundleTwistCokernelIso
    (D : EffectiveCartierDivisor (X := X)) (L : Modules.LineBundleData X)
    (E : CartierDivisor X) :
    cokernel (D.lineBundleTwistSequence L E).f ≅
      (D.lineBundleTwistSequence L E).X₃ :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (D.lineBundleTwistSequence L E).f)
    (D.lineBundleTwistSequence_shortExact L E).gIsCokernel

/-- The quotient in the line-bundle-twisted sequence is coherent. -/
theorem lineBundleTwistTarget_isCoherent
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    Scheme.coherent X (D.lineBundleTwistSequence L E).X₃ :=
  (Scheme.coherent X).prop_of_iso (D.lineBundleTwistCokernelIso L E)
    ((Scheme.coherent X).prop_cokernel
      (D.lineBundleTwistSequence L E).f
      (D.lineBundleTwistSource_isCoherent L E)
      (D.lineBundleTwistMiddle_isCoherent L E))

/-- The coherent-sheaf form of the line-bundle-twisted Cartier sequence. Its
first two objects are the canonical `Coh X` avatars of the two tensor-product
line bundles. -/
noncomputable def cohLineBundleTwistSequence
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    ShortComplex (Coh X) :=
  ShortComplex.mk
    (⟨(D.lineBundleTwistSequence L E).f⟩ :
      (⟨(D.lineBundleTwistSequence L E).X₁,
        D.lineBundleTwistSource_isCoherent L E⟩ : Coh X) ⟶
        (⟨(D.lineBundleTwistSequence L E).X₂,
          D.lineBundleTwistMiddle_isCoherent L E⟩ : Coh X))
    (⟨(D.lineBundleTwistSequence L E).g⟩ :
      (⟨(D.lineBundleTwistSequence L E).X₂,
        D.lineBundleTwistMiddle_isCoherent L E⟩ : Coh X) ⟶
        (⟨(D.lineBundleTwistSequence L E).X₃,
          D.lineBundleTwistTarget_isCoherent L E⟩ : Coh X))
    (by
      apply ObjectProperty.hom_ext
      exact (D.lineBundleTwistSequence L E).zero)

/-- The coherent line-bundle-twisted Cartier sequence is short exact. -/
theorem cohLineBundleTwistSequence_shortExact
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    (D.cohLineBundleTwistSequence L E).ShortExact := by
  letI : (Coh.ι X).Faithful := by
    change (Scheme.coherent X).ι.Faithful
    infer_instance
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (Coh.ι X)
  change (D.lineBundleTwistSequence L E).ShortExact
  exact D.lineBundleTwistSequence_shortExact L E

end

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor
