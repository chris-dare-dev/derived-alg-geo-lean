/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic.Definitions
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.PhaseGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.WeakHnTilt

/-!
# Stability functions on weak HN tilts from generator positivity

An HRS-tilted heart is generated under extensions by the HN-torsion objects
and the shifts of HN-free objects. Consequently, an additive ambient charge is
a strict stability function on the tilt as soon as it lies in the semi-closed
upper half-plane on every nonzero generator of those two kinds.

This assembly is independent of how generator positivity is proved. In
particular, Mukai-square and support-dimension arguments belong in a Mukai
consumer, not in this generic weak-tilting module.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u

namespace CategoryTheory.Triangulated.WeakStabilityFunctionOn

attribute [local instance] TStructure.heartFullSubcategoryAbelian

variable {C : Type u} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {t : TStructure C}

/-- An additive ambient charge is positive on a nonzero object of the HN tilt
when it is positive on every nonzero torsion generator and shifted free
generator. -/
theorem mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) (Z : K₀ C →+ ℂ)
    (hTors : ∀ (T₀ : t.heart.FullSubcategory), ¬IsZero T₀ →
      T₀ ∈ hnTors W μ₀ → Z (K₀.of C T₀.obj) ∈ semiClosedUpperHalfPlane)
    (hFree : ∀ (F₀ : t.heart.FullSubcategory), ¬IsZero F₀ →
      F₀ ∈ hnFree W μ₀ →
        Z (K₀.of C (F₀.obj⟦(1 : ℤ)⟧)) ∈ semiClosedUpperHalfPlane)
    {X : C} (hX : (W.hnTilt μ₀ hHN).heart X) (hX0 : ¬IsZero X) :
    Z (K₀.of C X) ∈ semiClosedUpperHalfPlane := by
  obtain ⟨F₀, T₀, hF, hT, f, g, h, hdist⟩ :=
    (W.hnTilt_heart_iff μ₀ hHN X).mp hX
  let FH : t.heart.FullSubcategory := ⟨F₀, hF.1⟩
  let TH : t.heart.FullSubcategory := ⟨T₀, hT.1⟩
  have hsplit : Z (K₀.of C X) =
      Z (K₀.of C (F₀⟦(1 : ℤ)⟧)) + Z (K₀.of C T₀) := by
    have hK := congrArg Z (K₀.of_triangle C (Triangle.mk f g h) hdist)
    simpa only [Triangle.mk, map_add] using hK
  by_cases hF0 : IsZero FH
  · have hF0' : IsZero F₀ := (t.heart).ι.map_isZero hF0
    have hFshift0 : IsZero (F₀⟦(1 : ℤ)⟧) :=
      (shiftFunctor C (1 : ℤ)).map_isZero hF0'
    by_cases hT0 : IsZero TH
    · have hT0' : IsZero T₀ := (t.heart).ι.map_isZero hT0
      exact absurd
        ((Triangle.mk f g h).isZero₂_of_isZero₁₃ hdist hFshift0 hT0') hX0
    · have hTupper : Z (K₀.of C T₀) ∈ semiClosedUpperHalfPlane :=
        hTors TH hT0 hT.2
      rw [hsplit, K₀.of_isZero C hFshift0, Z.map_zero, zero_add]
      exact hTupper
  · have hFupper : Z (K₀.of C (F₀⟦(1 : ℤ)⟧)) ∈ semiClosedUpperHalfPlane :=
      hFree FH hF0 hF.2
    by_cases hT0 : IsZero TH
    · have hT0' : IsZero T₀ := (t.heart).ι.map_isZero hT0
      rw [hsplit, K₀.of_isZero C hT0', Z.map_zero, add_zero]
      exact hFupper
    · have hTupper : Z (K₀.of C T₀) ∈ semiClosedUpperHalfPlane :=
        hTors TH hT0 hT.2
      rw [hsplit]
      exact add_mem_semiClosedUpperHalfPlane hFupper hTupper

/-- Build a strict stability function on the HN-tilted heart from positivity
on its two kinds of nonzero generators. -/
def hnTiltStabilityFunction
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) (Z : K₀ C →+ ℂ)
    (hTors : ∀ (T₀ : t.heart.FullSubcategory), ¬IsZero T₀ →
      T₀ ∈ hnTors W μ₀ → Z (K₀.of C T₀.obj) ∈ semiClosedUpperHalfPlane)
    (hFree : ∀ (F₀ : t.heart.FullSubcategory), ¬IsZero F₀ →
      F₀ ∈ hnFree W μ₀ →
        Z (K₀.of C (F₀.obj⟦(1 : ℤ)⟧)) ∈ semiClosedUpperHalfPlane) :
    WeakStabilityCondition.StabilityFunction (W.hnTilt μ₀ hHN) where
  Z := Z
  nonzero_mem _ hX :=
    W.mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart μ₀ hHN Z
      hTors hFree hX.1 hX.2

@[simp]
theorem hnTiltStabilityFunction_Z
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) (Z : K₀ C →+ ℂ)
    (hTors : ∀ (T₀ : t.heart.FullSubcategory), ¬IsZero T₀ →
      T₀ ∈ hnTors W μ₀ → Z (K₀.of C T₀.obj) ∈ semiClosedUpperHalfPlane)
    (hFree : ∀ (F₀ : t.heart.FullSubcategory), ¬IsZero F₀ →
      F₀ ∈ hnFree W μ₀ →
        Z (K₀.of C (F₀.obj⟦(1 : ℤ)⟧)) ∈ semiClosedUpperHalfPlane) :
    (W.hnTiltStabilityFunction μ₀ hHN Z hTors hFree).Z = Z := rfl

end CategoryTheory.Triangulated.WeakStabilityFunctionOn
