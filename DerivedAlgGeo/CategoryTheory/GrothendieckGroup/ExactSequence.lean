/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Grothendieck classes of bounded exact sequences

This file supplies the abelian-group calculation needed to take the Euler
class of a bounded cohomology sequence.  For an exact pair `X ⟶ Y ⟶ Z`, the
middle class is the sum of the two image classes.  Applying that identity to
the three consecutive exact pairs in

`… ⟶ Aᵢ ⟶ Bᵢ ⟶ Cᵢ ⟶ Aᵢ₊₁ ⟶ …`

and summing with alternating signs gives

`χ(B) = χ(A) + χ(C)`.

The finiteness hypothesis is stated as finite support of the nonzero objects,
not merely of their `K₀Ab` classes.  A nonzero object may have zero
Grothendieck class, while the proof also has to control the image objects.
For bounded cohomology families the stronger objectwise statement is exactly
what the usual vanishing bounds provide.
-/

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

namespace K₀Ab

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- An indexed family has finite nonzero support when all but finitely many of
its objects are zero objects. -/
def HasFiniteNonzeroSupport {ι : Type*} (X : ι → A) : Prop :=
  {i | ¬ IsZero (X i)}.Finite

/-- An exact pair decomposes the class of its middle object into the classes
of the two images. -/
theorem of_exact {S : ShortComplex A} (hS : S.Exact) :
    of S.X₂ = of (Abelian.image S.f) + of (Abelian.image S.g) := by
  let S' : ShortComplex A :=
    ShortComplex.mk (Abelian.image.ι S.f) (factorThruImage S.g) (by
      apply (cancel_mono (image.ι S.g)).1
      simpa only [Category.assoc, image.fac, zero_comp] using
        Abelian.image_ι_comp_eq_zero S.zero)
  have hImage :
      (ShortComplex.mk (Abelian.image.ι S.f) S.g
        (Abelian.image_ι_comp_eq_zero S.zero)).Exact :=
    (S.exact_iff_exact_image_ι).mp hS
  have hS'Exact : S'.Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    simpa only [S'] using hImage.isColimitImage
  have hS'ShortExact : S'.ShortExact :=
    { mono_f := inferInstance
      epi_g := inferInstance
      exact := hS'Exact }
  have h := of_shortExact S' hS'ShortExact
  rw [← of_iso (Abelian.imageIsoImage S.g)] at h
  exact h

/-- The alternating Grothendieck class of an integer-indexed family.  The
definition is total; the additivity theorem below uses finite nonzero support. -/
noncomputable def eulerClass (X : ℤ → A) : K₀Ab A :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • of (X i)

private theorem hasFiniteSupport_altImage {X Y : ℤ → A}
    (f : ∀ i, X i ⟶ Y i) (hX : HasFiniteNonzeroSupport X) :
    Function.HasFiniteSupport
      (fun i : ℤ => (i.negOnePow : ℤ) • of (Abelian.image (f i))) := by
  refine hX.subset ?_
  intro i hi hXi
  have himage : IsZero (Abelian.image (f i)) :=
    hXi.of_epi (Abelian.factorThruImage (f i))
  apply hi
  change (i.negOnePow : ℤ) • of (Abelian.image (f i)) = 0
  rw [of_isZero himage, smul_zero]

/-- The alternating Grothendieck class is additive along a bounded
`ℤ`-indexed long exact sequence

`… ⟶ A i ⟶ B i ⟶ C i ⟶ A (i+1) ⟶ …`.

There are no endpoint mono/epi hypotheses: the proof telescopes after shifting
the integer index. -/
theorem eulerClass_add_of_exact
    {A₀ B C : ℤ → A}
    (f : ∀ i, A₀ i ⟶ B i) (g : ∀ i, B i ⟶ C i)
    (δ : ∀ i, C i ⟶ A₀ (i + 1))
    (hfg₀ : ∀ i, f i ≫ g i = 0)
    (hgδ₀ : ∀ i, g i ≫ δ i = 0)
    (hδf₀ : ∀ i, δ i ≫ f (i + 1) = 0)
    (hfg : ∀ i, (ShortComplex.mk (f i) (g i) (hfg₀ i)).Exact)
    (hgδ : ∀ i, (ShortComplex.mk (g i) (δ i) (hgδ₀ i)).Exact)
    (hδf : ∀ i, (ShortComplex.mk (δ i) (f (i + 1)) (hδf₀ i)).Exact)
    (hA : HasFiniteNonzeroSupport A₀)
    (hB : HasFiniteNonzeroSupport B)
    (hC : HasFiniteNonzeroSupport C) :
    eulerClass B = eulerClass A₀ + eulerClass C := by
  let alt (X : ℤ → A) (i : ℤ) : K₀Ab A :=
    (i.negOnePow : ℤ) • of (X i)
  let ρ : ℤ → K₀Ab A := fun i =>
    (i.negOnePow : ℤ) • of (Abelian.image (f i))
  let σ : ℤ → K₀Ab A := fun i =>
    (i.negOnePow : ℤ) • of (Abelian.image (g i))
  let d : ℤ → K₀Ab A := fun i =>
    (i.negOnePow : ℤ) • of (Abelian.image (δ i))
  have hρ : Function.HasFiniteSupport ρ :=
    hasFiniteSupport_altImage f hA
  have hσ : Function.HasFiniteSupport σ :=
    hasFiniteSupport_altImage g hB
  have hd : Function.HasFiniteSupport d :=
    hasFiniteSupport_altImage δ hC
  have hb : ∀ i, alt B i = ρ i + σ i := by
    intro i
    dsimp only [alt, ρ, σ]
    rw [of_exact (hfg i), smul_add]
  have hc : ∀ i, alt C i = σ i + d i := by
    intro i
    dsimp only [alt, σ, d]
    rw [of_exact (hgδ i), smul_add]
  have ha : ∀ i, alt A₀ (i + 1) = -(d i) + ρ (i + 1) := by
    intro i
    dsimp only [alt, d, ρ]
    rw [of_exact (hδf i), Int.negOnePow_succ]
    simp only [Units.val_neg, neg_smul, smul_add]
  have sB : ∑ᶠ i : ℤ, alt B i = (∑ᶠ i : ℤ, ρ i) + ∑ᶠ i : ℤ, σ i := by
    rw [← finsum_add_distrib hρ hσ]
    exact finsum_congr hb
  have sC : ∑ᶠ i : ℤ, alt C i = (∑ᶠ i : ℤ, σ i) + ∑ᶠ i : ℤ, d i := by
    rw [← finsum_add_distrib hσ hd]
    exact finsum_congr hc
  have sA : ∑ᶠ i : ℤ, alt A₀ i = (∑ᶠ i : ℤ, ρ i) - ∑ᶠ i : ℤ, d i := by
    have shift : ∑ᶠ i : ℤ, alt A₀ (i + 1) = ∑ᶠ i : ℤ, alt A₀ i :=
      finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    have shiftρ : ∑ᶠ i : ℤ, ρ (i + 1) = ∑ᶠ i : ℤ, ρ i :=
      finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    have hneg : Function.HasFiniteSupport (fun i => -(d i)) := by
      change (Function.support fun i => -(d i)).Finite
      change (Function.support d).Finite at hd
      have heq : Function.support (fun i => -(d i)) = Function.support d := by
        ext i
        simp only [Function.mem_support, neg_ne_zero]
      rw [heq]
      exact hd
    have hρshift : Function.HasFiniteSupport (fun i => ρ (i + 1)) := by
      change (Function.support fun i => ρ (i + 1)).Finite
      change (Function.support ρ).Finite at hρ
      have heq : Function.support (fun i : ℤ => ρ (i + 1)) =
          (fun i : ℤ => i + 1) ⁻¹' Function.support ρ := rfl
      rw [heq]
      exact hρ.preimage ((Equiv.addRight (1 : ℤ)).injective.injOn)
    calc
      ∑ᶠ i : ℤ, alt A₀ i = ∑ᶠ i : ℤ, alt A₀ (i + 1) := shift.symm
      _ = ∑ᶠ i : ℤ, (-(d i) + ρ (i + 1)) := finsum_congr ha
      _ = (∑ᶠ i : ℤ, -(d i)) + ∑ᶠ i : ℤ, ρ (i + 1) :=
        finsum_add_distrib hneg hρshift
      _ = -(∑ᶠ i : ℤ, d i) + ∑ᶠ i : ℤ, ρ i := by
        rw [finsum_neg_distrib, shiftρ]
      _ = (∑ᶠ i : ℤ, ρ i) - ∑ᶠ i : ℤ, d i := by abel
  change (∑ᶠ i : ℤ, alt B i) =
    (∑ᶠ i : ℤ, alt A₀ i) + ∑ᶠ i : ℤ, alt C i
  rw [sA, sB, sC]
  abel

end K₀Ab

end CategoryTheory
