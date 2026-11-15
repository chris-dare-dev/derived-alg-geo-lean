/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Descent along locally surjective morphisms

A morphism of presheaves of types `p : P ⟶ X` that is locally surjective for a Grothendieck
topology `J` is an epimorphism towards every `J`-sheaf: a morphism `φ : P ⟶ F` to a sheaf of types
that is constant on the fibres of `p` factors uniquely through `p`. Neither `P` nor `X` need be a
sheaf, and no sheafification is used, so this applies on large sites whose presheaf categories
have no sheafification functor.

## Main definitions

* `CategoryTheory.Presheaf.descOfIsLocallySurjective`: the factorization of `φ` through `p`.

## Main results

* `CategoryTheory.Presheaf.fac_descOfIsLocallySurjective`: `p ≫ descOfIsLocallySurjective = φ`.
* `CategoryTheory.Presheaf.hom_ext_of_isLocallySurjective`: two morphisms `X ⟶ F` to a sheaf that
  agree after precomposition with `p` are equal.

## Implementation notes

The value of the factorization on a section `x` of `X` is the amalgamation, over the covering
sieve `Presheaf.imageSieve p x`, of the images under `φ` of the local preimages of `x`. Mathlib's
`Sheaf.epi_of_isLocallySurjective'` is the uniqueness half for morphisms of sheaves.

## References

No literature source is followed. The gluing is that of Mathlib's `Subfunctor.sheafifyLift`,
applied to the local preimages `Presieve.FamilyOfElements.localPreimage` instead of to the sections
of a subpresheaf.

## Tags

sheaf, locally surjective, descent
-/

universe w v u

open Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {P X F : Cᵒᵖ ⥤ Type w}

/-- Two morphisms from the target of a locally surjective morphism of presheaves of types to a
sheaf are equal when they agree after precomposition with it. -/
theorem hom_ext_of_isLocallySurjective (p : P ⟶ X) [IsLocallySurjective J p]
    (hF : Presieve.IsSheaf J F) {ψ₁ ψ₂ : X ⟶ F} (h : p ≫ ψ₁ = p ≫ ψ₂) : ψ₁ = ψ₂ := by
  ext ⟨T⟩ x
  change ψ₁.app _ x = ψ₂.app _ x
  refine (hF _ (imageSieve_mem J p x)).isSeparatedFor.ext fun V f ⟨a, ha⟩ ↦ ?_
  have h₁ := NatTrans.naturality_apply ψ₁ f.op x
  have h₂ := NatTrans.naturality_apply ψ₂ f.op x
  rw [← h₁, ← h₂, ← ha]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) a

variable (p : P ⟶ X) [IsLocallySurjective J p] (hF : Presieve.IsSheaf J F) (φ : P ⟶ F)
  (hφ : ∀ ⦃T : Cᵒᵖ⦄ (a b : P.obj T), p.app T a = p.app T b → φ.app T a = φ.app T b)

include hφ in
/-- The images under `φ` of local preimages of a section of `X` are compatible when `φ` is
constant on the fibres of `p`. -/
lemma compatible_map_localPreimage {T : Cᵒᵖ} (x : X.obj T) :
    ((Presieve.FamilyOfElements.localPreimage p x).map φ).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
  simp only [Presieve.FamilyOfElements.map, Presieve.FamilyOfElements.localPreimage]
  rw [← NatTrans.naturality_apply φ g₁.op, ← NatTrans.naturality_apply φ g₂.op]
  apply hφ
  rw [NatTrans.naturality_apply p g₁.op, NatTrans.naturality_apply p g₂.op,
    app_localPreimage, app_localPreimage, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, ← op_comp, ← op_comp, w]

/-- A morphism `φ : P ⟶ F` to a sheaf of types that is constant on the fibres of a locally
surjective morphism `p : P ⟶ X` factors through `p`. -/
noncomputable def descOfIsLocallySurjective : X ⟶ F where
  app T := TypeCat.ofHom fun x ↦ (hF _ (imageSieve_mem J p x)).amalgamate _
    (compatible_map_localPreimage p φ hφ x)
  naturality T T' g := by
    ext x
    refine (hF _ (imageSieve_mem J p (X.map g x))).isSeparatedFor.ext fun V f hf ↦ ?_
    have hf' : imageSieve p x (f ≫ g.unop) := by
      change (imageSieve p x).pullback g.unop f
      rw [pullback_imageSieve]
      exact hf
    dsimp
    rw [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← Functor.map_comp_apply,
      show g ≫ f.op = (f ≫ g.unop).op from rfl, Presieve.IsSheafFor.valid_glue _ _ _ hf']
    simp only [Presieve.FamilyOfElements.map, Presieve.FamilyOfElements.localPreimage]
    apply hφ
    rw [app_localPreimage, app_localPreimage, op_comp, Functor.map_comp_apply]
    rfl

@[reassoc (attr := simp)]
lemma fac_descOfIsLocallySurjective : p ≫ descOfIsLocallySurjective p hF φ hφ = φ := by
  ext T a
  refine (hF _ (imageSieve_mem J p (p.app T a))).isSeparatedFor.ext fun V f hf ↦ ?_
  dsimp [descOfIsLocallySurjective]
  rw [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← NatTrans.naturality_apply φ f.op]
  simp only [Presieve.FamilyOfElements.map, Presieve.FamilyOfElements.localPreimage]
  apply hφ
  rw [app_localPreimage, NatTrans.naturality_apply p f.op]

end CategoryTheory.Presheaf
