/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.HarderNarasimhan
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subobject lemmas for owner stability functions

These are the categorical primitives needed by the owner HN existence and
uniqueness arguments in the repository-owned stability-function API.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- The canonical cokernel sequence of a monomorphism is short exact. -/
theorem shortExact_of_mono {X Y : A} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (by simp)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f)
    inferInstance inferInstance

/-- A subobject has zero underlying object exactly when it is bottom. -/
@[simp]
theorem subobject_isZero_iff_eq_bot {E : A} (B : Subobject E) :
    IsZero (B : A) ↔ B = ⊥ := by
  constructor
  · intro hB
    have harrow : B.arrow = 0 := zero_of_source_iso_zero _ hB.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · rintro rfl
    exact (isZero_zero A).of_iso Subobject.botCoeIsoZero

/-- A nonzero subobject is not bottom. -/
theorem subobject_ne_bot_of_not_isZero {E : A} {B : Subobject E}
    (hB : ¬IsZero (B : A)) : B ≠ ⊥ :=
  fun h => hB ((subobject_isZero_iff_eq_bot B).2 h)

/-- A subobject distinct from bottom has nonzero underlying object. -/
theorem subobject_not_isZero_of_ne_bot {E : A} {B : Subobject E}
    (hB : B ≠ ⊥) : ¬IsZero (B : A) :=
  fun h => hB ((subobject_isZero_iff_eq_bot B).1 h)

/-- The top and bottom subobjects of a nonzero object differ. -/
theorem subobject_top_ne_bot_of_not_isZero {E : A} (hE : ¬IsZero E) :
    (⊤ : Subobject E) ≠ ⊥ := by
  intro h
  apply hE
  have htop : IsZero ((⊤ : Subobject E) : A) :=
    (subobject_isZero_iff_eq_bot _).2 h
  exact htop.of_iso (asIso (⊤ : Subobject E).arrow).symm

/-- The inclusion from the bottom subobject is the zero morphism. -/
@[simp]
theorem subobject_ofLE_bot {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    Subobject.ofLE ⊥ S h = 0 :=
  zero_of_source_iso_zero _ Subobject.botCoeIsoZero

/-- The cokernel of the inclusion from bottom is the target subobject. -/
def subobjectCokernelBotIso {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    cokernel (Subobject.ofLE ⊥ S h) ≅ (S : A) := by
  rw [subobject_ofLE_bot S h]
  exact cokernelZeroIsoTarget

/-- A proper subobject of an abelian object has nonzero cokernel. -/
theorem cokernel_not_isZero_of_ne_top {E : A} {B : Subobject E}
    (hB : B ≠ ⊤) : ¬IsZero (cokernel B.arrow) := by
  intro hcoker
  haveI : Epi B.arrow := Preadditive.epi_of_isZero_cokernel B.arrow hcoker
  haveI : IsIso B.arrow := isIso_of_mono_of_epi B.arrow
  exact hB (Subobject.eq_top_of_isIso_arrow B)

/-- Precomposing a morphism by an epimorphism does not change its image
subobject in an abelian category. -/
theorem imageSubobject_epi_comp {X Y Z : A} (e : X ⟶ Y) [Epi e]
    (f : Y ⟶ Z) : imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Mono (Subobject.ofLE _ _ hle) := by
    apply (mono_comp_iff_of_mono _ (imageSubobject f).arrow).mp
    rw [Subobject.ofLE_arrow]
    infer_instance
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle)) (by
    rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow])

/-- The image subobject of an epimorphism is top. -/
theorem imageSubobject_eq_top_of_epi {X Y : A} (f : X ⟶ Y) [Epi f] :
    imageSubobject f = ⊤ := by
  haveI : Epi (imageSubobject f).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp f)
  haveI : IsIso (imageSubobject f).arrow :=
    isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

/-- Pullback along an epimorphism is injective on subobjects. -/
theorem pullback_obj_injective_of_epi {X Y : A} (p : X ⟶ Y) [Epi p] :
    Function.Injective (Subobject.pullback p).obj := by
  intro B₁ B₂ h
  haveI : Epi (Subobject.pullbackπ p B₁) := by
    rw [← (Subobject.isPullback p B₁).isoPullback_hom_fst]
    infer_instance
  haveI : Epi (Subobject.pullbackπ p B₂) := by
    rw [← (Subobject.isPullback p B₂).isoPullback_hom_fst]
    infer_instance
  calc
    B₁ = imageSubobject (Subobject.pullbackπ p B₁ ≫ B₁.arrow) := by
      rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    _ = imageSubobject (((Subobject.pullback p).obj B₁).arrow ≫ p) := by
      rw [(Subobject.isPullback p B₁).w]
    _ = imageSubobject (((Subobject.pullback p).obj B₂).arrow ≫ p) := by rw [h]
    _ = imageSubobject (Subobject.pullbackπ p B₂ ≫ B₂.arrow) := by
      rw [← (Subobject.isPullback p B₂).w]
    _ = B₂ := by
      rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]

end StabilityFunction

end CategoryTheory.Triangulated
