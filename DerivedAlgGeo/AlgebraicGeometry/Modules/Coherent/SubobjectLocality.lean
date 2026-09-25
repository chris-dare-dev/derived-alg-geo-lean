/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Noetherian
import DerivedAlgGeo.CategoryTheory.Subobject.JointReflection

/-!
# Coherent subobject order is local on an open cover

Restriction to any open cover of a locally Noetherian scheme reflects order and
equality between coherent subobjects of one fixed coherent sheaf. The required
finite-limit preservation of `Coh.restrict` is established only inside the
order proof. No local subobject is extended or glued here.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Coh

variable {U : Scheme.{u}} [IsLocallyNoetherian U]
  (𝒰 : Scheme.OpenCover.{v} U) (E : Coh U) (P Q : Subobject E)

/-- An open cover detects order between existing coherent subobjects of `E`.
The cover need not be finite. -/
theorem subobject_le_iff_restrict_openCover :
    P ≤ Q ↔ ∀ i : 𝒰.I₀,
      Subobject.mapFunctor (restrict (𝒰.f i)) P ≤
        Subobject.mapFunctor (restrict (𝒰.f i)) Q := by
  let F : (i : 𝒰.I₀) → Coh U ⥤ Coh (𝒰.X i) := fun i => restrict (𝒰.f i)
  letI : ∀ i : 𝒰.I₀, PreservesFiniteLimits (F i) := fun i => by
    haveI : PreservesFiniteLimits (F i ⋙ ι (𝒰.X i)) := by
      change PreservesFiniteLimits (ι U ⋙ Scheme.Modules.restrictFunctor (𝒰.f i))
      exact comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_reflects_of_preserves (F i) (ι (𝒰.X i))
  letI : ∀ i : 𝒰.I₀, PreservesLimitsOfShape WalkingCospan (F i) :=
    fun i => inferInstance
  letI : ∀ i : 𝒰.I₀, (F i).PreservesMonomorphisms := fun i => inferInstance
  have hF : JointlyReflectIsomorphisms F := by
    constructor
    intro M N f hf
    exact restrict_jointlyReflectsIsomorphisms 𝒰 f (fun i => by
      change IsIso ((F i).map f)
      infer_instance)
  exact Subobject.le_iff_mapFunctor_le_of_jointlyReflectsIsomorphisms F hF P Q

/-- Equality of existing coherent subobjects is local on an open cover. -/
theorem subobject_eq_iff_restrict_openCover :
    P = Q ↔ ∀ i : 𝒰.I₀,
      Subobject.mapFunctor (restrict (𝒰.f i)) P =
        Subobject.mapFunctor (restrict (𝒰.f i)) Q := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply le_antisymm
    · exact (subobject_le_iff_restrict_openCover 𝒰 E P Q).2
        (fun i => (h i).le)
    · exact (subobject_le_iff_restrict_openCover 𝒰 E Q P).2
        (fun i => (h i).ge)

end AlgebraicGeometry.Coh
