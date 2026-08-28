/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.CategoryTheory.FiniteFiltration
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Almost-disconnected morphisms

This is the neutral scheme-morphism root of Definition B.1 in
[arXiv:2607.28411v1](https://arxiv.org/abs/2607.28411v1).  A witness for `p : X ⟶ Y`
consists of a finite filtration of `𝒪_X`; each graded piece is the pushforward of the inverse of
an invertible sheaf from a closed subscheme `Xᵢ ↪ X` whose composite with `p` is an isomorphism
to `Y`.

The definition deliberately contains no stability-condition, moduli, or quotient-presentation
data.  It is a `MorphismProperty`, so generic behavior belongs at this root and downstream
stability adapters can consume it without owning it.

The paper also proves flat-base-change and composition closure (Lemma B.2).  Those theorems are
not asserted here: at the pinned Mathlib revision, the required arbitrary cartesian comparison
`g^* i_* L ≅ i'_* g'^* L` and an exact scheme-module pullback API are not available at this
neutral import boundary.  In particular, the repository's current exact flat-pullback theorem
lives below `StabilityCondition/Families`, which this root must not import.
-/

open CategoryTheory Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

namespace AlmostDisconnected

variable {X Y : Scheme.{u}}

/-- The structure sheaf, regarded as an object of the scheme's module category. -/
noncomputable abbrev structureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Explicit data witnessing that a scheme morphism is almost disconnected.

This is Definition B.1 of arXiv:2607.28411v1, with equalities replaced by chosen isomorphisms.
The line bundle stores both `Lᵢ` and its tensor inverse, so `gradedIso` can name `Lᵢ⁻¹`
without making a noncanonical choice. -/
structure Witness (p : X ⟶ Y) where
  /-- The filtration `0 = F₀ ⊂ ⋯ ⊂ Fₘ = 𝒪_X`. -/
  filtration : FiniteFiltration X.Modules (structureSheaf X)
  /-- The closed support `Xᵢ` of each graded piece. -/
  support : Fin filtration.length → Scheme.{u}
  /-- The inclusion `ιᵢ : Xᵢ ⟶ X`. -/
  inclusion : ∀ i, support i ⟶ X
  /-- Each `ιᵢ` is a closed immersion. -/
  inclusion_isClosedImmersion : ∀ i, IsClosedImmersion (inclusion i)
  /-- The restriction of `p` to `Xᵢ` identifies `Xᵢ` with the base. -/
  baseIso : ∀ i, support i ≅ Y
  /-- The chosen base isomorphism is the composite `ιᵢ ≫ p`. -/
  baseIso_hom : ∀ i, (baseIso i).hom = inclusion i ≫ p
  /-- The invertible sheaf `Lᵢ` and its chosen inverse. -/
  lineBundle : ∀ i, Scheme.Modules.LineBundleData (support i)
  /-- The `i`th graded piece is `ιᵢ,* Lᵢ⁻¹`. -/
  gradedIso : ∀ i,
    filtration.graded i ≅
      (Scheme.Modules.pushforward (inclusion i)).obj (lineBundle i).inverse

namespace Witness

variable {p : X ⟶ Y}

/-- Install the closed-immersion certificate carried by a witness. -/
instance (W : Witness p) (i : Fin W.filtration.length) :
    IsClosedImmersion (W.inclusion i) :=
  W.inclusion_isClosedImmersion i

end Witness

/-- The one-step filtration `0 ⊂ 𝒪_X` used by the identity morphism. -/
private noncomputable def identityFiltration (X : Scheme.{u}) :
    FiniteFiltration X.Modules (structureSheaf X) where
  length := 1
  object := Fin.cases (0 : X.Modules) (fun _ => structureSheaf X)
  inclusion := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact 0
  graded := fun _ => structureSheaf X
  projection := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact 𝟙 _
  zero := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact Limits.zero_comp
  shortExact := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change (ShortComplex.mk
      (0 : (0 : X.Modules) ⟶ structureSheaf X)
      (𝟙 (structureSheaf X)) Limits.zero_comp).ShortExact
    apply ShortComplex.ShortExact.mk'
    · rw [ShortComplex.exact_iff_mono _ (by rfl)]
      infer_instance
    · infer_instance
    · infer_instance
  initialIsZero := by
    change IsZero (0 : X.Modules)
    exact isZero_zero _
  terminalIso := Iso.refl _

/-- Explicit almost-disconnected data for the identity morphism. -/
noncomputable def identityWitness (X : Scheme.{u}) : Witness (𝟙 X) where
  filtration := identityFiltration X
  support := fun _ => X
  inclusion := fun _ => 𝟙 X
  inclusion_isClosedImmersion := fun _ => inferInstance
  baseIso := fun _ => Iso.refl X
  baseIso_hom := fun _ => by simp
  lineBundle := fun _ => Scheme.Modules.LineBundleData.unit X
  gradedIso := fun i => by
    change structureSheaf X ≅
      (Scheme.Modules.pushforward (𝟙 X)).obj (structureSheaf X)
    exact ((Scheme.Modules.pushforwardId X).app (structureSheaf X)).symm

end AlmostDisconnected

/-- The morphism property of admitting the filtration in Definition B.1 of
arXiv:2607.28411v1. -/
def IsAlmostDisconnected : MorphismProperty Scheme :=
  fun _ _ p => Nonempty (AlmostDisconnected.Witness p)

namespace IsAlmostDisconnected

/-- The identity morphism is almost disconnected. -/
theorem id (X : Scheme.{u}) : IsAlmostDisconnected (𝟙 X) :=
  ⟨AlmostDisconnected.identityWitness X⟩

instance : IsAlmostDisconnected.ContainsIdentities where
  id_mem := id

end IsAlmostDisconnected

end AlgebraicGeometry
