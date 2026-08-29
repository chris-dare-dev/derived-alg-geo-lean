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

The paper also proves flat-base-change and composition closure (Lemma B.2).  The geometric part
of composition is implemented here at the common `SupportData` root.  The full closure theorems
are not yet asserted: composition still needs line-bundle pullback and the tensor--pushforward
projection formula, while base change needs the arbitrary cartesian comparison
`g^* i_* L ≅ i'_* g'^* L` and an exact scheme-module pullback API.  In particular, the
repository's current exact flat-pullback theorem lives below `StabilityCondition/Families`, which
this root must not import.
-/

open CategoryTheory Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

namespace AlmostDisconnected

variable {X Y Z : Scheme.{u}}

/-- The structure sheaf, regarded as an object of the scheme's module category. -/
noncomputable abbrev structureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The geometric support carried by one graded piece of an almost-disconnected witness.

This is the common root of the graded-piece hierarchy: it owns only the closed subscheme and
its identification with the base.  Line bundles and quotient comparisons are attached by
`GradedPieceData`, so composition of supports does not depend on any module-theoretic choices. -/
structure SupportData (p : X ⟶ Y) where
  /-- The closed support of the graded piece. -/
  support : Scheme.{u}
  /-- Its inclusion into the source. -/
  inclusion : support ⟶ X
  /-- The support is a closed subscheme of the source. -/
  inclusion_isClosedImmersion : IsClosedImmersion inclusion
  /-- The support identifies with the target. -/
  baseIso : support ≅ Y
  /-- The chosen identification is induced by the original morphism. -/
  baseIso_hom : baseIso.hom = inclusion ≫ p

namespace SupportData

variable {p : X ⟶ Y}

/-- Install the closed-immersion certificate carried by a support datum. -/
instance (D : SupportData p) : IsClosedImmersion D.inclusion :=
  D.inclusion_isClosedImmersion

/-- The tautological support datum for an identity morphism. -/
def identity (X : Scheme.{u}) : SupportData (𝟙 X) where
  support := X
  inclusion := 𝟙 X
  inclusion_isClosedImmersion := inferInstance
  baseIso := Iso.refl X
  baseIso_hom := by simp

/-- Compose two support data.

If `S ⟶ X` identifies `S` with `Y`, and `T ⟶ Y` identifies `T` with `Z`, then `T`
embeds in `X` through `T ⟶ Y ⟶ S ⟶ X` and identifies with `Z`.  This is the geometric
part of the composition proof in Lemma B.2, independent of the later tensor and projection-
formula comparison for the associated line bundles. -/
def comp {q : Y ⟶ Z} (D : SupportData p) (E : SupportData q) :
    SupportData (p ≫ q) where
  support := E.support
  inclusion := E.inclusion ≫ D.baseIso.inv ≫ D.inclusion
  inclusion_isClosedImmersion := by infer_instance
  baseIso := E.baseIso
  baseIso_hom := by
    have h : D.baseIso.inv ≫ D.inclusion ≫ p ≫ q = q := by
      rw [← Category.assoc D.inclusion p q, ← D.baseIso_hom]
      simp
    rw [E.baseIso_hom]
    simp only [Category.assoc]
    rw [h]

@[simp]
theorem comp_support {q : Y ⟶ Z} (D : SupportData p) (E : SupportData q) :
    (D.comp E).support = E.support :=
  rfl

@[simp]
theorem comp_inclusion {q : Y ⟶ Z} (D : SupportData p) (E : SupportData q) :
    (D.comp E).inclusion = E.inclusion ≫ D.baseIso.inv ≫ D.inclusion :=
  rfl

@[simp]
theorem comp_baseIso {q : Y ⟶ Z} (D : SupportData p) (E : SupportData q) :
    (D.comp E).baseIso = E.baseIso :=
  rfl

end SupportData

/-- One graded piece of an almost-disconnected witness.

The geometric support extends `SupportData`; the module-theoretic child adds the line bundle and
the comparison with the relevant quotient.  Keeping this inheritance explicit prevents future
consumers from growing parallel support records with subtly different composition laws. -/
structure GradedPieceData (p : X ⟶ Y) (Q : X.Modules) extends SupportData p where
  /-- The invertible sheaf whose inverse presents the quotient. -/
  lineBundle : Scheme.Modules.LineBundleData toSupportData.support
  /-- The quotient is the pushforward of the inverse line bundle from its support. -/
  gradedIso : Q ≅
    (Scheme.Modules.pushforward toSupportData.inclusion).obj lineBundle.inverse

/-- Explicit data witnessing that a scheme morphism is almost disconnected.

This is Definition B.1 of arXiv:2607.28411v1, with equalities replaced by chosen isomorphisms.
The line bundle stores both `Lᵢ` and its tensor inverse, so `gradedIso` can name `Lᵢ⁻¹`
without making a noncanonical choice. -/
structure Witness (p : X ⟶ Y) where
  /-- The filtration `0 = F₀ ⊂ ⋯ ⊂ Fₘ = 𝒪_X`. -/
  filtration : FiniteFiltration X.Modules (structureSheaf X)
  /-- The geometrically rooted data attached to each graded quotient. -/
  piece : ∀ i, GradedPieceData p (filtration.graded i)

namespace Witness

variable {p : X ⟶ Y}

/-- The closed support `Xᵢ` of a witness's `i`th graded piece. -/
abbrev support (W : Witness p) (i : Fin W.filtration.length) : Scheme.{u} :=
  (W.piece i).support

/-- The inclusion `ιᵢ : Xᵢ ⟶ X`. -/
abbrev inclusion (W : Witness p) (i : Fin W.filtration.length) : W.support i ⟶ X :=
  (W.piece i).inclusion

/-- The closed-immersion certificate for the `i`th support. -/
abbrev inclusion_isClosedImmersion (W : Witness p) (i : Fin W.filtration.length) :
    IsClosedImmersion (W.inclusion i) :=
  (W.piece i).inclusion_isClosedImmersion

/-- The identification of the `i`th support with the base. -/
abbrev baseIso (W : Witness p) (i : Fin W.filtration.length) : W.support i ≅ Y :=
  (W.piece i).baseIso

/-- The support identification is induced by the original morphism. -/
abbrev baseIso_hom (W : Witness p) (i : Fin W.filtration.length) :
    (W.baseIso i).hom = W.inclusion i ≫ p :=
  (W.piece i).baseIso_hom

/-- The line bundle attached to the `i`th support. -/
abbrev lineBundle (W : Witness p) (i : Fin W.filtration.length) :
    Scheme.Modules.LineBundleData (W.support i) :=
  (W.piece i).lineBundle

/-- The `i`th quotient is the pushforward of the inverse line bundle from its support. -/
abbrev gradedIso (W : Witness p) (i : Fin W.filtration.length) :
    W.filtration.graded i ≅
      (Scheme.Modules.pushforward (W.inclusion i)).obj (W.lineBundle i).inverse :=
  (W.piece i).gradedIso

/-- Install the closed-immersion certificate carried by a witness. -/
instance (W : Witness p) (i : Fin W.filtration.length) :
    IsClosedImmersion (W.inclusion i) :=
  W.inclusion_isClosedImmersion i

/-- The outer-major pair indexing the graded pieces in a composite witness. -/
abbrev CompositionIndex {q : Y ⟶ Z} (W : Witness p) (V : Witness q) :=
  Fin W.filtration.length × Fin V.filtration.length

/-- Outer-major pairs are canonically the finite interval of product length. -/
def compositionIndexEquiv {q : Y ⟶ Z} (W : Witness p) (V : Witness q) :
    CompositionIndex W V ≃
      Fin (W.filtration.length * V.filtration.length) :=
  finProdFinEquiv

/-- The composite geometric support attached to an outer/inner pair of graded pieces. -/
def compositionSupportData {q : Y ⟶ Z} (W : Witness p) (V : Witness q)
    (ij : CompositionIndex W V) : SupportData (p ≫ q) :=
  (W.piece ij.1).toSupportData.comp (V.piece ij.2).toSupportData

@[simp]
theorem compositionSupportData_support {q : Y ⟶ Z} (W : Witness p) (V : Witness q)
    (ij : CompositionIndex W V) :
    (compositionSupportData W V ij).support = V.support ij.2 :=
  rfl

@[simp]
theorem compositionSupportData_inclusion {q : Y ⟶ Z} (W : Witness p) (V : Witness q)
    (ij : CompositionIndex W V) :
    (compositionSupportData W V ij).inclusion =
      V.inclusion ij.2 ≫ (W.baseIso ij.1).inv ≫ W.inclusion ij.1 :=
  rfl

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
  piece := fun _ =>
    { toSupportData := SupportData.identity X
      lineBundle := Scheme.Modules.LineBundleData.unit X
      gradedIso := by
        change structureSheaf X ≅
          (Scheme.Modules.pushforward (𝟙 X)).obj (structureSheaf X)
        exact ((Scheme.Modules.pushforwardId X).app (structureSheaf X)).symm }

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
