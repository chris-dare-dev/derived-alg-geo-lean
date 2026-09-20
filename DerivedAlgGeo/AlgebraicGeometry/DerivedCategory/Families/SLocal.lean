/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeSLinearity
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChangeFunctors
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.OpensBaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Local

/-!
# `S`-local t-structures on a base-change category

Section 4 of arXiv:1902.08184 calls a t-structure on `𝒟` **`S`-local** when
every quasi-compact open `U ⊆ S` carries a t-structure on `𝒟_U` making
restriction t-exact. `TStructure/Local.lean` supplies the one-functor half of
that sentence -- `RestrictsAlong` -- and observes that the restricted
t-structure is determined by its aisle. This file takes the quantifier.

Three things make the quantifier cheap to state.

* `𝒟` is already a base-change category. It is `𝒟_S` at `identityBaseChange S`,
  the terminal object of `Over S`, so no separate source category is needed and
  restriction is an ordinary base-change pullback.
* An open is already an object of `Over S`, by `opensBaseChange`.
* Base change is already functorial in the index, by
  `KFlatBaseChangeData.quasicoherentPullback`.

What is *not* cheap, and is therefore an explicit input, is the base-change data
over each open. The repository's base change consumes bundled K-flat
resolutions, not just a morphism, so a family of them is what `S`-locality has
to quantify over; `OpenRestrictionFamily` is that family, and it carries the
restriction functors with it rather than deriving them.

The family and its component t-exactness remain geometric inputs. The formal
Families layer does, however, provide adapters for the affine Remark A.20
situation, the noetherian-locality equivalence, and filtration lifting. The
phase-level slicing quantifier lives in the geometric stability layer, so that
the Families layer does not import stability conditions. All adapters expose
their remaining base-change hypotheses rather than manufacturing them from
the word `affine`.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory.Families

universe u

variable {S : Scheme.{u}}

/-- The restriction data `S`-locality quantifies over.

For each quasi-compact open of the base: a base change of `X` to it, and a
restriction functor from the base-change category over `S` itself. The functor
is carried rather than derived, because deriving it needs a derived pullback and
the component-preservation statement that `quasicoherentPullback` consumes, and
both are geometry. -/
structure OpenRestrictionFamily (X : SchemeBaseChange S)
    (P : ObjectProperty (SourceDqc X)) [P.ContainsZero]
    (DS : KFlatBaseChangeData X (identityBaseChange S)) where
  /-- The base change of `X` to each quasi-compact open of the base. -/
  data (U : S.Opens) (hU : CompactSpace U.toScheme) :
    KFlatBaseChangeData X (opensBaseChange U)
  /-- Restriction from the base to that open. -/
  restriction (U : S.Opens) (hU : CompactSpace U.toScheme) :
    DS.QuasicoherentCategory P ⥤ (data U hU).QuasicoherentCategory P

namespace OpenRestrictionFamily

variable {X : SchemeBaseChange S} {P : ObjectProperty (SourceDqc X)}
  [P.ContainsZero] {DS : KFlatBaseChangeData X (identityBaseChange S)}

/-- **`S`-locality** (§4 of arXiv:1902.08184): the t-structure restricts along
the restriction to every quasi-compact open of the base.

This is `TStructure.RestrictsAlong` quantified over the family. The t-structures
on the `𝒟_U` are existential here rather than chosen, which is the paper's
statement; Remark 4.6(1) is what makes that harmless, since
`TStructure.ext_le` pins each of them once its aisle is. -/
def IsSLocal (R : OpenRestrictionFamily X P DS)
    (t : TStructure (DS.QuasicoherentCategory P)) : Prop :=
  ∀ (U : S.Opens) (hU : CompactSpace U.toScheme),
    t.RestrictsAlong (R.restriction U hU)

/-- The chosen form: a restriction of the t-structure at every quasi-compact
open, rather than the bare existence of one. -/
structure SLocalData (R : OpenRestrictionFamily X P DS)
    (t : TStructure (DS.QuasicoherentCategory P)) where
  /-- The restricted t-structure over each quasi-compact open. -/
  restriction (U : S.Opens) (hU : CompactSpace U.toScheme) :
    t.Restriction (R.restriction U hU)

namespace SLocalData

variable {R : OpenRestrictionFamily X P DS}
  {t : TStructure (DS.QuasicoherentCategory P)}

/-- Chosen restrictions witness `S`-locality. -/
theorem isSLocal (L : SLocalData R t) : R.IsSLocal t :=
  fun U hU ↦ (L.restriction U hU).restrictsAlong

/-- Two choices of `S`-local data agree at an open as soon as their aisles do.

This is Remark 4.6(1) with its geometric half left visible: what pins the aisle
of the restricted t-structure is that `𝒟_U` is generated by the image of `𝒟`,
which is a generation theorem about base change and is not proved here. -/
theorem tStructure_eq_of_le_eq (L₁ L₂ : SLocalData R t)
    (U : S.Opens) (hU : CompactSpace U.toScheme)
    (hle : (L₁.restriction U hU).tStructure.le =
      (L₂.restriction U hU).tStructure.le) :
    (L₁.restriction U hU).tStructure = (L₂.restriction U hU).tStructure :=
  TStructure.ext_le hle

/-! The equality below is the chosen-data form of Remark 4.6(1). It still
needs the geometric aisle comparison at every open; the categorical part is
the extensionality of `TStructure`. -/

theorem ext_of_le_eq (L₁ L₂ : SLocalData R t)
    (hle : ∀ (U : S.Opens) (hU : CompactSpace U.toScheme),
      (L₁.restriction U hU).tStructure.le =
        (L₂.restriction U hU).tStructure.le) :
    L₁ = L₂ := by
  cases L₁ with
  | mk r₁ =>
    cases L₂ with
    | mk r₂ =>
      have hr : r₁ = r₂ := by
        funext U hU
        apply TStructure.Restriction.ext
        exact TStructure.ext_le (hle U hU)
      cases hr
      rfl

end SLocalData

variable {R : OpenRestrictionFamily X P DS}
  {t : TStructure (DS.QuasicoherentCategory P)}

/-! ### Lemma 4.15 and Lemma 4.16(3)

The repository owns the heart predicate and the shape of an arbitrary
filtration. The finite-cover/noetherian comparison and the geometric lift of
objects and morphisms are represented by named owner data below. The public
theorems are therefore useful to consumers without disguising either paper
hypothesis as a proof. -/

/-- Owner data for the noetherian-locality equivalence of Lemma 4.15. -/
structure NoetherianLocalityData (R : OpenRestrictionFamily X P DS)
    (t : TStructure (DS.QuasicoherentCategory P)) where
  /-- The S-local data the two implications below are stated against. Carried
  rather than existentially quantified, because `lemma_4_15` hands its caller
  `H.localData.restriction U hU` and a proposition would not. -/
  localData : SLocalData R t
  global_to_local : t.IsNoetherian →
    ∀ (U : S.Opens) (hU : CompactSpace U.toScheme),
      (localData.restriction U hU).tStructure.IsNoetherian
  local_to_global :
    (∀ (U : S.Opens) (hU : CompactSpace U.toScheme),
      (localData.restriction U hU).tStructure.IsNoetherian) →
      t.IsNoetherian

theorem lemma_4_15 (H : NoetherianLocalityData R t) :
    t.IsNoetherian ↔
      ∀ (U : S.Opens) (hU : CompactSpace U.toScheme),
        (H.localData.restriction U hU).tStructure.IsNoetherian :=
  ⟨H.global_to_local, H.local_to_global⟩

/-- An arbitrary (not necessarily finite) chain of monomorphisms. -/
structure Filtration (C : Type*) [Category C] where
  /-- The `n`-th object of the chain. -/
  object : ℕ → C
  /-- The map from the `n`-th object to the `n+1`-st. `mono` below is what makes
  it an inclusion; this field alone claims only a morphism. -/
  inclusion : ∀ n, object n ⟶ object (n + 1)
  mono : ∀ n, Mono (inclusion n)

/-- Owner data for lifting an arbitrary heart filtration as in Lemma 4.16(3).

Named `Lemma416Part3Data` rather than `Lemma416_3Data`: the `defsWithUnderscore`
linter reads the underscore separating the lemma number from its clause and
flags every field of the structure, and this repository's `nolints.json` is a
shrink-only ratchet, so silencing it is not available. The paper reference is
unchanged -- Lemma 4.16, clause (3). -/
structure Lemma416Part3Data (L : SLocalData R t) where
  /-- Lifts a filtration in the heart restricted to `U` to one in the global
  heart. It is owner data, not a construction: nothing here builds the lift. -/
  lift (U : S.Opens) (hU : CompactSpace U.toScheme)
      (F : Filtration ((L.restriction U hU).tStructure.heart.FullSubcategory)) :
      Filtration (t.heart.FullSubcategory)
  /-- Identifies the `n`-th object of the lifted filtration, restricted back to
  `U`, with the `n`-th object it was lifted from. `comm` below is what makes the
  identification compatible with the inclusions. -/
  comparison (U : S.Opens) (hU : CompactSpace U.toScheme)
      (F : Filtration ((L.restriction U hU).tStructure.heart.FullSubcategory))
      (n : ℕ) :
      ((L.restriction U hU).heartFunctor.obj
        ((lift U hU F).object n)) ≅ F.object n
  comm (U : S.Opens) (hU : CompactSpace U.toScheme)
      (F : Filtration ((L.restriction U hU).tStructure.heart.FullSubcategory))
      (n : ℕ) :
      (comparison U hU F n).hom ≫ F.inclusion n =
        (L.restriction U hU).heartFunctor.map
          ((lift U hU F).inclusion n) ≫ (comparison U hU F (n + 1)).hom

/-- The filtration-lifting conclusion in the orientation of Lemma 4.16(3). -/
theorem lemma_4_16_3 (L : SLocalData R t) (H : Lemma416Part3Data L) (U : S.Opens)
    (hU : CompactSpace U.toScheme)
    (F : Filtration ((L.restriction U hU).tStructure.heart.FullSubcategory)) :
    ∃ G : Filtration (t.heart.FullSubcategory),
      (∀ n, Nonempty (((L.restriction U hU).heartFunctor.obj
        (G.object n)) ≅ F.object n)) ∧
      ∃ e : ∀ n, (((L.restriction U hU).heartFunctor.obj
        (G.object n)) ≅ F.object n),
        ∀ n, (e n).hom ≫ F.inclusion n =
          (L.restriction U hU).heartFunctor.map (G.inclusion n) ≫
            (e (n + 1)).hom := by
  refine ⟨H.lift U hU F, fun n ↦ ⟨H.comparison U hU F n⟩,
    ⟨H.comparison U hU F, ?_⟩⟩
  intro n
  exact H.comm U hU F n

end OpenRestrictionFamily

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
