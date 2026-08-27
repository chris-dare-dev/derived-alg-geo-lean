/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.ProjectiveSpaceVariety
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Polynomial projective space is locally Noetherian, and is its own projective presentation

`Proj/ProjectiveSpaceVariety.lean` exhibits `Pⁿ = Proj k[Xᵢ]` as a `Variety k` and `O(d)` as an
object of `Coh Pⁿ`. Those are the only geometric objects this repository constructs, and until
now nothing said that `Pⁿ` satisfies the two adjectives every consumer of a variety asks for.
This file supplies both.

## Locally Noetherian

`Coh X` is `Abelian` only for `[IsLocallyNoetherian X]`
(`CoherentSheaf/Abelian/Basic.lean`), so without this instance the one worked example in the
repository sat in a category with no kernels — `⊕O(-d) ↠ F` could not even be *stated* about
`Pⁿ`, and `Dᵇ(Coh Pⁿ)` did not exist.

The proof is a transfer and nothing more: `Spec k` is locally Noetherian because a field is a
Noetherian ring, the structure morphism is `LocallyOfFiniteType` by
`Proj.locallyOfFiniteType_projectiveSpaceToSpec`, and Mathlib's
`LocallyOfFiniteType.isLocallyNoetherian` carries the property along it. `Finite ι` is what makes
the structure morphism of finite type, so it is required here for the same reason it is required
there.

## Its own projective presentation

`Variety.IsProjective` asks for a `ProjectivePresentation` — a closed immersion into some
`projectiveSpace ι k`. For `Pⁿ` that embedding is the identity, and the only real content is that
the two lanes' structure morphisms agree.

They are built from different maps onto the degree-zero part of the grading:
`Variety/Projective.lean` uses `homogeneousZeroRingEquiv`, whose forward map is
`MvPolynomial.C`, and `Proj/ProjectiveSpaceVariety.lean` uses `algebraMap k ↥(𝒜 0)`.
`homogeneousZeroRingEquiv_toRingHom_eq_algebraMap` is the statement that these are the same ring
homomorphism, and it is the mathematical content of this half of the file; everything after it is
transport.

The two grading spellings are *not* content: `Proj.polynomialGrading` is an `abbrev` for
`MvPolynomial.homogeneousSubmodule`, so `projectiveSpace ι k` and
`(projectiveSpaceVariety ι k).toScheme` are the same term and the identity typechecks between
them without an `eqToHom`.

## What this file does not do

* **It proves nothing about smoothness.** `SmoothProperVariety` and every K3 statement need
  `Smooth (structureMorphism)`, which needs the relative cotangent complex of `Proj`; none of that
  is at the pin, and nothing here approaches it.
* **It exhibits no new sheaf.** The consequences unlocked here are categorical — `Coh Pⁿ` is
  abelian, `Pⁿ` is projective hence proper — and the objects available on `Pⁿ` are still exactly
  `O_X` and the twists `O(d)`.
* **It does not connect to `NumericalVarietyData`.** The realization `K₀(Dᵇ(Coh X)) → N` remains
  data supplied by a caller (`Numerical/GrothendieckGroup/Realization.lean`), so no Chern
  character or Mukai vector of `O(d)` follows from anything here.

## Main results

* `isLocallyNoetherian_projectiveSpace` — `Pⁿ` is locally Noetherian.
* `homogeneousZeroRingEquiv_toRingHom_eq_algebraMap` — the two maps onto the degree-zero part
  agree.
* `projectiveSpaceSelfPresentation` — `Pⁿ` presented in itself by the identity.
* `isProjective_projectiveSpaceVariety` — `Pⁿ` is a projective variety.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Proj

variable (ι k : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Locally Noetherian -/

/-- **Polynomial projective space is locally Noetherian.**

The structure morphism is of finite type and the base is the spectrum of a field, so Mathlib's
transfer along a finite-type morphism applies. `Finite ι` is genuine: it is what makes
`projectiveSpaceToSpec` of finite type in the first place. -/
instance isLocallyNoetherian_projectiveSpace [Finite ι] :
    IsLocallyNoetherian (Proj (polynomialGrading ι k)) :=
  LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceToSpec ι k)

/-- The same statement in the `Variety` spelling.

`projectiveSpaceVariety` is a plain definition rather than an `abbrev`, so instance search will
not unfold it; without this restatement the instance above does not fire for callers that hold a
`Variety k`. In particular it is this form that makes `Coh (projectiveSpaceVariety ι k).toScheme`
abelian. -/
instance isLocallyNoetherian_projectiveSpaceVariety [Finite ι] [Nonempty ι] :
    IsLocallyNoetherian (projectiveSpaceVariety ι k).toScheme :=
  inferInstanceAs (IsLocallyNoetherian (Proj (polynomialGrading ι k)))

/-! ## The identity presentation -/

/-- The base field's two routes into the degree-zero part of the standard grading agree.

`homogeneousZeroRingEquiv` sends `r` to the constant polynomial `MvPolynomial.C r`, and the
algebra map of the degree-zero subalgebra sends `r` to `r • 1`, which is the same constant. This
is the only place the two lanes' conventions have to be reconciled. -/
theorem homogeneousZeroRingEquiv_toRingHom_eq_algebraMap :
    (_root_.AlgebraicGeometry.homogeneousZeroRingEquiv ι k).toRingHom
      = algebraMap k ↥(polynomialGrading ι k 0) := by
  ext r
  rfl

/-- The two lanes build the same structure morphism `Pⁿ ⟶ Spec k`. -/
theorem projectiveSpaceToSpec_eq [Finite ι] [Nonempty ι] :
    _root_.AlgebraicGeometry.projectiveSpaceToSpec ι k
      = (projectiveSpaceVariety ι k).structureMorphism := by
  show Proj.toSpecZero _ ≫
      Spec.map (CommRingCat.ofHom
        (_root_.AlgebraicGeometry.homogeneousZeroRingEquiv ι k).toRingHom)
    = Proj.toSpecZero _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap k ↥(polynomialGrading ι k 0)))
  rw [homogeneousZeroRingEquiv_toRingHom_eq_algebraMap]

/-- The identity, read as a map from `Pⁿ` as a variety into `Pⁿ` as an ambient projective space.

No `eqToHom` appears because there is no equation to transport along: the source and target are
the same term, `polynomialGrading` being an `abbrev` for `MvPolynomial.homogeneousSubmodule`. -/
noncomputable def projectiveSpaceSelfEmbedding [Finite ι] [Nonempty ι] :
    (projectiveSpaceVariety ι k).toScheme ⟶ _root_.AlgebraicGeometry.projectiveSpace ι k :=
  𝟙 (_root_.AlgebraicGeometry.projectiveSpace ι k)

/-- The identity is a closed immersion.

Stated rather than synthesized for the same reason as the Noetherian restatement above: instance
search does not unfold `projectiveSpaceSelfEmbedding` to see the identity. -/
instance projectiveSpaceSelfEmbedding_isClosedImmersion [Finite ι] [Nonempty ι] :
    IsClosedImmersion (projectiveSpaceSelfEmbedding ι k) :=
  inferInstanceAs (IsClosedImmersion (𝟙 (_root_.AlgebraicGeometry.projectiveSpace ι k)))

/-- **Polynomial projective space presents itself.**

The ambient space of the presentation is `Pⁿ` itself and the embedding is the identity; the
`overBase` field is `projectiveSpaceToSpec_eq` after cancelling that identity. -/
noncomputable def projectiveSpaceSelfPresentation [Finite ι] [Nonempty ι] :
    ProjectivePresentation (projectiveSpaceVariety ι k) where
  index := ι
  embedding := projectiveSpaceSelfEmbedding ι k
  overBase :=
    (Category.id_comp (_root_.AlgebraicGeometry.projectiveSpaceToSpec ι k)).trans
      (projectiveSpaceToSpec_eq ι k)

/-- **Polynomial projective space is a projective variety.**

With this instance `Pⁿ` meets the hypothesis that `Variety.IsProjective` states, and properness
of its structure morphism follows through `ProjectivePresentation.isProper_structureMorphism`
rather than through a separate appeal to `Proj.toSpecZero`. -/
instance isProjective_projectiveSpaceVariety [Finite ι] [Nonempty ι] :
    (projectiveSpaceVariety ι k).IsProjective :=
  Variety.IsProjective.ofPresentation (projectiveSpaceSelfPresentation ι k)

end AlgebraicGeometry.Proj
