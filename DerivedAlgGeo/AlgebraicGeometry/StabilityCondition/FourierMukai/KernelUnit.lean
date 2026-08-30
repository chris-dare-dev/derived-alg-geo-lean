/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelConvolution
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.FourierMukai

/-!
# The unit kernel `𝒪_Δ`: the third ledger

`Symmetry/Autoequivalence/FourierMukai.lean` defines `UnitKernelData` — a
kernel presenting the identity functor as a transform — and until now nothing
geometric could discharge it: the classical unit kernel is `𝒪_Δ = Rδ_* 𝒪_X`
along the diagonal `δ : X ⟶ X ×_S X`, and neither `𝒪_X` nor anything about
`δ` was named.

This file is the ledger for it, in the same shape as the two kernel ledgers:

* `diagonalKernel` is a **definition** — `Rδ_*` applied to the tensor unit —
  built from functors the first ledger already names plus the coherent
  derived-tensor root (`HasCoherentDerivedTensor`).
* `geometricUnitIso`, the statement that its transform is the identity, is
  **derived** from four inputs: the right-slot projection formula at `δ`
  (an *existing* class, consumed here at a second site), the coherent left
  unitor,
  and the two retraction classes below.
* `geometricUnitKernelData` assembles a genuine
  `UnitKernelData (geometricCorrespondence X X Z p q)` from exactly those
  inputs and no others.

## Where the diagonal geometry lives

Classically every input below is a theorem about the diagonal of a product:
`δ ≫ p = 𝟙 = δ ≫ q` are the defining triangle identities, pullback and
pushforward along a retraction compose to the identity by functoriality, and
`− ⊗ 𝒪` is the identity because `𝒪` is the monoidal unit. The tensor unit and
unitor now come from one structure whose triangle law is explicit. The two
retraction classes carry their triangle identity as
a `comm` **guard** — deliberately not consumed by the derivation, which uses
`iso` alone; the guard is what makes `iso` the right thing to ask for.

## What this file does not assert

* **Nothing constructs an instance of any class here**, and no scheme is
  shown to admit one. Inhabitant-free, like both kernel ledgers.
* Nothing identifies `Z` with `X ×_S X` or `δ` with an actual diagonal; the
  classes are stated at arbitrary morphisms with the guards making the
  intended instantiation precise.
* No `DualKernel`. The classical dual kernel is `P^∨ ⊗ p^* ω_X [dim X]`,
  which needs derived duals and a dualizing complex — machinery with no
  substrate in this repository when this file was written.

  Half of that reason has since lapsed and the sentence is corrected rather
  than left standing: `KernelAdjunction.lean` now ledgers the three constituent
  adjunctions, and they *are* consumed — by
  `FourierMukai.ConstituentRightAdjoints`, and through it by
  `KernelAutoequivalence.DualKernel.ofRightAdjointKernel`. What remains true is
  the other half: nothing discharges those classes. A `DualKernel` is now
  reachable — `KernelSwap.geometricDualKernel` assembles one — but only from
  that whole uninhabited ledger plus a supplied equivalence, so this file's
  own inputs still do not produce one.
* This file alone does not prove the kernel is a unit *for convolution*;
  `KernelUnitConvolution.lean` derives those laws from additional section and
  base-change geometry.
-/

universe u

namespace AlgebraicGeometry.StabilityCondition.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section UnitInputs

/-- Compatibility record for a raw tensor bifunctor with a chosen left unit.

New stable unit and convolution APIs require `HasCoherentDerivedTensor`, where
this unit and both unitors belong to the same monoidal structure as the
associator, pentagon, and triangle. -/
class HasTensorUnit (T : SchemeBaseChange S) [IsLocallyNoetherian T.left]
    [HasDerivedTensor T] where
  /-- The unit object, playing `𝒪_T`. -/
  unit : SchemeBoundedCoherentDerivedCategory T.left
  /-- Twisting by the unit is the identity. -/
  iso : (derivedTensor T).obj unit ≅
    𝟭 (SchemeBoundedCoherentDerivedCategory T.left)

/-- Forget the coherent root to the old selected-unit capability.

This supports raw intermediate callers without allowing a selected unit to
synthesize monoidal coherence. -/
noncomputable instance hasTensorUnitOfCoherent (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentDerivedTensor T] :
    HasTensorUnit T where
  unit := coherentDerivedTensorUnit T
  iso := coherentDerivedTensorLeftUnitor T

/-- **Derived pullback along a section collapses, supplied.**

For a section-retraction pair `δ ≫ p = 𝟙`, the composite of the two derived
pullbacks is the identity. The equation is a guard: the derivation consumes
`iso` alone, and `comm` is what makes it the right isomorphism to ask for. -/
class HasPullbackRetraction {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (δ : X ⟶ Z) (p : Z ⟶ X)
    [HasCoherentPullback δ] [HasCoherentPullback p] where
  /-- The triangle identity. A guard, not consumed. -/
  comm : δ ≫ p = 𝟙 X
  /-- Pullback along the retraction then the section is the identity. -/
  iso : boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback δ ≅
    𝟭 (SchemeBoundedCoherentDerivedCategory X.left)

/-- **Derived pushforward along a section collapses, supplied.**

The pushforward companion: for `δ ≫ q = 𝟙`, pushing forward along the
section and then the retraction is the identity. Guard as above. -/
class HasPushforwardRetraction {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (δ : X ⟶ Z) (q : Z ⟶ X)
    [HasDerivedPushforward δ] [HasDerivedPushforward q] where
  /-- The triangle identity. A guard, not consumed. -/
  comm : δ ≫ q = 𝟙 X
  /-- Pushforward along the section then the retraction is the identity. -/
  iso : derivedPushforward δ ⋙ derivedPushforward q ≅
    𝟭 (SchemeBoundedCoherentDerivedCategory X.left)

end UnitInputs

section Derivation

/-- Collapse an adjacent triple to one functor at the head of a
right-associated composite. Same combinator as in `KernelConvolution.lean`;
private there, so restated. -/
private def tripleCollapse' {A₁ A₂ A₃ A₄ A₅ : Type*} [Category A₁]
    [Category A₂] [Category A₃] [Category A₄] [Category A₅]
    {F : A₁ ⥤ A₂} {G : A₂ ⥤ A₃} {H : A₃ ⥤ A₄} {K : A₁ ⥤ A₄} (R : A₄ ⥤ A₅)
    (e : F ⋙ G ⋙ H ≅ K) : F ⋙ G ⋙ H ⋙ R ≅ K ⋙ R :=
  Functor.isoWhiskerLeft F (Functor.associator G H R).symm ≪≫
    (Functor.associator F (G ⋙ H) R).symm ≪≫ Functor.isoWhiskerRight e R

/-- Delete a head factor that is isomorphic to the identity. -/
private def vanishHead {A B : Type*} [Category A] [Category B]
    {T : A ⥤ A} (R : A ⥤ B) (e : T ≅ 𝟭 A) : T ⋙ R ≅ R :=
  Functor.isoWhiskerRight e R ≪≫ R.leftUnitor

/-- **The unit kernel, `𝒪_Δ` — a definition, not supplied data.**

`Rδ_*` applied to the tensor unit. The classical `𝒪_Δ`, built from functors
the ledgers already name. -/
noncomputable def diagonalKernel {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (δ : X ⟶ Z) [HasDerivedPushforward δ]
    [HasCoherentDerivedTensor X] :
    SchemeBoundedCoherentDerivedCategory Z.left :=
  (derivedPushforward δ).obj (coherentDerivedTensorUnit X)

/-- **The transform of the unit kernel is the identity — derived.**

The chain is the classical argument, four steps, each naming its input:

| step | rewrites | input |
|---|---|---|
| 1 | `(⊗ 𝒪_Δ)` → `δ^* ⋙ (⊗𝒪) ⋙ δ_*` | `HasProjectionFormulaRight` at `δ` |
| 2 | `(⊗𝒪)` deleted | `HasCoherentDerivedTensor` left unitor |
| 3 | `δ_* ⋙ q_*` deleted | `HasPushforwardRetraction` |
| 4 | `p^* ⋙ δ^*` → `𝟭` | `HasPullbackRetraction` |

Written in the same style as `geometricCompIso`: every intermediate functor
and every step is `let`-bound with a fully ascribed type. -/
noncomputable def geometricUnitIso {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (p q : Z ⟶ X) (δ : X ⟶ Z)
    [HasCoherentPullback p] [HasCoherentPullback δ]
    [HasDerivedTensor Z] [HasCoherentDerivedTensor X]
    [HasDerivedPushforward q] [HasDerivedPushforward δ]
    [HasProjectionFormulaRight δ]
    [HasPullbackRetraction δ p] [HasPushforwardRetraction δ q] :
    𝟭 (SchemeBoundedCoherentDerivedCategory X.left) ≅
      (geometricCorrespondence X X Z p q).transform (diagonalKernel δ) :=
  let u : SchemeBoundedCoherentDerivedCategory X.left :=
    coherentDerivedTensorUnit X
  let U₀ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory X.left :=
    boundedCoherentDerivedPullback p ⋙
      (derivedTensor Z).obj (diagonalKernel δ) ⋙ derivedPushforward q
  let U₁ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory X.left :=
    boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback δ ⋙
      (derivedTensor X).obj u ⋙ derivedPushforward δ ⋙ derivedPushforward q
  let U₂ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory X.left :=
    boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback δ ⋙
      derivedPushforward δ ⋙ derivedPushforward q
  let U₃ : SchemeBoundedCoherentDerivedCategory X.left ⥤
      SchemeBoundedCoherentDerivedCategory X.left :=
    boundedCoherentDerivedPullback p ⋙ boundedCoherentDerivedPullback δ
  -- Seam: the transform is `U₀` definitionally.
  let t₀ : (geometricCorrespondence X X Z p q).transform (diagonalKernel δ) ≅
      U₀ := Iso.refl _
  -- Step 1, the right-slot projection formula at `δ`, reversed.
  let t₁ : U₀ ≅ U₁ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p)
      (tripleCollapse' (derivedPushforward q)
        (HasProjectionFormulaRight.iso (q := δ) u)).symm
  -- Step 2, the tensor unit deletes itself.
  let t₂ : U₁ ≅ U₂ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p)
      (Functor.isoWhiskerLeft (boundedCoherentDerivedPullback δ)
        (vanishHead (derivedPushforward δ ⋙ derivedPushforward q)
          (coherentDerivedTensorLeftUnitor X)))
  -- Step 3, the pushforward retraction collapses the tail.
  let t₃ : U₂ ≅ U₃ :=
    Functor.isoWhiskerLeft (boundedCoherentDerivedPullback p)
      (Functor.isoWhiskerLeft (boundedCoherentDerivedPullback δ)
        (HasPushforwardRetraction.iso (δ := δ) (q := q)) ≪≫
          (boundedCoherentDerivedPullback δ).rightUnitor)
  -- Step 4, the pullback retraction finishes.
  let t₄ : U₃ ≅ 𝟭 (SchemeBoundedCoherentDerivedCategory X.left) :=
    HasPullbackRetraction.iso (δ := δ) (p := p)
  (t₀ ≪≫ t₁ ≪≫ t₂ ≪≫ t₃ ≪≫ t₄).symm

/-- **The geometric unit kernel data, assembled — with no supplied fields.**

A `UnitKernelData` for the geometric correspondence of `X` with itself, with
`unitKernel` the constructed `diagonalKernel` and `unitIso` the derived
`geometricUnitIso`. Together with `KernelAutoequivalence.id` this makes the
identity a *kernel* autoequivalence, geometrically, conditional on the four
named inputs. -/
noncomputable def geometricUnitKernelData {X Z : SchemeBaseChange S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Z.left]
    (p q : Z ⟶ X) (δ : X ⟶ Z)
    [HasCoherentPullback p] [HasCoherentPullback δ]
    [HasDerivedTensor Z] [HasCoherentDerivedTensor X]
    [HasDerivedPushforward q] [HasDerivedPushforward δ]
    [HasProjectionFormulaRight δ]
    [HasPullbackRetraction δ p] [HasPushforwardRetraction δ q] :
    Symmetry.UnitKernelData (geometricCorrespondence X X Z p q) where
  unitKernel := diagonalKernel δ
  unitIso := geometricUnitIso p q δ

end Derivation

/-! ## What the three ledgers together leave

The unit side of the autoequivalence story is now: a caller who discharges
the first ledger's contracts at `p`, `q`, `δ` plus `HasProjectionFormulaRight`
at `δ`, `HasCoherentDerivedTensor`, and the two retraction classes gets
`KernelAutoequivalence.id` with a geometric kernel. Still absent, and named
absences rather than ledgers: `DualKernel` (needs derived duals and a
dualizing complex) and the unit's compatibility with convolution (needs
`ConvolutionData` for the self-correspondence and a comparison of
`convKernel` with `diagonalKernel`).
-/

end AlgebraicGeometry.StabilityCondition.FourierMukai
