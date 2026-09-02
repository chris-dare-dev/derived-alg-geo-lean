/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic

/-!
# A geometric Fourier--Mukai correspondence: the dependency ledger

`CategoryTheory/Triangulated/FourierMukai/Basic.lean` defines an abstract
`Correspondence 𝒳 𝒴 𝒵` — a source functor in the role of `Lp^*`, a bifunctor in
the role of `⊗^L`, and a target functor in the role of `Rq_*` — and everything
in the Fourier--Mukai lane is conditional on one being supplied. **Nothing in
this repository supplies one.** This file is the ledger that says precisely
what supplying one would take.

It follows the pattern of `Families/BoundedGeometry.lean` and the
inhabitant-free ledgers of the `SchemeDerived` track: each geometric input is a
named class with a docstring, nothing is constructed, and the payoff is that
`geometricCorrespondence` assembles a genuine `Correspondence` from exactly
those inputs and no others. The gap becomes enumerated instead of implicit.

## What already exists

* `SchemeBoundedCoherentDerivedCategory X = Dᵇ(Coh X)` for locally Noetherian
  `X`, with `Perf(X)` inside it (`BoundedGeometry`).
* **Derived pullback**, as a contract rather than a construction:
  `HasCoherentPullback f` supplies the coherent-sheaf pullback together with
  exactness and the derived lift, and `boundedCoherentDerivedPullback` is the
  functor on `Dᵇ(Coh)` obtained from it. So the `pull` slot is *already*
  reducible to an existing named obligation.
* Base-change witnesses and relative Harder--Narasimhan machinery
  (`GeometricBaseChange`, `FiniteTypeGeometry`), none of which this file needs.

## What does not exist, and is named here

* **Derived pushforward.** Nothing in the repository defines `Rq_*` on derived
  categories; a search for one finds only a docstring in
  `TStructure/Exactness.lean` describing its t-exactness. This is where
  *properness* enters: pushforward preserves coherence only under a properness
  hypothesis, and `HasDerivedPushforward` is where a caller discharges it.
* **Derived tensor product.** Likewise absent. `Modules/Tensor/Basic.lean` tensors
  invertible sheaves and `Modules/` tensors module sheaves; neither is `⊗^L` on
  `Dᵇ(Coh)`.

## What this ledger deliberately does *not* require

**The middle scheme is not required to be a product.** `Correspondence` never
mentions one: it needs a category `𝒵`, a functor into it, a bifunctor on it,
and a functor out of it. Requiring `Z ≅ X ×_S Y` here would be adding a
hypothesis the structure does not consume — precisely the shape both review
rounds attacked.

The product *is* needed, but downstream and for a different purpose: it is what
makes `ConvolutionData` — the composition law `Φ_Q ∘ Φ_P ≅ Φ_{Q∗P}` — provable,
via the projection formula and flat base change on a triple product. Those are
listed in the closing section as the next ledger, not smuggled in here.

Nor is `Z` required locally Noetherian *as a consequence* of `X` and `Y` being
so. Mathlib has no instance making a pullback of schemes locally Noetherian, so
it is a hypothesis like any other.

## What this file does not assert

* **Nothing constructs a `HasDerivedPushforward` or a `HasDerivedTensor`**, and
  no scheme is shown to admit either. This file is inhabitant-free by design; a
  reader must not take `geometricCorrespondence` as evidence that a geometric
  Fourier--Mukai transform exists in this repository.
* No projection formula, no flat base change, no Grothendieck duality, and no
  claim that the derived pushforward is right adjoint to the derived pullback.
* Nothing about when the resulting transform is an *equivalence* — that is the
  classical theorem the whole lane is conditional on, and it is not approached
  here.
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section Pushforward

/-- **Derived pushforward along `f`, supplied.**

The `Rq_*` slot of a Fourier--Mukai correspondence, and the one where
*properness* lives: pushforward preserves coherence only for a proper morphism,
so a caller discharging this class is asserting exactly that much geometry.

Deliberately stated directly on `Dᵇ(Coh)` rather than, as `HasCoherentPullback`
does, on `Coh` with a derived lift. The reason is asymmetry in the mathematics,
not convenience: pullback of a coherent sheaf is coherent, so the sheaf-level
functor exists and the derived one is induced; pushforward of a coherent sheaf
is *not* coherent in general, and there is no sheaf-level functor to induce
from. The derived functor is the primitive object here. -/
class HasDerivedPushforward {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] where
  /-- The derived pushforward on bounded coherent derived categories. -/
  derivedPushforward :
    SchemeBoundedCoherentDerivedCategory T.left ⥤
      SchemeBoundedCoherentDerivedCategory U.left
  /-- It is additive. -/
  additive : derivedPushforward.Additive
  /-- It commutes with the shift. -/
  commShift : derivedPushforward.CommShift ℤ
  /-- It is triangulated.  Together with `commShift` this is the exactness the
  Fourier--Mukai transform needs of its `push` constituent. -/
  isTriangulated : derivedPushforward.IsTriangulated

/-- The derived pushforward functor, named. -/
def derivedPushforward {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] :
    SchemeBoundedCoherentDerivedCategory T.left ⥤
      SchemeBoundedCoherentDerivedCategory U.left :=
  HasDerivedPushforward.derivedPushforward f

instance derivedPushforward_additive {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] : (derivedPushforward f).Additive := by
  dsimp [derivedPushforward]
  exact HasDerivedPushforward.additive

instance derivedPushforwardCommShift {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] : (derivedPushforward f).CommShift ℤ := by
  dsimp [derivedPushforward]
  exact HasDerivedPushforward.commShift

instance derivedPushforward_isTriangulated {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasDerivedPushforward f] : (derivedPushforward f).IsTriangulated := by
  dsimp [derivedPushforward]
  exact HasDerivedPushforward.isTriangulated

end Pushforward

section Tensor

/-- **Derived tensor product on `Dᵇ(Coh Z)`, supplied.**

The `⊗^L` slot.  Stated as a bifunctor, matching `Correspondence.tensor`, so
that `tensor.obj K` is "twist by the kernel `K`".

Exactness is asked of each *twist* rather than of the bifunctor: the
Fourier--Mukai transform with kernel `K` needs `− ⊗^L K` to be triangulated, and
demanding it for every `K` at once is the honest reading of that, but it is
strictly more than any single transform consumes.  A caller who can only supply
exactness for particular kernels should weaken this class rather than
instantiate it dishonestly.

No monoidal structure is asked for: not associativity, not symmetry, not a
unit.  `Correspondence` uses none of them, and `FourierMukai/Basic.lean`'s own
docstring is explicit that it assumes none. -/
class HasDerivedTensor (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left] where
  /-- The derived tensor bifunctor. -/
  derivedTensor :
    SchemeBoundedCoherentDerivedCategory Z.left ⥤
      SchemeBoundedCoherentDerivedCategory Z.left ⥤
        SchemeBoundedCoherentDerivedCategory Z.left
  /-- Each twist is additive. -/
  additive : ∀ K, (derivedTensor.obj K).Additive
  /-- Each twist commutes with the shift. -/
  commShift : ∀ K, (derivedTensor.obj K).CommShift ℤ
  /-- Each twist is triangulated. -/
  isTriangulated : ∀ K, (derivedTensor.obj K).IsTriangulated

/-- The derived tensor bifunctor, named. -/
def derivedTensor (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] :
    SchemeBoundedCoherentDerivedCategory Z.left ⥤
      SchemeBoundedCoherentDerivedCategory Z.left ⥤
        SchemeBoundedCoherentDerivedCategory Z.left :=
  HasDerivedTensor.derivedTensor

instance derivedTensor_additive (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).obj K).Additive := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.additive K

instance derivedTensorCommShift (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).obj K).CommShift ℤ := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.commShift K

instance derivedTensor_isTriangulated (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).obj K).IsTriangulated := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.isTriangulated K

end Tensor

section Assembly

variable (X Y Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian Z.left]

/-- **The geometric Fourier--Mukai correspondence, assembled from the ledger.**

Given the two projection-like morphisms `p : Z ⟶ X` and `q : Z ⟶ Y`, the
derived pullback contract along `p`, a derived tensor on `Z`, and the derived
pushforward contract along `q`, this is a genuine
`Correspondence (Dᵇ(Coh X)) (Dᵇ(Coh Y)) (Dᵇ(Coh Z))` — so the whole abstract
Fourier--Mukai lane applies to it.

**This constructs no geometry.** Every input is a hypothesis; the content is
that these are exactly the inputs needed and there are no others. In particular
`Z` is not required to be `X ×_S Y` and `p`, `q` are not required to be
projections — `Correspondence` does not consume that, and requiring it here
would be adding an unconsumed hypothesis. -/
@[reducible] noncomputable def geometricCorrespondence (p : Z ⟶ X) (q : Z ⟶ Y)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q] :
    Correspondence (SchemeBoundedCoherentDerivedCategory X.left)
      (SchemeBoundedCoherentDerivedCategory Y.left)
      (SchemeBoundedCoherentDerivedCategory Z.left) where
  pull := boundedCoherentDerivedPullback p
  tensor := derivedTensor Z
  push := derivedPushforward q

@[simp]
theorem geometricCorrespondence_pull (p : Z ⟶ X) (q : Z ⟶ Y)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q] :
    (geometricCorrespondence X Y Z p q).pull = boundedCoherentDerivedPullback p :=
  rfl

@[simp]
theorem geometricCorrespondence_tensor (p : Z ⟶ X) (q : Z ⟶ Y)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q] :
    (geometricCorrespondence X Y Z p q).tensor = derivedTensor Z :=
  rfl

@[simp]
theorem geometricCorrespondence_push (p : Z ⟶ X) (q : Z ⟶ Y)
    [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q] :
    (geometricCorrespondence X Y Z p q).push = derivedPushforward q :=
  rfl

/-! ### Exactness of the assembled correspondence, reachable by instance search

`geometricCorrespondence` is `@[reducible]` so that instance search can unfold
`.pull`, `.tensor` and `.push` to the contracts that carry their exactness. The
three projection lemmas above are `rfl` and rewrite fine in a proof, but a
`CommShift`/`IsTriangulated` argument is *synthesised*, not rewritten, and
synthesis never sees them.

That gap was not academic: without it, every downstream consumer stated against
a `Correspondence` -- `transform_isTriangulated`, `transformK₀`, and through
them `actStab` and `actStabOfDual` -- was unreachable for the geometric
correspondence, so the geometric side of the lane could not reach the stability
transport it exists for. It surfaced as a bare
`failed to synthesize (geometricCorrespondence X X Z p q).pull.CommShift ℤ`.

Reducibility rather than hand-rolled instances, and the difference matters:
`IsTriangulated` is indexed by the `CommShift` instance, so an instance stated
against the ambient one is a different term from the one a use site
synthesises -- `CommShift` would resolve and `IsTriangulated` would not.
`Symmetry/Autoequivalence/FourierMukai` documents the same trap for `trans`.
Reducibility reaches the original instances with the indexing intact. -/

section Exactness

variable (X Y Z : SchemeBaseChange S)
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian Z.left]
  (p : Z ⟶ X) (q : Z ⟶ Y)
  [HasCoherentPullback p] [HasDerivedTensor Z] [HasDerivedPushforward q]

/-- **The geometric transform is triangulated.**

`FourierMukai.transform_isTriangulated` at the geometric correspondence — the
first statement that the assembled transform is exact, and the thing the six
instances above exist to make statable. -/
theorem geometricTransform_isTriangulated
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((geometricCorrespondence X Y Z p q).transform K).IsTriangulated :=
  inferInstance

/-- The geometric transform is additive. -/
theorem geometricTransform_additive
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((geometricCorrespondence X Y Z p q).transform K).Additive :=
  inferInstance

end Exactness

end Assembly

/-! ## The next ledger, and what is in it

`geometricCorrespondence` reaches everything in the Fourier--Mukai lane that
needs only a `Correspondence`: `transform`, `IsKernelFunctor`, `transformK₀`,
and — once a caller also supplies a `KernelAutoequivalence` — the transport of
stability conditions.

It does **not** reach the composition law. `ConvolutionData` asks for a kernel
operation `conv` together with `Φ_P ⋙ Φ_Q ≅ Φ_{conv P Q}` *uniformly in `Q`*,
and that is where the product structure finally becomes load-bearing. A second
ledger would have to name:

* `Z ≅ X ×_S Y`, and a triple product `X ×_S Y ×_S W` with its three
  projections;
* the **projection formula** `Rq_*(A ⊗^L Lq^* B) ≅ Rq_* A ⊗^L B`;
* **flat base change** for the square formed by two of the three projections;
* and the identification of `conv` itself as
  `Rπ_{XZ*}(π_{XY}^* P ⊗^L π_{YZ}^* Q)`.

None of those is stated here.  Similarly, a `UnitKernelData` would need `𝒪_Δ`
along the diagonal, and a `DualKernel` the derived dual `P^∨ ⊗ p^*ω[dim]` —
both geometric, both absent.
-/

end AlgebraicGeometry.DerivedCategory.FourierMukai
