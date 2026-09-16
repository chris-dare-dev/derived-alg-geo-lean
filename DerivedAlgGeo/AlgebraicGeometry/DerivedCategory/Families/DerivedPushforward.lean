/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry

/-!
# Derived pushforward on bounded coherent derived fibers, as a supplied capability

`HasDerivedPushforward f` is the geometry-level contract for a triangulated direct image
`Dᵇ(Coh T) ⥤ Dᵇ(Coh U)` along a morphism of scheme base changes.  It is a **supplied
capability, not a construction**: this file inhabits nothing.

## Why it is stated directly on `Dᵇ(Coh)`

Deliberately stated on `Dᵇ(Coh)` rather than, as `HasCoherentPullback` does, on `Coh`
with a derived lift.  The reason is asymmetry in the mathematics, not convenience:
pullback of a coherent sheaf is coherent, so the sheaf-level functor exists and the
derived one is induced; pushforward of a coherent sheaf is *not* coherent in general, and
there is no sheaf-level functor to induce from.  The derived functor is the primitive
object here.

This is also where **properness** lives.  Pushforward preserves coherence only for a
proper morphism, so a caller discharging this class is asserting exactly that much
geometry.

## Its relation to the exact coherent pushforward next door

`Families/CoherentPushforward.lean` carries a *different, stronger* contract.
`HasCoherentPushforward f` asks for an exact pushforward on coherent sheaves and derives
the bounded derived functor from it degreewise, which is why finite morphisms inhabit it.
That route is unavailable for a proper morphism that is not affine, where `f_*` is only
left exact on coherent sheaves; such a morphism does not inhabit
`HasCoherentPushforward`, and `HasDerivedPushforward` is the weaker contract that
accommodates it.

The two are deliberately **not** connected by an instance here.  Deriving
`HasDerivedPushforward` from `HasCoherentPushforward` would be new mathematics -- a
discharge -- and MO1.10 is a placement split.  A consumer wanting both states both.

## Placement

MO1.10 (#1321) extracted this capability from
`DerivedCategory/FourierMukai/KernelCorrespondence.lean` to the existing owner of derived
direct images on scheme base changes, beside `Families/CoherentPushforward.lean` and
`Families/RightDerivedPushforward.lean`.  Fourier--Mukai is a consumer of a pushforward,
not its subject.  Per the cutover ledger's standing decision that paths move and
namespaces do not, the declarations keep the
`AlgebraicGeometry.DerivedCategory.FourierMukai` namespace they were introduced with;
this also keeps them distinct from the unrelated `SchemeBaseChange.derivedPushforward` of
`Families/RightDerivedPushforward.lean`, which is the right-derived functor of an
arbitrary module-sheaf pushforward.

## References

* `docs/architecture/cutover-ledger.md`, row 10.
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

/-- **Derived pushforward along `f`, supplied.**

The `Rq_*` slot of a Fourier--Mukai correspondence, and the one where *properness* lives:
pushforward preserves coherence only for a proper morphism, so a caller discharging this
class is asserting exactly that much geometry.

Deliberately stated directly on `Dᵇ(Coh)` rather than, as `HasCoherentPullback` does, on
`Coh` with a derived lift.  The reason is asymmetry in the mathematics, not convenience:
pullback of a coherent sheaf is coherent, so the sheaf-level functor exists and the
derived one is induced; pushforward of a coherent sheaf is *not* coherent in general, and
there is no sheaf-level functor to induce from.  The derived functor is the primitive
object here.

**Nothing inhabits this class.**  The exact coherent pushforward of
`Families/CoherentPushforward.lean` is a different and stronger contract, and this file
deliberately supplies no instance from it. -/
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

end AlgebraicGeometry.DerivedCategory.FourierMukai
