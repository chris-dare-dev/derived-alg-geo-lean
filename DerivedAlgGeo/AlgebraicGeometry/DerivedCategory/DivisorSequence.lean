/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.SingleTriangle
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.CartierDivisor
import DerivedAlgGeo.AlgebraicGeometry.Divisors.EffectiveLineBundle
import DerivedAlgGeo.CategoryTheory.Triangulated.FullSubcategory

/-!
# Coherent short exact sequences in derived categories

Mathlib's `ShortExact.singleTriangle` is the canonical passage from a short
exact sequence in an abelian category to a distinguished triangle in its
derived category. This file exposes that construction for coherent sheaves
on a locally Noetherian scheme, together with its functorial maps in both the
ambient and bounded derived categories. The bounded construction consumes the
generic full-triangulated-subcategory lifting API.

The effective Cartier-divisor API already constructs the coherent twisted
sequence

`0 ⟶ O_X(E-D) ⟶ O_X(E) ⟶ O_X(E) ⊗ i_* O_D ⟶ 0`.

`EffectiveCartierDivisor.cohTwistTriangle` is its derived-category triangle.
The closing API tensors this sequence by arbitrary `LineBundleData`, giving
canonical coherent and bounded triangles with endpoint comparisons. The
connecting morphism is always supplied by the derived-category construction;
it is not chosen objectwise. Geometric consumers remain responsible only for
claims such as residual orthogonality of the quotient.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory

noncomputable section

/-- The canonical derived triangle attached to a short exact sequence of
coherent sheaves. -/
noncomputable def cohShortExactTriangle
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    Triangle (SchemeCoherentDerivedCategory X) :=
  ShortComplex.ShortExact.singleTriangle hS

/-- The coherent short-exact triangle is distinguished. -/
theorem cohShortExactTriangle_distinguished
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    cohShortExactTriangle hS ∈ distTriang (SchemeCoherentDerivedCategory X) :=
  ShortComplex.ShortExact.singleTriangle_distinguished hS

/-- A map of short exact coherent sequences induces a map of their derived
triangles. In particular, the connecting morphisms are natural for the same
sequence maps used by the source and target triangles. -/
noncomputable def cohShortExactTriangleMap
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S₁ S₂ : ShortComplex (Coh X)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    cohShortExactTriangle h₁ ⟶ cohShortExactTriangle h₂ :=
  ShortComplex.ShortExact.singleTriangle.map h₁ h₂ f

/-- The coherent short-exact triangle map preserves identities. -/
@[simp]
theorem cohShortExactTriangleMap_id
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    cohShortExactTriangleMap hS hS (𝟙 S) =
      𝟙 (cohShortExactTriangle hS) :=
  ShortComplex.ShortExact.singleTriangle.map_id hS

/-- The coherent short-exact triangle map preserves composition. -/
@[simp, reassoc]
theorem cohShortExactTriangleMap_comp
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S₁ S₂ S₃ : ShortComplex (Coh X)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (h₃ : S₃.ShortExact)
    (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    cohShortExactTriangleMap h₁ h₃ (f ≫ g) =
      cohShortExactTriangleMap h₁ h₂ f ≫
        cohShortExactTriangleMap h₂ h₃ g :=
  ShortComplex.ShortExact.singleTriangle.map_comp h₁ h₂ h₃ f g

/-- All three objects of a coherent short-exact triangle are bounded for the
canonical derived t-structure. -/
theorem cohShortExactTriangle_onBounded
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    ((DerivedCategory.TStructure.t (C := Coh X)).bounded).OnTriangle
      (cohShortExactTriangle hS) := by
  constructor
  · change (DerivedCategory.TStructure.t (C := Coh X)).bounded
      ((DerivedCategory.singleFunctor (Coh X) 0).obj S.X₁)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  · change (DerivedCategory.TStructure.t (C := Coh X)).bounded
      ((DerivedCategory.singleFunctor (Coh X) 0).obj S.X₂)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  · change (DerivedCategory.TStructure.t (C := Coh X)).bounded
      ((DerivedCategory.singleFunctor (Coh X) 0).obj S.X₃)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩

/-- The canonical short-exact triangle viewed in the bounded coherent derived
subcategory. -/
noncomputable def cohShortExactBoundedTriangle
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    Triangle (SchemeBoundedCoherentDerivedCategory X) := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  exact P.liftTriangle (cohShortExactTriangle hS)
    (cohShortExactTriangle_onBounded hS)

/-- The canonical comparison between the bounded lift after inclusion and the
original coherent short-exact triangle. -/
noncomputable def cohShortExactBoundedTriangleInclusionIso
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
      (DerivedCategory.TStructure.t (C := Coh X)).bounded
    P.ι.mapTriangle.obj (cohShortExactBoundedTriangle hS) ≅
      cohShortExactTriangle hS := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  exact P.liftTriangleIso (cohShortExactTriangle hS)
    (cohShortExactTriangle_onBounded hS)

/-- The bounded coherent short-exact triangle is distinguished. -/
theorem cohShortExactBoundedTriangle_distinguished
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    cohShortExactBoundedTriangle hS ∈
      distTriang (SchemeBoundedCoherentDerivedCategory X) := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  exact P.liftTriangle_distinguished (cohShortExactTriangle hS)
    (cohShortExactTriangle_onBounded hS)
    (cohShortExactTriangle_distinguished hS)

/-- A map of short exact coherent sequences induces a map of their bounded
derived triangles. -/
noncomputable def cohShortExactBoundedTriangleMap
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S₁ S₂ : ShortComplex (Coh X)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    cohShortExactBoundedTriangle h₁ ⟶ cohShortExactBoundedTriangle h₂ := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  exact P.liftTriangleMap
    (cohShortExactTriangle_onBounded h₁)
    (cohShortExactTriangle_onBounded h₂)
    (cohShortExactTriangleMap h₁ h₂ f)

/-- The bounded coherent short-exact triangle map preserves identities. -/
@[simp]
theorem cohShortExactBoundedTriangleMap_id
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    cohShortExactBoundedTriangleMap hS hS (𝟙 S) =
      𝟙 (cohShortExactBoundedTriangle hS) := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  change P.liftTriangleMap
      (cohShortExactTriangle_onBounded hS)
      (cohShortExactTriangle_onBounded hS)
      (cohShortExactTriangleMap hS hS (𝟙 S)) =
    𝟙 (P.liftTriangle (cohShortExactTriangle hS)
      (cohShortExactTriangle_onBounded hS))
  rw [cohShortExactTriangleMap_id]
  exact P.liftTriangleMap_id _ _

/-- The bounded coherent short-exact triangle map preserves composition. -/
@[simp, reassoc]
theorem cohShortExactBoundedTriangleMap_comp
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S₁ S₂ S₃ : ShortComplex (Coh X)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (h₃ : S₃.ShortExact)
    (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    cohShortExactBoundedTriangleMap h₁ h₃ (f ≫ g) =
      cohShortExactBoundedTriangleMap h₁ h₂ f ≫
        cohShortExactBoundedTriangleMap h₂ h₃ g := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  change P.liftTriangleMap
      (cohShortExactTriangle_onBounded h₁)
      (cohShortExactTriangle_onBounded h₃)
      (cohShortExactTriangleMap h₁ h₃ (f ≫ g)) =
    P.liftTriangleMap
        (cohShortExactTriangle_onBounded h₁)
        (cohShortExactTriangle_onBounded h₂)
        (cohShortExactTriangleMap h₁ h₂ f) ≫
      P.liftTriangleMap
        (cohShortExactTriangle_onBounded h₂)
        (cohShortExactTriangle_onBounded h₃)
        (cohShortExactTriangleMap h₂ h₃ g)
  rw [cohShortExactTriangleMap_comp]
  exact P.liftTriangleMap_comp _ _ _ _ _

/-- Under the canonical inclusion comparisons, the bounded triangle map is
the original coherent derived triangle map. -/
theorem cohShortExactBoundedTriangleMap_ambient
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S₁ S₂ : ShortComplex (Coh X)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
      (DerivedCategory.TStructure.t (C := Coh X)).bounded
    (cohShortExactBoundedTriangleInclusionIso h₁).inv ≫
        P.ι.mapTriangle.map (cohShortExactBoundedTriangleMap h₁ h₂ f) ≫
        (cohShortExactBoundedTriangleInclusionIso h₂).hom =
      cohShortExactTriangleMap h₁ h₂ f := by
  let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
    (DerivedCategory.TStructure.t (C := Coh X)).bounded
  exact P.liftTriangleMap_ambient
    (cohShortExactTriangle_onBounded h₁)
    (cohShortExactTriangle_onBounded h₂)
    (cohShortExactTriangleMap h₁ h₂ f)

end

end AlgebraicGeometry.DerivedCategory

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

open AlgebraicGeometry.DerivedCategory

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The distinguished triangle in `D(Coh X)` supplied by the twisted exact
sequence of an effective Cartier divisor. -/
noncomputable def cohTwistTriangle
    (D : EffectiveCartierDivisor (X := X)) (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    Triangle (SchemeCoherentDerivedCategory X) :=
  cohShortExactTriangle (D.cohTwistSequence_shortExact E hSource hMiddle)

/-- The effective Cartier-divisor twist triangle is distinguished. -/
theorem cohTwistTriangle_distinguished
    (D : EffectiveCartierDivisor (X := X)) (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    D.cohTwistTriangle E hSource hMiddle ∈
      distTriang (SchemeCoherentDerivedCategory X) :=
  cohShortExactTriangle_distinguished
    (D.cohTwistSequence_shortExact E hSource hMiddle)

/-- The bounded coherent derived triangle supplied by the twisted exact
sequence of an effective Cartier divisor. -/
noncomputable def cohTwistBoundedTriangle
    (D : EffectiveCartierDivisor (X := X)) (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    Triangle (SchemeBoundedCoherentDerivedCategory X) :=
  cohShortExactBoundedTriangle
    (D.cohTwistSequence_shortExact E hSource hMiddle)

/-- The canonical comparison between the bounded effective-divisor triangle
after inclusion and its ambient coherent derived triangle. -/
noncomputable def cohTwistBoundedTriangleInclusionIso
    (D : EffectiveCartierDivisor (X := X)) (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    let P : ObjectProperty (SchemeCoherentDerivedCategory X) :=
      (DerivedCategory.TStructure.t (C := Coh X)).bounded
    P.ι.mapTriangle.obj (D.cohTwistBoundedTriangle E hSource hMiddle) ≅
      D.cohTwistTriangle E hSource hMiddle :=
  cohShortExactBoundedTriangleInclusionIso
    (D.cohTwistSequence_shortExact E hSource hMiddle)

/-- The bounded effective Cartier-divisor twist triangle is distinguished. -/
theorem cohTwistBoundedTriangle_distinguished
    (D : EffectiveCartierDivisor (X := X)) (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    D.cohTwistBoundedTriangle E hSource hMiddle ∈
      distTriang (SchemeBoundedCoherentDerivedCategory X) :=
  cohShortExactBoundedTriangle_distinguished
    (D.cohTwistSequence_shortExact E hSource hMiddle)

/-! ### Canonical twists by arbitrary line bundles -/

/-- The distinguished triangle obtained by tensoring a Cartier-divisor
sequence with an arbitrary line bundle. Unlike `cohTwistTriangle`, this API
needs no separately supplied coherence proofs. -/
noncomputable def cohLineBundleTwistTriangle
    (D : EffectiveCartierDivisor (X := X))
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    Triangle (SchemeCoherentDerivedCategory X) :=
  cohShortExactTriangle (D.cohLineBundleTwistSequence_shortExact L E)

/-- The line-bundle-twisted Cartier triangle is distinguished. -/
theorem cohLineBundleTwistTriangle_distinguished
    (D : EffectiveCartierDivisor (X := X))
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    D.cohLineBundleTwistTriangle L E ∈
      distTriang (SchemeCoherentDerivedCategory X) :=
  cohShortExactTriangle_distinguished
    (D.cohLineBundleTwistSequence_shortExact L E)

/-- The line-bundle-twisted Cartier triangle in `Dᵇ(Coh X)`. -/
noncomputable def cohLineBundleTwistBoundedTriangle
    (D : EffectiveCartierDivisor (X := X))
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    Triangle (SchemeBoundedCoherentDerivedCategory X) :=
  cohShortExactBoundedTriangle
    (D.cohLineBundleTwistSequence_shortExact L E)

/-- The bounded line-bundle-twisted Cartier triangle is distinguished. -/
theorem cohLineBundleTwistBoundedTriangle_distinguished
    (D : EffectiveCartierDivisor (X := X))
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    D.cohLineBundleTwistBoundedTriangle L E ∈
      distTriang (SchemeBoundedCoherentDerivedCategory X) :=
  cohShortExactBoundedTriangle_distinguished
    (D.cohLineBundleTwistSequence_shortExact L E)

/-- The first vertex of the bounded line-bundle-twisted triangle is the
canonical derived object of `L ⊗ O_X(E-D)`. -/
noncomputable def cohLineBundleTwistBoundedTriangleObj₁Iso
    (D : EffectiveCartierDivisor (X := X))
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    (D.cohLineBundleTwistBoundedTriangle L E).obj₁ ≅
      (L.tensor
        (CartierDivisor.lineBundleData (E - D.divisor))).boundedDerivedObject :=
  ObjectProperty.isoMk
    (P := (DerivedCategory.TStructure.t (C := Coh X)).bounded)
    ((DerivedCategory.singleFunctor (Coh X) 0).mapIso
      (ObjectProperty.isoMk (P := Scheme.coherent X) (Iso.refl _)))

/-- The second vertex of the bounded line-bundle-twisted triangle is the
canonical derived object of `L ⊗ O_X(E)`. -/
noncomputable def cohLineBundleTwistBoundedTriangleObj₂Iso
    (D : EffectiveCartierDivisor (X := X))
    (L : Modules.LineBundleData X) (E : CartierDivisor X) :
    (D.cohLineBundleTwistBoundedTriangle L E).obj₂ ≅
      (L.tensor
        (CartierDivisor.lineBundleData E)).boundedDerivedObject :=
  ObjectProperty.isoMk
    (P := (DerivedCategory.TStructure.t (C := Coh X)).bounded)
    ((DerivedCategory.singleFunctor (Coh X) 0).mapIso
      (ObjectProperty.isoMk (P := Scheme.coherent X) (Iso.refl _)))

end

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor
