/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback

/-!
# Derived pullback from K-projective replacements, with no hypothesis on the morphism

`PullbackAcyclicResolution` and `KFlatPullbackAcyclic` both carry two fields
that are assertions *about the morphism being derived*: that pullback along
`f` inverts the quasi-isomorphisms produced by the replacement, and that it
inverts the comparison of an already replaced complex. Until now those two
fields were supplied by the caller for every nonexact `f`, so the arbitrary
derived pullback was inhabited only by assuming the preservation it was
supposed to construct.

This file removes both assertions for replacements whose values are
K-projective. A quasi-isomorphism between K-projective cochain complexes is
already an isomorphism in the homotopy category, and degreewise pullback is
additive, so it preserves the homotopies witnessing that isomorphism. The two
acyclicity fields are therefore theorems, proved for an arbitrary morphism of
scheme base changes: no exactness, no flatness, no limit preservation, and no
caller-supplied assertion about `f`.

What remains supplied is the replacement itself. Nothing here constructs a
functorial K-projective -- or K-flat -- replacement on `X.Modules`, and this
file makes no claim that one exists. That is a separate open deliverable of
SF8.5, and on a general scheme the category of all `𝒪_X`-modules does not have
enough projectives, so the honest general-scheme route is a K-flat replacement
whose transport along `f` is still open. The statements below are about what a
replacement buys once it is in hand, and they are phrased so that the
K-projectivity hypothesis stays visible at every call site.

## Main statements

- `SchemeBaseChange.quasiIso_complexPullback_map_of_isKProjective`: degreewise
  pullback along an arbitrary morphism preserves quasi-isomorphisms between
  K-projective complexes.
- `SchemeBaseChange.PullbackAcyclicResolution.ofKProjective`: a functorial
  K-projective replacement is a pullback-acyclic resolution along every
  morphism.
- `SchemeBaseChange.kFlatPullbackAcyclic_of_isKProjective`: the K-flat
  pullback-acyclicity hypothesis of `kFlatLeftDerivedPullback` is discharged,
  rather than assumed, for a K-projective-valued K-flat replacement.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

/-- Degreewise pullback along an arbitrary morphism of scheme base changes
carries a quasi-isomorphism between K-projective complexes to a
quasi-isomorphism.

The morphism carries no exactness, flatness, or limit-preservation
hypothesis. Only additivity of module-sheaf pullback is used, and that holds
for every scheme morphism. -/
theorem quasiIso_complexPullback_map_of_isKProjective (f : T ⟶ U)
    {K L : CochainComplex U.left.Modules ℤ}
    [_root_.CochainComplex.IsKProjective K]
    [_root_.CochainComplex.IsKProjective L]
    {g : K ⟶ L}
    (hg : HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ) g) :
    HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ)
      ((complexPullback f).map g) :=
  _root_.CochainComplex.IsKProjective.quasiIso_map (modulePullback f) hg

/-- The localized form of `quasiIso_complexPullback_map_of_isKProjective`:
pullback of a quasi-isomorphism between K-projective complexes becomes an
isomorphism in the derived category of the source scheme. -/
theorem isIso_complexPullback_map_of_isKProjective (f : T ⟶ U)
    {K L : CochainComplex U.left.Modules ℤ}
    [_root_.CochainComplex.IsKProjective K]
    [_root_.CochainComplex.IsKProjective L]
    {g : K ⟶ L}
    (hg : HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ) g) :
    IsIso ((complexPullback f ⋙ SchemeDerivedCategory.Q T.left).map g) := by
  apply Localization.inverts (SchemeDerivedCategory.Q T.left)
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
  exact quasiIso_complexPullback_map_of_isKProjective f hg

namespace PullbackAcyclicResolution

/-- A functorial replacement whose values are K-projective is a
pullback-acyclic resolution along every morphism of scheme base changes.

Both acyclicity fields of `PullbackAcyclicResolution` are proved here. The
hypotheses `hcomparison` and `hKProjective` speak only about the replacement
on `U`; neither mentions `f`, so one replacement serves every morphism out of
`U` simultaneously. -/
def ofKProjective (f : T ⟶ U)
    (resolution : CochainComplex U.left.Modules ℤ ⥤
      CochainComplex U.left.Modules ℤ)
    (comparison : resolution ⟶ 𝟭 (CochainComplex U.left.Modules ℤ))
    (hcomparison : ∀ K : CochainComplex U.left.Modules ℤ,
      HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)
        (comparison.app K))
    (hKProjective : ∀ K : CochainComplex U.left.Modules ℤ,
      _root_.CochainComplex.IsKProjective (resolution.obj K)) :
    PullbackAcyclicResolution f where
  resolution := resolution
  comparison := comparison
  comparison_quasiIso := hcomparison
  pullback_inverts := by
    intro K L g hg
    letI := hKProjective K
    letI := hKProjective L
    exact isIso_complexPullback_map_of_isKProjective f
      (CategoryTheory.CochainComplex.quasiIso_map_of_comparison comparison
        hcomparison g hg)
  resolved_comparison_isIso K := by
    letI := hKProjective (resolution.obj K)
    letI : _root_.CochainComplex.IsKProjective
        ((𝟭 (CochainComplex U.left.Modules ℤ)).obj (resolution.obj K)) :=
      hKProjective K
    exact isIso_complexPullback_map_of_isKProjective f
      (hcomparison (resolution.obj K))

end PullbackAcyclicResolution

/-- Arbitrary left-derived pullback, inhabited from a functorial K-projective
replacement alone.

There is no hypothesis on `f` and no supplied preservation assertion: the
universal property comes from `PullbackAcyclicResolution.isLeftDerived`, and
its two acyclicity inputs are proved in `ofKProjective`. -/
def kProjectiveLeftDerivedPullback (f : T ⟶ U)
    (resolution : CochainComplex U.left.Modules ℤ ⥤
      CochainComplex U.left.Modules ℤ)
    (comparison : resolution ⟶ 𝟭 (CochainComplex U.left.Modules ℤ))
    (hcomparison : ∀ K : CochainComplex U.left.Modules ℤ,
      HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)
        (comparison.app K))
    (hKProjective : ∀ K : CochainComplex U.left.Modules ℤ,
      _root_.CochainComplex.IsKProjective (resolution.obj K)) :
    LeftDerivedPullback f :=
  (PullbackAcyclicResolution.ofKProjective f resolution comparison hcomparison
    hKProjective).toLeftDerivedPullback

/-- When ordinary pullback happens to be exact, the K-projective construction
normalizes to the existing exact derived pullback. -/
def kProjectiveExactComparison (f : T ⟶ U) [IsExactPullback f]
    (resolution : CochainComplex U.left.Modules ℤ ⥤
      CochainComplex U.left.Modules ℤ)
    (comparison : resolution ⟶ 𝟭 (CochainComplex U.left.Modules ℤ))
    (hcomparison : ∀ K : CochainComplex U.left.Modules ℤ,
      HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)
        (comparison.app K))
    (hKProjective : ∀ K : CochainComplex U.left.Modules ℤ,
      _root_.CochainComplex.IsKProjective (resolution.obj K)) :
    (kProjectiveLeftDerivedPullback f resolution comparison hcomparison
      hKProjective).functor ≅ derivedPullback f :=
  (kProjectiveLeftDerivedPullback f resolution comparison hcomparison
    hKProjective).exactComparison

/-- Pullback-acyclicity of a K-flat replacement is a theorem, not a
caller-supplied hypothesis, as soon as the replacement is K-projective valued.

This discharges the `KFlatPullbackAcyclic` argument of
`kFlatLeftDerivedPullback` for an arbitrary morphism, where previously it was
provable only for exact and flat morphisms and otherwise assumed. -/
theorem kFlatPullbackAcyclic_of_isKProjective (R : SchemeKFlatResolution U.left)
    (f : T ⟶ U)
    (hKProjective : ∀ K : CochainComplex U.left.Modules ℤ,
      _root_.CochainComplex.IsKProjective (R.resolution.obj K)) :
    KFlatPullbackAcyclic R f where
  pullback_inverts := by
    intro K L g hg
    letI := hKProjective K
    letI := hKProjective L
    exact isIso_complexPullback_map_of_isKProjective f (R.map_quasiIso g hg)
  resolved_comparison_isIso K := by
    letI := hKProjective (R.resolution.obj K)
    letI : _root_.CochainComplex.IsKProjective
        ((𝟭 (CochainComplex U.left.Modules ℤ)).obj (R.resolution.obj K)) :=
      hKProjective K
    exact isIso_complexPullback_map_of_isKProjective f
      (R.comparison_quasiIso (R.resolution.obj K))

/-- The K-flat derived pullback along an arbitrary morphism, with its
acyclicity hypothesis proved rather than supplied. -/
def kFlatLeftDerivedPullbackOfKProjective (R : SchemeKFlatResolution U.left)
    (f : T ⟶ U)
    (hKProjective : ∀ K : CochainComplex U.left.Modules ℤ,
      _root_.CochainComplex.IsKProjective (R.resolution.obj K)) :
    LeftDerivedPullback f :=
  kFlatLeftDerivedPullback R f
    (kFlatPullbackAcyclic_of_isKProjective R f hKProjective)

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
