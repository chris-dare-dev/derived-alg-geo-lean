/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Coproducts
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization

/-!
# Coproducts in the affine quasi-coherent realization of `Dqc`

`Dqc.lean` gives the honest locus `Dqc(X)` its `ι`-indexed coproducts on an
arbitrary scheme (#721), and the inclusion into the all-sheaf derived category
preserves them.  Nothing there says anything about the *affine realization*
functor of `AffineRealization.lean`, and that is what this file supplies.

Four layers, none of them transported along an unproved equivalence:

1. **Abelian.** Quasi-coherent sheaves on `Spec R` have `ι`-indexed coproducts
   and the inclusion into `(Spec R).Modules` creates them
   (`Modules/Quasicoherent/Coproducts.lean`, arbitrary scheme, no hypotheses);
   those coproducts are exact, by the tilde equivalence with `ModuleCat R`
   (`Affine.lean`).  The second half is affine-only and is the only place an
   equivalence is used.
2. **Derived.** `D(QCoh(Spec R))` therefore has `ι`-indexed coproducts, `Q`
   preserves them, and so does every `Hⁿ`.  These are the repository's
   `DerivedCategory.Coproducts` instances, now applicable because layer 1 has
   supplied their AB4 hypothesis.
3. **The exact derived inclusion** `D(QCoh(Spec R)) ⥤ D((Spec R).Modules)`
   preserves them, by
   `Functor.mapDerivedCategory_preservesCoproductsOfShape` applied to the exact,
   coproduct-preserving inclusion of layer 1.
4. **The realization** `affineQuasicoherentDerivedToDqc` preserves them: its
   composite with the honest `Dqc` inclusion is layer 3, and that inclusion
   reflects coproducts, because closure makes it create them.

## What this does not prove

Preservation of coproducts is one of the two standing hypotheses of every
compact-generation argument; it is not the argument.  In particular this file
still claims no unbounded essential surjectivity of
`affineQuasicoherentDerivedToDqc` — `AffineQuasicoherentDqcIdentification`
remains uninhabited — no compact-equals-perfect comparison, no generator
closure, and no `S`-linearity.  The bounded identification, which is proved,
comes from `AffineQuasicoherentIdentification.lean` by a cone argument that
needs finite amplitude and does not extend to the unbounded case.

Coproducts are indexed by a type in the universe of the coordinate ring, one
indexing type at a time, matching the repository's universe-explicit colimit
idiom rather than claiming closure under all coproducts.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) (ι : Type u)

/-! ### The abelian layer -/

/-- The inclusion of affine quasi-coherent sheaves into all module sheaves
preserves `ι`-indexed coproducts: the affine case of the arbitrary-scheme
statement, recorded here as the moduli lane's entry point.

With `affineQuasicoherentSheavesInclusion_preservesFiniteLimits` and its colimit
counterpart this makes it an exact, coproduct-preserving functor, which is
exactly the input the derived layer below consumes. -/
theorem affineQuasicoherentSheavesInclusion_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) (affineQuasicoherentSheavesInclusion R) :=
  quasicoherentSheavesInclusion_preservesCoproductsOfShape (Spec R) ι

/-! ### The derived layer -/

/-- **The affine quasi-coherent derived category has `ι`-indexed coproducts.**

This is `DerivedCategory.hasCoproductsOfShape` at the abelian category
`AffineQuasicoherentSheaves R`, and it is available exactly because
`affineQuasicoherentSheavesHasExactCoproducts` supplies the AB4 hypothesis that
instance asks for.  Coproducts alone would not do: the construction needs
quasi-isomorphisms to be stable under coproducts, which is exactness. -/
theorem affineQuasicoherentDerivedCategory_hasCoproductsOfShape :
    HasCoproductsOfShape ι (AffineQuasicoherentDerivedCategory R) :=
  inferInstance

/-- The localization functor from cochain complexes of affine quasi-coherent
sheaves preserves `ι`-indexed coproducts, so the coproduct of a family in
`D(QCoh(Spec R))` is represented by their degreewise coproduct. -/
theorem affineQuasicoherentQ_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.Q (C := AffineQuasicoherentSheaves R)) :=
  inferInstance

/-- Every cohomology functor on the affine quasi-coherent derived category
preserves `ι`-indexed coproducts. -/
theorem affineQuasicoherentHomologyFunctor_preservesCoproductsOfShape (n : ℤ) :
    PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.homologyFunctor (AffineQuasicoherentSheaves R) n) :=
  inferInstance

/-- Derived tilde preserves `ι`-indexed coproducts.  It is an equivalence
(`affineQuasicoherentDerivedEquivalence`), so this is its left adjoint half and
needs no further input; recording it identifies the coproducts of layer 2 with
the ones `D(ModuleCat R)` already had. -/
theorem affineTildeDerivedFunctor_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) (affineTildeDerivedFunctor R) := by
  haveI : (affineTildeDerivedFunctor R).IsEquivalence :=
    inferInstanceAs (affineQuasicoherentDerivedEquivalence R).functor.IsEquivalence
  infer_instance

/-- Derived global sections preserves `ι`-indexed coproducts, being the
quasi-inverse equivalence.  This is a genuine statement about the affine
quasi-coherent category and not about `RΓ` on an arbitrary scheme, where
commuting with coproducts is the quasi-compactness-and-separatedness input to
compact generation and is not proved anywhere in this repository. -/
theorem affineGammaDerivedFunctor_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) (affineGammaDerivedFunctor R) := by
  haveI : (affineGammaDerivedFunctor R).IsEquivalence :=
    inferInstanceAs (affineQuasicoherentDerivedEquivalence R).inverse.IsEquivalence
  infer_instance

/-! ### The realization -/

/-- **The exact affine derived inclusion preserves `ι`-indexed coproducts.**

`Functor.mapDerivedCategory_preservesCoproductsOfShape` applied to the exact,
coproduct-preserving inclusion of affine quasi-coherent sheaves into all module
sheaves.  Both AB4 hypotheses that theorem needs are present and neither is
assumed here: on the source by `affineQuasicoherentSheavesHasExactCoproducts`,
on the target by `Scheme.Modules.ab4`. -/
theorem affineQuasicoherentDerivedInclusion_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) (affineQuasicoherentDerivedInclusion R) := by
  haveI := affineQuasicoherentSheavesInclusion_preservesCoproductsOfShape R ι
  exact (affineQuasicoherentSheavesInclusion R).mapDerivedCategory_preservesCoproductsOfShape ι

/-- **The affine realization into `Dqc(Spec R)` preserves `ι`-indexed
coproducts.**

The composite of the realization with the honest `Dqc` inclusion is the exact
derived inclusion above, and that inclusion reflects coproducts
(`SchemeQuasicoherentDerivedCategory.ι_reflectsCoproductsOfShape`), so
preservation transfers from the composite to the realization itself.

The `Dqc` side of that argument is where the honesty lives: reflection holds
because the locus *creates* its coproducts, so the coproduct of a family of
realized complexes is computed in the all-sheaf derived category and then
observed to stay in the locus.  Nothing here identifies the two categories. -/
theorem affineQuasicoherentDerivedToDqc_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι) (affineQuasicoherentDerivedToDqc R) := by
  haveI := affineQuasicoherentDerivedInclusion_preservesCoproductsOfShape R ι
  haveI : PreservesColimitsOfShape (Discrete ι)
      (affineQuasicoherentDerivedToDqc R ⋙
        SchemeQuasicoherentDerivedCategory.ι (Spec R)) :=
    preservesColimitsOfShape_of_natIso
      (affineQuasicoherentDerivedToDqcCompInclusion R).symm
  haveI := SchemeQuasicoherentDerivedCategory.ι_reflectsCoproductsOfShape (Spec R) ι
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (affineQuasicoherentDerivedToDqc R) (SchemeQuasicoherentDerivedCategory.ι (Spec R))

end

end AlgebraicGeometry.DerivedCategory.Dqc
