/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Extensions
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Zero
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# The abelian category of coherent sheaves

On a locally noetherian scheme, coherent module sheaves contain zero and are closed under
finite products, kernels, and cokernels. Mathlib's full-subcategory infrastructure therefore
makes `Coh X` abelian. The inclusion into all module sheaves creates kernels and cokernels,
hence preserves finite limits and finite colimits and is exact.

## Main results

* `Coh.abelian`;
* `Coh.exactInclusion`;
* `Coh.shortExact_map_ι`.
-/

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The coherent property contains a zero module sheaf. -/
noncomputable instance coherent_containsZero : (coherent X).ContainsZero := by
  change (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero
  exact SheafOfModules.isFinitePresentation_containsZero (R := X.ringCatSheaf)

/-- Coherent module sheaves are closed under binary products. -/
noncomputable instance coherent_isClosedUnderBinaryProducts :
    (coherent X).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    refine (coherent X).prop_of_iso ?_ ((coherent X).prop_biprod
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- Coherent module sheaves are closed under finite products. -/
noncomputable instance coherent_isClosedUnderFiniteProducts :
    (coherent X).IsClosedUnderFiniteProducts := .mk'

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Coh

variable (X : Scheme.{u})

/-- The preadditive structure inherited by the full subcategory of coherent sheaves. -/
noncomputable instance preadditive : Preadditive (Coh X) :=
  inferInstanceAs (Preadditive (Scheme.coherent X).FullSubcategory)

/-- Coherent sheaves on a locally noetherian scheme form an abelian category.

Built by spreading `preadditive` over the full subcategory's own `Abelian`
instance, rather than by `change … ; infer_instance`. The two are defeq, but only
at default transparency: written the second way, `abelian.toPreadditive` is the
preadditive field of the subcategory's instance, and reaching `Coh.preadditive`
from it needs `Coh` — a `def` — unfolded. Instance search does not do that, so
every Mathlib instance asking for `[Abelian C]` alongside a second
`Preadditive`-parameterised class silently fails to fire on `Coh X`;
`Variety.derivedLinear` is the case that found it.

The spread pins `toPreadditive` to `preadditive X` syntactically. `Abelian`'s
other parents, `IsNormalMonoCategory` and `IsNormalEpiCategory`, are `Prop`s, so
no second diamond can hide behind this one. -/
noncomputable instance abelian [IsLocallyNoetherian X] : Abelian (Coh X) :=
  letI src : Abelian (Scheme.coherent X).FullSubcategory := inferInstance
  { preadditive X, src with }

/-- Regression test for #662: `abelian.toPreadditive` must be `preadditive` at
`.instances` transparency, which is the transparency instance search runs at.
Note that `with_reducible` is *not* the right check here — `abelian` is an
instance, so it does not unfold at `.reducible`, and the check fails whether or
not the diamond is present. -/
example [IsLocallyNoetherian X] : (abelian X).toPreadditive = preadditive X := by
  with_reducible_and_instances rfl

/-- The inclusion of coherent sheaves preserves zero morphisms. -/
noncomputable instance ι_preservesZeroMorphisms : (ι X).PreservesZeroMorphisms := by
  change (Scheme.coherent X).ι.PreservesZeroMorphisms
  infer_instance

/-- The inclusion of coherent sheaves is additive. -/
noncomputable instance ι_additive : (ι X).Additive := by
  change (Scheme.coherent X).ι.Additive
  infer_instance

/-- The inclusion of coherent sheaves preserves finite limits. -/
noncomputable instance ι_preservesFiniteLimits [IsLocallyNoetherian X] :
    PreservesFiniteLimits (ι X) := by
  letI : HasBinaryBiproducts (Coh X) := HasBinaryBiproducts.of_hasBinaryProducts
  letI : ∀ {A B : Coh X} (f : A ⟶ B), PreservesLimit (parallelPair f 0) (ι X) :=
    fun f ↦ (Scheme.coherent X).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels (ι X)

/-- The inclusion of coherent sheaves preserves finite colimits. -/
noncomputable instance ι_preservesFiniteColimits [IsLocallyNoetherian X] :
    PreservesFiniteColimits (ι X) := by
  letI : HasBinaryBiproducts (Coh X) := HasBinaryBiproducts.of_hasBinaryCoproducts
  letI : ∀ {A B : Coh X} (f : A ⟶ B), PreservesColimit (parallelPair f 0) (ι X) :=
    fun f ↦ (Scheme.coherent X).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels (ι X)

/-- The inclusion of coherent sheaves into all module sheaves, packaged as an exact functor. -/
noncomputable def exactInclusion [IsLocallyNoetherian X] :
    ExactFunctor (Coh X) X.Modules :=
  ExactFunctor.of (ι X)

/-- The inclusion of coherent sheaves sends short exact sequences to short exact sequences. -/
theorem shortExact_map_ι [IsLocallyNoetherian X] {S : ShortComplex (Coh X)}
    (hS : S.ShortExact) : (S.map (ι X)).ShortExact := by
  have hExact : ∀ (T : ShortComplex (Coh X)), T.ShortExact →
      (T.map (ι X)).ShortExact :=
    ((@Functor.exact_tfae _ _ _ _ _ _ (ι X) (ι_additive X)).out 3 0).mp
      (show PreservesFiniteLimits (ι X) ∧ PreservesFiniteColimits (ι X) from
        ⟨inferInstance, inferInstance⟩)
  exact hExact S hS

end AlgebraicGeometry.Coh
