/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.CategoryTheory.FiniteFiltration
import DerivedAlgGeo.Topology.Sheaves.PushforwardStalks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Exact module-sheaf pushforward along a closed immersion

The underlying abelian-sheaf pushforward along a closed embedding is exact.  This file transports
that theorem through the faithful, exact, and epi-reflecting forgetful functor at the neutral
`Scheme.Modules` layer.  The result is registered on Mathlib's existing `Modules.pushforward`
functor, so every generic exact construction—including `FiniteFiltration.map`—uses the common
functor directly.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Module-sheaf pushforward along a closed immersion preserves epimorphisms. -/
noncomputable instance pushforward_preservesEpimorphisms_of_isClosedImmersion :
    (pushforward f).PreservesEpimorphisms := by
  let U := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base
  letI hUColimits : PreservesFiniteColimits U :=
    DerivedAlgGeo.Topology.preservesFiniteColimits_pushforward f.base
      f.isClosedEmbedding.isInducing f.isClosedEmbedding.isClosed_range
  letI hUEpi : U.PreservesEpimorphisms :=
    CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape U
  haveI : (toSheaf X ⋙ U).PreservesEpimorphisms := {
    preserves := fun g hg => by
      rw [Functor.comp_map]
      have h : Epi ((toSheaf X).map g) := inferInstance
      exact @Functor.PreservesEpimorphisms.preserves _ _ _ _ U hUEpi _ _
        ((toSheaf X).map g) h }
  haveI : (pushforward f ⋙ toSheaf Y).PreservesEpimorphisms := by
    change (toSheaf X ⋙ U).PreservesEpimorphisms
    infer_instance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    (pushforward f) (toSheaf Y)

/-- Module-sheaf pushforward along a closed immersion preserves homology. -/
noncomputable instance pushforward_preservesHomology_of_isClosedImmersion :
    (pushforward f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Module-sheaf pushforward along a closed immersion preserves finite colimits. -/
noncomputable instance pushforward_preservesFiniteColimits_of_isClosedImmersion :
    PreservesFiniteColimits (pushforward f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Pushing a short exact sequence through a closed immersion remains short exact. -/
theorem shortExact_map_pushforward_of_isClosedImmersion
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (pushforward f)).ShortExact :=
  hS.map_of_exact (pushforward f)

/-! The generic filtration adapter now applies without a geometric wrapper. -/

noncomputable example {M : X.Modules} (F : FiniteFiltration X.Modules M) :
    FiniteFiltration Y.Modules ((pushforward f).obj M) :=
  F.map (pushforward f)

end AlgebraicGeometry.Scheme.Modules
