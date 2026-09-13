/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.CategoryTheory.FiniteFiltration
import DerivedAlgGeo.Topology.Sheaves.PushforwardStalks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Module-sheaf pushforward along a closed immersion

An inducing map has faithful module-sheaf pushforward: every source open is the preimage of its
canonical target open, so equality after pushforward detects every component of a module-sheaf
morphism.  For a closed immersion this makes the pullback/pushforward adjunction counit epic.

The underlying abelian-sheaf pushforward along a closed embedding is also exact.  This file
transports that theorem through the faithful, exact, and epi-reflecting forgetful functor at the
neutral `Scheme.Modules` layer.  The results are registered on Mathlib's existing functors, so
every generic exact or adjunction construction uses the common API directly.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Module-sheaf pushforward is faithful when the underlying continuous map is inducing.

For a source open `U`, `hf.functorObj U` is a target open whose preimage is exactly `U`.
Evaluating equality of pushed-forward morphisms there recovers equality of their components on
`U`. -/
theorem pushforward_faithful_of_isInducing (hf : Topology.IsInducing f.base) :
    (pushforward f).Faithful where
  map_injective {M N} g h e := by
    apply hom_ext
    intro U
    have happ := congrArg
      (fun k : (pushforward f).obj M ⟶ (pushforward f).obj N ↦
        k.app (hf.functorObj U)) e
    change g.app ((TopologicalSpace.Opens.map f.base).obj (hf.functorObj U)) =
      h.app ((TopologicalSpace.Opens.map f.base).obj (hf.functorObj U)) at happ
    rw [hf.map_functorObj U] at happ
    exact happ

/-- Module-sheaf pushforward along a closed immersion is faithful. -/
noncomputable instance pushforward_faithful_of_isClosedImmersion
    [IsClosedImmersion f] :
    (pushforward f).Faithful :=
  pushforward_faithful_of_isInducing f f.isClosedEmbedding.isInducing

/-- Every component of the module-sheaf pullback/pushforward counit along a closed immersion is
epic.  This uses only faithfulness of the right adjoint, not the stronger standard assertion that
the counit is an isomorphism. -/
theorem pullbackPushforwardAdjunction_counit_epi_of_isClosedImmersion
    [IsClosedImmersion f] (M : X.Modules) :
    Epi ((pullbackPushforwardAdjunction f).counit.app M) :=
  inferInstance

variable [IsClosedImmersion f]

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
