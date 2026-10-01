import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback

/-!
# Scheme-module pullback audit

This slice checks the neutral pullback root independently of line-bundle, determinant, divisor,
and Picard-group consumers. Intrinsic rank-one invertibility is inherited through Mathlib's
existing scheme-module pullback rather than stored in a parallel carrier. Strong monoidality is
a theorem (`pullbackMonoidal`, Stacks 01CD): the standard `Functor.Monoidal` class is inhabited for
every morphism, not stored in a parallel capability record.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-! ## Affine tilde and pullback comparison -/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeMapHomologicalComplexIso

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverIso
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardOverIso
#print axioms AlgebraicGeometry.Scheme.Modules.overEquiv_map_pushforwardOverIso_hom
#print axioms AlgebraicGeometry.Scheme.Modules.overEquiv_map_pullbackOverIso_hom
#print axioms AlgebraicGeometry.Scheme.Modules.overEquiv_map_pullbackOverAdjunction_unit
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardOverFunctor_map_transport
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardOverIso_map_normal_form
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverIso_unit_app
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTrivializationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_pullback
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackLocalGeneratorsData
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackLocalGeneratorsData_generators_I
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallyFreeData_pullbackLocalGeneratorsData
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback

/-! ## Pullback on slices, and the structure sheaf -/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardOverFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverAdjunction
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverFunctor_preservesColimits
#print axioms AlgebraicGeometry.Scheme.Modules.overEquivFunctorUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.overEquivInverseUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackRestrictUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOverUnitIso
#print axioms AlgebraicGeometry.Scheme.Hom.coversTop_preimage

/-! ## Coherence is preserved by pullback

`Coh.pullback` with its exactness: right exact always, left exact when module-sheaf pullback is.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackPresentationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isFinite_pullbackPresentationOver
#print axioms AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback
#print axioms AlgebraicGeometry.Scheme.Modules.isCoherent_pullback
#print axioms AlgebraicGeometry.Coh.pullback
#print axioms AlgebraicGeometry.Coh.pullbackCompι
#print axioms AlgebraicGeometry.Coh.pullbackComp
#print axioms AlgebraicGeometry.Coh.pullbackId
#print axioms AlgebraicGeometry.Coh.pullbackEquivalence
#print axioms AlgebraicGeometry.Coh.pullback_preservesFiniteColimits
#print axioms AlgebraicGeometry.Coh.pullback_preservesFiniteLimits
#print axioms AlgebraicGeometry.Coh.pullback_additive

/-! ## Monoidal structure (Stacks 01CD, issue #1664)

`pullbackMonoidal` is the strong monoidal structure on module-sheaf pullback along every morphism
of schemes, obtained by upgrading the doctrinal oplax structure of the lax monoidal pushforward;
`pullbackTensorIso` and `pullbackUnitIso` are its comparison isomorphisms.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorHom
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorHom_unit_app_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_stalkMap_pullbackTensorHom
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_pullbackTensorHom
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackMonoidal
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackMonoidal_toOplaxMonoidal
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_inv
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom

/-! ## The projection formula (Stacks 01E8 at `q = 0`, issue #1664)

`projectionMap f M L : f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)` is built from the unit and the lax structure of
`f_*`; it is an isomorphism for an invertible `L`.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_isMonoidal
#print axioms AlgebraicGeometry.Scheme.Modules.projectionMap
#print axioms AlgebraicGeometry.Scheme.Modules.projectionMap_eq
#print axioms AlgebraicGeometry.Scheme.Modules.projectionMap_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.projectionMap_naturality_right
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.tensorInverse
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_projectionMap
#print axioms AlgebraicGeometry.Scheme.Modules.projectionIso
#print axioms AlgebraicGeometry.Scheme.Modules.projectionIso_hom
#print axioms AlgebraicGeometry.Scheme.Modules.projectionNatIso

-- The two comparisons elaborate with no `Functor.Monoidal` argument: the instance is canonical.
noncomputable example (f : X ⟶ Y) (M N : Y.Modules) :
    Scheme.Modules.tensorObj ((pullback f).obj M) ((pullback f).obj N) ≅
      (pullback f).obj (Scheme.Modules.tensorObj M N) :=
  Scheme.Modules.pullbackTensorIso f M N

example [SheafOfModules.IsInvertible.{u, u, u}
    (show SheafOfModules Y.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj M) :=
  inferInstance

end AlgebraicGeometry.Scheme.Modules
