/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.ClosedImmersion
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Projective
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective

/-!
# Serre finiteness for projective varieties

**A projective variety over `k` has finite-dimensional coherent cohomology in every degree**, and
its `FiniteDimensionalCohomology` package is a theorem: step 3 of `#332`, closing it for every
variety with a projective presentation into a projective space with at least two coordinates.

## The transport, and why it has to be linear

The closed-immersion comparison identifies `Hⁱ(X, F)` with `Hⁱ(Pⁿ, ι_* F)` as abelian groups.
An additive isomorphism onto a finite-dimensional `k`-space bounds nothing over an infinite field,
so the identification has to be shown `k`-linear before finiteness can cross it. The base field
acts on both sides through global functions, and the two actions match because `ι` is a morphism
over `Spec k`: the global function a scalar becomes on `X` is the pullback of the one it becomes on
`Pⁿ` (`baseFieldToGlobalSections_comp`), and pushforward carries multiplication by the pulled-back
function to multiplication by the original (`pushforward_varietyScalarAction`). The comparison is
natural in the sheaf (`coherentHPushforwardAddEquiv_naturality`, from `extAdjunctionMap_comp_mk₀`
and associativity of `Ext`), so it commutes with the scalar endomorphisms, which is linearity.

## The `HasExt` witness

`coherentH` names its groups at `HasExt.standard`, in universe `u + 1`;
`cohCohomologyPushforwardAddEquiv` lets instance search find the Grothendieck-category witness in
universe `u`, so it compares different groups. `coherentHPushforwardAddEquiv` is the same
comparison instantiated at the standard witness (`cohomologyPushforwardAddEquivAt`), which is what
lets it be stated against `coherentH` at all.

## Two coordinates

The projective-space theorem takes `Nontrivial ι`: on `P⁰`, a point, a negative twist is the
structure sheaf and its degree-zero cohomology is `k`, not `0`, so the dévissage's degree-zero
step needs a different argument there. A presentation into `P⁰` or into the empty `P⁻¹` describes
a point or the empty scheme, whose cohomology is the affine case; it is excluded here by the
`Nontrivial P.index` hypothesis rather than treated.

## Two spellings of the structure morphism

`ProjectivePresentation` states its compatibility against `AlgebraicGeometry.projectiveSpaceToSpec`,
built from `homogeneousZeroRingEquiv`; the `Over` instance on `Pⁿ` uses
`Proj.projectiveSpaceToSpec`, built from the algebra map. `projectiveSpaceToSpec_eq` says they are
the same morphism, because both ring maps send `r` to the constant polynomial `r`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]

/-- **A scalar becomes, on `X`, the pullback of the global function it becomes on `Y`**, for
`g : X ⟶ Y` over `Spec k`. -/
theorem baseFieldToGlobalSections_comp (g : X ⟶ Y)
    (hg : X ↘ Spec (CommRingCat.of k) = g ≫ (Y ↘ Spec (CommRingCat.of k))) (r : k) :
    baseFieldToGlobalSections X r = g.appTop.hom (baseFieldToGlobalSections Y r) := by
  rw [baseFieldToGlobalSections, baseFieldToGlobalSections, hg, Scheme.Hom.comp_appTop]
  rfl

/-- **Pushforward carries the scalar action to the scalar action.** Over an open `U` of `Y`, both
sides multiply a section of `F` over `g⁻¹ U` by the restriction of the same global function of
`X`; the pushforward's module structure is restriction of scalars along `g`, which is what turns
the function of `Y` into that function of `X`. -/
theorem pushforward_varietyScalarAction (g : X ⟶ Y)
    (hg : X ↘ Spec (CommRingCat.of k) = g ≫ (Y ↘ Spec (CommRingCat.of k)))
    (F : X.Modules) (r : k) :
    (Scheme.Modules.pushforward g).map (varietyScalarAction X F r)
      = varietyScalarAction Y ((Scheme.Modules.pushforward g).obj F) r := by
  ext U m
  change ((globalSectionSmul F (baseFieldToGlobalSections X r)).val.app (op (g ⁻¹ᵁ U))).hom m
    = ((globalSectionSmul ((Scheme.Modules.pushforward g).obj F)
        (baseFieldToGlobalSections Y r)).val.app (op U)).hom m
  rw [globalSectionSmul_app, globalSectionSmul_app, baseFieldToGlobalSections_comp g hg]
  exact congrArg (fun s : X.presheaf.obj (op (g ⁻¹ᵁ U)) => s • (show Γ(F, g ⁻¹ᵁ U) from m))
    (ConcreteCategory.congr_hom (g.naturality (homOfLE (le_top (a := U))).op)
      (baseFieldToGlobalSections Y r)).symm

/-- **Pushforward carries the coherent scalar action to the coherent scalar action.** -/
theorem pushforward_coherentScalarAction [IsLocallyNoetherian Y] (g : X ⟶ Y) [IsFinite g]
    (hg : X ↘ Spec (CommRingCat.of k) = g ≫ (Y ↘ Spec (CommRingCat.of k)))
    (F : Coh X) (r : k) :
    (Coh.pushforward g).map (coherentScalarAction X F r)
      = coherentScalarAction Y ((Coh.pushforward g).obj F) r :=
  ObjectProperty.hom_ext _ (pushforward_varietyScalarAction g hg ((Coh.ι X).obj F) r)

omit [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))] in
/-- **`Hⁱ(X, F) ≃+ Hⁱ(Y, g_* F)` for a closed immersion `g`, at the `HasExt` witness `coherentH`
uses.** The same comparison as `cohCohomologyPushforwardAddEquiv`, instantiated at
`HasExt.standard` rather than at the witness instance search finds. -/
noncomputable def coherentHPushforwardAddEquiv [IsLocallyNoetherian Y] (g : X ⟶ Y)
    [IsClosedImmersion g] (F : Coh X) (n : ℕ) :
    (coherentH X n).obj F ≃+ (coherentH Y n).obj ((Coh.pushforward g).obj F) :=
  DerivedAlgGeo.Topology.cohomologyPushforwardAddEquivAt g.base
    (IsClosedImmersion.isClosedEmbedding g).isInducing
    (IsClosedImmersion.isClosedEmbedding g).isClosed_range
    (HasExt.standard _) (HasExt.standard _) ((Scheme.Modules.toSheaf X).obj ((Coh.ι X).obj F)) n

omit [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))] in
/-- **The closed-immersion comparison is natural in the coherent sheaf**: the abstract naturality
`cohomologyPushforwardAddEquivAt_naturality`, read through `toSheaf`, which commutes with
pushforward on the nose. -/
theorem coherentHPushforwardAddEquiv_naturality [IsLocallyNoetherian Y] (g : X ⟶ Y)
    [IsClosedImmersion g] {F F' : Coh X} (φ : F ⟶ F') (n : ℕ) (x : (coherentH X n).obj F) :
    coherentHPushforwardAddEquiv g F' n ((coherentH X n).map φ x)
      = (coherentH Y n).map ((Coh.pushforward g).map φ)
          (coherentHPushforwardAddEquiv g F n x) :=
  DerivedAlgGeo.Topology.cohomologyPushforwardAddEquivAt_naturality g.base
    (IsClosedImmersion.isClosedEmbedding g).isInducing
    (IsClosedImmersion.isClosedEmbedding g).isClosed_range
    (HasExt.standard _) (HasExt.standard _) ((Scheme.Modules.toSheaf X).map ((Coh.ι X).map φ)) n x

/-- **The closed-immersion comparison is base-field linear.** Naturality against the scalar
endomorphism, followed by the identification of its pushforward with the scalar endomorphism of
the pushforward. -/
theorem coherentHPushforwardAddEquiv_smul [IsLocallyNoetherian Y] (g : X ⟶ Y)
    [IsClosedImmersion g]
    (hg : X ↘ Spec (CommRingCat.of k) = g ≫ (Y ↘ Spec (CommRingCat.of k)))
    (F : Coh X) (n : ℕ) (r : k) (x : (coherentH X n).obj F) :
    letI := coherentHModule k X n F
    letI := coherentHModule k Y n ((Coh.pushforward g).obj F)
    coherentHPushforwardAddEquiv g F n (r • x) = r • coherentHPushforwardAddEquiv g F n x := by
  change coherentHPushforwardAddEquiv g F n ((coherentH X n).map (coherentScalarAction X F r) x)
    = (coherentH Y n).map (coherentScalarAction Y ((Coh.pushforward g).obj F) r)
        (coherentHPushforwardAddEquiv g F n x)
  rw [coherentHPushforwardAddEquiv_naturality, pushforward_coherentScalarAction g hg F r]

/-- **`Hⁱ(X, F) ≃ₗ[k] Hⁱ(Y, g_* F)`** for a closed immersion `g` over `Spec k`. -/
noncomputable def coherentHPushforwardLinearEquiv [IsLocallyNoetherian Y] (g : X ⟶ Y)
    [IsClosedImmersion g]
    (hg : X ↘ Spec (CommRingCat.of k) = g ≫ (Y ↘ Spec (CommRingCat.of k)))
    (F : Coh X) (n : ℕ) :
    (linearCoherentH k X n).obj F ≃ₗ[k] (linearCoherentH k Y n).obj ((Coh.pushforward g).obj F) :=
  { coherentHPushforwardAddEquiv g F n with
    map_smul' := coherentHPushforwardAddEquiv_smul g hg F n }

/-- **Finite-dimensionality descends along a closed immersion over `Spec k`.** -/
theorem module_finite_linearCoherentH_of_isClosedImmersion [IsLocallyNoetherian Y] (g : X ⟶ Y)
    [IsClosedImmersion g]
    (hg : X ↘ Spec (CommRingCat.of k) = g ≫ (Y ↘ Spec (CommRingCat.of k)))
    (F : Coh X) (n : ℕ)
    (hY : Module.Finite k ((linearCoherentH k Y n).obj ((Coh.pushforward g).obj F))) :
    Module.Finite k ((linearCoherentH k X n).obj F) :=
  Module.Finite.equiv (coherentHPushforwardLinearEquiv g hg F n).symm

end AlgebraicGeometry.Cohomology

namespace AlgebraicGeometry

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The two structure morphisms of polynomial projective space agree.** `homogeneousZeroRingEquiv`
and the algebra map both send `r` to the constant polynomial `r`. -/
theorem projectiveSpaceToSpec_eq (ι k : Type u) [Field k] :
    projectiveSpaceToSpec ι k = Proj.projectiveSpaceToSpec ι k := by
  unfold projectiveSpaceToSpec Proj.projectiveSpaceToSpec
  congr 3

namespace ProjectivePresentation

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- **Serre finiteness for a projective variety**: every coherent sheaf on `X` has
finite-dimensional cohomology in every degree, given a presentation into a projective space with
at least two coordinates. -/
theorem module_finite_linearCoherentH (P : ProjectivePresentation k X) [Nontrivial P.index]
    (i : ℕ) (F : Coh X) : Module.Finite k ((Cohomology.linearCoherentH k X i).obj F) := by
  haveI := Fintype.ofFinite P.index
  haveI : IsProper (Proj (polynomialGrading P.index k) ↘ Spec (CommRingCat.of k)) :=
    Proj.isProper_projectiveSpaceToSpec P.index k
  haveI : IsNoetherian (Proj (polynomialGrading P.index k)) :=
    Variety.isNoetherian_of_isProper (k := k)
  have hg : X ↘ Spec (CommRingCat.of k)
      = P.embedding ≫ (Proj (polynomialGrading P.index k) ↘ Spec (CommRingCat.of k)) := by
    rw [← P.overBase, projectiveSpaceToSpec_eq]
    rfl
  exact Cohomology.module_finite_linearCoherentH_of_isClosedImmersion
    (Y := Proj (polynomialGrading P.index k)) P.embedding hg F i
    (Proj.module_finite_linearCoherentH_projectiveSpace P.index k i _)

variable [IsVariety k X]

/-- **The finite-dimensional cohomology package of a projective variety**, proved from a
presentation rather than supplied. -/
noncomputable def finiteDimensionalCohomology (P : ProjectivePresentation k X)
    [Nontrivial P.index] : Cohomology.FiniteDimensionalCohomology k X where
  toLinearCohomology := Cohomology.canonicalLinearCohomology X
  finite := fun i F => P.module_finite_linearCoherentH i F

/-- **The finite cohomology package of a projective variety**: Serre finiteness with the
finite-affine-cover vanishing bound. -/
noncomputable def finiteCohomology (P : ProjectivePresentation k X) [Nontrivial P.index] :
    Cohomology.FiniteCohomology k X :=
  haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := P.isProper_structureMorphism
  haveI : IsNoetherian X := Variety.isNoetherian_of_isProper (k := k)
  haveI : X.IsSeparated := Variety.isSeparated_of_isProper (k := k)
  P.finiteDimensionalCohomology.toFiniteCohomology

end ProjectivePresentation

end AlgebraicGeometry
