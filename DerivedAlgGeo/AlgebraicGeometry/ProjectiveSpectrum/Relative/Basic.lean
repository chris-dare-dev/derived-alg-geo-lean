/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.GradedAlgebraData
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Relative `Proj` of a quasi-coherent graded algebra

For a quasi-coherent graded `𝒪_S`-algebra `𝒜`, given as
`AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData`, the schemes `Proj 𝒜(U)` over the
affine opens `U` of `S` glue to a scheme `Proj_S(𝒜)` over `S`, with
`π⁻¹(U) ≅ Proj 𝒜(U)` over `U` for every affine open `U` (Stacks 01NQ, 01O0).

## Main definitions

* `QuasicoherentGradedAlgebraData.projToSpec 𝒜 U`: the structure map
  `Proj 𝒜(U) → Spec Γ(S, U)`.
* `QuasicoherentGradedAlgebraData.relativeProj 𝒜`: the relative `Proj`, `Proj_S(𝒜)`.
* `QuasicoherentGradedAlgebraData.relativeProjToBase 𝒜`: the structure morphism
  `π : Proj_S(𝒜) → S`.
* `QuasicoherentGradedAlgebraData.relativeProjι 𝒜 U`: the open immersion
  `Proj 𝒜(U) → Proj_S(𝒜)` onto `π⁻¹(U)`.
* `QuasicoherentGradedAlgebraData.relativeProjAffineIso 𝒜 U`: the isomorphism
  `π⁻¹(U) ≅ Proj 𝒜(U)`.
* `QuasicoherentGradedAlgebraData.relativeProjIsoOfEqTop 𝒜 U`: over an affine base `S = U`,
  `Proj_S(𝒜) ≅ Proj 𝒜(S)` (Stacks 01NQ for `U = S`).

## Main results

* `QuasicoherentGradedAlgebraData.isPullback_map_restrict`: for a basic open `V = D(f)` of an
  affine open `U`, `Proj 𝒜(V)` is the preimage of `V` in `Proj 𝒜(U)` (Stacks 01NO for a basic
  open).
* `QuasicoherentGradedAlgebraData.relativeProjAffineIso_hom_comp`: the isomorphism
  `π⁻¹(U) ≅ Proj 𝒜(U)` lies over `U`.
* `QuasicoherentGradedAlgebraData.relativeProjAffineIso_compat`: these isomorphisms are
  compatible with the restriction maps `Proj 𝒜(V) → Proj 𝒜(U)` (Stacks 01NO, 01NP).
* `QuasicoherentGradedAlgebraData.relativeProjToBase_iff`: a property of morphisms that is local on
  the target holds for `π` if and only if it holds for every `Proj 𝒜(U) → Spec Γ(S, U)`.
* `QuasicoherentGradedAlgebraData.isSeparated_relativeProjToBase`: `π` is separated
  (Stacks 01O2).

## Implementation notes

The schemes `Proj 𝒜(U)` form a functor on Mathlib's small affine Zariski site, whose arrows are
the basic opens `D(f) ⟶ U`. Over such an arrow, `𝒜(D(f)) = 𝒜(U)_f` and `Γ(S, D(f)) = Γ(S, U)_f`,
so `𝒜(D(f)) = Γ(S, D(f)) ⊗ 𝒜(U)` and `Proj 𝒜(D(f))` is the base change of `Proj 𝒜(U)`
(`AlgebraicGeometry.Proj.isPullback_map_of_isPushout`). The structure maps to `Spec Γ(S, U)`
therefore form an equifibered natural transformation, and Mathlib's relative gluing
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, Stacks 01LH) over the directed cover of `S`
by its affine opens glues them. This replaces the explicit cocycle check of Stacks 01NP:
`IsPullback` squares on the arrows of a locally directed cover are the gluing data.

The compatibility statement is for the arrows of the affine Zariski site, the basic opens, since
those are the restriction maps the data records. Base change of `Proj_S` and the twisting sheaves
`𝒪(d)` are not constructed here; functoriality is in `Relative/Functoriality.lean`.

## References

* [Stacks, Section 27.15 (Tag 01NM)](https://stacks.math.columbia.edu/tag/01NM): relative Proj
  via glueing, Lemmas 27.15.2–27.15.4 (Tags 01NO, 01NP, 01NQ).
* [Stacks, Definition 27.16.7 (Tag 01O0)](https://stacks.math.columbia.edu/tag/01O0).
* [Stacks, Lemma 27.16.9 (Tag 01O2)](https://stacks.math.columbia.edu/tag/01O2): `π` is separated.
* EGA II, §3.1.

## Tags

relative Proj, Proj, gluing, quasi-coherent graded algebra, affine Zariski site
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData

open AffineZariskiSite

variable {S : Scheme.{u}} (𝒜 : S.QuasicoherentGradedAlgebraData)

/-- The structure map `Proj 𝒜(U) → Spec 𝒜(U)₀ → Spec Γ(S, U)`. -/
noncomputable def projToSpec (U : S.AffineZariskiSite) :
    Proj (𝒜.grading U) ⟶ Spec Γ(S, U.toOpens) :=
  Proj.toSpecZero (𝒜.grading U) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.toOpens) (𝒜.grading U 0)))

/-- Over a basic open `D(f)` of an affine open `U`, the square of `Proj 𝒜(D(f)) → Proj 𝒜(U)` over
`Spec Γ(S, D(f)) → Spec Γ(S, U)` is a base change. -/
private theorem exists_isPullback_basicOpen (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    ∃ hirr, IsPullback (Proj.map (𝒜.restrict (U.basicOpen_le f)) hirr)
      (𝒜.projToSpec (U.basicOpen f)) (𝒜.projToSpec U)
      (Spec.map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op)) := by
  let _ : Algebra (𝒜.carrier U) (𝒜.carrier (U.basicOpen f)) :=
    (𝒜.restrict (U.basicOpen_le f)).toRingHom.toAlgebra
  let _ : Algebra Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens) :=
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom.toAlgebra
  let _ : Algebra Γ(S, U.toOpens) (𝒜.carrier (U.basicOpen f)) :=
    ((algebraMap Γ(S, (U.basicOpen f).toOpens) (𝒜.carrier (U.basicOpen f))).comp
      (algebraMap Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens))).toAlgebra
  have : IsScalarTower Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens)
      (𝒜.carrier (U.basicOpen f)) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, U.toOpens) (𝒜.carrier U) (𝒜.carrier (U.basicOpen f)) :=
    .of_algebraMap_eq fun r ↦ (𝒜.restrict_algebraMap (U.basicOpen_le f) r).symm
  have : IsLocalization.Away f Γ(S, (U.basicOpen f).toOpens) := U.2.isLocalization_basicOpen f
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝒜.carrier U) (Submonoid.powers f))
      (𝒜.carrier (U.basicOpen f)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact 𝒜.isLocalization_basicOpen U f
  have : Algebra.IsPushout Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens) (𝒜.carrier U)
      (𝒜.carrier (U.basicOpen f)) :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers f) Γ(S, (U.basicOpen f).toOpens)
      (𝒜.carrier U) (𝒜.carrier (U.basicOpen f))).symm
  exact ⟨_, Proj.isPullback_map_of_isPushout (𝒜.restrict (U.basicOpen_le f)) fun _ ↦ rfl⟩

/-- The restriction maps satisfy the hypothesis of `Proj.map`. -/
theorem irrelevant_le_map_restrict {U V : S.AffineZariskiSite} (h : V ≤ U) :
    HomogeneousIdeal.irrelevant (𝒜.grading V) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading U)).map (𝒜.restrict h) := by
  obtain ⟨f, hf⟩ := id h
  obtain rfl : U.basicOpen f = V := Subtype.ext hf
  exact (𝒜.exists_isPullback_basicOpen U f).1

/-- **`Proj` of a basic open is a preimage** (Stacks 01NO, for a basic open). For a basic open
`V = D(f)` of an affine open `U`, the square

    Proj 𝒜(V) ⟶ Proj 𝒜(U)
       ↓             ↓
    Spec Γ(S, V) ⟶ Spec Γ(S, U)

is cartesian. -/
theorem isPullback_map_restrict {U V : S.AffineZariskiSite} (h : V ≤ U) :
    IsPullback (Proj.map (𝒜.restrict h) (𝒜.irrelevant_le_map_restrict h)) (𝒜.projToSpec V)
      (𝒜.projToSpec U) (Spec.map (S.presheaf.map (homOfLE (toOpens_mono h)).op)) := by
  obtain ⟨f, hf⟩ := id h
  obtain rfl : U.basicOpen f = V := Subtype.ext hf
  exact (𝒜.exists_isPullback_basicOpen U f).2

/-- The charts `U ↦ Proj 𝒜(U)`, as a functor on the affine Zariski site. -/
@[simps obj]
noncomputable def projFunctor : S.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := Proj (𝒜.grading U)
  map {V U} i := Proj.map (𝒜.restrict (leOfHom i)) (𝒜.irrelevant_le_map_restrict (leOfHom i))
  map_id U := by
    rw [← Proj.map_id]
    congr 1
    exact GradedRingHom.ext (𝒜.restrict_id U)
  map_comp {W V U} i j := by
    rw [← Proj.map_comp]
    congr 1
    exact GradedRingHom.ext fun x ↦ (𝒜.restrict_comp _ _ x).symm

/-- The structure maps `Proj 𝒜(U) → Spec Γ(S, U)`, as a natural transformation. -/
@[simps app]
noncomputable def projNatTrans :
    𝒜.projFunctor ⟶ toOpensFunctor S ⋙ S.presheaf.rightOp ⋙ Scheme.Spec where
  app U := 𝒜.projToSpec U
  naturality _ _ i := (𝒜.isPullback_map_restrict (leOfHom i)).w

theorem equifibered_projNatTrans : 𝒜.projNatTrans.Equifibered :=
  fun _ _ i ↦ 𝒜.isPullback_map_restrict (leOfHom i)

/-- The relative gluing datum of the charts `Proj 𝒜(U)` over the directed cover of `S` by its
affine opens (Stacks 01LH). -/
noncomputable def relativeGluingData :
    (AffineZariskiSite.directedCover S).RelativeGluingData where
  functor := 𝒜.projFunctor
  natTrans := 𝒜.projNatTrans ≫ (restrictIsoSpec S).inv
  equifibered := 𝒜.equifibered_projNatTrans.comp
    (NatTrans.Equifibered.of_isIso (restrictIsoSpec S).inv)

private lemma relativeGluingData_natTrans_app (U : S.AffineZariskiSite) :
    𝒜.relativeGluingData.natTrans.app U = 𝒜.projToSpec U ≫ U.2.isoSpec.inv :=
  rfl

instance : (𝒜.relativeGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- **The relative `Proj`** `Proj_S(𝒜)` of a quasi-coherent graded algebra (Stacks 01NQ, 01O0),
glued from the schemes `Proj 𝒜(U)` over the affine opens `U` of `S`. -/
noncomputable def relativeProj : Scheme.{u} :=
  𝒜.relativeGluingData.glued

/-- The structure morphism `π : Proj_S(𝒜) → S`. -/
noncomputable def relativeProjToBase : 𝒜.relativeProj ⟶ S :=
  𝒜.relativeGluingData.toBase

/-- The chart `Proj 𝒜(U) → Proj_S(𝒜)` over an affine open `U`. -/
noncomputable def relativeProjι (U : S.AffineZariskiSite) :
    Proj (𝒜.grading U) ⟶ 𝒜.relativeProj :=
  colimit.ι 𝒜.relativeGluingData.functor U

instance (U : S.AffineZariskiSite) : IsOpenImmersion (𝒜.relativeProjι U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι 𝒜.relativeGluingData.functor U))

instance {U V : S.AffineZariskiSite} (h : V ≤ U) :
    IsOpenImmersion (Proj.map (𝒜.restrict h) (𝒜.irrelevant_le_map_restrict h)) :=
  inferInstanceAs (IsOpenImmersion (𝒜.relativeGluingData.functor.map (homOfLE h)))

@[reassoc (attr := simp)]
theorem map_restrict_relativeProjι {U V : S.AffineZariskiSite} (h : V ≤ U) :
    Proj.map (𝒜.restrict h) (𝒜.irrelevant_le_map_restrict h) ≫ 𝒜.relativeProjι U =
      𝒜.relativeProjι V :=
  colimit.w 𝒜.relativeGluingData.functor (homOfLE h)

/-- The chart over `U` lies over `U`. -/
@[reassoc (attr := simp)]
theorem relativeProjι_toBase (U : S.AffineZariskiSite) :
    𝒜.relativeProjι U ≫ 𝒜.relativeProjToBase = 𝒜.projToSpec U ≫ U.2.fromSpec := by
  refine (𝒜.relativeGluingData.ι_toBase U).trans ?_
  rw [relativeGluingData_natTrans_app]
  exact Category.assoc _ _ _

/-- The chart over `U` is the preimage of `U`. -/
theorem opensRange_relativeProjι (U : S.AffineZariskiSite) :
    (𝒜.relativeProjι U).opensRange = 𝒜.relativeProjToBase ⁻¹ᵁ U.toOpens := by
  have := 𝒜.relativeGluingData.toBase_preimage_eq_opensRange_ι U
  simp only [Opens.opensRange_ι] at this
  exact this.symm

/-- The chart `Proj 𝒜(U) → Proj_S(𝒜)` is the base change of `U → S`. -/
theorem isPullback_relativeProjι (U : S.AffineZariskiSite) :
    IsPullback (𝒜.projToSpec U ≫ U.2.isoSpec.inv) (𝒜.relativeProjι U) U.toOpens.ι
      𝒜.relativeProjToBase :=
  𝒜.relativeGluingData.isPullback_natTrans_ι_toBase U

/-- **The relative `Proj` over an affine open** (Stacks 01NQ): `π⁻¹(U) ≅ Proj 𝒜(U)`. -/
noncomputable def relativeProjAffineIso (U : S.AffineZariskiSite) :
    (𝒜.relativeProjToBase ⁻¹ᵁ U.toOpens).toScheme ≅ Proj (𝒜.grading U) :=
  (𝒜.relativeProj.isoOfEq (𝒜.opensRange_relativeProjι U)).symm ≪≫
    (𝒜.relativeProjι U).isoOpensRange.symm

@[reassoc (attr := simp)]
theorem relativeProjAffineIso_inv_ι (U : S.AffineZariskiSite) :
    (𝒜.relativeProjAffineIso U).inv ≫ (𝒜.relativeProjToBase ⁻¹ᵁ U.toOpens).ι =
      𝒜.relativeProjι U := by
  simp [relativeProjAffineIso]

/-- The isomorphism `π⁻¹(U) ≅ Proj 𝒜(U)` lies over `U ≅ Spec Γ(S, U)`. -/
@[reassoc]
theorem relativeProjAffineIso_hom_comp (U : S.AffineZariskiSite) :
    (𝒜.relativeProjAffineIso U).hom ≫ 𝒜.projToSpec U ≫ U.2.isoSpec.inv =
      𝒜.relativeProjToBase ∣_ U.toOpens := by
  rw [← cancel_mono U.toOpens.ι, morphismRestrict_ι, Category.assoc, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, ← relativeProjι_toBase, ← relativeProjAffineIso_inv_ι,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- **Compatibility with restriction** (Stacks 01NO, 01NP): for a basic open `V` of an affine
open `U`, the isomorphisms `π⁻¹(V) ≅ Proj 𝒜(V)` and `π⁻¹(U) ≅ Proj 𝒜(U)` intertwine the inclusion
`π⁻¹(V) ⊆ π⁻¹(U)` with `Proj 𝒜(V) → Proj 𝒜(U)`. -/
@[reassoc]
theorem relativeProjAffineIso_compat {U V : S.AffineZariskiSite} (h : V ≤ U) :
    (𝒜.relativeProjAffineIso V).inv ≫
        𝒜.relativeProj.homOfLE (𝒜.relativeProjToBase.preimage_mono (toOpens_mono h)) =
      Proj.map (𝒜.restrict h) (𝒜.irrelevant_le_map_restrict h) ≫
        (𝒜.relativeProjAffineIso U).inv := by
  rw [← cancel_mono (𝒜.relativeProjToBase ⁻¹ᵁ U.toOpens).ι, Category.assoc, Category.assoc,
    homOfLE_ι, relativeProjAffineIso_inv_ι, relativeProjAffineIso_inv_ι,
    map_restrict_relativeProjι]

/-- **The relative `Proj` over an affine base** (Stacks 01NQ for `U = S`): if the affine open `U`
is all of `S`, then `Proj_S(𝒜) ≅ Proj 𝒜(U)`, the `Proj` of the graded algebra of global sections,
over `S ≅ Spec Γ(S, U)` by `relativeProjAffineIso_hom_comp`. -/
noncomputable def relativeProjIsoOfEqTop (U : S.AffineZariskiSite) (hU : U.toOpens = ⊤) :
    𝒜.relativeProj ≅ Proj (𝒜.grading U) :=
  𝒜.relativeProj.topIso.symm ≪≫
    𝒜.relativeProj.isoOfEq (by rw [hU, Scheme.Hom.preimage_top]) ≪≫ 𝒜.relativeProjAffineIso U

theorem relativeProjIsoOfEqTop_inv (U : S.AffineZariskiSite) (hU : U.toOpens = ⊤) :
    (𝒜.relativeProjIsoOfEqTop U hU).inv = 𝒜.relativeProjι U := by
  simp [relativeProjIsoOfEqTop]

/-- Morphisms out of `Proj_S(𝒜)` agree once they agree on every chart `Proj 𝒜(U)`. -/
theorem relativeProj_hom_ext {T : Scheme.{u}} {f g : 𝒜.relativeProj ⟶ T}
    (h : ∀ U, 𝒜.relativeProjι U ≫ f = 𝒜.relativeProjι U ≫ g) : f = g :=
  colimit.hom_ext h

/-- **`π` is determined by the charts.** A property of morphisms that is local on the target
holds for `π : Proj_S(𝒜) → S` if and only if it holds for every structure map
`Proj 𝒜(U) → Spec Γ(S, U)`, since `π⁻¹(U) ≅ Proj 𝒜(U)` over `U ≅ Spec Γ(S, U)`. -/
theorem relativeProjToBase_iff (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P 𝒜.relativeProjToBase ↔ ∀ U, P (𝒜.projToSpec U) := by
  refine ⟨fun H U ↦ ?_, fun H ↦ ?_⟩
  · rw [← P.cancel_right_of_respectsIso _ U.2.isoSpec.inv]
    exact IsZariskiLocalAtTarget.of_isPullback (𝒜.isPullback_relativeProjι U).flip H
  · refine IsZariskiLocalAtTarget.of_openCover (AffineZariskiSite.directedCover S) fun U ↦ ?_
    refine (P.arrow_mk_iso_iff (Arrow.isoMk (𝒜.isPullback_relativeProjι U).flip.isoPullback
      (Iso.refl _) ?_)).mp ((P.cancel_right_of_respectsIso _ U.2.isoSpec.inv).mpr (H U))
    simp only [Cover.pullbackHom, Iso.refl_hom, Category.comp_id]
    exact (𝒜.isPullback_relativeProjι U).flip.isoPullback_hom_snd

/-- **`Proj_S(𝒜) → S` is separated** (Stacks 01O2): over an affine open `U` it is
`Proj 𝒜(U) → Spec 𝒜(U)₀ → Spec Γ(S, U)`, separated followed by affine. -/
instance isSeparated_relativeProjToBase : IsSeparated 𝒜.relativeProjToBase :=
  (𝒜.relativeProjToBase_iff @IsSeparated).mpr fun U ↦ by
    rw [projToSpec]
    infer_instance

end AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData
