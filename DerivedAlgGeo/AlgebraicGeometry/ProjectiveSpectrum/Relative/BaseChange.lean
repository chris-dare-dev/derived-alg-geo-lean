/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Pullback

/-!
# Base change of relative `Proj`

For a morphism `g : S' ⟶ S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`, the relative `Proj`
of the pullback `g^*𝒜` (`QuasicoherentGradedAlgebraData.pullback`) is the base change of
`Proj_S(𝒜)`:

    Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)
          ↓              ↓
          S'      ⟶      S

is cartesian (Stacks 01O3).

## Main definitions

* `QuasicoherentGradedAlgebraData.relativeProjPullbackMap 𝒜 g`: the morphism
  `Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)`, given on the chart over the source of an affine pair `(V', V)`
  by `Proj` of `𝒜(V) → (g^*𝒜)(V')`.

## Main results

* `QuasicoherentGradedAlgebraData.isPullback_map_pullbackChartHom`: over an affine pair `(V', V)`,
  `Proj (g^*𝒜)(V')` is the base change of `Proj 𝒜(V)` along `Spec Γ(S', V') → Spec Γ(S, V)`.
* `QuasicoherentGradedAlgebraData.relativeProjι_relativeProjPullbackMap`: the base change
  morphism on charts.
* `QuasicoherentGradedAlgebraData.relativeProj_isPullback`: relative `Proj` commutes with base
  change (Stacks 01O3).

## Implementation notes

The chart `Proj (g^*𝒜)(U')` over an affine open `U'` of `S'` need not map into a chart of
`Proj_S(𝒜)`, since `g(U')` need not lie in an affine open of `S`. The charts over the sources of
affine pairs do, so `Proj_{S'}(g^*𝒜)` is first reglued over the cover of `S'` by those sources
(`pullbackGluingData`), and the regluing is identified with `Proj_{S'}(g^*𝒜)` chart by chart
(`pullbackGluedToRelativeProj` is an isomorphism). The base change morphism is defined on the
regluing, and the square is checked to be cartesian over the same cover with
`AlgebraicGeometry.Scheme.isPullback_of_openCover`: on each chart it is the base change of `Proj`
of a pushout of graded rings (`AlgebraicGeometry.Proj.isPullback_map_of_isPushout`) followed by
`π⁻¹(V) ≅ Proj 𝒜(V)`.

The compatibility of twisting sheaves in Stacks 01O3 is not proved here. The twisting sheaves
`𝒪(d)` of relative `Proj` are in `Relative/Twisting.lean`, and comparing their pullback along
`relativeProjPullbackMap` with those of `Proj_{S'}(g^*𝒜)` is not done.

## References

* [Stacks, Lemma 27.16.10 (Tag 01O3)](https://stacks.math.columbia.edu/tag/01O3).
* [Stacks, Lemma 27.11.6 (Tag 01N2)](https://stacks.math.columbia.edu/tag/01N2): `Proj` commutes
  with base change of graded rings.

## Tags

relative Proj, base change, pullback, quasi-coherent graded algebra
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData

open AffineZariskiSite

variable {S S' : Scheme.{u}} (𝒜 : S.QuasicoherentGradedAlgebraData) {g : S' ⟶ S}

/-! ### The chartwise square -/

/-- Over an affine pair, the base change square of `Proj` of the local models, together with
the hypothesis of `Proj.map` for `𝒜(V) → (g^*𝒜)(V')`. -/
private theorem exists_isPullback_pullbackChartHom (p : AffinePair g) :
    ∃ hirr, IsPullback (Proj.map (𝒜.pullbackChartHom p) hirr)
      ((𝒜.pullback g).projToSpec p.src) (𝒜.projToSpec p.tgt)
      (Spec.map (g.appLE p.tgt.toOpens p.src.toOpens p.le_preimage)) := by
  let _ : Algebra (𝒜.carrier p.tgt) ((𝒜.pullback g).carrier p.src) :=
    (𝒜.pullbackChartHom p).toRingHom.toAlgebra
  let _ : Algebra Γ(S, p.tgt.toOpens) ((𝒜.pullback g).carrier p.src) :=
    ((algebraMap Γ(S', p.src.toOpens) ((𝒜.pullback g).carrier p.src)).comp
      (algebraMap Γ(S, p.tgt.toOpens) p.Sections)).toAlgebra
  have : IsScalarTower Γ(S, p.tgt.toOpens) p.Sections ((𝒜.pullback g).carrier p.src) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, p.tgt.toOpens) (𝒜.carrier p.tgt)
      ((𝒜.pullback g).carrier p.src) := by
    refine .of_algebraMap_eq fun r ↦ (𝒜.chartIso p).commRingCatIsoToRingEquiv.injective ?_
    change (𝒜.chartIso p).hom
        (algebraMap Γ(S', p.src.toOpens) ((𝒜.pullback g).carrier p.src) _) =
      (𝒜.chartIso p).hom (𝒜.pullbackChartHom p _)
    rw [chartIso_hom_algebraMap, chartIso_hom_pullbackChartHom]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  have : Algebra.IsPushout Γ(S, p.tgt.toOpens) p.Sections (𝒜.carrier p.tgt)
      ((𝒜.pullback g).carrier p.src) :=
    CommRingCat.isPushout_iff_isPushout.mp (𝒜.isPushout_pullbackChartHom p)
  exact ⟨_, Proj.isPullback_map_of_isPushout (𝒜.pullbackChartHom p) fun _ ↦ rfl⟩

/-- The map `𝒜(V) → (g^*𝒜)(V')` satisfies the hypothesis of `Proj.map`. -/
theorem irrelevant_le_map_pullbackChartHom (p : AffinePair g) :
    HomogeneousIdeal.irrelevant ((𝒜.pullback g).grading p.src) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading p.tgt)).map (𝒜.pullbackChartHom p) :=
  (𝒜.exists_isPullback_pullbackChartHom p).1

/-- **Base change on a chart**: over an affine pair `(V', V)`, the square

    Proj (g^*𝒜)(V') ⟶ Proj 𝒜(V)
         ↓                ↓
    Spec Γ(S', V')  ⟶ Spec Γ(S, V)

is cartesian. -/
theorem isPullback_map_pullbackChartHom (p : AffinePair g) :
    IsPullback (Proj.map (𝒜.pullbackChartHom p) (𝒜.irrelevant_le_map_pullbackChartHom p))
      ((𝒜.pullback g).projToSpec p.src) (𝒜.projToSpec p.tgt)
      (Spec.map (g.appLE p.tgt.toOpens p.src.toOpens p.le_preimage)) :=
  (𝒜.exists_isPullback_pullbackChartHom p).2

/-! ### Regluing over the affine pairs -/

variable (g) in
/-- The charts `Proj (g^*𝒜)(V')` over the sources of the affine pairs, as a relative gluing
datum over the cover of `S'` by those sources. -/
noncomputable def pullbackGluingData : (AffinePair.cover g).RelativeGluingData where
  functor := AffinePair.srcFunctor g ⋙ (𝒜.pullback g).projFunctor
  natTrans := Functor.whiskerLeft (AffinePair.srcFunctor g)
    ((𝒜.pullback g).projNatTrans ≫ (restrictIsoSpec S').inv)
  equifibered _ _ f :=
    (𝒜.pullback g).relativeGluingData.equifibered ((AffinePair.srcFunctor g).map f)

instance : ((𝒜.pullbackGluingData g).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The comparison of the regluing with `Proj_{S'}(g^*𝒜)`. -/
noncomputable def pullbackGluedToRelativeProj :
    (𝒜.pullbackGluingData g).glued ⟶ (𝒜.pullback g).relativeProj :=
  colimit.desc (𝒜.pullbackGluingData g).functor
    ((colimit.cocone (𝒜.pullback g).relativeGluingData.functor).whisker
      (AffinePair.srcFunctor g))

/-- The chart `Proj (g^*𝒜)(V')` of the regluing over an affine pair. -/
noncomputable def pullbackGluedι (p : AffinePair g) :
    Proj ((𝒜.pullback g).grading p.src) ⟶ (𝒜.pullbackGluingData g).glued :=
  colimit.ι (𝒜.pullbackGluingData g).functor p

theorem isPullback_pullbackGluedι (p : AffinePair g) :
    IsPullback ((𝒜.pullback g).projToSpec p.src ≫ p.src.2.isoSpec.inv) (𝒜.pullbackGluedι p)
      p.src.toOpens.ι (𝒜.pullbackGluingData g).toBase :=
  (𝒜.pullbackGluingData g).isPullback_natTrans_ι_toBase p

@[reassoc (attr := simp)]
theorem pullbackGluedι_pullbackGluedToRelativeProj (p : AffinePair g) :
    𝒜.pullbackGluedι p ≫ 𝒜.pullbackGluedToRelativeProj = (𝒜.pullback g).relativeProjι p.src :=
  colimit.ι_desc _ _

theorem pullbackGluedToRelativeProj_toBase :
    𝒜.pullbackGluedToRelativeProj ≫ (𝒜.pullback g).relativeProjToBase =
      (𝒜.pullbackGluingData g).toBase := by
  refine colimit.hom_ext fun p ↦ ?_
  change 𝒜.pullbackGluedι p ≫ _ = 𝒜.pullbackGluedι p ≫ _
  rw [pullbackGluedι_pullbackGluedToRelativeProj_assoc, relativeProjι_toBase,
    ← (𝒜.isPullback_pullbackGluedι p).w, Category.assoc, IsAffineOpen.isoSpec_inv_ι]

/-- The charts `Proj (g^*𝒜)(V')` over the sources of the affine pairs cover
`Proj_{S'}(g^*𝒜)`. -/
noncomputable def pullbackChartCover : (𝒜.pullback g).relativeProj.OpenCover where
  I₀ := AffinePair g
  X p := Proj ((𝒜.pullback g).grading p.src)
  f p := (𝒜.pullback g).relativeProjι p.src
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨p, hp⟩ := AffinePair.exists_mem (g := g) ((𝒜.pullback g).relativeProjToBase x)
    have hx : x ∈ ((𝒜.pullback g).relativeProjι p.src).opensRange := by
      rw [opensRange_relativeProjι]
      exact hp
    obtain ⟨y, rfl⟩ := hx
    exact ⟨p, y, rfl⟩

instance : IsIso (𝒜.pullbackGluedToRelativeProj (g := g)) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := .isomorphisms _) 𝒜.pullbackChartCover
    fun (p : AffinePair g) ↦ ?_
  have h : IsPullback (𝒜.pullbackGluedι p) (𝟙 _)
      𝒜.pullbackGluedToRelativeProj ((𝒜.pullback g).relativeProjι p.src) := by
    refine (IsPullback.of_right ?_
      (by rw [Category.id_comp, pullbackGluedι_pullbackGluedToRelativeProj])
      ((𝒜.pullback g).isPullback_relativeProjι p.src)).flip
    rw [Category.id_comp, pullbackGluedToRelativeProj_toBase]
    exact 𝒜.isPullback_pullbackGluedι p
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk h.isoPullback (Iso.refl _) ?_)).mp
    (MorphismProperty.isomorphisms.infer_property (𝟙 (Proj ((𝒜.pullback g).grading p.src))))
  simp only [Cover.pullbackHom, Iso.refl_hom, Category.comp_id]
  exact h.isoPullback_hom_snd

/-- The morphism from the regluing to `Proj_S(𝒜)`. -/
noncomputable def pullbackGluedToBaseProj :
    (𝒜.pullbackGluingData g).glued ⟶ 𝒜.relativeProj :=
  colimit.desc (𝒜.pullbackGluingData g).functor
    { pt := 𝒜.relativeProj
      ι :=
        { app p := Proj.map (𝒜.pullbackChartHom p) (𝒜.irrelevant_le_map_pullbackChartHom p) ≫
            𝒜.relativeProjι p.tgt
          naturality {q p} f := by
            have h := leOfHom f
            change Proj.map _ _ ≫ Proj.map _ _ ≫ _ = (Proj.map _ _ ≫ _) ≫ 𝟙 _
            rw [Category.comp_id, ← map_restrict_relativeProjι 𝒜 (AffinePair.tgt_le h),
              ← Category.assoc, ← Category.assoc, ← Proj.map_comp, ← Proj.map_comp]
            congr 2
            exact GradedRingHom.ext fun a ↦ 𝒜.pullbackChartHom_restrict h a } }

variable (g) in
/-- **The base change morphism** `Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)`: on the chart over the source of
an affine pair `(V', V)` it is `Proj` of `𝒜(V) → (g^*𝒜)(V')`. -/
noncomputable def relativeProjPullbackMap : (𝒜.pullback g).relativeProj ⟶ 𝒜.relativeProj :=
  inv 𝒜.pullbackGluedToRelativeProj ≫ 𝒜.pullbackGluedToBaseProj

@[reassoc]
theorem relativeProjι_relativeProjPullbackMap (p : AffinePair g) :
    (𝒜.pullback g).relativeProjι p.src ≫ 𝒜.relativeProjPullbackMap g =
      Proj.map (𝒜.pullbackChartHom p) (𝒜.irrelevant_le_map_pullbackChartHom p) ≫
        𝒜.relativeProjι p.tgt := by
  rw [relativeProjPullbackMap, ← pullbackGluedι_pullbackGluedToRelativeProj, Category.assoc,
    IsIso.hom_inv_id_assoc]
  exact colimit.ι_desc _ _

/-- **Relative `Proj` commutes with base change** (Stacks 01O3): for `g : S' ⟶ S`, the
square

    Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)
          ↓              ↓
          S'      ⟶      S

is cartesian. -/
theorem relativeProj_isPullback :
    IsPullback (𝒜.relativeProjPullbackMap g) (𝒜.pullback g).relativeProjToBase
      𝒜.relativeProjToBase g := by
  refine (Scheme.isPullback_of_openCover (𝒜.pullback g).relativeProjToBase
    (𝒜.relativeProjPullbackMap g) g 𝒜.relativeProjToBase (AffinePair.cover g) fun p ↦ ?_).flip
  have hQ := ((𝒜.pullback g).isPullback_relativeProjι p.src).flip
  have hres : Spec.map (g.appLE p.tgt.toOpens p.src.toOpens p.le_preimage) ≫
      p.tgt.2.isoSpec.inv = p.src.2.isoSpec.inv ≫ g.resLE p.tgt.toOpens p.src.toOpens
        p.le_preimage := by
    rw [← cancel_mono p.tgt.toOpens.ι, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec]
  have hU : IsPullback ((𝒜.pullback g).projToSpec p.src ≫ p.src.2.isoSpec.inv)
      (Proj.map (𝒜.pullbackChartHom p) (𝒜.irrelevant_le_map_pullbackChartHom p))
      (g.resLE p.tgt.toOpens p.src.toOpens p.le_preimage)
      (𝒜.projToSpec p.tgt ≫ p.tgt.2.isoSpec.inv) :=
    (𝒜.isPullback_map_pullbackChartHom p).flip.of_iso (Iso.refl _) p.src.2.isoSpec.symm
      (Iso.refl _) p.tgt.2.isoSpec.symm (by simp) (by simp) hres (by simp)
  have hK := hU.paste_vert (𝒜.isPullback_relativeProjι p.tgt)
  rw [Scheme.Hom.resLE_comp_ι, ← relativeProjι_relativeProjPullbackMap] at hK
  refine hK.of_iso hQ.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp)
    (by simp)
  · simp only [Iso.refl_hom, Category.comp_id, Cover.pullbackHom]
    exact hQ.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = hQ.isoPullback.hom ≫ pullback.fst _ _ ≫ _
    rw [IsPullback.isoPullback_hom_fst_assoc]

end AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData
