/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Extension
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The degree-one chart, as seen by the affine extension lemma

`#585`'s chart step. A section of a quasi-coherent `F` over `D₊(g) ⊓ D₊(f)` extends to a section
over `D₊(g)` after clearing a power of `f / g`. `Modules/Affine/Extension.lean` supplies the
algebra; what is here is the geometry that lets it be applied, and the naming that lets it
elaborate.

## The geometry is two rewrites

`degreeOneChart_image_top` and `degreeOneChart_image_basicOpen` say the chart covers exactly
`D₊(g)` and meets `D₊(f)` in `D₊(g) ⊓ D₊(f)`. Both fall out of
`Scheme.Hom.image_preimage_eq_opensRange_inf` and `opensRange_awayι`, with
`Proj.awayι_preimage_basicOpen` naming the element: for `f` and `g` both of degree one it is
exactly `f / g`. Translating sections across the chart is free, because
`Scheme.Modules.restrictAppIso` is `Iso.refl`.

## The naming is not cosmetic

Stated inline, `IsIso (F.restrict (degreeOneChart 𝒜 hg)).fromTildeΓ` **does not elaborate**: it
runs `isDefEq` past 1.6M heartbeats and gives up, and pinning the arguments explicitly
(`references/instance-transparency.md` technique 7) does not rescue it. This is the
`Scheme.Modules` wrapper that `Modules/Affine/Equivalence.lean` documents.

Technique 5 fixes it, in two steps, and the second is the one that is easy to miss:

* `chartRestrict` names the restriction at an explicit result type, so the wrapper is crossed once
  here rather than at every use site;
* that alone is not enough — but it converts the timeout into a *fast, precise* mismatch, which is
  itself the argument for the technique. `fromTildeΓ` quantifies over `(Spec (.of ↑R)).Modules`
  with `R : CommRingCat`, and Lean cannot invert the coercion to solve `↑?R ≡ Away 𝒜 g`. So the
  result type is written through `chartRing`, a reducible `abbrev` for the bundled ring, and `?R`
  is then matched syntactically.

With that, the instance and the theorem each elaborate in seconds.

## Choosing one exponent

`exists_pow_smul_eq_res_chart_of_le` raises the exponent — the extension times `(f/g)^(m-n)` works
for any `m ≥ n`, because the restriction map is linear over the chart ring. With that,
`exists_pow_smul_eq_res_chart_uniform` gives a **single** `n` for a finite family of charts: each
supplies its own, finiteness bounds the range, and raising does the rest.

## Scope

`#585` is still not closed. What remains is everything after the exponent:

* the sections produced here live on **different sheaves**, one per chart, so they cannot be
  compared yet — `twistBy` carrying each into the single sheaf `F(n)` is the missing passage;
* their agreement on overlaps, which is what `exists_pow_smul_res_eq_zero` is for;
* the gluing itself, to a section over `⊤` of `Proj 𝒜` rather than over one chart.

Note also that the cover is an input here, not a construction: `degreeOneCharts_coversTop`
(`Proj/Modules/Finiteness.lean`) supplies it from `Algebra.adjoin (𝒜 0) (range g) = ⊤`, and the
finiteness of the index is a separate hypothesis.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- The degree-one chart through `g`. -/
noncomputable abbrev degreeOneChart {g : A} (hg : g ∈ 𝒜 1) :
    Spec (.of <| HomogeneousLocalization.Away 𝒜 g) ⟶ Proj 𝒜 :=
  awayι 𝒜 g hg Nat.one_pos

/-- **The chart covers exactly its own basic open.** -/
theorem degreeOneChart_image_top {g : A} (hg : g ∈ 𝒜 1) :
    degreeOneChart 𝒜 hg ''ᵁ ⊤ = basicOpen 𝒜 g := by
  rw [show (⊤ : (Spec (.of <| HomogeneousLocalization.Away 𝒜 g)).Opens) =
      degreeOneChart 𝒜 hg ⁻¹ᵁ ⊤ from rfl,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_top_eq,
    opensRange_awayι 𝒜 g hg Nat.one_pos]

/-- **A second chart meets the first in the intersection of their basic opens** — the open the
affine extension lemma is applied over. -/
theorem degreeOneChart_image_basicOpen {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    degreeOneChart 𝒜 hg ''ᵁ
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hg hf) =
      basicOpen 𝒜 g ⊓ basicOpen 𝒜 f := by
  rw [← awayι_preimage_basicOpen 𝒜 hg Nat.one_pos hf Nat.one_pos,
    Scheme.Hom.image_preimage_eq_opensRange_inf, opensRange_awayι 𝒜 g hg Nat.one_pos]

/-! ### Naming the restriction

`references/instance-transparency.md` technique 5: naming the value with an explicit result type
stops the `Scheme.Modules` wrapper being crossed at every use site. Stating the restriction inline
makes instance search solve for the chart ring *and* peel the wrapper at once, which does not
terminate. -/

/-- The chart's degree-zero away ring, bundled.

Reducible, and written through rather than inlined, so that `fromTildeΓ`'s `R : CommRingCat` is
matched syntactically rather than by inverting a coercion. It takes `g` and not a proof about it:
the ring does not depend on the degree. -/
noncomputable abbrev chartRing (g : A) : CommRingCat.{u} :=
  .of (HomogeneousLocalization.Away 𝒜 g)

/-- **The restriction of `F` to the degree-one chart through `g`, named at its result type.** -/
noncomputable def chartRestrict (F : (Proj 𝒜).Modules) {g : A} (hg : g ∈ 𝒜 1) :
    (Spec (.of ↑(chartRing 𝒜 g))).Modules :=
  F.restrict (degreeOneChart 𝒜 hg)

instance chartRestrict_isQuasicoherent (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {g : A} (hg : g ∈ 𝒜 1) : (chartRestrict 𝒜 F hg).IsQuasicoherent :=
  inferInstanceAs ((F.restrict (degreeOneChart 𝒜 hg)).IsQuasicoherent)

instance isIso_fromTildeΓ_chartRestrict (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {g : A} (hg : g ∈ 𝒜 1) : IsIso (chartRestrict 𝒜 F hg).fromTildeΓ :=
  Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _

/-- **The affine extension lemma, over a degree-one chart.**

`s` lives over `D₊(g) ⊓ D₊(f)`, which in the chart is the basic open of `f / g`; a power of that
element carries it to a section over the whole chart, i.e. over `D₊(g)`. -/
theorem exists_pow_smul_eq_res_chart (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (s : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf)))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • s :=
  Scheme.Modules.exists_pow_smul_eq_res_of_top_of_isQuasicoherent _ _ s

/-- **The exponent can be raised.**

If clearing `(f/g)ⁿ` extends `s` over the chart, so does clearing any higher
power: multiply the extension by `(f/g)^(m-n)`. The restriction map is linear
over the chart ring, so nothing but `pow_add` is involved.

This is what makes a *single* `n` across a finite cover possible — each chart
supplies its own exponent, and this raises them all to the maximum.

No quasi-coherence hypothesis: unlike `exists_pow_smul_eq_res_chart`, which
needs it to produce an extension at all, raising an exponent uses only that the
restriction map is linear. -/
theorem exists_pow_smul_eq_res_chart_of_le (F : (Proj 𝒜).Modules)
    {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (s : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf))))
    {n m : ℕ} (hnm : n ≤ m)
    (h : ∃ t : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj (op ⊤),
      (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • s) :
    ∃ t : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj (op ⊤),
      (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ m • s := by
  obtain ⟨t, ht⟩ := h
  refine ⟨HomogeneousLocalization.Away.isLocalizationElem hg hf ^ (m - n) • t, ?_⟩
  rw [map_smul, ht, smul_smul, ← pow_add]
  congr 2
  omega

/-- **One exponent for a finite family of charts.**

Each chart supplies its own `nᵢ` from `exists_pow_smul_eq_res_chart`; finiteness
of the index makes the range of exponents bounded, and
`exists_pow_smul_eq_res_chart_of_le` raises every chart to the bound.

This is the first of the three things `#585`'s glue needs. The other two — that
the resulting local sections agree on overlaps once carried into `F(n)`, and
that they therefore glue to a section over `⊤` of `Proj 𝒜` — are not here. Note
in particular that the sections produced below still live on *different* sheaves,
one per chart; `twistBy` is what makes them comparable, and it is not applied
yet. -/
theorem exists_pow_smul_eq_res_chart_uniform (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {f : A} (hf : f ∈ 𝒜 1) {ι : Type*} [Finite ι] {g : ι → A} (hg : ∀ i, g i ∈ 𝒜 1)
    (s : ∀ i, (modulesSpecToSheaf.obj (chartRestrict 𝒜 F (hg i))).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem (hg i) hf)))) :
    ∃ n : ℕ, ∀ i,
      ∃ t : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F (hg i))).presheaf.obj (op ⊤),
        (modulesSpecToSheaf.obj (chartRestrict 𝒜 F (hg i))).presheaf.map
            (homOfLE le_top).op t =
          HomogeneousLocalization.Away.isLocalizationElem (hg i) hf ^ n • s i := by
  choose N t ht using fun i => exists_pow_smul_eq_res_chart 𝒜 F hf (hg i) (s i)
  obtain ⟨n, hn⟩ := (Set.finite_range N).bddAbove
  exact ⟨n, fun i =>
    exists_pow_smul_eq_res_chart_of_le 𝒜 F hf (hg i) (s i) (hn ⟨i, rfl⟩) ⟨t i, ht i⟩⟩

end AlgebraicGeometry.Proj
