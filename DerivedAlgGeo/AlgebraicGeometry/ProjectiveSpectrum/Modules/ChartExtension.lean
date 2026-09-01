/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Extension
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The chart of a positive-degree element, as seen by the affine extension lemma

`#585`'s chart step. A section of a quasi-coherent `F` over `D₊(g) ⊓ D₊(f)` extends to a section
over `D₊(g)` after clearing a power of `f / g`. `Modules/Affine/Extension.lean` supplies the
algebra; what is here is the geometry that lets it be applied, and the naming that lets it
elaborate.

## The geometry is two rewrites

`ChartScalar.lean`'s `awayι_image_top` and `awayι_image_basicOpen` say the chart covers exactly
`D₊(g)` and meets `D₊(f)` in `D₊(g) ⊓ D₊(f)`. They are stated there, one layer up, because that is
where the scalar comparison needs them; this file only needs the chart itself. Translating sections
across the chart is free, because `Scheme.Modules.restrictAppIso` is `Iso.refl`.

## The naming is not cosmetic

Stated inline, `IsIso (F.restrict (awayι 𝒜 g hg hd)).fromTildeΓ` **does not elaborate**: it
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

## The same three, for *agreement* rather than extension

`exists_pow_smul_eq_of_res_eq_chart`, `..._of_le` and `..._uniform` mirror the three above with
`exists_pow_smul_eq_of_res_eq_of_isQuasicoherent` in place of the extension lemma, and are needed
for a reason the obvious reading of `#585` misses.

Two charts' twisted sections are only visibly equal where `D₊(f)` reaches: there each restricts to
the same `twistBy fⁿ` of `s`. But `TopCat.Sheaf.IsCompatible` demands agreement on the whole
pairwise overlap `D₊(gᵢ) ⊓ D₊(gⱼ)`, which is **not** contained in `D₊(f)`. Closing that distance
costs a second exponent, and these raise and unify it exactly as the first three do.

The uniform version's index is deliberately arbitrary rather than the chart index: agreement has to
be forced on every *pair* at once, so a pair type is what gets passed.

## Scope

One chart, in the chart's own coordinates. Everything after the exponent is elsewhere:

* the sections produced here live on **different sheaves**, one per chart, so they cannot be
  compared here — `twistBy` carrying each into a single sheaf `F(N)` is the passage, and
  `Proj/Modules/Glue.lean` is where it is taken;
* their agreement on overlaps, which needs a second exponent from `Proj/Modules/AwayChart.lean`
  because the overlap is a degree-*two* chart;
* the gluing itself, to a section over `⊤` of `Proj 𝒜` rather than over one chart.

`ChartProj.lean` restates the six theorems here on `Proj 𝒜`, and `Glue.lean` assembles them into
`exists_globalSection_twistBy`, which is `#585`'s deliverable.

Note also that the cover is an input here, not a construction: `degreeOneCharts_coversTop`
(`Proj/Modules/Finiteness.lean`) supplies it from `Algebra.adjoin (𝒜 0) (range g) = ⊤`, and the
finiteness of the index is a separate hypothesis.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

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

/-- **The restriction of `F` to the chart of a homogeneous element of positive degree**, named at
its result type so that `fromTildeΓ`'s bundled ring is matched syntactically.

There is no separate degree-one spelling. `#585`'s cover is made of degree-one charts and its
pairwise overlaps are not -- `D₊(gᵢ) ⊓ D₊(gⱼ) = D₊(gᵢ gⱼ)` has degree two -- so both degrees were
needed from the start, and the two names for one definition were a `rfl` apart. -/
noncomputable def awayRestrict (F : (Proj 𝒜).Modules) {d : ℕ} {g : A} (hg : g ∈ 𝒜 d)
    (hd : 0 < d) : (Spec (.of ↑(chartRing 𝒜 g))).Modules :=
  F.restrict (awayι 𝒜 g hg hd)

instance awayRestrict_isQuasicoherent (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d) : (awayRestrict 𝒜 F hg hd).IsQuasicoherent :=
  inferInstanceAs ((F.restrict (awayι 𝒜 g hg hd)).IsQuasicoherent)

instance isIso_fromTildeΓ_awayRestrict (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d) : IsIso (awayRestrict 𝒜 F hg hd).fromTildeΓ :=
  Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _

/-- **The affine extension lemma, over the chart of a positive-degree element.**

`s` lives over `D₊(g) ⊓ D₊(f)`, which in the chart is the basic open of `f / g`; a power of that
element carries it to a section over the whole chart, i.e. over `D₊(g)`.

The degrees of `f` and `g` are unconstrained apart from `0 < deg g`, which is what the chart itself
needs. `#585` calls this at degree one; the pairwise overlaps of that cover are degree-two charts,
and the agreement statements in `AwayChart.lean` were general from the start for exactly that
reason. There is no mathematical asymmetry between the two, so there is none here either. -/
theorem exists_pow_smul_eq_res_chart (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (s : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf)))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • s :=
  Scheme.Modules.exists_pow_smul_eq_res_of_top_of_isQuasicoherent _ _ s

/-- **The exponent can be raised.**

If clearing `(f/g)ⁿ` extends `s` over the chart, so does clearing any higher power: multiply the
extension by `(f/g)^(m-n)`. The restriction map is linear over the chart ring, so nothing but
`pow_add` is involved.

This is what makes a *single* `n` across a finite cover possible — each chart supplies its own
exponent, and this raises them all to the maximum.

No quasi-coherence hypothesis: unlike `exists_pow_smul_eq_res_chart`, which needs it to produce an
extension at all, raising an exponent uses only that the restriction map is linear. -/
theorem exists_pow_smul_eq_res_chart_of_le (F : (Proj 𝒜).Modules)
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (s : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf))))
    {n m : ℕ} (hnm : n ≤ m)
    (h : ∃ t : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op ⊤),
      (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • s) :
    ∃ t : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op ⊤),
      (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ m • s := by
  obtain ⟨t, ht⟩ := h
  refine ⟨HomogeneousLocalization.Away.isLocalizationElem hg hf ^ (m - n) • t, ?_⟩
  rw [map_smul, ht, smul_smul, ← pow_add]
  congr 2
  omega

/-- **One exponent for a finite family of charts.**

Each chart supplies its own `nᵢ` from `exists_pow_smul_eq_res_chart`; finiteness of the index makes
the range of exponents bounded, and `exists_pow_smul_eq_res_chart_of_le` raises every chart to the
bound.

This is the first of the three things `#585`'s glue needs. The other two — that the resulting local
sections agree on overlaps once carried into `F(n)`, and that they therefore glue to a section over
`⊤` of `Proj 𝒜` — are not here. Note in particular that the sections produced below still live on
*different* sheaves, one per chart; `twistBy` is what makes them comparable, and it is not applied
yet. -/
theorem exists_pow_smul_eq_res_chart_uniform (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d e : ℕ} {f : A} (hf : f ∈ 𝒜 e) {ι : Type*} [Finite ι] {g : ι → A}
    (hg : ∀ i, g i ∈ 𝒜 d) (hd : 0 < d)
    (s : ∀ i, (modulesSpecToSheaf.obj (awayRestrict 𝒜 F (hg i) hd)).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem (hg i) hf)))) :
    ∃ n : ℕ, ∀ i,
      ∃ t : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F (hg i) hd)).presheaf.obj (op ⊤),
        (modulesSpecToSheaf.obj (awayRestrict 𝒜 F (hg i) hd)).presheaf.map
            (homOfLE le_top).op t =
          HomogeneousLocalization.Away.isLocalizationElem (hg i) hf ^ n • s i := by
  choose N t ht using fun i => exists_pow_smul_eq_res_chart 𝒜 F hf (hg i) hd (s i)
  obtain ⟨n, hn⟩ := (Set.finite_range N).bddAbove
  exact ⟨n, fun i =>
    exists_pow_smul_eq_res_chart_of_le 𝒜 F hf (hg i) hd (s i) (hn ⟨i, rfl⟩) ⟨t i, ht i⟩⟩

end AlgebraicGeometry.Proj
