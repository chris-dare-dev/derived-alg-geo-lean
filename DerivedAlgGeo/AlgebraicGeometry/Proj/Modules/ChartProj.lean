/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ChartScalar

/-!
# The chart lemmas, restated on `Proj 𝒜`

`ChartExtension.lean` and `AwayChart.lean` state extension and agreement in the chart's own
coordinates: sections of `modulesSpecToSheaf.obj (awayRestrict …)` over opens of
`Spec A_{(g)}`, scaled by the away ring's element `isLocalizationElem`. `#585`'s glue consumes them
on `Proj 𝒜`: sections of `F` over opens of `Proj 𝒜`, scaled by a structure-sheaf section. This file
is that restatement, and it is the last step before the cover.

## The transport is a substitution, not a transport

`Scheme.Modules.restrictAppIso` is `Iso.refl`, so `Γ(awayRestrict 𝒜 F hg hd, U)` **is**
`Γ(F, awayι 𝒜 g hg hd ''ᵁ U)` — nothing has to move. What is left is that the glue wants the
opens spelled `D₊(g)` and `D₊(g) ⊓ D₊(f)` rather than as chart images, and those are equal only
propositionally (`awayι_image_top`, `awayι_image_basicOpen`).

Rather than transporting sections along `eqToHom`, each statement here takes the opens as
*variables* together with an equation pinning them to the chart's images. `subst` then turns the
statement into the chart's own, and the caller instantiates the variables at whatever spelling it
wants. The restriction maps and the `≤` proofs come along for free: morphisms of `Opens` are
proof-carrying data in a poset, so proof irrelevance identifies `homOfLE hVW` with the chart's own
`homOfLE (image_mono le_top)`.

That is why the hypotheses are oriented `chart image = W` and not `W = chart image`: `subst`
eliminates the variable, and the variable has to be the one that disappears.

## Scope

Extension and agreement, on `Proj 𝒜`, for a finite family. The cover itself, the twist that puts
the family into one sheaf, and the gluing are not here.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- **Extension across the chart of a positive-degree element, on `Proj 𝒜`.**

A section over `D₊(g) ⊓ D₊(f)` extends to `D₊(g)` after multiplying by `(f / g)ⁿ`. -/
theorem exists_pow_smul_eq_res_image (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (hd : 0 < d)
    {W V : (Proj 𝒜).Opens}
    (hW : awayι 𝒜 g hg hd ''ᵁ ⊤ = W)
    (hV : awayι 𝒜 g hg hd ''ᵁ
      PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hg hf) = V)
    (hVW : V ≤ W) (hVg : V ≤ ProjectiveSpectrum.basicOpen 𝒜 g) (s : Γ(F, V)) :
    ∃ (n : ℕ) (t : Γ(F, W)),
      (F.presheaf.map (homOfLE hVW).op).hom t
        = (show Γ(Proj 𝒜, V) from isLocalizationFrac 𝒜 hf hg n hVg) • s := by
  subst hW
  subst hV
  obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res_chart 𝒜 F hf hg hd s
  exact ⟨n, t, ht.trans (isLocalizationElem_pow_smul_eq 𝒜 F hf hg hd n s)⟩

/-- **One exponent for a finite family of charts, on `Proj 𝒜`.** -/
theorem exists_pow_smul_eq_res_image_uniform (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d e : ℕ} {f : A} (hf : f ∈ 𝒜 e) {ι : Type*} [Finite ι] {g : ι → A}
    (hg : ∀ i, g i ∈ 𝒜 d) (hd : 0 < d)
    {W V : ι → (Proj 𝒜).Opens}
    (hW : (fun i => awayι 𝒜 (g i) (hg i) hd ''ᵁ ⊤) = W)
    (hV : (fun i => awayι 𝒜 (g i) (hg i) hd ''ᵁ
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem (hg i) hf)) = V)
    (hVW : ∀ i, V i ≤ W i) (hVg : ∀ i, V i ≤ ProjectiveSpectrum.basicOpen 𝒜 (g i))
    (s : ∀ i, Γ(F, V i)) :
    ∃ n : ℕ, ∀ i, ∃ t : Γ(F, W i),
      (F.presheaf.map (homOfLE (hVW i)).op).hom t
        = (show Γ(Proj 𝒜, V i) from isLocalizationFrac 𝒜 hf (hg i) n (hVg i)) • s i := by
  subst hW
  subst hV
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_res_chart_uniform 𝒜 F hf hg hd s
  refine ⟨n, fun i => ?_⟩
  obtain ⟨t, ht⟩ := hn i
  exact ⟨t, ht.trans (isLocalizationElem_pow_smul_eq 𝒜 F hf (hg i) hd n (s i))⟩

/-- **One exponent forcing a finite family of agreements, on `Proj 𝒜`.**

The charts here are of arbitrary positive degree because `#585` calls this on the *pairwise
overlaps* of a degree-one cover, and those are the charts of products `gᵢ gⱼ`. -/
theorem exists_pow_smul_eq_of_res_eq_image_uniform (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {ι : Type*} [Finite ι] {d e : ℕ} {f b : ι → A}
    (hf : ∀ p, f p ∈ 𝒜 e) (hb : ∀ p, b p ∈ 𝒜 d) (hd : 0 < d)
    {W V : ι → (Proj 𝒜).Opens}
    (hW : (fun p => awayι 𝒜 (b p) (hb p) hd ''ᵁ ⊤) = W)
    (hV : (fun p => awayι 𝒜 (b p) (hb p) hd ''ᵁ
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem (hb p) (hf p))) = V)
    (hVW : ∀ p, V p ≤ W p) (hWb : ∀ p, W p ≤ ProjectiveSpectrum.basicOpen 𝒜 (b p))
    (t t' : ∀ p, Γ(F, W p))
    (h : ∀ p, (F.presheaf.map (homOfLE (hVW p)).op).hom (t p)
      = (F.presheaf.map (homOfLE (hVW p)).op).hom (t' p)) :
    ∃ n : ℕ, ∀ p,
      (show Γ(Proj 𝒜, W p) from isLocalizationFrac 𝒜 (hf p) (hb p) n (hWb p)) • t p
        = (show Γ(Proj 𝒜, W p) from isLocalizationFrac 𝒜 (hf p) (hb p) n (hWb p)) • t' p := by
  subst hW
  subst hV
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_of_res_eq_away_uniform 𝒜 F hf hb hd t t' h
  exact ⟨n, fun p =>
    ((isLocalizationElem_pow_smul_eq 𝒜 F (hf p) (hb p) hd n (t p)).symm.trans (hn p)).trans
      (isLocalizationElem_pow_smul_eq 𝒜 F (hf p) (hb p) hd n (t' p))⟩

end AlgebraicGeometry.Proj
