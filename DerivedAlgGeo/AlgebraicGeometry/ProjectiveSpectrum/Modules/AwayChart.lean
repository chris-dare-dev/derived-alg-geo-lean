/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.ChartExtension

/-!
# Agreement on the chart of a homogeneous element of any positive degree

`ChartExtension.lean` supplies the chart, its restriction `awayRestrict`, and the *extension* half
of `Modules/Affine/Extension.lean` read on it. This file supplies the *separatedness* half: two
sections of the chart that agree on a basic open of it agree after multiplying by a power of the
chart's distinguished element.

## Main definitions

This file introduces no new definitions.

## Main results

* `AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_away`: two sections of the chart of `g`
  that agree on the basic open of `f / g` agree after multiplying by a power of `f / g`.
* `AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_away_of_le`: that exponent can be raised.
* `AlgebraicGeometry.Proj.exists_pow_smul_eq_of_res_eq_away_uniform`: one exponent for a finite
  family of agreements.

## Implementation notes

### A separate file per half, not per degree

Both halves are general in the degree of the chart, and both degrees are needed: the cover used by
the section-extension lemma `exists_globalSection_twistBy` is made of degree-one charts, while its
pairwise overlaps are not, since `D₊(gᵢ) ⊓ D₊(gⱼ) = D₊(gᵢ gⱼ)` has degree two. Extension and
agreement are the same theorem with one lemma swapped, so what is here is only the half
`ChartExtension.lean` does not state.

### Scope

One chart, one basic open of it. No cover, no gluing.

## References

`AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_of_res_eq_of_isQuasicoherent`, the affine
separatedness lemma this file reads on the chart.

## Tags

projective spectrum, affine chart, quasi-coherent sheaf, separatedness
-/
universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- **Two sections of a chart agreeing on a basic open agree after clearing a power.**

`Scheme.Modules.exists_pow_smul_eq_of_res_eq_of_isQuasicoherent` read on the chart of `g`. It is
needed beyond degree one because the pairwise overlap `D₊(gᵢ) ⊓ D₊(gⱼ)` of a degree-one cover is
the chart of `gᵢ gⱼ`, which has degree two. -/
theorem exists_pow_smul_eq_of_res_eq_away (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (t t' : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op ⊤))
    (h : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.map
        (homOfLE (le_top (a := PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf)))).op t =
      (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.map
        (homOfLE (le_top (a := PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf)))).op t') :
    ∃ n : ℕ, HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • t =
      HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • t' :=
  Scheme.Modules.exists_pow_smul_eq_of_res_eq_of_isQuasicoherent _ _ t t' h

/-- **That exponent can be raised**, exactly as in the degree-one case and for the same reason: a
single exponent across all pairs of a finite cover needs every pair raised to the maximum. -/
theorem exists_pow_smul_eq_of_res_eq_away_of_le (F : (Proj 𝒜).Modules)
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (t t' : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op ⊤))
    {n m : ℕ} (hnm : n ≤ m)
    (h : HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • t =
      HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • t') :
    HomogeneousLocalization.Away.isLocalizationElem hg hf ^ m • t =
      HomogeneousLocalization.Away.isLocalizationElem hg hf ^ m • t' := by
  have hm : m = (m - n) + n := by omega
  rw [hm, pow_add, mul_smul, mul_smul, h]

/-- **One exponent for a finite family of agreements**, the shape the gluing in
`exists_globalSection_twistBy` needs: agreement has to be forced on every pairwise overlap at once,
so the family is indexed by pairs. -/
theorem exists_pow_smul_eq_of_res_eq_away_uniform (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {ι : Type*} [Finite ι] {d e : ℕ} {f g : ι → A}
    (hf : ∀ i, f i ∈ 𝒜 e) (hg : ∀ i, g i ∈ 𝒜 d) (hd : 0 < d)
    (t t' : ∀ i, (modulesSpecToSheaf.obj (awayRestrict 𝒜 F (hg i) hd)).presheaf.obj (op ⊤))
    (h : ∀ i, (modulesSpecToSheaf.obj (awayRestrict 𝒜 F (hg i) hd)).presheaf.map
        (homOfLE (le_top (a := PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem (hg i) (hf i))))).op (t i) =
      (modulesSpecToSheaf.obj (awayRestrict 𝒜 F (hg i) hd)).presheaf.map
        (homOfLE (le_top (a := PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem (hg i) (hf i))))).op (t' i)) :
    ∃ n : ℕ, ∀ i,
      HomogeneousLocalization.Away.isLocalizationElem (hg i) (hf i) ^ n • t i =
        HomogeneousLocalization.Away.isLocalizationElem (hg i) (hf i) ^ n • t' i := by
  choose N hN using fun i =>
    exists_pow_smul_eq_of_res_eq_away 𝒜 F (hf i) (hg i) hd (t i) (t' i) (h i)
  obtain ⟨n, hn⟩ := (Set.finite_range N).bddAbove
  exact ⟨n, fun i => exists_pow_smul_eq_of_res_eq_away_of_le 𝒜 F (hf i) (hg i) hd (t i) (t' i)
    (hn ⟨i, rfl⟩) (hN i)⟩

end AlgebraicGeometry.Proj
