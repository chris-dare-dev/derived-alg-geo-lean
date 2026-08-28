/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ChartExtension

/-!
# Agreement on the chart of a homogeneous element of any positive degree

`ChartExtension.lean` supplies the chart, its restriction `awayRestrict`, and the *extension* half
of `Modules/Affine/Extension.lean` read on it. This file supplies the *separatedness* half.

## Why it is a separate file rather than a separate degree

It used to be both. `ChartExtension.lean` was degree-one only and this file repeated the same three
statements one degree up, because `#585`'s cover is made of degree-one charts while its pairwise
overlaps are not: `D₊(gᵢ) ⊓ D₊(gⱼ) = D₊(gᵢ gⱼ)` has degree two. The stated reason for the split --
"`#585` extends only across degree-one charts" -- was true of `#585` and false as a design
principle, and the two trios were the same theorem with one lemma swapped. `#822` collapsed that:
`ChartExtension.lean` is now general in the degree, and what remains here is only the half it does
not state.

## Scope

One chart, one basic open of it. No cover, no gluing.
-/
universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- **Two sections of a chart agreeing on a basic open agree after clearing a power.**

`exists_pow_smul_eq_of_res_eq_chart` one degree up, and the reason it is needed: `#585`'s pairwise
overlap `D₊(gᵢ) ⊓ D₊(gⱼ)` is the chart of `gᵢ gⱼ`, which has degree two. -/
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

/-- **One exponent for a finite family of agreements**, the shape `#585`'s glue calls: agreement
has to be forced on every pairwise overlap at once, so the family is indexed by pairs. -/
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
