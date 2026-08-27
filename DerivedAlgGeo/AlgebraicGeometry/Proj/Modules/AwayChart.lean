/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ChartExtension

/-!
# The chart of a homogeneous element of any positive degree

`ChartExtension.lean` works with degree-one charts, which is what `#585`'s cover is made of. Its
*pairwise overlaps* are not: `D₊(gᵢ) ⊓ D₊(gⱼ) = D₊(gᵢ gⱼ)` and `gᵢ gⱼ` has degree two. Forcing two
chart extensions to agree on an overlap is an affine statement over that chart, so the same
restriction has to exist one degree up.

## What is here

`awayRestrict` is `chartRestrict` for `g ∈ 𝒜 d` with `0 < d`, with the same two instances and the
same naming discipline -- `references/instance-transparency.md` technique 5, for the same reason:
stated inline, `IsIso (F.restrict (awayι 𝒜 g hg hd)).fromTildeΓ` does not elaborate.

`exists_pow_smul_eq_of_res_eq_away` is the separatedness half of `Modules/Affine/Extension.lean`
read on such a chart. The extension half is not repeated: `#585` extends only across degree-one
charts, and `ChartExtension.lean` already has it there.

## Relation to `chartRestrict`

`chartRestrict 𝒜 F hg` is `awayRestrict 𝒜 F hg Nat.one_pos` by definition, so a statement about one
can be discharged by the other with `exact`. The degree-one name is kept because the extension
lemmas that consume it are stated with it.

## Scope

One chart, one basic open of it. No cover, no gluing.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- **The restriction of `F` to the chart of a homogeneous element of positive degree**, named at
its result type so that `fromTildeΓ`'s bundled ring is matched syntactically. -/
noncomputable def awayRestrict (F : (Proj 𝒜).Modules) {d : ℕ} {g : A} (hg : g ∈ 𝒜 d)
    (hd : 0 < d) : (Spec (.of ↑(chartRing 𝒜 g))).Modules :=
  F.restrict (awayι 𝒜 g hg hd)

/-- The degree-one chart is the case `d = 1`. -/
theorem chartRestrict_eq_awayRestrict (F : (Proj 𝒜).Modules) {g : A} (hg : g ∈ 𝒜 1) :
    chartRestrict 𝒜 F hg = awayRestrict 𝒜 F hg Nat.one_pos :=
  rfl

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
