/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.LocalizedModule.NestedSubmodule

/-!
# The opposite chart of nested principal localization

The canonical map from `M[1/s]` to `M[1/(r*s)]` and the corresponding
submodule-span identity. The product is kept in the order `r*s`, so both chart
maps have literally the same target. No regularity or finiteness is required.
-/

namespace LocalizedModule

universe u v

private theorem isUnit_awayToAwayLeft
    {R : Type u} [CommRing R] (r s : R) (t : Submonoid.powers s) :
    IsUnit (algebraMap R (Localization.Away (r * s)) (t : R)) := by
  obtain ⟨n, hn⟩ := t.property
  rw [← hn, map_pow]
  exact (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (r * s))
    (x := r * s) (dvd_mul_left s r)).pow n

/-- The canonical `R`-linear map from localization away from `s` to
localization away from `r * s`. -/
noncomputable def awayToAwayLeftLinearMap
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) :
    LocalizedModule.Away s M →ₗ[R] LocalizedModule.Away (r * s) M :=
  IsLocalizedModule.lift (Submonoid.powers s)
    (LocalizedModule.mkLinearMap (Submonoid.powers s) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M)
    (by
      intro t
      have hEnd := (isUnit_awayToAwayLeft r s t).map
        (Algebra.lsmul R (A := Localization.Away (r * s))
          R (LocalizedModule.Away (r * s) M))
      simpa only [← (Algebra.lsmul R (A := Localization.Away (r * s))
        R (LocalizedModule.Away (r * s) M)).commutes] using hEnd)

@[simp]
theorem awayToAwayLeftLinearMap_mk
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (m : M) :
    awayToAwayLeftLinearMap (M := M) r s
        (LocalizedModule.mk m (1 : Submonoid.powers s)) =
      LocalizedModule.mk m (1 : Submonoid.powers (r * s)) := by
  simpa only [awayToAwayLeftLinearMap, LocalizedModule.mkLinearMap_apply] using
    (IsLocalizedModule.lift_apply (Submonoid.powers s)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M) _ m)

end LocalizedModule

namespace Submodule

universe u v

/-- If `P` is a submodule of `M[1/s]`, localization of its inverse image in
`M` away from `r*s` is the `R[1/(r*s)]`-span of its canonical image. This also
holds when either factor is a zero divisor or `r*s = 0`. -/
theorem localized'_comap_awayToAwayLeft_eq_span
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (P : Submodule (Localization.Away s) (LocalizedModule.Away s M)) :
    let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
    let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
    let α := LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
    ((P.restrictScalars R).comap fs).localized'
        (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
      Submodule.span (Localization.Away (r * s)) (α '' (P : Set (LocalizedModule.Away s M))) := by
  dsimp only
  let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
  let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
  let α := LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
  let N : Submodule R M := (P.restrictScalars R).comap fs
  let Q : Submodule (Localization.Away (r * s)) (LocalizedModule.Away (r * s) M) :=
    N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs
  have hrecover : N.localized' (Localization.Away s) (Submonoid.powers s) fs = P :=
    (Submodule.localized'gi (Localization.Away s) (Submonoid.powers s) fs).l_u_eq P
  change Q = Submodule.span (Localization.Away (r * s)) (α '' (P : Set _))
  apply le_antisymm
  · change N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs ≤ _
    rw [Submodule.localized'_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact Submodule.subset_span ⟨fs m, hm,
      LocalizedModule.awayToAwayLeftLinearMap_mk r s m⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    rw [← hrecover] at hp
    obtain ⟨m, hm, t, ht⟩ := hp
    have hmp : fs m = (t : R) • p := (IsLocalizedModule.mk'_eq_iff).mp ht
    have hfrs : frs m ∈ Q := ⟨m, hm, 1, by simp⟩
    have hscalar : (algebraMap R (Localization.Away (r * s)) (t : R)) • α p = frs m := by
      rw [algebraMap_smul, ← map_smul, ← hmp]
      exact LocalizedModule.awayToAwayLeftLinearMap_mk r s m
    apply (Q.smul_mem_iff_of_isUnit
      (LocalizedModule.isUnit_awayToAwayLeft r s t)).mp
    rw [hscalar]
    exact hfrs

/-- Localizing a chosen submodule `N ≤ M` away from `r*s` is the span of the
canonical image of its localization away from `s`. No finiteness or regularity
hypothesis is needed. -/
theorem localized'_away_mul_eq_span_awayToAwayLeft
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (N : Submodule R M) :
    let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
    let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
    let α := LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
    N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
      Submodule.span (Localization.Away (r * s))
        (α '' (N.localized' (Localization.Away s) (Submonoid.powers s) fs :
          Set (LocalizedModule.Away s M))) := by
  dsimp only
  let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
  let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
  let α := LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
  let P := N.localized' (Localization.Away s) (Submonoid.powers s) fs
  let Q := N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs
  change Q = Submodule.span (Localization.Away (r * s)) (α '' (P : Set _))
  apply le_antisymm
  · change N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs ≤ _
    rw [Submodule.localized'_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact Submodule.subset_span ⟨fs m, ⟨m, hm, 1, by simp⟩,
      LocalizedModule.awayToAwayLeftLinearMap_mk r s m⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨m, hm, t, ht⟩ := hp
    have hmp : fs m = (t : R) • p := (IsLocalizedModule.mk'_eq_iff).mp ht
    have hfrs : frs m ∈ Q := ⟨m, hm, 1, by simp⟩
    have hscalar : (algebraMap R (Localization.Away (r * s)) (t : R)) • α p = frs m := by
      rw [algebraMap_smul, ← map_smul, ← hmp]
      exact LocalizedModule.awayToAwayLeftLinearMap_mk r s m
    apply (Q.smul_mem_iff_of_isUnit
      (LocalizedModule.isUnit_awayToAwayLeft r s t)).mp
    rw [hscalar]
    exact hfrs

end Submodule
