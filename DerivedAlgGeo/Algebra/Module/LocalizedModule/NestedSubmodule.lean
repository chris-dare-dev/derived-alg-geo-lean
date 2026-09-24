/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Submodules under nested principal localizations

The canonical map from a module localized away from `r` to its localization away from
`r * s` is constructed using the universal property. No regularity or finiteness
assumption on `r`, `s`, or the module is needed.
-/

namespace LocalizedModule

universe u v

private theorem isUnit_awayToAwayRight
    {R : Type u} [CommRing R] (r s : R) (t : Submonoid.powers r) :
    IsUnit (algebraMap R (Localization.Away (r * s)) (t : R)) := by
  obtain ⟨n, hn⟩ := t.property
  rw [← hn, map_pow]
  exact (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (r * s))
    (x := r * s) (dvd_mul_right r s)).pow n

/-- The canonical `R`-linear map from localization away from `r` to localization
away from `r * s`. -/
noncomputable def awayToAwayRightLinearMap
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) :
    LocalizedModule.Away r M →ₗ[R] LocalizedModule.Away (r * s) M :=
  IsLocalizedModule.lift (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M)
    (by
      intro t
      have hEnd := (isUnit_awayToAwayRight r s t).map
        (Algebra.lsmul R (A := Localization.Away (r * s))
        R (LocalizedModule.Away (r * s) M))
      simpa only [← (Algebra.lsmul R (A := Localization.Away (r * s))
        R (LocalizedModule.Away (r * s) M)).commutes] using hEnd)

@[simp]
theorem awayToAwayRightLinearMap_mk
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (m : M) :
    awayToAwayRightLinearMap (M := M) r s
        (LocalizedModule.mk m (1 : Submonoid.powers r)) =
      LocalizedModule.mk m (1 : Submonoid.powers (r * s)) := by
  simpa only [awayToAwayRightLinearMap, LocalizedModule.mkLinearMap_apply] using
    (IsLocalizedModule.lift_apply (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M) _ m)

end LocalizedModule

namespace Submodule

universe u v

/-- Let `P` be a submodule of `M[1/r]`, and pull it back to `M`. Its localization
away from `r * s` is the `R[1/(r*s)]`-span of the image of `P` under the canonical
map `M[1/r] → M[1/(r*s)]`. This works even when `r` or `s` is a zero divisor. -/
theorem localized'_comap_awayToAwayRight_eq_span
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (P : Submodule (Localization.Away r) (LocalizedModule.Away r M)) :
    let fr := LocalizedModule.mkLinearMap (Submonoid.powers r) M
    let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
    let α := LocalizedModule.awayToAwayRightLinearMap (M := M) r s
    ((P.restrictScalars R).comap fr).localized'
        (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
      Submodule.span (Localization.Away (r * s)) (α '' (P : Set (LocalizedModule.Away r M))) := by
  dsimp only
  let fr := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
  let α := LocalizedModule.awayToAwayRightLinearMap (M := M) r s
  let N : Submodule R M := (P.restrictScalars R).comap fr
  let Q : Submodule (Localization.Away (r * s)) (LocalizedModule.Away (r * s) M) :=
    N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs
  have hrecover : N.localized' (Localization.Away r) (Submonoid.powers r) fr = P :=
    (Submodule.localized'gi (Localization.Away r) (Submonoid.powers r) fr).l_u_eq P
  change Q = Submodule.span (Localization.Away (r * s)) (α '' (P : Set _))
  apply le_antisymm
  · change N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs ≤ _
    rw [Submodule.localized'_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact Submodule.subset_span ⟨fr m, hm,
      LocalizedModule.awayToAwayRightLinearMap_mk r s m⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    rw [← hrecover] at hp
    obtain ⟨m, hm, t, ht⟩ := hp
    have hmp : fr m = (t : R) • p := (IsLocalizedModule.mk'_eq_iff).mp ht
    have hfrs : frs m ∈ Q := ⟨m, hm, 1, by simp⟩
    have hscalar : (algebraMap R (Localization.Away (r * s)) (t : R)) • α p = frs m := by
      rw [algebraMap_smul, ← map_smul, ← hmp]
      exact LocalizedModule.awayToAwayRightLinearMap_mk r s m
    apply (Q.smul_mem_iff_of_isUnit
      (LocalizedModule.isUnit_awayToAwayRight r s t)).mp
    rw [hscalar]
    exact hfrs

end Submodule
