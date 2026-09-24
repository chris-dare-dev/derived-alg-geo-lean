/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Patching submodules across two principal localizations

For a finite module over a Noetherian ring, submodules of its localizations away from `r` and
`s` that agree in the common localization away from `r * s` come from one finitely generated
submodule. The witness is the intersection of their inverse images in the original module.

The overlap hypothesis compares the localizations at `r * s` of those two inverse images. This
is a purely algebraic two-chart statement. It constructs no sheaf or coherent subobject on a
union of basic opens, and proves no quasi-compact-open descent theorem.
-/

namespace Submodule

universe u v w x

private theorem localized'_eq_of_smul_mem
    {R : Type u} [CommSemiring R] {R' : Type v} [CommSemiring R']
    [Algebra R R'] {M : Type w} [AddCommMonoid M] [Module R M]
    {M' : Type x} [AddCommMonoid M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (S : Submonoid R) [IsLocalization S R']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (P : Submodule R' M') (N : Submodule R M)
    (hN : N ≤ (P.restrictScalars R).comap f)
    (hden : ∀ m : M, f m ∈ P → ∃ t : S, t • m ∈ N) :
    N.localized' R' S f = P := by
  apply le_antisymm
  · exact ((Submodule.localized'gi R' S f).gc N P).2 hN
  · intro y hy
    obtain ⟨⟨m, t⟩, hmt⟩ := IsLocalizedModule.mk'_surjective S f y
    change IsLocalizedModule.mk' f m t = y at hmt
    have hmP : f m ∈ P := by
      rw [← IsLocalizedModule.mk'_cancel' f m t]
      rw [hmt]
      exact P.smul_of_tower_mem (t : R) hy
    obtain ⟨q, hq⟩ := hden m hmP
    change ∃ n ∈ N, ∃ s : S, IsLocalizedModule.mk' f n s = y
    exact ⟨q • m, hq, q * t, (IsLocalizedModule.mk'_cancel_left f m q t).trans hmt⟩

private theorem exists_smul_mem_of_mem_localized'
    {R : Type u} [CommRing R] {R' : Type v} [CommRing R']
    [Algebra R R'] {M : Type w} [AddCommGroup M] [Module R M]
    {M' : Type x} [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (S : Submonoid R) [IsLocalization S R']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (N : Submodule R M) (m : M)
    (hm : f m ∈ N.localized' R' S f) :
    ∃ t : S, t • m ∈ N := by
  obtain ⟨n, hn, t, ht⟩ := hm
  have heq' : f n = t • f m := IsLocalizedModule.mk'_eq_iff.mp ht
  have heq : f n = f (t • m) := by
    simpa only [Submonoid.smul_def, map_smul] using heq'
  obtain ⟨q, hq⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) heq
  refine ⟨q * t, ?_⟩
  rw [mul_smul, ← hq]
  exact N.smul_mem q hn

private theorem exists_fg_two_away_localized_submodule_of_cross_denominators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r s : R)
    (Pr : Submodule (Localization.Away r) (LocalizedModule.Away r M))
    (Ps : Submodule (Localization.Away s) (LocalizedModule.Away s M))
    (hrs : ∀ m : M,
      LocalizedModule.mkLinearMap (Submonoid.powers r) M m ∈ Pr →
        ∃ n : ℕ, LocalizedModule.mkLinearMap (Submonoid.powers s) M (r ^ n • m) ∈ Ps)
    (hsr : ∀ m : M,
      LocalizedModule.mkLinearMap (Submonoid.powers s) M m ∈ Ps →
        ∃ n : ℕ, LocalizedModule.mkLinearMap (Submonoid.powers r) M (s ^ n • m) ∈ Pr) :
    ∃ N : Submodule R M, N.FG ∧
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M) = Pr ∧
      N.localized' (Localization.Away s) (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) M) = Ps := by
  let fr := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
  let N : Submodule R M := (Pr.restrictScalars R).comap fr ⊓ (Ps.restrictScalars R).comap fs
  refine ⟨N, Submodule.FG.of_le Module.Finite.fg_top le_top, ?_, ?_⟩
  · apply localized'_eq_of_smul_mem (Submonoid.powers r) fr Pr N
    · intro m hm
      exact hm.1
    · intro m hm
      obtain ⟨n, hn⟩ := hrs m hm
      let t : Submonoid.powers r := ⟨r ^ n, ⟨n, rfl⟩⟩
      refine ⟨t, ?_⟩
      constructor
      · change fr (r ^ n • m) ∈ Pr
        rw [map_smul]
        exact Pr.smul_of_tower_mem (r ^ n) hm
      · exact hn
  · apply localized'_eq_of_smul_mem (Submonoid.powers s) fs Ps N
    · intro m hm
      exact hm.2
    · intro m hm
      obtain ⟨n, hn⟩ := hsr m hm
      let t : Submonoid.powers s := ⟨s ^ n, ⟨n, rfl⟩⟩
      refine ⟨t, ?_⟩
      constructor
      · exact hn
      · change fs (s ^ n • m) ∈ Ps
        rw [map_smul]
        exact Ps.smul_of_tower_mem (s ^ n) hm

/-- Two compatible submodules on the principal localizations of a finite module have a single
finitely generated lift. Compatibility is equality in the canonical common localization away
from `r * s`, after pulling both submodules back to `M`. The witness is the intersection of
these two inverse images. No geometric sheaf-gluing statement is asserted. -/
theorem exists_fg_two_away_localized_submodule_of_overlap
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r s : R)
    (Pr : Submodule (Localization.Away r) (LocalizedModule.Away r M))
    (Ps : Submodule (Localization.Away s) (LocalizedModule.Away s M))
    (hOverlap :
      let fr := LocalizedModule.mkLinearMap (Submonoid.powers r) M
      let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
      let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
      ((Pr.restrictScalars R).comap fr).localized'
          (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
        ((Ps.restrictScalars R).comap fs).localized'
          (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs) :
    ∃ N : Submodule R M, N.FG ∧
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M) = Pr ∧
      N.localized' (Localization.Away s) (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) M) = Ps := by
  let fr := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
  let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
  have hrs : ∀ m : M, fr m ∈ Pr → ∃ n : ℕ, fs (r ^ n • m) ∈ Ps := by
    intro m hm
    have hloc : frs m ∈ ((Pr.restrictScalars R).comap fr).localized'
        (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs := by
      exact ⟨m, hm, 1, by simp⟩
    rw [hOverlap] at hloc
    obtain ⟨t, ht⟩ := exists_smul_mem_of_mem_localized'
      (Submonoid.powers (r * s)) frs ((Ps.restrictScalars R).comap fs) m hloc
    obtain ⟨n, hn⟩ := t.property
    refine ⟨n, ?_⟩
    have hmem : fs ((r * s) ^ n • m) ∈ Ps := by
      change fs ((t : R) • m) ∈ Ps at ht
      simpa only [hn] using ht
    have hunit : IsUnit (algebraMap R (Localization.Away s) (s ^ n)) := by
      simpa only [map_pow] using
        ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s).pow n)
    apply (Ps.smul_mem_iff_of_isUnit hunit).mp
    have heq : (algebraMap R (Localization.Away s) (s ^ n)) • fs (r ^ n • m) =
        fs ((r * s) ^ n • m) := by
      rw [algebraMap_smul, ← map_smul, smul_smul, mul_comm (s ^ n) (r ^ n), ← mul_pow]
    rw [heq]
    exact hmem
  have hsr : ∀ m : M, fs m ∈ Ps → ∃ n : ℕ, fr (s ^ n • m) ∈ Pr := by
    intro m hm
    have hloc : frs m ∈ ((Ps.restrictScalars R).comap fs).localized'
        (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs := by
      exact ⟨m, hm, 1, by simp⟩
    rw [← hOverlap] at hloc
    obtain ⟨t, ht⟩ := exists_smul_mem_of_mem_localized'
      (Submonoid.powers (r * s)) frs ((Pr.restrictScalars R).comap fr) m hloc
    obtain ⟨n, hn⟩ := t.property
    refine ⟨n, ?_⟩
    have hmem : fr ((r * s) ^ n • m) ∈ Pr := by
      change fr ((t : R) • m) ∈ Pr at ht
      simpa only [hn] using ht
    have hunit : IsUnit (algebraMap R (Localization.Away r) (r ^ n)) := by
      simpa only [map_pow] using
        ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).pow n)
    apply (Pr.smul_mem_iff_of_isUnit hunit).mp
    have heq : (algebraMap R (Localization.Away r) (r ^ n)) • fr (s ^ n • m) =
        fr ((r * s) ^ n • m) := by
      rw [algebraMap_smul, ← map_smul, smul_smul, ← mul_pow]
    rw [heq]
    exact hmem
  exact exists_fg_two_away_localized_submodule_of_cross_denominators r s Pr Ps hrs hsr

end Submodule
