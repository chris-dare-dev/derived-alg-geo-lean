import DerivedAlgGeo.Algebra.Module.LocalizedModule.NestedSubmoduleLeft
import Mathlib.Data.ZMod.Basic

/-! # Opposite-chart nested localization audit and direct clients -/

universe u v

#print axioms LocalizedModule.awayToAwayLeftLinearMap
#print axioms LocalizedModule.awayToAwayLeftLinearMap_mk
#print axioms Submodule.localized'_comap_awayToAwayLeft_eq_span
#print axioms Submodule.localized'_away_mul_eq_span_awayToAwayLeft

-- The two canonical chart maps have the same target, in the order `r * s`.
example {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (m : M) :
    LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
        (LocalizedModule.mk m (1 : Submonoid.powers s)) =
      LocalizedModule.awayToAwayRightLinearMap (M := M) r s
        (LocalizedModule.mk m (1 : Submonoid.powers r)) := by
  simp

example {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (P : Submodule (Localization.Away s) (LocalizedModule.Away s M)) :
    let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
    let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
    let α := LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
    ((P.restrictScalars R).comap fs).localized'
        (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
      Submodule.span (Localization.Away (r * s))
        (α '' (P : Set (LocalizedModule.Away s M))) :=
  Submodule.localized'_comap_awayToAwayLeft_eq_span r s P

example {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (N : Submodule R M) :
    let fs := LocalizedModule.mkLinearMap (Submonoid.powers s) M
    let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
    let α := LocalizedModule.awayToAwayLeftLinearMap (M := M) r s
    N.localized' (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
      Submodule.span (Localization.Away (r * s))
        (α '' (N.localized' (Localization.Away s) (Submonoid.powers s) fs :
          Set (LocalizedModule.Away s M))) :=
  Submodule.localized'_away_mul_eq_span_awayToAwayLeft r s N

-- The product can vanish, and the map into `M[1/s]` need not be injective.
example : (2 : ZMod 6) * 3 = 0 := by decide

example : ¬ Function.Injective
    (LocalizedModule.mkLinearMap (Submonoid.powers (3 : ZMod 6)) (ZMod 6)) := by
  intro hInjective
  have hzero :
      (LocalizedModule.mkLinearMap (Submonoid.powers (3 : ZMod 6)) (ZMod 6))
          (2 : ZMod 6) = 0 :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers (3 : ZMod 6))
      (LocalizedModule.mkLinearMap (Submonoid.powers (3 : ZMod 6)) (ZMod 6))).2
        ⟨⟨3, Submonoid.mem_powers 3⟩, by decide⟩
  have h : (2 : ZMod 6) = 0 := hInjective (by simpa using hzero)
  exact (by decide : (2 : ZMod 6) ≠ 0) h

example (P : Submodule (Localization.Away (3 : ZMod 6))
    (LocalizedModule.Away (3 : ZMod 6) (ZMod 6))) :
    let fs := LocalizedModule.mkLinearMap (Submonoid.powers (3 : ZMod 6)) (ZMod 6)
    let frs := LocalizedModule.mkLinearMap
      (Submonoid.powers ((2 : ZMod 6) * 3)) (ZMod 6)
    let α := LocalizedModule.awayToAwayLeftLinearMap (M := ZMod 6) (2 : ZMod 6) 3
    ((P.restrictScalars (ZMod 6)).comap fs).localized'
        (Localization.Away ((2 : ZMod 6) * 3))
        (Submonoid.powers ((2 : ZMod 6) * 3)) frs =
      Submodule.span (Localization.Away ((2 : ZMod 6) * 3))
        (α '' (P : Set (LocalizedModule.Away (3 : ZMod 6) (ZMod 6)))) :=
  Submodule.localized'_comap_awayToAwayLeft_eq_span 2 3 P
