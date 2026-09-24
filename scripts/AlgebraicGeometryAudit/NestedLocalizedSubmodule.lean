import DerivedAlgGeo.Algebra.Module.LocalizedModule.NestedSubmodule
import Mathlib.Data.ZMod.Basic

/-! # Nested principal-localization submodule audit and direct clients -/

universe u v

#print axioms LocalizedModule.awayToAwayRightLinearMap
#print axioms LocalizedModule.awayToAwayRightLinearMap_mk
#print axioms Submodule.localized'_comap_awayToAwayRight_eq_span

-- A direct owner-leaf import exposes both the canonical map and the exact span identity.
example {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (r s : R) (P : Submodule (Localization.Away r) (LocalizedModule.Away r M)) :
    let fr := LocalizedModule.mkLinearMap (Submonoid.powers r) M
    let frs := LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M
    let α := LocalizedModule.awayToAwayRightLinearMap (M := M) r s
    ((P.restrictScalars R).comap fr).localized'
        (Localization.Away (r * s)) (Submonoid.powers (r * s)) frs =
      Submodule.span (Localization.Away (r * s))
        (α '' (P : Set (LocalizedModule.Away r M))) :=
  Submodule.localized'_comap_awayToAwayRight_eq_span r s P

-- Neither the map nor the theorem assumes that the denominators are regular.
example : (2 : ZMod 6) * 3 = 0 := by decide

example (P : Submodule (Localization.Away (2 : ZMod 6))
    (LocalizedModule.Away (2 : ZMod 6) (ZMod 6))) :
    let fr := LocalizedModule.mkLinearMap (Submonoid.powers (2 : ZMod 6)) (ZMod 6)
    let frs := LocalizedModule.mkLinearMap
      (Submonoid.powers ((2 : ZMod 6) * 3)) (ZMod 6)
    let α := LocalizedModule.awayToAwayRightLinearMap (M := ZMod 6)
      (2 : ZMod 6) 3
    ((P.restrictScalars (ZMod 6)).comap fr).localized'
        (Localization.Away ((2 : ZMod 6) * 3))
        (Submonoid.powers ((2 : ZMod 6) * 3)) frs =
      Submodule.span (Localization.Away ((2 : ZMod 6) * 3))
        (α '' (P : Set (LocalizedModule.Away (2 : ZMod 6) (ZMod 6)))) :=
  Submodule.localized'_comap_awayToAwayRight_eq_span 2 3 P
