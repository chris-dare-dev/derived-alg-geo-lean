import DerivedAlgGeo.Algebra.Module.LocalizedModule.TwoChartSubmodule

/-! # Two-chart localized submodule audit and direct clients -/

universe u v

#print axioms Submodule.exists_fg_two_away_localized_submodule_of_overlap

-- A direct owner-leaf import can consume the precise common-localization hypothesis.
example {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
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
        (LocalizedModule.mkLinearMap (Submonoid.powers s) M) = Ps :=
  Submodule.exists_fg_two_away_localized_submodule_of_overlap r s Pr Ps hOverlap

-- The overlap equation is not vacuous or dependent on sheaf APIs: the top submodules
-- provide an immediately usable algebraic instance.
example {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r s : R) :
    ∃ N : Submodule R M, N.FG ∧
      N.localized' (Localization.Away r) (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M) = ⊤ ∧
      N.localized' (Localization.Away s) (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) M) = ⊤ := by
  apply Submodule.exists_fg_two_away_localized_submodule_of_overlap r s ⊤ ⊤
  simp
