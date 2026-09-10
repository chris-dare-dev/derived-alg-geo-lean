/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.Cech.BasisComparison
import DerivedAlgGeo.Topology.Sheaves.Cech.InjectiveFlasque
import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque abelian sheaves are acyclic for sheaf cohomology

For a flasque sheaf of abelian groups `F` on a topological space, `Sheaf.H F n` vanishes
for every `n ≥ 1`. This is Hartshorne III.2.5, proved by dimension shifting: embed `F` in
an injective sheaf `I`, which is flasque by `Sheaf.isFlasque_of_injective`; the quotient `Q`
is flasque by `IsFlasque.of_shortExact_of_isFlasque₁₂`; global sections of `I` surject onto
those of `Q` by `IsFlasque.epi_of_shortExact`, which kills `H¹ F`
(`Sheaf.H_one_subsingleton_of_sections_epi`); and `H^(n+2) F` vanishes once `H^(n+1) Q`
does (`Sheaf.H_succ_subsingleton_of_shortExact`), so the induction closes.

Nothing here is Čech-theoretic; compare `Sites/SheafCohomology/Cech/Comparison.lean`,
which obtains vanishing from Čech exactness instead.

## Main result

* `TopCat.Sheaf.subsingleton_H_of_isFlasque`.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- **Flasque sheaves are acyclic.** For a flasque sheaf of abelian groups `F` on a
topological space, `Sheaf.H F (n + 1)` is trivial for every `n`. -/
theorem subsingleton_H_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.derivedH hExt F (n + 1)) := by
  induction n generalizing F with
  | zero =>
    let ip : InjectivePresentation F := Classical.arbitrary _
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₁ := ‹F.IsFlasque›
    exact CategoryTheory.Sheaf.H_one_subsingleton_of_sections_epi ip
      (IsFlasque.epi_of_shortExact ip.shortExact_shortComplex)
  | succ n ih =>
    let ip : InjectivePresentation F := Classical.arbitrary _
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₁ := ‹F.IsFlasque›
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₂ :=
      CategoryTheory.Sheaf.isFlasque_of_injective ip.J
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₃ :=
      IsFlasque.of_shortExact_of_isFlasque₁₂ ip.shortExact_shortComplex
    haveI : Injective ip.shortComplex.X₂ := ip.injective
    haveI := ih ip.shortComplex.X₃
    exact CategoryTheory.Sheaf.H_succ_subsingleton_of_shortExact ip.shortExact_shortComplex
      (n + 1)

end TopCat.Sheaf
