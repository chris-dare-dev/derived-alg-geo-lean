/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.LocallyFree

/-!
# Fixed-rank locally free atlases under pullback

`FiniteLocallyFreeData E n` pulls back along any morphism of schemes to
`FiniteLocallyFreeData (f⁺ E) n`: the atlas is `pullbackLocalGeneratorsData`, whose index
types are those of the original atlas, so the rank equivalences carry over unchanged.  This is
the rank-`n` input behind coherent pullback preserving perfect complexes
(`DerivedCategory/Families/PerfectPullback.lean`).

## Main definitions

* `Scheme.Modules.FiniteLocallyFreeData.pullback`: the pulled-back atlas, of the same rank.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A fixed-rank locally free atlas pulls back along any morphism of schemes, with the same
rank: the pulled-back generator data has the original index types. -/
noncomputable def FiniteLocallyFreeData.pullback (f : X ⟶ Y) {E : Y.Modules} {n : ℕ}
    (D : FiniteLocallyFreeData E n) :
    FiniteLocallyFreeData ((Scheme.Modules.pullback f).obj E) n :=
  letI : D.localGenerators.IsLocallyFreeData := D.isLocallyFreeData
  { localGenerators := pullbackLocalGeneratorsData f D.localGenerators
    isLocallyFreeData := inferInstance
    rankEquiv := D.rankEquiv }

end AlgebraicGeometry.Scheme.Modules
