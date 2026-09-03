/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.GeneratingSections

/-!
# Local generator data transported along functors on slices

Local generator data for `M` on a covering family `X` is transported to local generator data
for `N` on a covering family `Y` of another ringed site, given on each member a colimit
preserving functor `F i` between the slice categories that fixes the structure sheaf and an
identification `(F i).obj (M.over (X i)) ≅ N.over (Y i)`: the generators on `Y i` are
Mathlib's `GeneratingSections.map` along `F i`, pushed along the identification.  Locally free
data is transported to locally free data, with the same index types.

The construction is stated on general ringed sites because its instance is proved by reducing
projections of the structure, and that reduction does not terminate in the default heartbeat
budget once the sites carry scheme-level instances; `Modules/Pullback/LocallyFree.lean`
applies it to pullback on the slices of a scheme.

## Main definitions

* `SheafOfModules.LocalGeneratorsData.transport`: the transported local generator data.

## Main results

* `SheafOfModules.LocalGeneratorsData.isLocallyFreeData_transport`: locally free data is
  transported to locally free data;
* `SheafOfModules.LocalGeneratorsData.transport_generators_I`: the index types are unchanged.
-/

open CategoryTheory Limits

namespace SheafOfModules

universe u w u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J'.over X) AddCommGrpCat.{u}]
  [∀ X, (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

variable {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} R'} (q : M.LocalGeneratorsData.{w})
  (Y : q.I → C') (hY : J'.CoversTop Y)
  (F : ∀ i, SheafOfModules.{u} (R.over (q.X i)) ⥤ SheafOfModules.{u} (R'.over (Y i)))
  [∀ i, PreservesColimitsOfSize.{u, u} (F i)]
  (η : ∀ i, unit (R'.over (Y i)) ≅ (F i).obj (unit (R.over (q.X i))))
  (e : ∀ i, (F i).obj (M.over (q.X i)) ≅ N.over (Y i))

/-- Transport local generator data along colimit-preserving functors on slices that fix the
structure sheaf: on `Y i` the generators are `GeneratingSections.map` along `F i`, pushed
along `e i`. -/
noncomputable def transport : N.LocalGeneratorsData.{w} where
  I := q.I
  X := Y
  coversTop := hY
  generators i := ((q.generators i).map (F i) (η i)).ofEpi (e i).hom

/-- Neither `GeneratingSections.map` nor `ofEpi` changes the index type of the generators, so
a fixed-rank atlas is transported with its rank. -/
@[simp]
lemma transport_generators_I (i : q.I) :
    ((q.transport Y hY F η e).generators i).I = (q.generators i).I :=
  rfl

/-- Locally free data is transported to locally free data: `GeneratingSections.map` sends an
isomorphism `π` to an isomorphism, and so does pushing along `e i`. -/
instance isLocallyFreeData_transport [q.IsLocallyFreeData] :
    (q.transport Y hY F η e).IsLocallyFreeData where
  isIso i := by
    change q.I at i
    haveI : IsIso (q.generators i).π := IsLocallyFreeData.isIso i
    haveI : IsIso ((q.generators i).map (F i) (η i)).π := by
      rw [GeneratingSections.map_π_eq]
      exact IsIso.comp_isIso' inferInstance (Functor.map_isIso _ _)
    change IsIso (((q.generators i).map (F i) (η i)).ofEpi (e i).hom).π
    exact GeneratingSections.isIso_ofEpi_π ((q.generators i).map (F i) (η i)) (e i).hom

end LocalGeneratorsData

end SheafOfModules
