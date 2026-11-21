/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descent of flatness over the base

Let `q : Y ⟶ T` be a morphism of schemes and `M` a module sheaf on `Y`. This file compares
flatness of `M` over `T` (`Scheme.Modules.IsFlatOver`) with flatness of its pullbacks.

## Main definitions

None: the file adds theorems about `Scheme.Modules.IsFlatOver`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.pullback_of_flat`: along a flat morphism
  `h : Y' ⟶ Y`, flatness over the base ascends (Stacks 02JZ).
* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.of_pullback_of_flat_of_surjective`: along a flat
  surjective morphism it also descends (Stacks 02JZ (1)).
* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.of_cover`: flatness over the base is local on the
  base for flat, jointly surjective families (Stacks 02JZ with 01U6).

## Implementation notes

Everything is stalkwise. At `y' ∈ Y'` the stalk of `h^* M` is `𝒪_{Y',y'} ⊗ M_{h y'}`
(`pullbackStalkIso`), and `𝒪_{Y,h y'} ⟶ 𝒪_{Y',y'}` is flat and local, hence faithfully flat.
Ascent and descent at one point are then Stacks 0584 with `R = 𝒪_{T,t}`,
`S = 𝒪_{Y,h y'}` and `S' = 𝒪_{Y',y'}` (`Module.Flat.tensorProduct_of_flat` and
`Module.Flat.of_flat_tensorProduct_of_faithfullyFlat`).

For a cover `{Tᵢ ⟶ T}` the two ways `𝒪_{T,t}` acts on a stalk of `Y ×_T Tᵢ` are the stalk maps
of the two sides of `pullback.condition`, at points of `T` that are only propositionally equal.
`flat_restrictScalars_stalkMap_congr` transports flatness along an equality of morphisms once,
by substitution, before Stacks 0584 is invoked.

## References

* [Stacks, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
* [Stacks, Tag 01U6](https://stacks.math.columbia.edu/tag/01U6)
* [Stacks, Tag 0584](https://stacks.math.columbia.edu/tag/0584)

## Tags

flat, faithfully flat, module sheaf, stalk, descent, flat cover
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Flatness of a stalk module over the base transports along an equality of morphisms. -/
private theorem flat_restrictScalars_stalkMap_congr {P T : Scheme.{u}} {f g : P ⟶ T}
    (hfg : f = g) (z : P) (N : ModuleCat.{u} (P.presheaf.stalk z))
    (hN : Module.Flat (T.presheaf.stalk (f z))
      ((ModuleCat.restrictScalars (f.stalkMap z).hom).obj N)) :
    Module.Flat (T.presheaf.stalk (g z))
      ((ModuleCat.restrictScalars (g.stalkMap z).hom).obj N) := by
  subst hfg
  exact hN

/-- **Stacks 02JZ, at one point.** Let `h : Y' ⟶ Y` have a flat stalk map at `y'`. The stalk at
`y'` of `h^* M` is flat over `T` through `h ≫ q` if and only if the stalk of `M` at `h y'` is flat
over `T` through `q`. -/
private theorem flat_stalk_pullback_iff {Y' Y T : Scheme.{u}} (h : Y' ⟶ Y) (q : Y ⟶ T)
    (M : Y.Modules) (y' : Y') (hh : (h.stalkMap y').hom.Flat) :
    Module.Flat (T.presheaf.stalk ((h ≫ q) y'))
        ((ModuleCat.restrictScalars ((h ≫ q).stalkMap y').hom).obj
          ((moduleStalkFunctor Y' y').obj ((pullback h).obj M))) ↔
      Module.Flat (T.presheaf.stalk (q (h y')))
        ((ModuleCat.restrictScalars (q.stalkMap (h y')).hom).obj
          ((moduleStalkFunctor Y (h y')).obj M)) := by
  letI : Algebra (T.presheaf.stalk ((h ≫ q) y')) (Y.presheaf.stalk (h y')) :=
    (q.stalkMap (h y')).hom.toAlgebra
  letI : Algebra (Y.presheaf.stalk (h y')) (Y'.presheaf.stalk y') :=
    (h.stalkMap y').hom.toAlgebra
  letI : Algebra (T.presheaf.stalk ((h ≫ q) y')) (Y'.presheaf.stalk y') :=
    ((h ≫ q).stalkMap y').hom.toAlgebra
  haveI : IsScalarTower (T.presheaf.stalk ((h ≫ q) y')) (Y.presheaf.stalk (h y'))
      (Y'.presheaf.stalk y') :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp h q y'))
  haveI : Module.Flat (Y.presheaf.stalk (h y')) (Y'.presheaf.stalk y') := hh
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (h y')) (Y'.presheaf.stalk y')) :=
    inferInstanceAs (IsLocalHom (h.stalkMap y').hom)
  haveI : Module.FaithfullyFlat (Y.presheaf.stalk (h y')) (Y'.presheaf.stalk y') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let My := (moduleStalkFunctor Y (h y')).obj M
  letI : Module (T.presheaf.stalk ((h ≫ q) y')) My :=
    Module.compHom My (algebraMap (T.presheaf.stalk ((h ≫ q) y')) (Y.presheaf.stalk (h y')))
  haveI : IsScalarTower (T.presheaf.stalk ((h ≫ q) y')) (Y.presheaf.stalk (h y')) My :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- The left side, as a module over `𝒪_{T,t}`, is `𝒪_{Y',y'} ⊗ My`.
  let e : (ModuleCat.restrictScalars ((h ≫ q).stalkMap y').hom).obj
      ((moduleStalkFunctor Y' y').obj ((pullback h).obj M)) ≃ₗ[T.presheaf.stalk ((h ≫ q) y')]
        Y'.presheaf.stalk y' ⊗[Y.presheaf.stalk (h y')] My :=
    ((ModuleCat.restrictScalars ((h ≫ q).stalkMap y').hom).mapIso
      ((pullbackStalkIso h y').app M)).toLinearEquiv.trans
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  change _ ↔ Module.Flat (T.presheaf.stalk ((h ≫ q) y')) My
  constructor
  · intro H
    haveI : Module.Flat (T.presheaf.stalk ((h ≫ q) y'))
        (Y'.presheaf.stalk y' ⊗[Y.presheaf.stalk (h y')] My) :=
      Module.Flat.of_linearEquiv e.symm
    exact Module.Flat.of_flat_tensorProduct_of_faithfullyFlat (S := Y.presheaf.stalk (h y'))
      (S' := Y'.presheaf.stalk y')
  · intro H
    haveI : Module.Flat (T.presheaf.stalk ((h ≫ q) y'))
        (Y'.presheaf.stalk y' ⊗[Y.presheaf.stalk (h y')] My) :=
      Module.Flat.tensorProduct_of_flat
    exact Module.Flat.of_linearEquiv e

/-- **Stacks 02JZ, ascent.** Flatness over the base survives pullback along a flat morphism of
the source: if `M` is flat over `T` through `q`, then `h^* M` is flat over `T` through `h ≫ q`.

Flatness of `h` cannot be dropped: for `Y = T = Spec ℤ`, `q = 𝟙`, `M = 𝒪` and
`h : Spec 𝔽₂ ⟶ Spec ℤ`, the stalk `𝔽₂` of `h^* 𝒪` is not flat over `ℤ_(2)`. -/
@[stacks 02JZ]
theorem IsFlatOver.pullback_of_flat {Y' Y T : Scheme.{u}} (h : Y' ⟶ Y) [Flat h]
    (q : Y ⟶ T) {M : Y.Modules} (hM : IsFlatOver q M) :
    IsFlatOver (h ≫ q) ((pullback h).obj M) := fun y' ↦
  (flat_stalk_pullback_iff h q M y' (Flat.stalkMap h y')).mpr (hM (h y'))

/-- **Stacks 02JZ (1), descent.** Along a flat surjective morphism `h : Y' ⟶ Y`, flatness over
the base descends: if `h^* M` is flat over `T` through `h ≫ q`, then `M` is flat over `T`
through `q`.

Neither hypothesis on `h` can be dropped.
* Flatness: for `T = Spec k[t]`, `Y = Spec k[t,x]/(tx, x²)`, `M = 𝒪_Y` and the surjective closed
  immersion `h : Y_red ≅ Spec k[t] ⟶ Y`, the pullback `𝒪_{Y_red}` is flat over `T`, but `x` is
  `t`-torsion in `𝒪_Y`.
* Surjectivity: for `Y = T = Spec ℤ`, `q = 𝟙`, `M = (ℤ/2)~` and `h : Spec ℚ ⟶ Spec ℤ`, the
  pullback `h^* M = 0` is flat, and `M` is not. -/
@[stacks 02JZ]
theorem IsFlatOver.of_pullback_of_flat_of_surjective {Y' Y T : Scheme.{u}} (h : Y' ⟶ Y)
    [Flat h] [Surjective h] (q : Y ⟶ T) {M : Y.Modules}
    (hM : IsFlatOver (h ≫ q) ((pullback h).obj M)) : IsFlatOver q M := by
  intro y
  obtain ⟨y', rfl⟩ := h.surjective y
  exact (flat_stalk_pullback_iff h q M y' (Flat.stalkMap h y')).mp (hM y')

/-- **Flatness over the base is local on the base** (Stacks 02JZ with 01U6). Let
`{Tᵢ ⟶ T}` be a flat, jointly surjective family. If, for every `i`, the pullback of `M` to
`Y ×_T Tᵢ` is flat over `Tᵢ`, then `M` is flat over `T`.

At `y ∈ Y` choose `i` and a point `y'` of `Y ×_T Tᵢ` over `y`. The stalk at `y'` is flat over
`𝒪_{Tᵢ}` and so over `𝒪_T` (01U6, `Module.Flat.trans`), and the projection to `Y` is flat, so
02JZ descends this to `M_y`. No quasi-compactness of the family and no quasi-coherence of `M` is
used.

Both conditions on the family are needed. On `Y = T = Spec ℤ`, `q = 𝟙`, `M = (ℤ/2)~`:
* flatness: for the family `{Spec ℚ, Spec 𝔽₂}`, the pullbacks `0` and `𝔽₂` are flat over the
  fields, and `M` is not flat;
* joint surjectivity: the family `{Spec ℚ}` alone. -/
@[stacks 02JZ "With Tag 01U6."]
theorem IsFlatOver.of_cover {Y T : Scheme.{u}} (q : Y ⟶ T) {M : Y.Modules}
    (𝒰 : T.Cover (Scheme.precoverage @Flat))
    (hM : ∀ i, IsFlatOver (Limits.pullback.snd q (𝒰.f i))
      ((pullback (Limits.pullback.fst q (𝒰.f i))).obj M)) :
    IsFlatOver q M := by
  intro y
  haveI : Scheme.JointlySurjective (Scheme.precoverage @Flat) :=
    Scheme.instJointlySurjectivePrecoverage (P := @Flat)
  obtain ⟨i, t, ht⟩ := 𝒰.exists_eq (q y)
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback y t ht.symm
  haveI : Flat (𝒰.f i) := 𝒰.map_prop i
  let fst := Limits.pullback.fst q (𝒰.f i)
  let snd := Limits.pullback.snd q (𝒰.f i)
  let N := (moduleStalkFunctor _ z).obj ((pullback fst).obj M)
  -- 01U6: the stalk is flat over `𝒪_{T}` through `snd ≫ 𝒰.f i`.
  have hsnd : Module.Flat (T.presheaf.stalk ((snd ≫ 𝒰.f i) z))
      ((ModuleCat.restrictScalars ((snd ≫ 𝒰.f i).stalkMap z).hom).obj N) := by
    letI : Algebra (T.presheaf.stalk ((snd ≫ 𝒰.f i) z)) ((𝒰.X i).presheaf.stalk (snd z)) :=
      ((𝒰.f i).stalkMap (snd z)).hom.toAlgebra
    haveI : Module.Flat (T.presheaf.stalk ((snd ≫ 𝒰.f i) z))
        ((𝒰.X i).presheaf.stalk (snd z)) :=
      Flat.stalkMap (𝒰.f i) (snd z)
    let N' := (ModuleCat.restrictScalars (snd.stalkMap z).hom).obj N
    haveI : Module.Flat ((𝒰.X i).presheaf.stalk (snd z)) N' := hM i z
    letI : Module (T.presheaf.stalk ((snd ≫ 𝒰.f i) z)) N' :=
      Module.compHom N' (algebraMap (T.presheaf.stalk ((snd ≫ 𝒰.f i) z))
        ((𝒰.X i).presheaf.stalk (snd z)))
    haveI : IsScalarTower (T.presheaf.stalk ((snd ≫ 𝒰.f i) z))
        ((𝒰.X i).presheaf.stalk (snd z)) N' :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    haveI : Module.Flat (T.presheaf.stalk ((snd ≫ 𝒰.f i) z)) N' :=
      Module.Flat.trans _ ((𝒰.X i).presheaf.stalk (snd z)) N'
    let e : N' ≃ₗ[T.presheaf.stalk ((snd ≫ 𝒰.f i) z)]
        (ModuleCat.restrictScalars ((snd ≫ 𝒰.f i).stalkMap z).hom).obj N :=
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r m ↦ by
          change (snd.stalkMap z).hom (((𝒰.f i).stalkMap (snd z)).hom r) • m =
            ((snd ≫ 𝒰.f i).stalkMap z).hom r • m
          rw [Scheme.Hom.stalkMap_comp]
          rfl }
    exact Module.Flat.of_linearEquiv e.symm
  have hfst := flat_restrictScalars_stalkMap_congr (Limits.pullback.condition).symm z N hsnd
  exact (flat_stalk_pullback_iff fst q M z (Flat.stalkMap fst z)).mp hfst

end AlgebraicGeometry.Scheme.Modules
