/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Gluing
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-!
# Flatness of a module sheaf over a morphism

`Scheme.Modules.IsFlatOver p M` says that `M` is flat over the base along
`p : X ⟶ S`, stalkwise: at every point of `X`, the stalk of `M` is flat as a
module over the corresponding stalk of `S`, restricted along the local-ring
map `p` induces.

Flatness over the identity is equivalent to flatness at each module stalk,
and is preserved by indexed coproducts of module sheaves.

Flatness over the base can be checked on affine opens: it holds as soon as
`Γ(U, M)` is flat over `Γ(V, 𝒪_S)` for all affine opens `U ⊆ X`, `V ⊆ S` with
`p(U) ⊆ V`, and for a quasi-coherent `M` it is equivalent to that condition.
It is stable under base change: for `p : X ⟶ S`, `g : S' ⟶ S` and the
projection `X ×_S S' ⟶ X`, the pullback of a module sheaf flat over `S` is
flat over `S'`. Pullback along that projection keeps a short exact sequence
short exact when its quotient is flat over `S`, with no flatness of `p`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsFlatOver` — stalkwise flatness of a module sheaf over a
  morphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFlatOverId_iff_stalkwiseFlat` — flatness over the identity
  is flatness of each module stalk over the local ring.
* `AlgebraicGeometry.Scheme.Modules.isFlatOverId_coprod` — flatness over the identity is closed
  under indexed coproducts.
* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.of_iso` — flatness over the base transports along
  isomorphisms of module sheaves, and `IsFlatOver.of_isZero` holds for a zero module sheaf.
* `AlgebraicGeometry.Scheme.Modules.isFlatOver_of_affine` — flatness of sections over compatible
  affine opens implies flatness over the base, for every module sheaf.
* `AlgebraicGeometry.Scheme.Modules.isFlatOver_iff_affine` — for a quasi-coherent module sheaf,
  flatness over the base is flatness of sections over compatible affine opens.
* `AlgebraicGeometry.Scheme.Modules.flat_stalk_of_isLocalizedModule` — for a quasi-coherent
  module sheaf, flatness of the stalk at a point follows from flatness of a localization of the
  sections over one affine chart.
* `AlgebraicGeometry.Scheme.Modules.flat_stalk_of_isPullback` — base change of flatness at a point,
  for any pullback square.
* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.of_isPullback` — flatness over the base is stable
  under base change along any pullback square; `isFlatOver_pullback` is the chosen fibre product.
* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.of_shortExact`, `IsFlatOver.biprod` and
  `IsFlatOver.of_isFlatOver_id` — flatness over the base passes to kernels of epimorphisms between
  flat modules and to biproducts, and flatness over the identity gives flatness over a flat
  morphism.
* `AlgebraicGeometry.Scheme.Modules.pullback_shortExact_of_isPullback` — base change keeps a short
  exact sequence short exact when its quotient is flat over the base; the chosen fibre product is
  `pullback_shortExact_of_isFlatOver`.

## Implementation notes

This is a property of one module sheaf and one morphism. It needs no derived
category, no moduli problem and no perfectness notion, and it is used before
any of them: Tor-amplitude models, geometric fibers and base-change arguments
all require flat terms. It lives with `X.Modules` for that reason — the
carrier in its public type is a module sheaf. The repository constructions it
uses are `moduleStalkFunctor` and `pullbackStalkIso` from the neighbouring
`Modules/Pullback/Stalk.lean`, and the basic-open localization of
quasi-coherent sections on `Spec R` from `Modules/Affine/Gluing.lean`.

### Not a morphism-flatness predicate

`Mathlib.AlgebraicGeometry.Morphisms.Flat` is a different subject: it asks
that the *morphism* be flat, which is this condition for the structure sheaf
alone. Nothing here specializes to or is implied by that class, and no
instance relates them. This file imports it only for its computation of the
sections of a fibre product over affine opens as a pushout of rings.

### Scalars on sections

In the affine statements `Γ(U, M)` is a `Γ(V, 𝒪_S)`-module by restriction of
scalars along `p.appLE V U _`. `IsFlatOver` restricts the stalk along
`p.stalkMap x`; the two meet through germs, and one private lemma records
`germ ≫ p.stalkMap x = p.appLE V U _ ≫ germ`.

### The affine characterization

For `isFlatOver_of_affine` the equational criterion is checked on the stalk:
finitely many germs and a relation among them are realized on one affine
neighbourhood, where the flatness of the sections makes the relation
trivial. No quasi-coherence is used. For the converse, quasi-coherence makes
the germ map `Γ(U, M) ⟶ M_x` a localization at the prime of `x` for affine
`U`. This is transported from the basic-open localization on
`Spec Γ(X, U)` along `IsAffineOpen.fromSpec`, and
`Module.flat_of_isLocalized_maximal` concludes.

### Base change

`flat_stalk_of_isPullback` is proved stalkwise, for any `IsPullback` square `P`, and needs no
quasi-coherence. `IsFlatOver.of_isPullback` applies it at every point, and
`isFlatOver_pullback` is that for the chosen fibre product. At a point `z` of `P`,
`pullbackStalkIso` identifies the stalk of
the pullback with `𝒪_{P,z} ⊗ M_y`. Over affine opens `U`, `V`, `V'` around the
images of `z`, the sections of `P` over `W = fst⁻¹ U ∩ snd⁻¹ V'` form the
pushout `Γ(U) ⊗_{Γ(V)} Γ(V')` (`isIso_pushoutSection_of_isAffineOpen`), and
`𝒪_{P,z}` is a localization of `Γ(W)`. The stalk is therefore a localization
of `Γ(V') ⊗_{Γ(V)} M_y`, which is flat over `Γ(V')`.

`pullback_shortExact_of_isPullback` uses the same presentation. Pullback is right exact, so only
injectivity on the left is at stake. At a point it is the injectivity of
`𝒪_{P,z} ⊗ M_{1,y} → 𝒪_{P,z} ⊗ M_{2,y}`, a localization of `Γ(V') ⊗_{Γ(V)} M_{1,y} →
Γ(V') ⊗_{Γ(V)} M_{2,y}`, which is injective because `M_{3,y}` is flat over `Γ(V)`
(`LinearMap.lTensor_injective_of_exact_of_flat`).

## References

* [Stacks, Tag 01U2](https://stacks.math.columbia.edu/tag/01U2): Definition 01U3 is
  `IsFlatOver`, Lemma 01U4 the affine characterization, Lemma 01U8 base change.

The file builds on Mathlib's `Module.Flat`, `ModuleCat.restrictScalars` and
`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`, and on
`AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor`.

## Tags

flat module, module sheaf, stalk, morphism of schemes, base change, affine open
-/

open scoped TensorProduct

/-- Localizing at a multiplicative subset of a larger ring keeps flatness over the base. -/
private theorem flat_of_isLocalizedModule_of_flat {R A M M' : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    (S : Submonoid A) (g : M →ₗ[A] M') [IsLocalizedModule S g] [Module.Flat R M] :
    Module.Flat R M' := by
  have H := (Module.Flat.iff_lTensor_injectiveₛ (R := R) (M := M)).mp inferInstance
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N ↦ ?_
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A),
    ← IsLocalizedModule.map_lTensor (S := S) (g := g) (f := N.subtype)]
  exact IsLocalizedModule.map_injective _ _ _ _ (by
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor]; exact H N)

/-- Let `L` localize `B` and `D` localize a `B`-algebra `C`, compatibly. For an `L`-module `M`,
the map `C ⊗[B] M → D ⊗[L] M` sending `c ⊗ m` to `c • (1 ⊗ m)` is a localization. -/
private theorem isLocalizedModule_tensor {B C L D : Type*} [CommRing B] [CommRing C]
    [CommRing L] [CommRing D] [Algebra B C] [Algebra B L] (SB : Submonoid B) [IsLocalization SB L]
    [Algebra C D] (SC : Submonoid C) [IsLocalization SC D]
    [Algebra L D] [Algebra B D] [IsScalarTower B L D] [IsScalarTower B C D]
    (M : Type*) [AddCommGroup M] [Module L M] [Module B M] [IsScalarTower B L M] :
    IsLocalizedModule SC ((TensorProduct.isBaseChange B M C).lift
      ((TensorProduct.mk L D M 1).restrictScalars B)) := by
  have h₁ : IsBaseChange L (LinearMap.id : M →ₗ[B] M) :=
    (isLocalizedModule_iff_isBaseChange SB L _).mp (isLocalizedModule_id SB M L)
  have h₂ : IsBaseChange D ((TensorProduct.mk L D M 1).restrictScalars B ∘ₗ LinearMap.id) :=
    h₁.comp (TensorProduct.isBaseChange L M D)
  have hC : IsBaseChange C (TensorProduct.mk B C M 1) := TensorProduct.isBaseChange B M C
  have hg : IsBaseChange D (hC.lift ((TensorProduct.mk L D M 1).restrictScalars B)) := by
    refine hC.of_comp ?_
    convert h₂ using 1
    exact hC.lift_comp _
  exact (isLocalizedModule_iff_isBaseChange SC D _).mpr hg

/-- The map of `isLocalizedModule_tensor` on pure tensors: `c ⊗ m ↦ c • (1 ⊗ m)`. -/
private theorem isBaseChange_lift_tmul {B C L D : Type*} [CommRing B] [CommRing C]
    [CommRing L] [CommRing D] [Algebra B C] [Algebra B L] [Algebra C D] [Algebra L D]
    [Algebra B D] [IsScalarTower B L D] [IsScalarTower B C D]
    {M : Type*} [AddCommGroup M] [Module L M] [Module B M] [IsScalarTower B L M]
    (c : C) (m : M) :
    (TensorProduct.isBaseChange B M C).lift ((TensorProduct.mk L D M 1).restrictScalars B)
      (c ⊗ₜ m) = c • ((1 : D) ⊗ₜ[L] m) := by
  have : c ⊗ₜ[B] m = c • (TensorProduct.mk B C M 1 m) := by
    simp [TensorProduct.smul_tmul']
  rw [this, LinearMap.map_smul, IsBaseChange.lift_eq]
  rfl

/-- The ring-level step of base change. Let `C` be the pushout `A' ⊗[A] B`, and let `L` localize
`B` and `D` localize `C`, compatibly. An `L`-module `M` flat over `A` then has `D ⊗[L] M` flat
over `A'`, as a localization of `C ⊗[B] M ≅ A' ⊗[A] M`. In `isFlatOver_pullback` the rings
`A`, `B`, `A'`, `C` are sections over affine opens and `L`, `D` are local rings. -/
private theorem flat_tensor_of_isPushout {A A' B C L D : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing C] [CommRing L] [CommRing D]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra B C] [Algebra A' C]
    [IsScalarTower A B C] [IsScalarTower A A' C] [Algebra.IsPushout A A' B C]
    [Algebra B L] (SB : Submonoid B) [IsLocalization SB L]
    [Algebra C D] (SC : Submonoid C) [IsLocalization SC D]
    [Algebra L D] [Algebra B D] [IsScalarTower B L D] [IsScalarTower B C D]
    [Algebra A' D] [IsScalarTower A' C D]
    (M : Type*) [AddCommGroup M] [Module L M] [Module A M] [Module B M] [IsScalarTower B L M]
    [IsScalarTower A B M] [Module.Flat A M] :
    Module.Flat A' (D ⊗[L] M) := by
  have : Module.Flat A' (C ⊗[B] M) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A A' B C M)
  have := isLocalizedModule_tensor SB (L := L) (D := D) SC M
  exact flat_of_isLocalizedModule_of_flat SC
    ((TensorProduct.isBaseChange B M C).lift ((TensorProduct.mk L D M 1).restrictScalars B))

/-- The ring-level step of exactness under base change. In the setting of
`flat_tensor_of_isPushout`, let `0 → M₁ → M₂ → M₃ → 0` be exact over `L` with `M₃` flat over
`A`. Then `D ⊗[L] M₁ → D ⊗[L] M₂` is injective. It is a localization of
`C ⊗[B] M₁ → C ⊗[B] M₂`, which is `A' ⊗[A] M₁ → A' ⊗[A] M₂`, injective because `M₃` is flat.
No flatness of `B` over `A` is used. -/
private theorem injective_baseChange_of_isPushout {A A' B C L D : Type*} [CommRing A]
    [CommRing A'] [CommRing B] [CommRing C] [CommRing L] [CommRing D]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra B C] [Algebra A' C]
    [IsScalarTower A B C] [IsScalarTower A A' C] [Algebra.IsPushout A A' B C]
    [Algebra B L] (SB : Submonoid B) [IsLocalization SB L]
    [Algebra C D] (SC : Submonoid C) [IsLocalization SC D]
    [Algebra L D] [Algebra B D] [IsScalarTower B L D] [IsScalarTower B C D]
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module L M₁] [Module A M₁] [Module B M₁]
    [IsScalarTower B L M₁] [IsScalarTower A B M₁]
    [AddCommGroup M₂] [Module L M₂] [Module A M₂] [Module B M₂]
    [IsScalarTower B L M₂] [IsScalarTower A B M₂]
    [AddCommGroup M₃] [Module L M₃] [Module A M₃] [Module B M₃]
    [IsScalarTower B L M₃] [IsScalarTower A B M₃] [Module.Flat A M₃]
    {g : M₁ →ₗ[L] M₂} {f : M₂ →ₗ[L] M₃} (hg : Function.Injective g)
    (hf : Function.Surjective f) (hgf : Function.Exact g f) :
    Function.Injective (g.baseChange D) := by
  let gB := g.restrictScalars B
  let gA := gB.restrictScalars A
  have h₁ : Function.Injective (gA.lTensor A') :=
    LinearMap.lTensor_injective_of_exact_of_flat ((f.restrictScalars B).restrictScalars A) hf
      gA hg hgf A'
  let e₁ := Algebra.IsPushout.cancelBaseChange A A' B C M₁
  let e₂ := Algebra.IsPushout.cancelBaseChange A A' B C M₂
  have hcomm : ∀ y : A' ⊗[A] M₁,
      gB.baseChange C (e₁.symm y) = e₂.symm (gA.lTensor A' y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a m => simp [e₁, e₂, gA, gB, Algebra.IsPushout.cancelBaseChange_symm_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : Function.Injective (gB.baseChange C) := by
    intro x y hxy
    rw [← e₁.symm_apply_apply x, ← e₁.symm_apply_apply y, hcomm, hcomm] at hxy
    exact e₁.injective (h₁ (e₂.symm.injective hxy))
  let ℓ₁ := (TensorProduct.isBaseChange B M₁ C).lift
    ((TensorProduct.mk L D M₁ 1).restrictScalars B)
  let ℓ₂ := (TensorProduct.isBaseChange B M₂ C).lift
    ((TensorProduct.mk L D M₂ 1).restrictScalars B)
  have hℓ₁ : IsLocalizedModule SC ℓ₁ := isLocalizedModule_tensor SB SC M₁
  have hℓ₂ : IsLocalizedModule SC ℓ₂ := isLocalizedModule_tensor SB SC M₂
  have hcomm' : ∀ x, (g.baseChange D) (ℓ₁ x) = ℓ₂ (gB.baseChange C x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c m =>
      change (g.baseChange D) (ℓ₁ (c ⊗ₜ m)) = ℓ₂ (c ⊗ₜ gB m)
      rw [show ℓ₁ (c ⊗ₜ m) = c • ((1 : D) ⊗ₜ[L] m) from isBaseChange_lift_tmul c m,
        show ℓ₂ (c ⊗ₜ gB m) = c • ((1 : D) ⊗ₜ[L] g m) from isBaseChange_lift_tmul c (g m),
        LinearMap.map_smul_of_tower, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.surj SC ℓ₁ x
  have hy' : (s : C) • x = ℓ₁ y := hy
  have h0 : ℓ₂ (gB.baseChange C y) = 0 := by
    rw [← hcomm', ← hy', LinearMap.map_smul_of_tower, hx, smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff SC ℓ₂).1 h0
  have ht' : (t : C) • gB.baseChange C y = 0 := ht
  have hty : (t : C) • y = 0 := by
    apply (injective_iff_map_eq_zero _).1 h₂
    rw [LinearMap.map_smul, ht']
  have hx0 : ((t * s : SC) : C) • x = 0 := by
    rw [Submonoid.coe_mul, mul_smul, hy', ← LinearMap.map_smul, hty, map_zero]
  have hu := IsLocalizedModule.map_units ℓ₁ (t * s)
  rw [Module.End.isUnit_iff] at hu
  apply hu.injective
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, smul_zero]
  exact hx0

/-- A product of two flat modules is flat: `N ⊗ (M₁ × M₂) ≅ (N ⊗ M₁) × (N ⊗ M₂)` naturally
in `N`. -/
private theorem flat_prod {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Flat R M₁] [Module.Flat R M₂] :
    Module.Flat R (M₁ × M₂) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ i hi
  have h₁ := Module.Flat.lTensor_preserves_injective_linearMap (M := M₁) i hi
  have h₂ := Module.Flat.lTensor_preserves_injective_linearMap (M := M₂) i hi
  let e := TensorProduct.prodLeft R R M₁ M₂ N
  let e' := TensorProduct.prodLeft R R M₁ M₂ N'
  have hc : ∀ x, e' (i.lTensor (M₁ × M₂) x) =
      LinearMap.prodMap (i.lTensor M₁) (i.lTensor M₂) (e x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n => obtain ⟨m₁, m₂⟩ := m; simp [e, e']
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply e.injective
  have := congrArg e' hxy
  rw [hc, hc] at this
  exact Prod.map_injective.2 ⟨h₁, h₂⟩ this

/-- In an exact sequence `0 → M₁ → M₂ → M₃ → 0` with `M₂` and `M₃` flat, `M₁` is flat: for an
injective `N → N'`, the composite `N ⊗ M₁ → N' ⊗ M₁ → N' ⊗ M₂` is `N ⊗ M₁ → N ⊗ M₂ → N' ⊗ M₂`,
injective as `M₃` and `M₂` are flat. -/
private theorem flat_of_exact_of_flat {R M₁ M₂ M₃ : Type*} [CommRing R] [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [Module.Flat R M₂] [Module.Flat R M₃] {g : M₁ →ₗ[R] M₂} {f : M₂ →ₗ[R] M₃}
    (hg : Function.Injective g) (hf : Function.Surjective f) (hgf : Function.Exact g f) :
    Module.Flat R M₁ := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ i hi
  have h₁ : Function.Injective (g.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf g hg hgf N
  have h₂ : Function.Injective (i.rTensor M₂) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  have hc : (g.lTensor N').comp (i.rTensor M₁) = (i.rTensor M₂).comp (g.lTensor N) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have : Function.Injective ((g.lTensor N').comp (i.rTensor M₁)) := by
    rw [hc]
    exact h₂.comp h₁
  exact Function.Injective.of_comp this

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

namespace Scheme

/-- A module sheaf on `X` is flat over `S` when every stalk, restricted along
the local-ring map induced by `p`, is a flat module over the corresponding
stalk of `S`. -/
def Modules.IsFlatOver {X S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) : Prop :=
  ∀ x : X, Module.Flat (S.presheaf.stalk (p x))
    ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((Scheme.Modules.moduleStalkFunctor X x).obj M))

/-- The identity morphism induces identity maps on stalk rings, and
`ModuleCat.restrictScalarsId'App` removes the scalar-restriction bookkeeping. -/
theorem Modules.isFlatOverId_iff_stalkwiseFlat
    (X : Scheme.{u}) (M : X.Modules) :
    Modules.IsFlatOver (𝟙 X) M ↔
      ∀ x : X, Module.Flat (X.presheaf.stalk x)
        ((Modules.moduleStalkFunctor X x).obj M) := by
  constructor
  · intro h x
    have h := h x
    dsimp [Modules.IsFlatOver] at h
    rw [Scheme.Hom.stalkMap_id] at h
    change Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
        ((Modules.moduleStalkFunctor X x).obj M)) at h
    letI : Module.Flat (X.presheaf.stalk x)
        ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
          ((Modules.moduleStalkFunctor X x).obj M)) := h
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
        ((Modules.moduleStalkFunctor X x).obj M)).toLinearEquiv.symm
  · intro h x
    have h := h x
    dsimp [Modules.IsFlatOver]
    rw [Scheme.Hom.stalkMap_id]
    change Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
        ((Modules.moduleStalkFunctor X x).obj M))
    letI : Module.Flat (X.presheaf.stalk x)
        ((Modules.moduleStalkFunctor X x).obj M) := h
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
        ((Modules.moduleStalkFunctor X x).obj M)).toLinearEquiv

/-- The stalk of a sheaf coproduct is a direct sum of its module stalks.
Direct sums of flat modules are flat, so identity-relative flatness is closed under coproducts. -/
theorem Modules.isFlatOverId_coprod (X : Scheme.{u}) {I : Type u}
    (G : I → X.Modules) (hG : ∀ i, Modules.IsFlatOver (𝟙 X) (G i)) :
    Modules.IsFlatOver (𝟙 X) (∐ G) := by
  apply (Modules.isFlatOverId_iff_stalkwiseFlat X (∐ G)).2
  intro x
  letI : DecidableEq I := Classical.decEq I
  let F : Discrete I ⥤ X.Modules := Discrete.functor G
  let Z : I → ModuleCat.{u} (X.presheaf.stalk x) :=
    fun i => (Modules.moduleStalkFunctor X x).obj (G i)
  haveI : PreservesColimitsOfShape (Discrete I) (Modules.moduleStalkFunctor X x) :=
    Modules.moduleStalkFunctor_preservesColimitsOfShape X x I
  let e₁ : (Modules.moduleStalkFunctor X x).obj (colimit F) ≅
      colimit (F ⋙ Modules.moduleStalkFunctor X x) :=
    preservesColimitIso (Modules.moduleStalkFunctor X x) F
  let e₂ : colimit (F ⋙ Modules.moduleStalkFunctor X x) ≅
      colimit (Discrete.functor Z) :=
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete G (Modules.moduleStalkFunctor X x))
  let e₃ := ModuleCat.coprodIsoDirectSum Z
  let e : (Modules.moduleStalkFunctor X x).obj (colimit F) ≅
      ModuleCat.of (X.presheaf.stalk x) (DirectSum I (fun i => ↑(Z i))) :=
    e₁ ≪≫ e₂ ≪≫ e₃
  have hflat : Module.Flat (X.presheaf.stalk x) (DirectSum I (fun i => ↑(Z i))) := by
    apply Module.Flat.directSum_iff.mpr
    intro i
    exact ((Modules.isFlatOverId_iff_stalkwiseFlat X (G i)).mp (hG i)) x
  change Module.Flat (X.presheaf.stalk x)
    ((Modules.moduleStalkFunctor X x).obj (colimit F))
  letI : Module.Flat (X.presheaf.stalk x) (DirectSum I (fun i => ↑(Z i))) := hflat
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end Scheme

namespace Scheme.Modules

open TopologicalSpace Opposite

section Germs

variable {X : Scheme.{u}}

/-- The germ at `x` of a section of a module sheaf, as an element of its module stalk. -/
private noncomputable def stalkGerm (M : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) :
    Γ(M, U) →+ (moduleStalkFunctor X x).obj M :=
  (M.presheaf.germ U x hx).hom

private theorem stalkGerm_smul (M : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U)
    (r : Γ(X, U)) (s : Γ(M, U)) :
    stalkGerm M U x hx (r • s) = X.presheaf.germ U x hx r • stalkGerm M U x hx s :=
  (PresheafOfModules.germ_smul (R := X.presheaf) M.val x U hx r s).trans
    ((PresheafOfModules.commStalkLinearEquiv X X.presheaf x M.val).symm.map_smul
      (X.presheaf.germ U x hx r) (TopCat.Presheaf.germ M.val.presheaf U x hx s))

private theorem stalkGerm_res (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (s : Γ(M, U)) :
    stalkGerm M V x hx (M.presheaf.map (homOfLE h).op s) = stalkGerm M U x (h hx) s :=
  TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE h) x hx s

private theorem exists_stalkGerm_eq (M : X.Modules) (x : X)
    (m : (moduleStalkFunctor X x).obj M) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)), stalkGerm M U x hx s = m :=
  TopCat.Presheaf.exists_germ_eq M.presheaf m

private theorem exists_res_eq_of_stalkGerm_eq (M : X.Modules) {U V : X.Opens} (x : X)
    (hU : x ∈ U) (hV : x ∈ V) (s : Γ(M, U)) (t : Γ(M, V))
    (h : stalkGerm M U x hU s = stalkGerm M V x hV t) :
    ∃ (W : X.Opens) (_ : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWV).op t := by
  obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq M.presheaf x hU hV s t h
  exact ⟨W, hW, leOfHom iU, leOfHom iV, e⟩

/-- The germ map as a linear map over the ring of sections. -/
private noncomputable def stalkGermLinearMap (M : X.Modules) (U : X.Opens) (x : X)
    (hx : x ∈ U) :
    Γ(M, U) →ₗ[Γ(X, U)] (ModuleCat.restrictScalars (X.presheaf.germ U x hx).hom).obj
      ((moduleStalkFunctor X x).obj M) where
  toFun := stalkGerm M U x hx
  map_add' := map_add _
  map_smul' := stalkGerm_smul M U x hx

end Germs

/-- The scalar maps of the stalkwise and the affine statements agree through germs. -/
private theorem germ_stalkMap_eq_appLE_germ {Y T : Scheme.{u}} (q : Y ⟶ T) {V : T.Opens}
    {U : Y.Opens} (hUV : U ≤ q ⁻¹ᵁ V) (x : Y) (hx : x ∈ U) (hxV : q x ∈ V) :
    T.presheaf.germ V (q x) hxV ≫ q.stalkMap x =
      q.appLE V U hUV ≫ Y.presheaf.germ U x hx := by
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- Flatness of a stalk over the local ring of the base is flatness over the sections of any
affine neighbourhood of the image point, of which that local ring is a localization. -/
private theorem flat_stalk_iff {Y T : Scheme.{u}} (q : Y ⟶ T) (M : Y.Modules) (x : Y)
    {V : T.Opens} (hV : IsAffineOpen V) (hxV : q x ∈ V) :
    Module.Flat (T.presheaf.stalk (q x))
        ((ModuleCat.restrictScalars (q.stalkMap x).hom).obj ((moduleStalkFunctor Y x).obj M)) ↔
      Module.Flat Γ(T, V) ((ModuleCat.restrictScalars
        (T.presheaf.germ V (q x) hxV ≫ q.stalkMap x).hom).obj
          ((moduleStalkFunctor Y x).obj M)) := by
  let N := (ModuleCat.restrictScalars (q.stalkMap x).hom).obj ((moduleStalkFunctor Y x).obj M)
  let : Algebra Γ(T, V) (T.presheaf.stalk (q x)) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf ⟨q x, hxV⟩
  have : IsLocalization.AtPrime (T.presheaf.stalk (q x)) (hV.primeIdealOf ⟨q x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨q x, hxV⟩
  let : Module Γ(T, V) N := Module.compHom N (algebraMap Γ(T, V) (T.presheaf.stalk (q x)))
  have : IsScalarTower Γ(T, V) (T.presheaf.stalk (q x)) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rw [Module.flat_iff_of_isLocalization (T.presheaf.stalk (q x))
    (hV.primeIdealOf ⟨q x, hxV⟩).asIdeal.primeCompl N]
  let e : N ≃ₗ[Γ(T, V)] (ModuleCat.restrictScalars
      (T.presheaf.germ V (q x) hxV ≫ q.stalkMap x).hom).obj ((moduleStalkFunctor Y x).obj M) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv e.symm, fun _ ↦ Module.Flat.of_linearEquiv e⟩

/-- The equational criterion on a stalk: if the sections over arbitrarily small
neighbourhoods of `x` are flat over `Γ(T, V)`, so is the stalk at `x`. -/
private theorem flat_stalk_of_forall_nhds {Y T : Scheme.{u}} (q : Y ⟶ T) (M : Y.Modules)
    (x : Y) {V : T.Opens} (hxV : q x ∈ V)
    (H : ∀ W : Y.Opens, x ∈ W → ∃ (U : Y.Opens) (_ : x ∈ U) (_ : U ≤ W) (hUV : U ≤ q ⁻¹ᵁ V),
      Module.Flat Γ(T, V) ((ModuleCat.restrictScalars (q.appLE V U hUV).hom).obj
        (ModuleCat.of Γ(Y, U) Γ(M, U)))) :
    Module.Flat Γ(T, V) ((ModuleCat.restrictScalars
      (T.presheaf.germ V (q x) hxV ≫ q.stalkMap x).hom).obj ((moduleStalkFunctor Y x).obj M)) := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f m} hfm ↦ ?_
  choose U hxU s hs using fun i ↦ exists_stalkGerm_eq M x (m i)
  have hxW₀ : x ∈ Finset.univ.inf U :=
    Finset.inf_induction (p := fun W : Y.Opens ↦ x ∈ W) trivial
      (fun _ h₁ _ h₂ ↦ ⟨h₁, h₂⟩) (fun i _ ↦ hxU i)
  obtain ⟨U₁, hxU₁, hU₁W₀, hU₁V, -⟩ := H _ hxW₀
  have hU₁ : ∀ i, U₁ ≤ U i := fun i ↦ hU₁W₀.trans (Finset.inf_le (Finset.mem_univ i))
  let t : Fin l → Γ(M, U₁) := fun i ↦ M.presheaf.map (homOfLE (hU₁ i)).op (s i)
  have ht : ∀ i, stalkGerm M U₁ x hxU₁ (t i) = m i := fun i ↦
    (stalkGerm_res M (hU₁ i) x hxU₁ (s i)).trans (hs i)
  have hφ : ∀ (U' : Y.Opens) (hxU' : x ∈ U') (hU'V : U' ≤ q ⁻¹ᵁ V) (a : Γ(T, V)),
      (T.presheaf.germ V (q x) hxV ≫ q.stalkMap x).hom a =
        Y.presheaf.germ U' x hxU' (q.appLE V U' hU'V a) := fun U' hxU' hU'V a ↦
    congrArg (fun φ ↦ φ.hom a) (germ_stalkMap_eq_appLE_germ q hU'V x hxU' hxV)
  let σ : Γ(M, U₁) := ∑ i, q.appLE V U₁ hU₁V (f i) • t i
  have hσ : stalkGerm M U₁ x hxU₁ σ = stalkGerm M U₁ x hxU₁ 0 := by
    rw [map_zero, map_sum]
    simp only [stalkGerm_smul, ht, ← hφ U₁ hxU₁ hU₁V]
    exact hfm
  obtain ⟨W, hxW, hWU₁, hWU₁', hW⟩ := exists_res_eq_of_stalkGerm_eq M x hxU₁ hxU₁ σ 0 hσ
  obtain ⟨U₂, hxU₂, hU₂W, hU₂V, hflat⟩ := H W hxW
  have hU₂U₁ : U₂ ≤ U₁ := hU₂W.trans hWU₁
  let N := (ModuleCat.restrictScalars (q.appLE V U₂ hU₂V).hom).obj
    (ModuleCat.of Γ(Y, U₂) Γ(M, U₂))
  let t' : Fin l → N := fun i ↦ M.presheaf.map (homOfLE hU₂U₁).op (t i)
  have h0 : M.presheaf.map (homOfLE hU₂U₁).op σ = 0 := by
    calc M.presheaf.map (homOfLE hU₂U₁).op σ
        = M.presheaf.map (homOfLE hU₂W).op (M.presheaf.map (homOfLE hWU₁).op σ) := by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
      _ = 0 := by rw [hW, map_zero, map_zero]
  have hrel : ∑ i, f i • t' i = 0 := by
    refine Eq.trans ?_ h0
    simp only [σ, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change q.appLE V U₂ hU₂V (f i) • M.presheaf.map (homOfLE hU₂U₁).op (t i) =
      M.presheaf.map (homOfLE hU₂U₁).op (q.appLE V U₁ hU₁V (f i) • t i)
    rw [Scheme.Modules.map_smul]
    congr 1
    rw [← Scheme.Hom.appLE_map q hU₁V (homOfLE hU₂U₁).op]
    rfl
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, a, fun j ↦ stalkGerm M U₂ x hxU₂ (y j), fun i ↦ ?_, ha⟩
  rw [← ht i, ← stalkGerm_res M hU₂U₁ x hxU₂ (t i)]
  change stalkGerm M U₂ x hxU₂ (t' i) = _
  rw [hy i]
  change stalkGerm M U₂ x hxU₂ (∑ j, (q.appLE V U₂ hU₂V (a i j) • y j : Γ(M, U₂))) = _
  refine (map_sum (stalkGerm M U₂ x hxU₂) _ _).trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  change stalkGerm M U₂ x hxU₂ (q.appLE V U₂ hU₂V (a i j) • y j) =
    (T.presheaf.germ V (q x) hxV ≫ q.stalkMap x).hom (a i j) • stalkGerm M U₂ x hxU₂ (y j)
  rw [hφ U₂ hxU₂ hU₂V]
  exact stalkGerm_smul M U₂ x hxU₂ _ (y j)

section QuasiCoherent

variable {X : Scheme.{u}}

/-- On `Spec Γ(X, U)`, the scalar action of `Γ(X, U)` on sections restricted along
`IsAffineOpen.fromSpec` is the action of the restricted sections over `X`. -/
private theorem fromSpec_appIso_inv_ΓSpecIso {U : X.Opens} (hU : IsAffineOpen U)
    (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).inv ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
      X.presheaf.map (homOfLE
        ((hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le)).op r := by
  have e : W ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]; exact le_top
  have h1 : hU.fromSpec.appLE U W e r = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, IsAffineOpen.fromSpec_app_self,
      CommRingCat.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← h1, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_appIso_inv]

/-- Sections of a quasi-coherent module sheaf over a basic open `D(f)` of an affine open `U`
are, up to a power of `f`, restrictions of sections over `U`. -/
private theorem exists_res_eq_pow_smul (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (t : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (s : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op s =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • t := by
  let ι := hU.fromSpec
  let N := M.restrict ι
  have hloc := N.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent f
  have himg : ι ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  have htop : U ≤ ι ''ᵁ ⊤ :=
    ((Scheme.Hom.image_top_eq_opensRange ι).trans hU.opensRange_fromSpec).ge
  let t' : Γ(M, ι ''ᵁ PrimeSpectrum.basicOpen f) := M.presheaf.map (eqToHom himg).op t
  obtain ⟨⟨s₀, ⟨_, n, rfl⟩⟩, hs'⟩ := hloc.surj (show Γ(N, PrimeSpectrum.basicOpen f) from t')
  let s' : Γ(M, ι ''ᵁ ⊤) := s₀
  refine ⟨n, M.presheaf.map (homOfLE htop).op s', ?_⟩
  have hle : ι ''ᵁ PrimeSpectrum.basicOpen f ≤ U :=
    (ι.image_le_opensRange _).trans hU.opensRange_fromSpec.le
  have key : M.presheaf.map (homOfLE (ι.image_mono le_top)).op s' =
      X.presheaf.map (homOfLE hle).op (f ^ n) • t' := by
    refine hs'.symm.trans ?_
    change (hU.fromSpec.appIso (PrimeSpectrum.basicOpen f : (Spec Γ(X, U)).Opens)).inv
      ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv (f ^ n))) •
        t' = _
    exact congrArg (· • t') (fromSpec_appIso_inv_ΓSpecIso hU _ (f ^ n))
  have hDX : X.basicOpen f ≤ ι ''ᵁ PrimeSpectrum.basicOpen f := himg.ge
  calc M.presheaf.map (homOfLE (X.basicOpen_le f)).op (M.presheaf.map (homOfLE htop).op s')
      = M.presheaf.map (homOfLE hDX).op
          (M.presheaf.map (homOfLE (ι.image_mono le_top)).op s') := by
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl
    _ = M.presheaf.map (homOfLE hDX).op (X.presheaf.map (homOfLE hle).op (f ^ n) • t') := by
        rw [key]
    _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • t := by
        rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        congr 1
        change M.presheaf.map (homOfLE hDX).op (M.presheaf.map (eqToHom himg).op t) = t
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact congrArg (fun φ ↦ (M.presheaf.map φ).hom t) (Subsingleton.elim _ (𝟙 _)) |>.trans
          (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- A section of a quasi-coherent module sheaf over an affine open `U` that vanishes on a basic
open `D(f)` is killed by a power of `f`. -/
private theorem exists_pow_smul_eq_zero (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (s : Γ(M, U))
    (hs : M.presheaf.map (homOfLE (X.basicOpen_le f)).op s = 0) :
    ∃ n : ℕ, f ^ n • s = 0 := by
  let ι := hU.fromSpec
  let N := M.restrict ι
  have hloc := N.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent f
  have himg : ι ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  have htop' : ι ''ᵁ ⊤ ≤ U := (ι.image_le_opensRange _).trans hU.opensRange_fromSpec.le
  have htop : U ≤ ι ''ᵁ ⊤ :=
    ((Scheme.Hom.image_top_eq_opensRange ι).trans hU.opensRange_fromSpec).ge
  let s' : Γ(M, ι ''ᵁ ⊤) := M.presheaf.map (homOfLE htop').op s
  have h0 : (N.basicOpenRestriction f).hom
      (show (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤) from s') =
        (N.basicOpenRestriction f).hom 0 := by
    rw [map_zero]
    change M.presheaf.map (homOfLE (ι.image_mono le_top)).op s' = 0
    calc M.presheaf.map (homOfLE (ι.image_mono le_top)).op s'
        = M.presheaf.map (eqToHom himg).op
            (M.presheaf.map (homOfLE (X.basicOpen_le f)).op s) := by
          rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
            ← Functor.map_comp]
          rfl
      _ = 0 := by rw [hs, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := hloc.exists_of_eq h0
  refine ⟨n, ?_⟩
  rw [smul_zero] at hc
  have hc' : X.presheaf.map (homOfLE htop').op (f ^ n) • s' = 0 := by
    refine Eq.trans ?_ hc
    change _ = (hU.fromSpec.appIso ⊤).inv
      ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv (f ^ n))) •
        s'
    exact congrArg (· • s') (fromSpec_appIso_inv_ΓSpecIso hU ⊤ (f ^ n)).symm
  rw [← Scheme.Modules.map_smul] at hc'
  calc f ^ n • s = M.presheaf.map (homOfLE htop).op
        (M.presheaf.map (homOfLE htop').op (f ^ n • s)) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact (congrArg (fun φ ↦ (M.presheaf.map φ).hom (f ^ n • s))
          (Subsingleton.elim _ (𝟙 _)) |>.trans (by rw [CategoryTheory.Functor.map_id]; rfl)).symm
    _ = 0 := by rw [hc', map_zero]

private theorem mem_basicOpen_fromSpec_iff {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (g : Γ(X, U)) :
    hU.fromSpec y ∈ X.basicOpen g ↔ g ∉ y.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  rfl

private theorem mem_basicOpen_pow {U : X.Opens} {x : X} (hx : x ∈ U) (f : Γ(X, U)) (n : ℕ)
    (hxf : x ∈ X.basicOpen f) : x ∈ X.basicOpen (f ^ n) := by
  rw [X.mem_basicOpen _ _ hx, map_pow]
  exact ((X.mem_basicOpen _ _ hx).mp hxf).pow n

/-- For a quasi-coherent module sheaf and an affine open `U`, the germ map
`Γ(U, M) ⟶ M_x` is the localization at the prime of `x`. -/
private theorem isLocalizedModule_stalkGerm (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    IsLocalizedModule y.asIdeal.primeCompl (stalkGermLinearMap M U (hU.fromSpec y) hy) where
  map_units g := by
    obtain ⟨u, hu⟩ := (X.mem_basicOpen (g : Γ(X, U)) _ hy).mp
      ((mem_basicOpen_fromSpec_iff hU y g).mpr g.2)
    rw [Module.End.isUnit_iff]
    refine ⟨fun m m' h ↦ ?_, fun m ↦ ⟨(↑u⁻¹ : X.presheaf.stalk (hU.fromSpec y)) • m, ?_⟩⟩
    · change X.presheaf.germ U _ hy g • m = X.presheaf.germ U _ hy g • m' at h
      rw [← hu] at h
      have := congrArg (fun z ↦ (↑u⁻¹ : X.presheaf.stalk (hU.fromSpec y)) • z) h
      simpa only [smul_smul, Units.inv_mul, one_smul] using this
    · change X.presheaf.germ U _ hy g • (↑u⁻¹ : X.presheaf.stalk (hU.fromSpec y)) • m = m
      rw [← hu, smul_smul, Units.mul_inv, one_smul]
  surj m := by
    obtain ⟨W, hxW, t, rfl⟩ := exists_stalkGerm_eq M _ m
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨_, hxW⟩ hy
    obtain ⟨n, s, hs⟩ := exists_res_eq_pow_smul M hU f (M.presheaf.map (homOfLE hfW).op t)
    have hn : f ^ n ∈ y.asIdeal.primeCompl :=
      (mem_basicOpen_fromSpec_iff hU y _).mp (mem_basicOpen_pow hy f n hxf)
    refine ⟨⟨s, ⟨f ^ n, hn⟩⟩, ?_⟩
    change X.presheaf.germ U _ hy (f ^ n) • stalkGerm M W _ hxW t = stalkGerm M U _ hy s
    rw [← stalkGerm_res M (X.basicOpen_le f) _ hxf s, hs, stalkGerm_smul, stalkGerm_res,
      TopCat.Presheaf.germ_res_apply]
  exists_of_eq {s₁ s₂} h := by
    have h' : stalkGerm M U _ hy (s₁ - s₂) = stalkGerm M U _ hy 0 := by
      rw [map_sub, map_zero, sub_eq_zero]; exact h
    obtain ⟨W, hxW, hWU, hWU', hW⟩ := exists_res_eq_of_stalkGerm_eq M _ hy hy _ _ h'
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨_, hxW⟩ hy
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero M hU f (s₁ - s₂) (by
      calc M.presheaf.map (homOfLE (X.basicOpen_le f)).op (s₁ - s₂)
          = M.presheaf.map (homOfLE hfW).op (M.presheaf.map (homOfLE hWU).op (s₁ - s₂)) := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
        _ = 0 := by rw [hW, map_zero, map_zero])
    refine ⟨⟨f ^ n, (mem_basicOpen_fromSpec_iff hU y _).mp (mem_basicOpen_pow hy f n hxf)⟩, ?_⟩
    change f ^ n • s₁ = f ^ n • s₂
    rwa [smul_sub, sub_eq_zero] at hn

end QuasiCoherent

/-- Flatness over the base transports along isomorphisms of module sheaves. -/
theorem IsFlatOver.of_iso {X S : Scheme.{u}} {p : X ⟶ S} {M N : X.Modules} (e : M ≅ N)
    (h : IsFlatOver p M) : IsFlatOver p N := fun x ↦
  have := h x
  Module.Flat.of_linearEquiv ((ModuleCat.restrictScalars (p.stalkMap x).hom).mapIso
    ((moduleStalkFunctor X x).mapIso e)).symm.toLinearEquiv

/-- A zero module sheaf is flat over every base, since each of its stalks is zero. -/
theorem IsFlatOver.of_isZero {X S : Scheme.{u}} {p : X ⟶ S} {M : X.Modules} (hM : IsZero M) :
    IsFlatOver p M := fun x ↦ by
  have := moduleStalkFunctor_preservesFiniteLimits X x
  have : Subsingleton ((moduleStalkFunctor X x).obj M) :=
    ModuleCat.subsingleton_of_isZero ((moduleStalkFunctor X x).map_isZero hM)
  have : Subsingleton ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((moduleStalkFunctor X x).obj M)) := this
  infer_instance

/-- Flatness over the base follows from flatness of sections over affine opens: if
`Γ(U, M)` is flat over `Γ(V, 𝒪_T)`, through `q.appLE V U`, for all affine opens `U ⊆ Y`,
`V ⊆ T` with `q(U) ⊆ V`, then `M` is flat over `T`.

No hypothesis on `M` is needed. The stalk `M_x` is the filtered colimit of the sections over
affine neighbourhoods of `x`, and the equational criterion for flatness passes to it. -/
theorem isFlatOver_of_affine {Y T : Scheme.{u}} (q : Y ⟶ T) (M : Y.Modules)
    (h : ∀ (U : Y.affineOpens) (V : T.affineOpens) (hUV : U.1 ≤ q ⁻¹ᵁ V.1),
      Module.Flat Γ(T, V.1) ((ModuleCat.restrictScalars (q.appLE V.1 U.1 hUV).hom).obj
        (ModuleCat.of Γ(Y, U.1) Γ(M, U.1)))) :
    IsFlatOver q M := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens (Opens.mem_top (q x))
  refine (flat_stalk_iff q M x hV hxV).mpr (flat_stalk_of_forall_nhds q M x hxV fun W hxW ↦ ?_)
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show x ∈ W ⊓ q ⁻¹ᵁ V from ⟨hxW, hxV⟩)
  exact ⟨U, hxU, hUW.trans inf_le_left, hUW.trans inf_le_right,
    h ⟨U, hU⟩ ⟨V, hV⟩ (hUW.trans inf_le_right)⟩

/-- **Flatness over the base is affine-local.** A quasi-coherent `M` is flat over `T` exactly
when `Γ(U, M)` is flat over `Γ(V, 𝒪_T)`, through `q.appLE V U`, for all affine opens `U ⊆ Y`,
`V ⊆ T` with `q(U) ⊆ V`.

Quasi-coherence is used only in the forward direction, where it makes the germ map
`Γ(U, M) ⟶ M_x` the localization at the prime of `x`. The reverse direction is
`isFlatOver_of_affine` and holds for every module sheaf. No witness is known here that the
forward direction fails without quasi-coherence. -/
@[stacks 01U4]
theorem isFlatOver_iff_affine {Y T : Scheme.{u}} (q : Y ⟶ T) (M : Y.Modules)
    [M.IsQuasicoherent] :
    IsFlatOver q M ↔ ∀ (U : Y.affineOpens) (V : T.affineOpens) (hUV : U.1 ≤ q ⁻¹ᵁ V.1),
      Module.Flat Γ(T, V.1) ((ModuleCat.restrictScalars (q.appLE V.1 U.1 hUV).hom).obj
        (ModuleCat.of Γ(Y, U.1) Γ(M, U.1))) := by
  refine ⟨fun hM ⟨U, hU⟩ ⟨V, hV⟩ hUV ↦ ?_, isFlatOver_of_affine q M⟩
  dsimp only at hUV ⊢
  let : Algebra Γ(T, V) Γ(Y, U) := (q.appLE V U hUV).hom.toAlgebra
  let N := (ModuleCat.restrictScalars (q.appLE V U hUV).hom).obj (ModuleCat.of Γ(Y, U) Γ(M, U))
  let : Module Γ(Y, U) N := inferInstanceAs (Module Γ(Y, U) Γ(M, U))
  have : IsScalarTower Γ(T, V) Γ(Y, U) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let pt : ∀ (P : Ideal Γ(Y, U)) [P.IsMaximal], PrimeSpectrum Γ(Y, U) :=
    fun P h ↦ ⟨P, h.isPrime⟩
  have hpt : ∀ (P : Ideal Γ(Y, U)) [P.IsMaximal], hU.fromSpec (pt P) ∈ U := fun P _ ↦ by
    have := Set.mem_range_self (f := hU.fromSpec) (pt P)
    rwa [hU.range_fromSpec] at this
  let Mₚ : ∀ (P : Ideal Γ(Y, U)) [P.IsMaximal], Type u := fun P _ ↦
    (ModuleCat.restrictScalars (Y.presheaf.germ U _ (hpt P)).hom).obj
      ((moduleStalkFunctor Y (hU.fromSpec (pt P))).obj M)
  let instA : ∀ (P : Ideal Γ(Y, U)) [P.IsMaximal], Module Γ(T, V) (Mₚ P) := fun P _ ↦
    Module.compHom _ (algebraMap Γ(T, V) Γ(Y, U))
  have instT : ∀ (P : Ideal Γ(Y, U)) [P.IsMaximal],
      letI := instA P; IsScalarTower Γ(T, V) Γ(Y, U) (Mₚ P) :=
    fun P _ ↦ by letI := instA P; exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have instL : ∀ (P : Ideal Γ(Y, U)) [P.IsMaximal],
      IsLocalizedModule.AtPrime P (stalkGermLinearMap M U _ (hpt P)) :=
    fun P _ ↦ isLocalizedModule_stalkGerm M hU (pt P) (hpt P)
  refine @Module.flat_of_isLocalized_maximal _ Γ(Y, U) _ _ _ N _ _ _ _ Mₚ
    (fun P _ ↦ inferInstanceAs (AddCommMonoid ((ModuleCat.restrictScalars
      (Y.presheaf.germ U _ (hpt P)).hom).obj ((moduleStalkFunctor Y (hU.fromSpec (pt P))).obj M))))
    instA
    (fun P _ ↦ inferInstanceAs (Module Γ(Y, U) ((ModuleCat.restrictScalars
      (Y.presheaf.germ U _ (hpt P)).hom).obj ((moduleStalkFunctor Y (hU.fromSpec (pt P))).obj M))))
    instT (fun P _ ↦ stalkGermLinearMap M U _ (hpt P)) instL fun P _ ↦ ?_
  have h := (flat_stalk_iff q M _ hV (hUV (hpt P))).mp (hM _)
  let := instA P
  let e : Mₚ P ≃ₗ[Γ(T, V)] (ModuleCat.restrictScalars
      (T.presheaf.germ V _ (hUV (hpt P)) ≫ q.stalkMap (hU.fromSpec (pt P))).hom).obj
        ((moduleStalkFunctor Y (hU.fromSpec (pt P))).obj M) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a m ↦ by
        change Y.presheaf.germ U _ (hpt P) (q.appLE V U hUV a) • m =
          (T.presheaf.germ V _ (hUV (hpt P)) ≫ q.stalkMap (hU.fromSpec (pt P))).hom a • m
        exact congrArg (· • m) (congrArg (fun φ ↦ φ.hom a)
          (germ_stalkMap_eq_appLE_germ q hUV _ (hpt P) (hUV (hpt P)))).symm }
  exact Module.Flat.of_linearEquiv e

/-- **Flatness at a point from one affine chart.** Let `M` be quasi-coherent, `U ⊆ Y` and
`V ⊆ T` affine opens with `q(U) ⊆ V`, and `x ∈ U`. If some localization `N` of `Γ(U, M)` at a
submonoid of `Γ(Y, U)` that does not vanish at `x` is flat over `Γ(T, V)`, through
`q.appLE V U`, then the stalk `M_x` is flat over `𝒪_{T, q x}`.

The stalk `M_x` localizes `N` further at the prime of `x`, as quasi-coherence makes the germ map
`Γ(U, M) ⟶ M_x` a localization there. The submonoid `{1}`, with `N = Γ(U, M)`, gives flatness
at every point of `U` from flatness of the sections. -/
theorem flat_stalk_of_isLocalizedModule {Y T : Scheme.{u}} (q : Y ⟶ T) (M : Y.Modules)
    [M.IsQuasicoherent] {U : Y.Opens} {V : T.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ q ⁻¹ᵁ V) {x : Y} (hx : x ∈ U) (Sm : Submonoid Γ(Y, U))
    (hSm : ∀ s ∈ Sm, x ∈ Y.basicOpen s) {N : Type u} [AddCommGroup N] [Module Γ(Y, U) N]
    (g : Γ(M, U) →ₗ[Γ(Y, U)] N) [IsLocalizedModule Sm g]
    (hN : Module.Flat Γ(T, V) ((ModuleCat.restrictScalars (q.appLE V U hUV).hom).obj
      (ModuleCat.of Γ(Y, U) N))) :
    Module.Flat (T.presheaf.stalk (q x))
      ((ModuleCat.restrictScalars (q.stalkMap x).hom).obj ((moduleStalkFunctor Y x).obj M)) := by
  obtain ⟨y, rfl⟩ : ∃ y : PrimeSpectrum Γ(Y, U), hU.fromSpec y = x :=
    ⟨_, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
  have hle : Sm ≤ y.asIdeal.primeCompl := fun s hs ↦
    (mem_basicOpen_fromSpec_iff hU y s).mp (hSm s hs)
  have := isLocalizedModule_stalkGerm M hU y hx
  let ℓ := IsLocalizedModule.liftOfLE Sm y.asIdeal.primeCompl hle g (stalkGermLinearMap M U _ hx)
  let : Algebra Γ(T, V) Γ(Y, U) := (q.appLE V U hUV).hom.toAlgebra
  let : Module Γ(T, V) N := Module.compHom N (algebraMap Γ(T, V) Γ(Y, U))
  have : IsScalarTower Γ(T, V) Γ(Y, U) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat Γ(T, V) N := hN
  let Mx := (ModuleCat.restrictScalars (Y.presheaf.germ U _ hx).hom).obj
    ((moduleStalkFunctor Y (hU.fromSpec y)).obj M)
  let : Module Γ(T, V) Mx := Module.compHom Mx (algebraMap Γ(T, V) Γ(Y, U))
  have : IsScalarTower Γ(T, V) Γ(Y, U) Mx := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat Γ(T, V) Mx := flat_of_isLocalizedModule_of_flat y.asIdeal.primeCompl ℓ
  refine (flat_stalk_iff q M _ hV (hUV hx)).mpr ?_
  let e : (ModuleCat.restrictScalars
      (T.presheaf.germ V _ (hUV hx) ≫ q.stalkMap (hU.fromSpec y)).hom).obj
        ((moduleStalkFunctor Y (hU.fromSpec y)).obj M) ≃ₗ[Γ(T, V)] Mx :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a m ↦ by
        change (T.presheaf.germ V _ (hUV hx) ≫ q.stalkMap (hU.fromSpec y)).hom a • m =
          Y.presheaf.germ U _ hx (q.appLE V U hUV a) • m
        exact congrArg (· • m) (congrArg (fun φ ↦ φ.hom a)
          (germ_stalkMap_eq_appLE_germ q hUV _ hx (hUV hx))) }
  exact Module.Flat.of_linearEquiv e

/-- **Base change of flatness, at a point.** For a pullback square `P = Y ×_T T'` with
projections `fst : P ⟶ Y` and `snd : P ⟶ T'`, if the stalk of `M` at `fst z` is flat over
`𝒪_{T, q (fst z)}`, then the stalk at `z` of the pullback of `M` along `fst` is flat over
`𝒪_{T', snd z}`.

No quasi-coherence is assumed. The stalk of the pullback is `𝒪_{P,z} ⊗ M_y`
(`pullbackStalkIso`), and over affine opens the local ring `𝒪_{P,z}` is a localization of the
pushout `Γ(U) ⊗_{Γ(V)} Γ(V')` of sections (`isIso_pushoutSection_of_isAffineOpen`). The square
is any `IsPullback` square, not only the chosen pullback, so that restriction to an open of the
base and pasting of pullbacks need no comparison of fibre products. -/
theorem flat_stalk_of_isPullback {P Y T T' : Scheme.{u}} {fst : P ⟶ Y} {snd : P ⟶ T'}
    {q : Y ⟶ T} {h : T' ⟶ T} (H : IsPullback fst snd q h) (M : Y.Modules) (z : P)
    (hM : Module.Flat (T.presheaf.stalk (q (fst z)))
      ((ModuleCat.restrictScalars (q.stalkMap (fst z)).hom).obj
        ((moduleStalkFunctor Y (fst z)).obj M))) :
    Module.Flat (T'.presheaf.stalk (snd z))
      ((ModuleCat.restrictScalars (snd.stalkMap z).hom).obj
        ((moduleStalkFunctor P z).obj ((Scheme.Modules.pullback fst).obj M))) := by
  have hcond : q (fst z) = h (snd z) := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hV, hyV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens (Opens.mem_top (q (fst z)))
  obtain ⟨U, hU, hyU, hUV⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show fst z ∈ q ⁻¹ᵁ V from hyV)
  obtain ⟨V', hV', hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show snd z ∈ h ⁻¹ᵁ V from (show h (snd z) ∈ V by rw [← hcond]; exact hyV))
  let W := fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V'
  have hzW : z ∈ W := ⟨hyU, hzV'⟩
  have hpush := (isIso_pushoutSection_iff H hV'V hUV (UY := W) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hV'V hUV rfl hV hV' hU)
  have hW : IsAffineOpen W := by
    have : IsAffine _ := hV
    have : IsAffine _ := hV'
    have : IsAffine _ := hU
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hV'V hUV rfl).isoPullback.hom
  have hUW : W ≤ fst ⁻¹ᵁ U := inf_le_left
  have hV'W : W ≤ snd ⁻¹ᵁ V' := inf_le_right
  -- The pushout square of sections `Γ(V) → Γ(U), Γ(V') → Γ(W)`.
  let : Algebra Γ(T, V) Γ(Y, U) := (q.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(T, V) Γ(T', V') := (h.appLE V V' hV'V).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(P, W) := (fst.appLE U W hUW).hom.toAlgebra
  let : Algebra Γ(T', V') Γ(P, W) := (snd.appLE V' W hV'W).hom.toAlgebra
  let : Algebra Γ(T, V) Γ(P, W) :=
    (q.appLE V U hUV ≫ fst.appLE U W hUW).hom.toAlgebra
  have : IsScalarTower Γ(T, V) Γ(Y, U) Γ(P, W) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(T, V) Γ(T', V') Γ(P, W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(T, V) Γ(T', V') Γ(Y, U) Γ(P, W) :=
    (CommRingCat.isPushout_iff_isPushout.mp hpush).symm
  -- The local rings at `fst z` and `z` localize `Γ(U)` and `Γ(W)`.
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (fst z)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨fst z, hyU⟩
  have := hU.isLocalization_stalk ⟨fst z, hyU⟩
  let : Algebra Γ(P, W) (P.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨z, hzW⟩
  have := hW.isLocalization_stalk ⟨z, hzW⟩
  let : Algebra (Y.presheaf.stalk (fst z)) (P.presheaf.stalk z) :=
    (fst.stalkMap z).hom.toAlgebra
  let : Algebra Γ(Y, U) (P.presheaf.stalk z) :=
    (Y.presheaf.germ U (fst z) hyU ≫ fst.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (fst z))
      (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Γ(P, W)
      (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (germ_stalkMap_eq_appLE_germ fst hUW z hzW hyU))
  let : Algebra Γ(T', V') (P.presheaf.stalk z) :=
    (T'.presheaf.germ V' (snd z) hzV' ≫ snd.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(T', V') Γ(P, W)
      (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (germ_stalkMap_eq_appLE_germ snd hV'W z hzW hzV'))
  -- The stalk `M_y`, flat over `Γ(V)`.
  let My := (moduleStalkFunctor Y (fst z)).obj M
  let : Module Γ(Y, U) My :=
    Module.compHom My (algebraMap Γ(Y, U) (Y.presheaf.stalk (fst z)))
  let : Module Γ(T, V) My := Module.compHom My
    ((algebraMap Γ(Y, U) (Y.presheaf.stalk (fst z))).comp (algebraMap Γ(T, V) Γ(Y, U)))
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (fst z)) My :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(T, V) Γ(Y, U) My := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat Γ(T, V) My := by
    have := (flat_stalk_iff q M (fst z) hV hyV).mp hM
    let e : My ≃ₗ[Γ(T, V)] (ModuleCat.restrictScalars
        (T.presheaf.germ V (q (fst z)) hyV ≫ q.stalkMap (fst z)).hom).obj My :=
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ by
          change Y.presheaf.germ U _ hyU (q.appLE V U hUV a) • m =
            (T.presheaf.germ V _ hyV ≫ q.stalkMap (fst z)).hom a • m
          exact congrArg (· • m) (congrArg (fun φ ↦ φ.hom a)
            (germ_stalkMap_eq_appLE_germ q hUV _ hyU hyV)).symm }
    exact Module.Flat.of_linearEquiv e
  have := flat_tensor_of_isPushout (A := Γ(T, V)) (A' := Γ(T', V')) (B := Γ(Y, U))
    (C := Γ(P, W)) (L := Y.presheaf.stalk (fst z))
    (D := P.presheaf.stalk z) (hU.primeIdealOf ⟨fst z, hyU⟩).asIdeal.primeCompl
    (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.primeCompl My
  -- The stalk of the pullback is `𝒪_{P,z} ⊗ M_y`.
  refine (flat_stalk_iff snd _ z hV' hzV').mpr ?_
  let e₁ := ((ModuleCat.restrictScalars (T'.presheaf.germ V' (snd z) hzV' ≫
    snd.stalkMap z).hom).mapIso ((pullbackStalkIso fst z).app M)).toLinearEquiv
  let e₂ : (ModuleCat.restrictScalars (T'.presheaf.germ V' (snd z) hzV' ≫
      snd.stalkMap z).hom).obj ((ModuleCat.extendScalars (fst.stalkMap z).hom).obj My) ≃ₗ[Γ(T', V')]
        P.presheaf.stalk z ⊗[Y.presheaf.stalk (fst z)] My :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Flat.of_linearEquiv (e₁.trans e₂)

/-- **Flatness over the base is stable under base change**, along any pullback square. For
`q : Y ⟶ T`, `h : T' ⟶ T` and a pullback square `P` with projections `fst : P ⟶ Y` and
`snd : P ⟶ T'`, if `M` is flat over `T` then `fst^* M` is flat over `T'` through `snd`. No
quasi-coherence is assumed; this is `flat_stalk_of_isPullback` at every point. -/
@[stacks 01U8]
theorem IsFlatOver.of_isPullback {P Y T T' : Scheme.{u}} {fst : P ⟶ Y} {snd : P ⟶ T'}
    {q : Y ⟶ T} {h : T' ⟶ T} (H : IsPullback fst snd q h) {M : Y.Modules}
    (hM : IsFlatOver q M) :
    IsFlatOver snd ((Scheme.Modules.pullback fst).obj M) := fun z ↦
  flat_stalk_of_isPullback H M z (hM _)

/-- **Flatness over the base is stable under base change.** For `q : Y ⟶ T` and `h : T' ⟶ T`,
if `M` is flat over `T` then its pullback along the projection `Y ×_T T' ⟶ Y` is flat over
`T'` through the other projection. This is `IsFlatOver.of_isPullback` for the chosen fibre
product. -/
@[stacks 01U8]
theorem isFlatOver_pullback {Y T T' : Scheme.{u}} (q : Y ⟶ T) (h : T' ⟶ T) (M : Y.Modules)
    (hM : IsFlatOver q M) :
    IsFlatOver (Limits.pullback.snd q h)
      ((Scheme.Modules.pullback (Limits.pullback.fst q h)).obj M) :=
  hM.of_isPullback (IsPullback.of_hasPullback q h)

/-- A module sheaf flat over the identity is flat over every flat morphism: its stalks are flat
over the local rings of `X`, which are flat over the local rings of `S`. -/
theorem IsFlatOver.of_isFlatOver_id {X S : Scheme.{u}} {p : X ⟶ S} [Flat p] {M : X.Modules}
    (hM : IsFlatOver (𝟙 X) M) : IsFlatOver p M := fun x ↦ by
  have h := (isFlatOverId_iff_stalkwiseFlat X M).1 hM x
  let : Algebra (S.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (p x)) (X.presheaf.stalk x) := Flat.stalkMap p x
  let Mx := (moduleStalkFunctor X x).obj M
  let : Module (S.presheaf.stalk (p x)) Mx := Module.compHom Mx (p.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (p x)) (X.presheaf.stalk x) Mx :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans (S.presheaf.stalk (p x)) (X.presheaf.stalk x) Mx

/-- In a short exact sequence of module sheaves whose middle and right terms are flat over the
base, the left term is flat over the base. Stalks are exact, so this is the statement for
modules, a consequence of `LinearMap.lTensor_injective_of_exact_of_flat`. -/
theorem IsFlatOver.of_shortExact {X S : Scheme.{u}} {p : X ⟶ S} {Sc : ShortComplex X.Modules}
    (hS : Sc.ShortExact) (h₂ : IsFlatOver p Sc.X₂) (h₃ : IsFlatOver p Sc.X₃) :
    IsFlatOver p Sc.X₁ := fun x ↦ by
  have := moduleStalkFunctor_preservesFiniteLimits X x
  have := moduleStalkFunctor_preservesFiniteColimits X x
  have hS' := hS.map_of_exact (moduleStalkFunctor X x)
  have := h₂ x
  have := h₃ x
  let r := (p.stalkMap x).hom
  have hg : Function.Injective ((moduleStalkFunctor X x).map Sc.f).hom :=
    (ModuleCat.mono_iff_injective (Sc.map (moduleStalkFunctor X x)).f).1 hS'.mono_f
  have hf : Function.Surjective ((moduleStalkFunctor X x).map Sc.g).hom :=
    (ModuleCat.epi_iff_surjective (Sc.map (moduleStalkFunctor X x)).g).1 hS'.epi_g
  have hgf : Function.Exact ((moduleStalkFunctor X x).map Sc.f).hom
      ((moduleStalkFunctor X x).map Sc.g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact
  exact flat_of_exact_of_flat
    (g := ((ModuleCat.restrictScalars r).map ((moduleStalkFunctor X x).map Sc.f)).hom)
    (f := ((ModuleCat.restrictScalars r).map ((moduleStalkFunctor X x).map Sc.g)).hom)
    hg hf hgf

/-- Flatness over the base is closed under binary biproducts: the stalk of `M ⊞ N` is the
product of the stalks, by the split short exact sequence `M → M ⊞ N → N`. -/
theorem IsFlatOver.biprod {X S : Scheme.{u}} {p : X ⟶ S} {M N : X.Modules}
    (hM : IsFlatOver p M) (hN : IsFlatOver p N) : IsFlatOver p (M ⊞ N) := by
  have hS : (ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) biprod.snd (by simp)).ShortExact :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact
  intro x
  have := moduleStalkFunctor_preservesFiniteLimits X x
  have := moduleStalkFunctor_preservesFiniteColimits X x
  have hS' := hS.map_of_exact (moduleStalkFunctor X x)
  have := hM x
  have := hN x
  let st := moduleStalkFunctor X x
  let F := ModuleCat.restrictScalars (p.stalkMap x).hom
  let g := (F.map (st.map (biprod.inl : M ⟶ M ⊞ N))).hom
  let f := (F.map (st.map (biprod.snd : M ⊞ N ⟶ N))).hom
  have hg : Function.Injective (st.map (biprod.inl : M ⟶ M ⊞ N)).hom :=
    (ModuleCat.mono_iff_injective
      ((ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) biprod.snd (by simp)).map st).f).1 hS'.mono_f
  have hgf : Function.Exact (st.map (biprod.inl : M ⟶ M ⊞ N)).hom
      (st.map (biprod.snd : M ⊞ N ⟶ N)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact
  let s := (F.map (st.map (biprod.inr : N ⟶ M ⊞ N))).hom
  have hs : f.comp s = LinearMap.id := by
    ext n
    change (st.map biprod.inr ≫ st.map biprod.snd).hom n = n
    rw [← st.map_comp, biprod.inr_snd, st.map_id]
    rfl
  let e := ((show Function.Exact g f from hgf).splitSurjectiveEquiv hg ⟨s, hs⟩).1
  have : Module.Flat (S.presheaf.stalk (p x)) (F.obj (st.obj M) × F.obj (st.obj N)) :=
    flat_prod
  exact Module.Flat.of_linearEquiv e

/-- **Exactness of base change at a point.** For a pullback square `P = Y ×_T T'` and a short
exact sequence `0 → M₁ → M₂ → M₃ → 0` of module sheaves on `Y` whose stalk `M₃` at `fst z` is
flat over `𝒪_{T, q (fst z)}`, the map of stalks at `z` of the pullbacks of `M₁ → M₂` along `fst`
is injective.

The stalks of the pullbacks are `𝒪_{P,z} ⊗ M_{i, fst z}` (`pullbackStalkIso`), and over affine
opens `𝒪_{P,z}` is a localization of the pushout of sections, as in
`flat_stalk_of_isPullback`. -/
private theorem mono_stalk_pullback_of_isPullback {P Y T T' : Scheme.{u}} {fst : P ⟶ Y}
    {snd : P ⟶ T'} {q : Y ⟶ T} {h : T' ⟶ T} (H : IsPullback fst snd q h)
    {Sc : ShortComplex Y.Modules} (hS : Sc.ShortExact) (z : P)
    (hM : Module.Flat (T.presheaf.stalk (q (fst z)))
      ((ModuleCat.restrictScalars (q.stalkMap (fst z)).hom).obj
        ((moduleStalkFunctor Y (fst z)).obj Sc.X₃))) :
    Mono ((ModuleCat.extendScalars (fst.stalkMap z).hom).map
      ((moduleStalkFunctor Y (fst z)).map Sc.f)) := by
  have hcond : q (fst z) = h (snd z) := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hV, hyV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens (Opens.mem_top (q (fst z)))
  obtain ⟨U, hU, hyU, hUV⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show fst z ∈ q ⁻¹ᵁ V from hyV)
  obtain ⟨V', hV', hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show snd z ∈ h ⁻¹ᵁ V from (show h (snd z) ∈ V by rw [← hcond]; exact hyV))
  let W := fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V'
  have hzW : z ∈ W := ⟨hyU, hzV'⟩
  have hpush := (isIso_pushoutSection_iff H hV'V hUV (UY := W) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hV'V hUV rfl hV hV' hU)
  have hW : IsAffineOpen W := by
    have : IsAffine _ := hV
    have : IsAffine _ := hV'
    have : IsAffine _ := hU
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hV'V hUV rfl).isoPullback.hom
  have hUW : W ≤ fst ⁻¹ᵁ U := inf_le_left
  have hV'W : W ≤ snd ⁻¹ᵁ V' := inf_le_right
  -- The pushout square of sections `Γ(V) → Γ(U), Γ(V') → Γ(W)`.
  let : Algebra Γ(T, V) Γ(Y, U) := (q.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(T, V) Γ(T', V') := (h.appLE V V' hV'V).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(P, W) := (fst.appLE U W hUW).hom.toAlgebra
  let : Algebra Γ(T', V') Γ(P, W) := (snd.appLE V' W hV'W).hom.toAlgebra
  let : Algebra Γ(T, V) Γ(P, W) :=
    (q.appLE V U hUV ≫ fst.appLE U W hUW).hom.toAlgebra
  have : IsScalarTower Γ(T, V) Γ(Y, U) Γ(P, W) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(T, V) Γ(T', V') Γ(P, W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(T, V) Γ(T', V') Γ(Y, U) Γ(P, W) :=
    (CommRingCat.isPushout_iff_isPushout.mp hpush).symm
  -- The local rings at `fst z` and `z` localize `Γ(U)` and `Γ(W)`.
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (fst z)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨fst z, hyU⟩
  have := hU.isLocalization_stalk ⟨fst z, hyU⟩
  let : Algebra Γ(P, W) (P.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨z, hzW⟩
  have := hW.isLocalization_stalk ⟨z, hzW⟩
  let : Algebra (Y.presheaf.stalk (fst z)) (P.presheaf.stalk z) :=
    (fst.stalkMap z).hom.toAlgebra
  let : Algebra Γ(Y, U) (P.presheaf.stalk z) :=
    (Y.presheaf.germ U (fst z) hyU ≫ fst.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (fst z))
      (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Γ(P, W)
      (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (germ_stalkMap_eq_appLE_germ fst hUW z hzW hyU))
  -- The stalks `M_{i, y}`, with `M_{3, y}` flat over `Γ(V)`.
  let L := Y.presheaf.stalk (fst z)
  let st := moduleStalkFunctor Y (fst z)
  let φB := algebraMap Γ(Y, U) L
  let φA := φB.comp (algebraMap Γ(T, V) Γ(Y, U))
  let M₁ := st.obj Sc.X₁
  let M₂ := st.obj Sc.X₂
  let M₃ := st.obj Sc.X₃
  let : Module Γ(Y, U) M₁ := Module.compHom M₁ φB
  let : Module Γ(Y, U) M₂ := Module.compHom M₂ φB
  let : Module Γ(Y, U) M₃ := Module.compHom M₃ φB
  let : Module Γ(T, V) M₁ := Module.compHom M₁ φA
  let : Module Γ(T, V) M₂ := Module.compHom M₂ φA
  let : Module Γ(T, V) M₃ := Module.compHom M₃ φA
  have : IsScalarTower Γ(Y, U) L M₁ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(Y, U) L M₂ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(Y, U) L M₃ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(T, V) Γ(Y, U) M₁ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(T, V) Γ(Y, U) M₂ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(T, V) Γ(Y, U) M₃ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat Γ(T, V) M₃ := by
    have := (flat_stalk_iff q Sc.X₃ (fst z) hV hyV).mp hM
    let e : M₃ ≃ₗ[Γ(T, V)] (ModuleCat.restrictScalars
        (T.presheaf.germ V (q (fst z)) hyV ≫ q.stalkMap (fst z)).hom).obj M₃ :=
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ by
          change Y.presheaf.germ U _ hyU (q.appLE V U hUV a) • m =
            (T.presheaf.germ V _ hyV ≫ q.stalkMap (fst z)).hom a • m
          exact congrArg (· • m) (congrArg (fun φ ↦ φ.hom a)
            (germ_stalkMap_eq_appLE_germ q hUV _ hyU hyV)).symm }
    exact Module.Flat.of_linearEquiv e
  have := moduleStalkFunctor_preservesFiniteLimits Y (fst z)
  have := moduleStalkFunctor_preservesFiniteColimits Y (fst z)
  have hS' := hS.map_of_exact st
  have hinj := injective_baseChange_of_isPushout (A := Γ(T, V)) (A' := Γ(T', V'))
    (B := Γ(Y, U)) (C := Γ(P, W)) (L := L) (D := P.presheaf.stalk z)
    (hU.primeIdealOf ⟨fst z, hyU⟩).asIdeal.primeCompl
    (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.primeCompl
    (g := (st.map Sc.f).hom) (f := (st.map Sc.g).hom)
    ((ModuleCat.mono_iff_injective (Sc.map st).f).1 hS'.mono_f)
    ((ModuleCat.epi_iff_surjective (Sc.map st).g).1 hS'.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact)
  rw [ModuleCat.mono_iff_injective]
  exact hinj

/-- **Base change is exact on sequences with a quotient flat over the base**, along any pullback
square. For `q : Y ⟶ T`, `h : T' ⟶ T` and a pullback square `P` with projections `fst : P ⟶ Y`
and `snd : P ⟶ T'`, pullback along `fst` keeps a short exact sequence of module sheaves on `Y`
short exact as soon as its quotient is flat over `T`.

No flatness of `q` and no quasi-coherence is assumed. Pullback is right exact, and injectivity is
checked on stalks, where it comes from the injectivity of `A' ⊗[A] M₁ → A' ⊗[A] M₂` for affine
sections `A ⟶ A'` of the base: `M₃` is flat over `A`. -/
theorem pullback_shortExact_of_isPullback {P Y T T' : Scheme.{u}} {fst : P ⟶ Y}
    {snd : P ⟶ T'} {q : Y ⟶ T} {h : T' ⟶ T} (H : IsPullback fst snd q h)
    {Sc : ShortComplex Y.Modules} (hS : Sc.ShortExact) (h₃ : IsFlatOver q Sc.X₃) :
    (Sc.map (Scheme.Modules.pullback fst)).ShortExact := by
  have (z : P) := moduleStalkFunctor_preservesFiniteLimits P z
  have (z : P) := moduleStalkFunctor_preservesFiniteColimits P z
  rw [(moduleStalkFunctors_jointlyReflectIsomorphisms P).shortExact_iff]
  intro z
  have := moduleStalkFunctor_preservesFiniteLimits Y (fst z)
  have := moduleStalkFunctor_preservesFiniteColimits Y (fst z)
  let r := (fst.stalkMap z).hom
  let S' := (Sc.map (moduleStalkFunctor Y (fst z))).map (ModuleCat.extendScalars r)
  let e : (Sc.map (Scheme.Modules.pullback fst)).map (moduleStalkFunctor P z) ≅ S' :=
    ShortComplex.isoMk ((pullbackStalkIso fst z).app _) ((pullbackStalkIso fst z).app _)
      ((pullbackStalkIso fst z).app _) ((pullbackStalkIso fst z).hom.naturality Sc.f).symm
      ((pullbackStalkIso fst z).hom.naturality Sc.g).symm
  refine ShortComplex.shortExact_of_iso e.symm ?_
  have hS' := hS.map_of_exact (moduleStalkFunctor Y (fst z))
  have hmono : Mono S'.f := mono_stalk_pullback_of_isPullback H hS z (h₃ _)
  have hepi : Epi (Sc.map (moduleStalkFunctor Y (fst z))).g := hS'.epi_g
  have hex : S'.Exact :=
    hS'.exact.map_of_epi_of_preservesCokernel _ hepi inferInstance
  have hepi' : Epi S'.g := by
    change Epi ((ModuleCat.extendScalars r).map _)
    infer_instance
  exact ShortComplex.ShortExact.mk' hex hmono hepi'

/-- **Base change is exact on sequences with a quotient flat over the base.** For `q : Y ⟶ T`
and `h : T' ⟶ T`, pullback along the projection `Y ×_T T' ⟶ Y` keeps a short exact sequence of
module sheaves on `Y` short exact as soon as its quotient is flat over `T`. This is
`pullback_shortExact_of_isPullback` for the chosen fibre product; no flatness of `q` is used. -/
theorem pullback_shortExact_of_isFlatOver {Y T T' : Scheme.{u}} (q : Y ⟶ T) (h : T' ⟶ T)
    {Sc : ShortComplex Y.Modules} (hS : Sc.ShortExact) (h₃ : IsFlatOver q Sc.X₃) :
    (Sc.map (Scheme.Modules.pullback (Limits.pullback.fst q h))).ShortExact :=
  pullback_shortExact_of_isPullback (IsPullback.of_hasPullback q h) hS h₃

end Scheme.Modules

end AlgebraicGeometry
