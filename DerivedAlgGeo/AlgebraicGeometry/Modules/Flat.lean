/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
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
flat over `S'`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsFlatOver` — stalkwise flatness of a module sheaf over a
  morphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFlatOverId_iff_stalkwiseFlat` — flatness over the identity
  is flatness of each module stalk over the local ring.
* `AlgebraicGeometry.Scheme.Modules.isFlatOverId_coprod` — flatness over the identity is closed
  under indexed coproducts.
* `AlgebraicGeometry.Scheme.Modules.IsFlatOver.of_iso` — flatness over the base transports along
  isomorphisms of module sheaves.
* `AlgebraicGeometry.Scheme.Modules.isFlatOver_of_affine` — flatness of sections over compatible
  affine opens implies flatness over the base, for every module sheaf.
* `AlgebraicGeometry.Scheme.Modules.isFlatOver_iff_affine` — for a quasi-coherent module sheaf,
  flatness over the base is flatness of sections over compatible affine opens.
* `AlgebraicGeometry.Scheme.Modules.isFlatOver_pullback` — flatness over the base is stable under
  base change.

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

`isFlatOver_pullback` is proved stalkwise and needs no quasi-coherence. At a
point `z` of the fibre product `P`, `pullbackStalkIso` identifies the stalk of
the pullback with `𝒪_{P,z} ⊗ M_y`. Over affine opens `U`, `V`, `V'` around the
images of `z`, the sections of `P` over `W = fst⁻¹ U ∩ snd⁻¹ V'` form the
pushout `Γ(U) ⊗_{Γ(V)} Γ(V')` (`isIso_pushoutSection_of_isAffineOpen`), and
`𝒪_{P,z}` is a localization of `Γ(W)`. The stalk is therefore a localization
of `Γ(V') ⊗_{Γ(V)} M_y`, which is flat over `Γ(V')`.

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
  have h₁ : IsBaseChange L (LinearMap.id : M →ₗ[B] M) :=
    (isLocalizedModule_iff_isBaseChange SB L _).mp (isLocalizedModule_id SB M L)
  have h₂ : IsBaseChange D ((TensorProduct.mk L D M 1).restrictScalars B ∘ₗ LinearMap.id) :=
    h₁.comp (TensorProduct.isBaseChange L M D)
  have hC : IsBaseChange C (TensorProduct.mk B C M 1) := TensorProduct.isBaseChange B M C
  let g : C ⊗[B] M →ₗ[C] D ⊗[L] M := hC.lift ((TensorProduct.mk L D M 1).restrictScalars B)
  have hg : IsBaseChange D g := by
    refine hC.of_comp ?_
    convert h₂ using 1
    exact hC.lift_comp _
  have : IsLocalizedModule SC g := (isLocalizedModule_iff_isBaseChange SC D g).mpr hg
  exact flat_of_isLocalizedModule_of_flat SC g

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

/-- **Flatness over the base is stable under base change.** For `q : Y ⟶ T` and `h : T' ⟶ T`,
if `M` is flat over `T` then its pullback along the projection `Y ×_T T' ⟶ Y` is flat over
`T'` through the other projection.

No quasi-coherence is assumed. The proof is stalkwise: the stalk of the pullback is
`𝒪_{P,z} ⊗ M_y` (`pullbackStalkIso`), and over affine opens the local ring `𝒪_{P,z}` is a
localization of the pushout `Γ(U) ⊗_{Γ(V)} Γ(V')` of sections
(`isIso_pushoutSection_of_isAffineOpen`). -/
@[stacks 01U8]
theorem isFlatOver_pullback {Y T T' : Scheme.{u}} (q : Y ⟶ T) (h : T' ⟶ T) (M : Y.Modules)
    (hM : IsFlatOver q M) :
    IsFlatOver (Limits.pullback.snd q h)
      ((Scheme.Modules.pullback (Limits.pullback.fst q h)).obj M) := by
  intro z
  let fst := Limits.pullback.fst q h
  let snd := Limits.pullback.snd q h
  have hcond : q (fst z) = h (snd z) := by
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨V, hV, hyV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens (Opens.mem_top (q (fst z)))
  obtain ⟨U, hU, hyU, hUV⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show fst z ∈ q ⁻¹ᵁ V from hyV)
  obtain ⟨V', hV', hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show snd z ∈ h ⁻¹ᵁ V from (show h (snd z) ∈ V by rw [← hcond]; exact hyV))
  let W := fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V'
  have hzW : z ∈ W := ⟨hyU, hzV'⟩
  have H := IsPullback.of_hasPullback q h
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
  let : Algebra Γ(Y, U) Γ(Limits.pullback q h, W) := (fst.appLE U W hUW).hom.toAlgebra
  let : Algebra Γ(T', V') Γ(Limits.pullback q h, W) := (snd.appLE V' W hV'W).hom.toAlgebra
  let : Algebra Γ(T, V) Γ(Limits.pullback q h, W) :=
    (q.appLE V U hUV ≫ fst.appLE U W hUW).hom.toAlgebra
  have : IsScalarTower Γ(T, V) Γ(Y, U) Γ(Limits.pullback q h, W) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(T, V) Γ(T', V') Γ(Limits.pullback q h, W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(T, V) Γ(T', V') Γ(Y, U) Γ(Limits.pullback q h, W) :=
    (CommRingCat.isPushout_iff_isPushout.mp hpush).symm
  -- The local rings at `fst z` and `z` localize `Γ(U)` and `Γ(W)`.
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (fst z)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨fst z, hyU⟩
  have := hU.isLocalization_stalk ⟨fst z, hyU⟩
  let : Algebra Γ(Limits.pullback q h, W) ((Limits.pullback q h).presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨z, hzW⟩
  have := hW.isLocalization_stalk ⟨z, hzW⟩
  let : Algebra (Y.presheaf.stalk (fst z)) ((Limits.pullback q h).presheaf.stalk z) :=
    (fst.stalkMap z).hom.toAlgebra
  let : Algebra Γ(Y, U) ((Limits.pullback q h).presheaf.stalk z) :=
    (Y.presheaf.germ U (fst z) hyU ≫ fst.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (fst z))
      ((Limits.pullback q h).presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Γ(Limits.pullback q h, W)
      ((Limits.pullback q h).presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (germ_stalkMap_eq_appLE_germ fst hUW z hzW hyU))
  let : Algebra Γ(T', V') ((Limits.pullback q h).presheaf.stalk z) :=
    (T'.presheaf.germ V' (snd z) hzV' ≫ snd.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(T', V') Γ(Limits.pullback q h, W)
      ((Limits.pullback q h).presheaf.stalk z) :=
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
    have := (flat_stalk_iff q M (fst z) hV hyV).mp (hM (fst z))
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
    (C := Γ(Limits.pullback q h, W)) (L := Y.presheaf.stalk (fst z))
    (D := (Limits.pullback q h).presheaf.stalk z) (hU.primeIdealOf ⟨fst z, hyU⟩).asIdeal.primeCompl
    (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.primeCompl My
  -- The stalk of the pullback is `𝒪_{P,z} ⊗ M_y`.
  refine (flat_stalk_iff snd _ z hV' hzV').mpr ?_
  let e₁ := ((ModuleCat.restrictScalars (T'.presheaf.germ V' (snd z) hzV' ≫
    snd.stalkMap z).hom).mapIso ((pullbackStalkIso fst z).app M)).toLinearEquiv
  let e₂ : (ModuleCat.restrictScalars (T'.presheaf.germ V' (snd z) hzV' ≫
      snd.stalkMap z).hom).obj ((ModuleCat.extendScalars (fst.stalkMap z).hom).obj My) ≃ₗ[Γ(T', V')]
        (Limits.pullback q h).presheaf.stalk z ⊗[Y.presheaf.stalk (fst z)] My :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Flat.of_linearEquiv (e₁.trans e₂)

end Scheme.Modules

end AlgebraicGeometry
