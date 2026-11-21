/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.FinitePresentation
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import DerivedAlgGeo.RingTheory.Flat.FilteredColimit
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Module sheaves along a cofiltered limit of schemes

Let `T = lim D_j` be a cofiltered limit of schemes with affine transition maps, `q : X ⟶ D_i`
locally of finite presentation with `X` quasi-compact, and `F` a finitely presented module sheaf
on `X`. If the pullback of `F` to `X ×_{D_i} T` is flat over `T`, then the pullback of `F` to
`X ×_{D_i} D_j` is flat over `D_j` for some `j ⟶ i` (Stacks 05LY with `Y_i = S_i`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_isFlatOver_of_isLimit`: the statement above; Stacks
  05LY, EGA IV₃ 11.2.6 (ii).
* `AlgebraicGeometry.Scheme.Modules.exists_isLocalizedModule_stalk_pullback`: for `f : P ⟶ X`,
  affine opens `U ⊆ X` and `W ⊆ f⁻¹ U` and `z ∈ W`, the stalk of `f^* F` at `z` localizes
  `Γ(P, W) ⊗_{Γ(X, U)} Γ(U, F)`.
* `AlgebraicGeometry.Scheme.Modules.flat_stalk_pullback_of_flat_baseChange` and
  `AlgebraicGeometry.Scheme.Modules.flat_baseChange_of_isFlatOver_pullback`: in a pullback square
  `X ×_S S'` over affine opens `U`, `V`, `V'`, flatness of `Γ(S', V') ⊗_{Γ(S, V)} Γ(U, F)` over
  `Γ(S', V')` gives flatness of the stalks of the pullback over the chart, and flatness of the
  pullback over `S'` gives it back.
* `AlgebraicGeometry.Scheme.Modules.exists_flat_stage_of_isLimit`: the algebra theorem
  `Module.Flat.exists_flat_of_isColimit` (Stacks 02JO (3)) over one affine open of `D_i`, for every
  stage below one stage.

## Implementation notes

The proof is that of Stacks 05LY with `Y_i = S_i`.
1. Cover `X` by finitely many affine opens `U_k` over affine opens `V_k ⊆ D_i`, chosen so that
   `Γ(U_k, F)` is finitely presented over `Γ(X, U_k)`
   (`exists_isAffineOpen_finitePresentation_sections`); `Γ(X, U_k)` is finitely presented over
   `Γ(D_i, V_k)` since `q` is locally of finite presentation.
2. The preimage of `V_k` in the limit is the limit of the restricted diagram `opensDiagram D i V_k`,
   indexed by `Over i`, whose objects are affine; `nonempty_isColimit_Γ_mapCocone` makes its ring of
   sections the filtered colimit of the `Γ(D_j, V_{k,j})`. The diagram is re-indexed by
   `Functor.copyObj` along `Scheme.Opens.topIso`, so that its rings are sections over opens of the
   `D_j`, the rings of the base-change charts.
3. The ring of the chart of `X ×_{D_i} D_j` over `U_k` and `V_{k,j}` is the pushout
   `Γ(D_j, V_{k,j}) ⊗_{Γ(D_i, V_k)} Γ(X, U_k)` (`isIso_pushoutSection_of_isAffineOpen`), and the
   stalks of the pullback of `F` on the chart are localizations of
   `Γ(D_j, V_{k,j}) ⊗_{Γ(D_i, V_k)} Γ(U_k, F)`. Flatness at the limit therefore gives flatness of
   this module over `Γ(T, V_{k,T})`, through `Module.flat_of_isLocalized_maximal`.
4. `Module.Flat.exists_flat_of_isColimit` gives a stage for each `k`; flatness persists to every
   later stage by base change, and a common stage below the finitely many exists in `Over i`.
5. At that stage every point of the pullback lies over some `U_k`, and its stalk is a localization
   of the flat module of step 3.

The algebraic steps are stated on stalks and on the chart rings, never on sections of the pulled
back module sheaf, so no comparison of `Γ(W, f^* F)` with a tensor product is needed.

## References

* [Stacks, Lemma 32.10.4 (Tag 05LY)](https://stacks.math.columbia.edu/tag/05LY), in the setting of
  [Stacks, Lemma 32.10.1 (Tag 01ZM)](https://stacks.math.columbia.edu/tag/01ZM)
* EGA IV₃ (Publ. Math. IHÉS 28), Théorème 11.2.6, pp. 123–124

## Tags

flat, cofiltered limit, limit of schemes, finite presentation, base change, module sheaf
-/

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules


/-- Localizing at a multiplicative subset of a larger ring keeps flatness over the base. -/
private theorem flat_of_isLocalizedModule_of_flat' {R A M M' : Type*} [CommRing R] [CommRing A]
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

/-- Let `L` localize `A` at `SB`, `N` localize the `A`-module `M` at `SB`, and let `D` localize the
`A`-algebra `C` at `SC`, compatibly with a map `L → D`. Then `D ⊗[L] N` localizes `C ⊗[A] M` at
`SC`. -/
theorem exists_isLocalizedModule_tensor {A C L D M N : Type*} [CommRing A] [CommRing C]
    [CommRing L] [CommRing D] [Algebra A C] [Algebra A L] [Algebra A D] [Algebra C D]
    [Algebra L D] [IsScalarTower A C D] [IsScalarTower A L D]
    (SB : Submonoid A) [IsLocalization SB L] (SC : Submonoid C) [IsLocalization SC D]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module L N] [Module A N]
    [IsScalarTower A L N] (g : M →ₗ[A] N) [IsLocalizedModule SB g] :
    ∃ ℓ : C ⊗[A] M →ₗ[C] D ⊗[L] N, IsLocalizedModule SC ℓ := by
  have h₁ : IsBaseChange L g := (isLocalizedModule_iff_isBaseChange SB L g).mp inferInstance
  have h₂ : IsBaseChange D ((TensorProduct.mk L D N 1).restrictScalars A ∘ₗ g) :=
    h₁.comp (TensorProduct.isBaseChange L N D)
  have hC : IsBaseChange C (TensorProduct.mk A C M 1) := TensorProduct.isBaseChange A M C
  let ℓ : C ⊗[A] M →ₗ[C] D ⊗[L] N := hC.lift ((TensorProduct.mk L D N 1).restrictScalars A ∘ₗ g)
  have hg : IsBaseChange D ℓ := by
    refine hC.of_comp ?_
    convert h₂ using 1
    exact hC.lift_comp _
  exact ⟨ℓ, (isLocalizedModule_iff_isBaseChange SC D ℓ).mpr hg⟩

/-- The scalar maps of the stalkwise and the affine statements agree through germs. -/
private theorem germ_stalkMap_eq_appLE_germ' {Y T : Scheme.{u}} (q : Y ⟶ T) {V : T.Opens}
    {U : Y.Opens} (hUV : U ≤ q ⁻¹ᵁ V) (x : Y) (hx : x ∈ U) (hxV : q x ∈ V) :
    T.presheaf.germ V (q x) hxV ≫ q.stalkMap x =
      q.appLE V U hUV ≫ Y.presheaf.germ U x hx := by
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- `hU.fromSpec` sends the prime `y` to a point whose prime is `y`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec y, hy⟩ = y :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec y, hy⟩)

/-- For a quasi-coherent module sheaf and an affine open `U ∋ x`, the germ map at `x` is the
localization at the prime of `x`. -/
theorem isLocalizedModule_germLinearMap_primeIdealOf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (germLinearMap F U x hx) := by
  have e := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  generalize hU.primeIdealOf ⟨x, hx⟩ = y at e ⊢
  subst e
  exact isLocalizedModule_germLinearMap F hU y hx

/-- **The stalk of a pullback over an affine chart.** Let `f : P ⟶ X`, `F` quasi-coherent on
`X`, `U ⊆ X` and `W ⊆ f⁻¹ U` affine opens and `z ∈ W`. The stalk at `z` of `f^* F`, as a
`Γ(P, W)`-module, is the localization of `Γ(P, W) ⊗_{Γ(X, U)} Γ(U, F)` at the prime of `z`. -/
theorem exists_isLocalizedModule_stalk_pullback {P X : Scheme.{u}} (f : P ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} {W : P.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ f ⁻¹ᵁ U) (z : P) (hz : z ∈ W) :
    ∃ ℓ : (ModuleCat.extendScalars (f.appLE U W hWU).hom).obj (ModuleCat.of Γ(X, U) Γ(F, U)) ⟶
        (ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
          ((moduleStalkFunctor P z).obj ((Scheme.Modules.pullback f).obj F)),
      IsLocalizedModule (hW.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ℓ.hom := by
  have hy : f z ∈ U := hWU hz
  let : Algebra Γ(X, U) Γ(P, W) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk (f z)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f z, hy⟩
  have := hU.isLocalization_stalk ⟨f z, hy⟩
  let : Algebra Γ(P, W) (P.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨z, hz⟩
  have := hW.isLocalization_stalk ⟨z, hz⟩
  let : Algebra (X.presheaf.stalk (f z)) (P.presheaf.stalk z) := (f.stalkMap z).hom.toAlgebra
  let : Algebra Γ(X, U) (P.presheaf.stalk z) :=
    (X.presheaf.germ U (f z) hy ≫ f.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk (f z)) (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) Γ(P, W) (P.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (germ_stalkMap_eq_appLE_germ' f hWU z hz hy))
  let N := (moduleStalkFunctor X (f z)).obj F
  let : Module Γ(X, U) N := Module.compHom N (algebraMap Γ(X, U) (X.presheaf.stalk (f z)))
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk (f z)) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let g : Γ(F, U) →ₗ[Γ(X, U)] N := germLinearMap F U (f z) hy
  have : IsLocalizedModule (hU.primeIdealOf ⟨f z, hy⟩).asIdeal.primeCompl g :=
    isLocalizedModule_germLinearMap_primeIdealOf F hU (f z) hy
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_isLocalizedModule_tensor (C := Γ(P, W)) (L := X.presheaf.stalk (f z))
    (D := P.presheaf.stalk z) (hU.primeIdealOf ⟨f z, hy⟩).asIdeal.primeCompl
    (hW.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl g
  let e := ((ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).mapIso
    ((pullbackStalkIso f z).app F)).toLinearEquiv
  let e' : (ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
      ((ModuleCat.extendScalars (f.stalkMap z).hom).obj N) ≃ₗ[Γ(P, W)]
        P.presheaf.stalk z ⊗[X.presheaf.stalk (f z)] N :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨ModuleCat.ofHom (X := Γ(P, W) ⊗[Γ(X, U)] Γ(F, U))
    (Y := (ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
      ((moduleStalkFunctor P z).obj ((Scheme.Modules.pullback f).obj F)))
    ((e.trans e').symm.toLinearMap ∘ₗ ℓ₀),
    IsLocalizedModule.of_linearEquiv _ ℓ₀ (e.trans e').symm⟩


/-- Flatness of a stalk over the local ring of the base is flatness over the sections of any
affine neighbourhood of the image point, of which that local ring is a localization. -/
private theorem flat_stalk_iff' {Y T : Scheme.{u}} (q : Y ⟶ T) (M : Y.Modules) (x : Y)
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

section PullbackSquare

variable {P X S S' : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ S'} {q : X ⟶ S} {h : S' ⟶ S}

/-- Flatness at a point of `P`, over the base `S'`, through the chart `W ⊆ P` and `V' ⊆ S'`:
the stalk is flat over `𝒪_{S', snd z}` exactly when, as a `Γ(P, W)`-module, it is flat over
`Γ(S', V')`. -/
private theorem flat_stalk_iff_section (F : P.Modules) {W : P.Opens} {V' : S'.Opens}
    (hV' : IsAffineOpen V') (hWV' : W ≤ snd ⁻¹ᵁ V') (z : P) (hz : z ∈ W) :
    letI := (snd.appLE V' W hWV').hom.toAlgebra
    letI : Module Γ(S', V') ((ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
        ((moduleStalkFunctor P z).obj F)) :=
      Module.compHom _ (snd.appLE V' W hWV').hom
    Module.Flat (S'.presheaf.stalk (snd z))
        ((ModuleCat.restrictScalars (snd.stalkMap z).hom).obj ((moduleStalkFunctor P z).obj F)) ↔
      Module.Flat Γ(S', V') ((ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
        ((moduleStalkFunctor P z).obj F)) := by
  let := (snd.appLE V' W hWV').hom.toAlgebra
  let : Module Γ(S', V') ((ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
      ((moduleStalkFunctor P z).obj F)) :=
    Module.compHom _ (snd.appLE V' W hWV').hom
  rw [flat_stalk_iff' snd F z hV' (hWV' hz)]
  let e : (ModuleCat.restrictScalars (S'.presheaf.germ V' (snd z) (hWV' hz) ≫
      snd.stalkMap z).hom).obj ((moduleStalkFunctor P z).obj F) ≃ₗ[Γ(S', V')]
        (ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
          ((moduleStalkFunctor P z).obj F) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a m ↦ by
        change (S'.presheaf.germ V' _ (hWV' hz) ≫ snd.stalkMap z).hom a • m =
          P.presheaf.germ W z hz (snd.appLE V' W hWV' a) • m
        exact congrArg (· • m) (congrArg (fun φ ↦ φ.hom a)
          (germ_stalkMap_eq_appLE_germ' snd hWV' z hz (hWV' hz))) }
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv e.symm, fun _ ↦ Module.Flat.of_linearEquiv e⟩

variable (H : IsPullback fst snd q h) (F : X.Modules) [F.IsQuasicoherent]
  {U : X.Opens} {V : S.Opens} {V' : S'.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hV' : IsAffineOpen V') (hUV : U ≤ q ⁻¹ᵁ V) (hV'V : V' ≤ h ⁻¹ᵁ V)

include H hU hV hV' hUV hV'V in
/-- The chart `fst⁻¹ U ∩ snd⁻¹ V'` of the pullback is affine. -/
private theorem isAffineOpen_chart : IsAffineOpen (fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V') := by
  have : IsAffine _ := hV
  have : IsAffine _ := hV'
  have : IsAffine _ := hU
  exact .of_isIso (Scheme.Hom.isPullback_resLE H hV'V hUV rfl).isoPullback.hom

omit [F.IsQuasicoherent] in
include H hV hV' hU in
/-- Over the chart `W = fst⁻¹ U ∩ snd⁻¹ V'`, `Γ(S', V') ⊗_{Γ(S, V)} Γ(U, F)` and
`Γ(P, W) ⊗_{Γ(X, U)} Γ(U, F)` are the same `Γ(S', V')`-module, the pushout of rings computing
`Γ(P, W)`; flatness over `Γ(S', V')` of one is flatness of the other. -/
private theorem flat_baseChange_iff_chart :
    letI : Module Γ(S', V') ((ModuleCat.extendScalars
        (fst.appLE U (fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V') inf_le_left).hom).obj
          (ModuleCat.of Γ(X, U) Γ(F, U))) :=
      Module.compHom _ (snd.appLE V' (fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V') inf_le_right).hom
    Module.Flat Γ(S', V') ((ModuleCat.extendScalars (h.appLE V V' hV'V).hom).obj
        ((ModuleCat.restrictScalars (q.appLE V U hUV).hom).obj (ModuleCat.of Γ(X, U) Γ(F, U)))) ↔
      Module.Flat Γ(S', V') ((ModuleCat.extendScalars
        (fst.appLE U (fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V') inf_le_left).hom).obj
          (ModuleCat.of Γ(X, U) Γ(F, U))) := by
  set W := fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V'
  have hpush := (isIso_pushoutSection_iff H hV'V hUV (UY := W) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hV'V hUV rfl hV hV' hU)
  let : Algebra Γ(S, V) Γ(X, U) := (q.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S', V') := (h.appLE V V' hV'V).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(P, W) := (fst.appLE U W inf_le_left).hom.toAlgebra
  let : Algebra Γ(S', V') Γ(P, W) := (snd.appLE V' W inf_le_right).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(P, W) := (q.appLE V U hUV ≫ fst.appLE U W inf_le_left).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(P, W) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, V) Γ(S', V') Γ(P, W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have : Algebra.IsPushout Γ(S, V) Γ(S', V') Γ(X, U) Γ(P, W) :=
    (CommRingCat.isPushout_iff_isPushout.mp hpush).symm
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ (q.appLE V U hUV).hom
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e := Algebra.IsPushout.cancelBaseChange Γ(S, V) Γ(S', V') Γ(X, U) Γ(P, W) Γ(F, U)
  let E := (ModuleCat.extendScalars (fst.appLE U W inf_le_left).hom).obj
    (ModuleCat.of Γ(X, U) Γ(F, U))
  let : Module Γ(S', V') E := Module.compHom _ (snd.appLE V' W inf_le_right).hom
  let e' : E ≃ₗ[Γ(S', V')] Γ(P, W) ⊗[Γ(X, U)] Γ(F, U) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  change Module.Flat Γ(S', V') (Γ(S', V') ⊗[Γ(S, V)] Γ(F, U)) ↔ Module.Flat Γ(S', V') E
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv (e'.trans e),
    fun _ ↦ Module.Flat.of_linearEquiv (e'.trans e).symm⟩

include H hV hV' hU in
/-- **Flatness at a finite stage, at a point.** In a pullback square `P = X ×_S S'`, if
`Γ(S', V') ⊗_{Γ(S, V)} Γ(U, F)` is flat over `Γ(S', V')`, then the stalk of `fst^* F` at every
point of `fst⁻¹ U ∩ snd⁻¹ V'` is flat over the local ring of `S'`. -/
theorem flat_stalk_pullback_of_flat_baseChange (z : P) (hzU : fst z ∈ U) (hzV' : snd z ∈ V')
    (hM : Module.Flat Γ(S', V') ((ModuleCat.extendScalars (h.appLE V V' hV'V).hom).obj
      ((ModuleCat.restrictScalars (q.appLE V U hUV).hom).obj (ModuleCat.of Γ(X, U) Γ(F, U))))) :
    Module.Flat (S'.presheaf.stalk (snd z))
      ((ModuleCat.restrictScalars (snd.stalkMap z).hom).obj
        ((moduleStalkFunctor P z).obj ((Scheme.Modules.pullback fst).obj F))) := by
  set W := fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V'
  have hz : z ∈ W := ⟨hzU, hzV'⟩
  have hW : IsAffineOpen W := isAffineOpen_chart H hU hV hV' hUV hV'V
  have hC := (flat_baseChange_iff_chart H F hU hV hV' hUV hV'V).mp hM
  rw [flat_stalk_iff_section _ hV' inf_le_right z hz]
  obtain ⟨ℓ, hℓ⟩ := exists_isLocalizedModule_stalk_pullback fst F hU hW inf_le_left z hz
  let : Algebra Γ(X, U) Γ(P, W) := (fst.appLE U W inf_le_left).hom.toAlgebra
  let : Algebra Γ(S', V') Γ(P, W) := (snd.appLE V' W inf_le_right).hom.toAlgebra
  let T := (ModuleCat.restrictScalars (P.presheaf.germ W z hz).hom).obj
    ((moduleStalkFunctor P z).obj ((Scheme.Modules.pullback fst).obj F))
  let : Module Γ(S', V') T := Module.compHom _ (snd.appLE V' W inf_le_right).hom
  have : IsScalarTower Γ(S', V') Γ(P, W) T := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let E := (ModuleCat.extendScalars (fst.appLE U W inf_le_left).hom).obj
    (ModuleCat.of Γ(X, U) Γ(F, U))
  let : Module Γ(S', V') E := Module.compHom _ (snd.appLE V' W inf_le_right).hom
  have : IsScalarTower Γ(S', V') Γ(P, W) E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat Γ(S', V') E := hC
  exact flat_of_isLocalizedModule_of_flat' (R := Γ(S', V')) (M := E)
    (hW.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ℓ.hom

include H hV hV' hU in
/-- **Flatness of the sections from flatness at the points.** In a pullback square
`P = X ×_S S'`, if `fst^* F` is flat over `S'`, then `Γ(S', V') ⊗_{Γ(S, V)} Γ(U, F)` is flat
over `Γ(S', V')`. -/
theorem flat_baseChange_of_isFlatOver_pullback
    (hF : IsFlatOver snd ((Scheme.Modules.pullback fst).obj F)) :
    Module.Flat Γ(S', V') ((ModuleCat.extendScalars (h.appLE V V' hV'V).hom).obj
      ((ModuleCat.restrictScalars (q.appLE V U hUV).hom).obj (ModuleCat.of Γ(X, U) Γ(F, U)))) := by
  set W := fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ V'
  have hW : IsAffineOpen W := isAffineOpen_chart H hU hV hV' hUV hV'V
  refine (flat_baseChange_iff_chart H F hU hV hV' hUV hV'V).mpr ?_
  let : Algebra Γ(S', V') Γ(P, W) := (snd.appLE V' W inf_le_right).hom.toAlgebra
  let pt : ∀ (Q : Ideal Γ(P, W)) [Q.IsMaximal], PrimeSpectrum Γ(P, W) :=
    fun Q h ↦ ⟨Q, h.isPrime⟩
  have hpt : ∀ (Q : Ideal Γ(P, W)) [Q.IsMaximal], hW.fromSpec (pt Q) ∈ W := fun Q _ ↦ by
    have := Set.mem_range_self (f := hW.fromSpec) (pt Q)
    rwa [hW.range_fromSpec] at this
  let Mₚ : ∀ (Q : Ideal Γ(P, W)) [Q.IsMaximal], Type u := fun Q _ ↦
    (ModuleCat.restrictScalars (P.presheaf.germ W _ (hpt Q)).hom).obj
      ((moduleStalkFunctor P (hW.fromSpec (pt Q))).obj ((Scheme.Modules.pullback fst).obj F))
  let instA : ∀ (Q : Ideal Γ(P, W)) [Q.IsMaximal], Module Γ(S', V') (Mₚ Q) := fun Q _ ↦
    Module.compHom _ (snd.appLE V' W inf_le_right).hom
  have instT : ∀ (Q : Ideal Γ(P, W)) [Q.IsMaximal],
      letI := instA Q; IsScalarTower Γ(S', V') Γ(P, W) (Mₚ Q) :=
    fun Q _ ↦ by let := instA Q; exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  choose ℓ hℓ using fun (Q : Ideal Γ(P, W)) [Q.IsMaximal] ↦
    exists_isLocalizedModule_stalk_pullback fst F hU hW inf_le_left _ (hpt Q)
  have instL : ∀ (Q : Ideal Γ(P, W)) [Q.IsMaximal], IsLocalizedModule.AtPrime Q (ℓ Q).hom :=
    fun Q _ ↦ by
      have := hℓ Q
      rwa [hW.primeIdealOf_fromSpec] at this
  let E := (ModuleCat.extendScalars (fst.appLE U W inf_le_left).hom).obj
    (ModuleCat.of Γ(X, U) Γ(F, U))
  let : Module Γ(S', V') E := Module.compHom _ (snd.appLE V' W inf_le_right).hom
  have : IsScalarTower Γ(S', V') Γ(P, W) E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine @Module.flat_of_isLocalized_maximal _ Γ(P, W) _ _ _ E _ _ _ _
    Mₚ (fun Q _ ↦ inferInstanceAs (AddCommMonoid ((ModuleCat.restrictScalars
      (P.presheaf.germ W _ (hpt Q)).hom).obj ((moduleStalkFunctor P (hW.fromSpec (pt Q))).obj
        ((Scheme.Modules.pullback fst).obj F)))))
    instA
    (fun Q _ ↦ inferInstanceAs (Module Γ(P, W) ((ModuleCat.restrictScalars
      (P.presheaf.germ W _ (hpt Q)).hom).obj ((moduleStalkFunctor P (hW.fromSpec (pt Q))).obj
        ((Scheme.Modules.pullback fst).obj F)))))
    instT (fun Q _ ↦ (ℓ Q).hom) instL fun Q _ ↦ ?_
  exact (flat_stalk_iff_section _ hV' inf_le_right _ (hpt Q)).mp (hF _)

end PullbackSquare



section Stage

/-- Flatness of an extension of scalars persists along a further ring map. -/
theorem flat_extendScalars_comp {R R₁ R₂ : CommRingCat.{u}} (f : R ⟶ R₁) (g : R₁ ⟶ R₂)
    (M : ModuleCat.{u} R) (h : Module.Flat R₁ ((ModuleCat.extendScalars f.hom).obj M)) :
    Module.Flat R₂ ((ModuleCat.extendScalars (f ≫ g).hom).obj M) := by
  let : Algebra R₁ R₂ := g.hom.toAlgebra
  have : Module.Flat R₂ (R₂ ⊗[R₁] ((ModuleCat.extendScalars f.hom).obj M)) := inferInstance
  have : Module.Flat R₂
      ((ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom).obj M) := this
  exact Module.Flat.of_linearEquiv
    ((ModuleCat.extendScalarsComp f.hom g.hom).app M).toLinearEquiv

/-- `appLE` along equal morphisms. -/
private theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- **Flatness descends to a finite stage over an affine open of the base.** Let `V ⊆ D_i` be
affine, `U` an affine open of `X` over `V` along `q : X ⟶ D_i` with `Γ(X, U)` finitely presented
over `Γ(D_i, V)`, and `M` a finitely presented `Γ(X, U)`-module. If `Γ(T, V_T) ⊗ M` is flat over
the sections of the preimage `V_T` of `V` in the limit, then `Γ(D_k, V_k) ⊗ M` is flat over the
sections of the preimage `V_k` of `V` in `D_k`, for all `k` below some stage. The open is written
`D.map (𝟙 i) ⁻¹ᵁ V`, the preimage at the stage `𝟙 i` of `Over i`. -/
theorem exists_flat_stage_of_isLimit {i : I} (V : (D.obj i).Opens) (hV : IsAffineOpen V)
    {A : CommRingCat.{u}} (φ : Γ(D.obj i, D.map (𝟙 i) ⁻¹ᵁ V) ⟶ A)
    (hφ : φ.hom.FinitePresentation) (M : ModuleCat.{u} A) [Module.FinitePresentation A M]
    (hM : Module.Flat Γ(c.pt, c.π.app i ⁻¹ᵁ V)
      ((ModuleCat.extendScalars ((c.π.app i).appLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V)
        (by rw [D.map_id]; exact le_rfl)).hom).obj ((ModuleCat.restrictScalars φ.hom).obj M))) :
    ∃ j : Over i, ∀ (k : Over i) (_ : k ⟶ j), Module.Flat Γ(D.obj k.left, D.map k.hom ⁻¹ᵁ V)
      ((ModuleCat.extendScalars ((D.map k.hom).appLE (D.map (𝟙 i) ⁻¹ᵁ V) (D.map k.hom ⁻¹ᵁ V)
        (by rw [D.map_id]; exact le_rfl)).hom).obj ((ModuleCat.restrictScalars φ.hom).obj M)) := by
  have : ∀ j : Over i, IsAffine ((opensDiagram D i V).obj j) := fun j ↦ hV.preimage (D.map j.hom)
  obtain ⟨hc₀⟩ := nonempty_isColimit_Γ_mapCocone (opensDiagram D i V) (opensCone D c i V)
    (isLimitOpensCone D c hc i V)
  let F₀ := (opensDiagram D i V).op ⋙ Scheme.Γ
  let e : ∀ j : (Over i)ᵒᵖ, F₀.obj j ≅ Γ(D.obj j.unop.left, D.map j.unop.hom ⁻¹ᵁ V) :=
    fun j ↦ (D.map j.unop.hom ⁻¹ᵁ V).topIso
  let G := F₀.copyObj (fun j ↦ Γ(D.obj j.unop.left, D.map j.unop.hom ⁻¹ᵁ V)) e
  let iso : F₀ ≅ G := F₀.isoCopyObj _ e
  have hc₁ := (IsColimit.precomposeInvEquiv iso _).symm hc₀
  have hG : ∀ {j k : (Over i)ᵒᵖ} (f : j ⟶ k), G.map f =
      (D.map f.unop.left).appLE (D.map j.unop.hom ⁻¹ᵁ V) (D.map k.unop.hom ⁻¹ᵁ V) (by
        rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w f.unop]) := by
    intro j k f
    change (e _).inv ≫ F₀.map f ≫ (e _).hom = _
    simp [F₀, e, opensDiagram, -Scheme.Opens.topIso_hom, -Scheme.Opens.topIso_inv]
  let j₀ : (Over i)ᵒᵖ := Opposite.op (Over.mk (𝟙 i))
  obtain ⟨j', f, hf⟩ := Module.Flat.exists_flat_of_isColimit hc₁ (j := j₀) φ hφ M (by
    have hι : ((Cocone.precompose iso.inv).obj (Scheme.Γ.mapCocone (opensCone D c i V).op)).ι.app
        j₀ = (c.π.app i).appLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V)
          (by rw [D.map_id]; exact le_rfl) ≫ (c.π.app i ⁻¹ᵁ V).topIso.inv := by
      change (e j₀).inv ≫ ((c.π.app i).resLE (D.map (𝟙 i) ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) _).app ⊤ = _
      rw [Scheme.Hom.resLE_app_top]
      exact Iso.inv_hom_id_assoc _ _
    rw [hι]
    exact flat_extendScalars_comp _ _ _ hM)
  refine ⟨j'.unop, fun k g ↦ ?_⟩
  have h := flat_extendScalars_comp (G.map f) (G.map g.op) _ hf
  rw [← G.map_comp, hG] at h
  have hmor : D.map (f ≫ g.op).unop.left = D.map k.hom :=
    congrArg D.map (by simpa [j₀] using Over.w (f ≫ g.op).unop)
  rwa [appLE_eq_of_eq hmor] at h


end Stage

/-- **Flatness over the base descends to a finite stage of a cofiltered limit** (Stacks, Limits,
Lemma 32.10.4, Tag 05LY, with `Y_i = S_i`, in the setting of Lemma 32.10.1, Tag 01ZM; EGA IV₃,
Théorème 11.2.6 (ii) with `Y = S`).

Let `T = lim D_j` be a cofiltered limit of schemes with affine transition maps, `q : X ⟶ D_i`
locally of finite presentation with `X` quasi-compact, and `F` a finitely presented module sheaf
on `X`. If the pullback of `F` to `X ×_{D_i} T` is flat over `T`, then for some `j ⟶ i` the
pullback of `F` to `X ×_{D_i} D_j` is flat over `D_j`.

Stacks asks the `D_j` to be quasi-compact and quasi-separated. That is not used: only `X` is
quasi-compact, and `Γ` of the limit is computed on the affine preimages of affine opens of `D_i`.

The three hypotheses on `q` and `F` are load-bearing. Let `k` be a field and
`D_n = Spec R_n`, `R_n = k[y₁, y₂, …] ⧸ (y₁, …, y_n)`, indexed by `ℕᵒᵖ`; the transition maps are
closed immersions and `T = Spec k`. Take `i = 0`. Each `R_n` is a domain, and a nonzero module
killed by a nonzero element is not flat over it.
* (d) `X` quasi-compact: take `X = ⨆_{m ≥ 1} D_0`, `q` the identity on each copy, and
  `F = (R_0 ⧸ (y_m))~` on the `m`-th copy. Over `T` every piece is `k` over `k`, which is flat; at
  stage `n` the copy `m = n + 1` carries `R_n ⧸ (y_{n+1}) ≠ 0`, which is not flat.
* (e) `q` locally of finite presentation: take the closed immersion
  `X = Spec R_0 ⧸ (y₁, y₂, …) ⟶ D_0` and `F = 𝒪_X`. At stage `n` the pullback is `Spec k` with
  module `R_n ⧸ (y_{n+1}, …) ≅ k`, which is not flat over `R_n`; over `T` it is `k` over `k`.
* (f) `F` finitely presented: take `q = 𝟙` and `F = (R_0 ⧸ (y₁, y₂, …))~`, with the computation
  of (e). -/
@[stacks 05LY]
theorem exists_isFlatOver_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {c : Cone D} (hc : IsLimit c) {i : I} {X : Scheme.{u}} (q : X ⟶ D.obj i)
    [CompactSpace X] [LocallyOfFinitePresentation q] (F : X.Modules)
    [SheafOfModules.IsFinitePresentation.{u, u, u} F]
    (hF : IsFlatOver (pullback.snd q (c.π.app i))
      ((Scheme.Modules.pullback (pullback.fst q (c.π.app i))).obj F)) :
    ∃ (j : I) (f : j ⟶ i), IsFlatOver (pullback.snd q (D.map f))
      ((Scheme.Modules.pullback (pullback.fst q (D.map f))).obj F) := by
  classical
  have : F.IsQuasicoherent := by
    obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
    exact σ.isQuasicoherent
  have := isAffineHom_π_app D c hc i
  have key : ∀ x : X, ∃ (V : (D.obj i).Opens) (U : X.Opens), IsAffineOpen V ∧ IsAffineOpen U ∧
      x ∈ U ∧ U ≤ q ⁻¹ᵁ V ∧ Module.FinitePresentation Γ(X, U) Γ(F, U) := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (D.obj i).isBasis_affineOpens (TopologicalSpace.Opens.mem_top (q x))
    obtain ⟨U, hU, hxU, hUV, hfp⟩ :=
      exists_isAffineOpen_finitePresentation_sections F x (q ⁻¹ᵁ V) hxV
    exact ⟨V, U, hV, hU, hxU, hUV, hfp⟩
  choose V U hV hU hxU hUV hfp using key
  obtain ⟨s, hs⟩ : ∃ s : Finset X, ∀ x : X, ∃ y ∈ s, x ∈ U y := by
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
      (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    refine ⟨s, fun x ↦ ?_⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨y, hy, hxy⟩
  have hV₀ : ∀ y, IsAffineOpen (D.map (𝟙 i) ⁻¹ᵁ V y) := fun y ↦ (hV y).preimage _
  have hUV₀ : ∀ y, U y ≤ q ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ V y) := fun y ↦ by
    rw [D.map_id]; exact hUV y
  have hstage : ∀ y, ∃ j : Over i, ∀ (k : Over i) (_ : k ⟶ j),
      Module.Flat Γ(D.obj k.left, D.map k.hom ⁻¹ᵁ V y)
        ((ModuleCat.extendScalars ((D.map k.hom).appLE (D.map (𝟙 i) ⁻¹ᵁ V y)
          (D.map k.hom ⁻¹ᵁ V y) (by rw [D.map_id]; exact le_rfl)).hom).obj
          ((ModuleCat.restrictScalars (q.appLE _ (U y) (hUV₀ y)).hom).obj
            (ModuleCat.of Γ(X, U y) Γ(F, U y)))) := fun y ↦ by
    have := hfp y
    exact exists_flat_stage_of_isLimit D hc (V y) (hV y) (q.appLE _ (U y) (hUV₀ y))
      (HasRingHomProperty.appLE @LocallyOfFinitePresentation q ‹_› ⟨_, hV₀ y⟩ ⟨U y, hU y⟩
        (hUV₀ y))
      (ModuleCat.of _ Γ(F, U y))
      (flat_baseChange_of_isFlatOver_pullback (IsPullback.of_hasPullback q (c.π.app i)) F
        (hU y) (hV₀ y) ((hV y).preimage (c.π.app i)) (hUV₀ y) _ hF)
  choose j hj using hstage
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (s.image j)
  refine ⟨k.left, k.hom, fun z ↦ ?_⟩
  obtain ⟨y, hy, hzy⟩ := hs (pullback.fst q (D.map k.hom) z)
  obtain ⟨g⟩ := hk (Finset.mem_image_of_mem j hy)
  have hsnd : pullback.snd q (D.map k.hom) z ∈ D.map k.hom ⁻¹ᵁ V y := by
    change D.map k.hom (pullback.snd q (D.map k.hom) z) ∈ V y
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hUV y hzy
  exact flat_stalk_pullback_of_flat_baseChange (IsPullback.of_hasPullback q (D.map k.hom)) F
    (hU y) (hV₀ y) ((hV y).preimage (D.map k.hom)) (hUV₀ y) _ z hzy hsnd (hj y k g)

end AlgebraicGeometry.Scheme.Modules
