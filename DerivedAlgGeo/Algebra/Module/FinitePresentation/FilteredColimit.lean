/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finitely presented modules over a filtered colimit of rings

Let `R : J ⥤ CommRingCat` be a filtered diagram and `c` a cocone over `R` whose underlying cocone
of types is a colimit, so that `c.pt` is the filtered colimit of the rings `R.obj j`. Finitely
presented `c.pt`-modules and their homomorphisms descend to a finite stage: the category of
finitely presented `c.pt`-modules is the colimit of the categories of finitely presented
`R.obj j`-modules ([Stacks 05N7]).

## Main results

* `Module.FinitePresentation.exists_extended`: every finitely presented `c.pt`-module is the
  extension of scalars of a finitely presented `R.obj j`-module for some `j`.
* `Module.FinitePresentation.exists_linearMap_extended`: for a finitely presented
  `R.obj j`-module `N`, every `c.pt`-linear map from the extension of `N` to the extension of
  `N'` is the extension of an `R.obj j'`-linear map for some `f : j ⟶ j'`.
* `Module.FinitePresentation.eventually_eq_of_extended_eq`: for a finite `R.obj j`-module `N`,
  two maps `N ⟶ N'` that agree after extension to `c.pt` agree after extension to some `R.obj j'`.

These are the module analogue of `CommRingCat.preservesColimit_coyoneda_of_finitePresentation`,
which descends finitely presented algebras and their morphisms.

## Implementation notes

The colimit hypothesis is `IsColimit ((forget CommRingCat).mapCocone c)`, the form the proofs
use. For a small index category it follows from `hc : IsColimit c` as
`isColimitOfPreserves (forget CommRingCat) hc`, since `forget CommRingCat` preserves filtered
colimits. The index category is only assumed `IsFilteredOrEmpty`.

The proofs are elementwise. The stages under `j` are the rings `R.obj k` for `j ⟶ k`, as
`R.obj j`-modules indexed by the filtered category `Under j`. Tensoring with an `R.obj j`-module
`P` commutes with this filtered colimit elementwise: every element of `c.pt ⊗ P` comes from a
stage, and an element of a stage that vanishes in `c.pt ⊗ P` vanishes at a later stage. The
second statement holds coordinatewise for free modules and follows in general from right
exactness of the tensor product. Parts (2) and (3) are then proved as in [Stacks 05LI], and part
(1) lifts the finitely many coefficients of a finite presentation.

Part (2) compares extension along `c.ι.app j` with extension along `R.map f` followed by extension
along `c.ι.app j'` through `ModuleCat.extendScalarsComp'`.

## References

* [Stacks Project, Lemma 10.127.6, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
* [Stacks Project, Lemma 10.127.5, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)

## Tags

finitely presented module, filtered colimit, extension of scalars, limit preserving
-/

universe v u uJ vJ

open CategoryTheory Limits ModuleCat
open scoped TensorProduct ChangeOfRings

namespace Module.FinitePresentation

/-! ### Finite families in a filtered category -/

section Filtered

variable {I : Type*} [Category* I]

/-- Finitely many objects of a filtered category map to a common object. -/
private lemma exists_nonempty_hom [IsFiltered I] {ι : Type*} [Finite ι] (k : ι → I) :
    ∃ t : I, ∀ x, Nonempty (k x ⟶ t) := by
  have := Fintype.ofFinite ι
  obtain ⟨c⟩ := IsFiltered.cocone_nonempty (Discrete.functor k)
  exact ⟨c.pt, fun x => ⟨c.ι.app ⟨x⟩⟩⟩

/-- A finite family of conditions on morphisms out of `i`, each stable under postcomposition and
each satisfied by some morphism, is satisfied by a single morphism. -/
private lemma exists_forall_of_finite [IsFilteredOrEmpty I] {ι : Type*} [Finite ι] {i : I}
    (p : ι → ∀ {t : I}, (i ⟶ t) → Prop)
    (hp : ∀ x {t t' : I} (g : i ⟶ t) (h : t ⟶ t'), p x g → p x (g ≫ h))
    (ex : ∀ x, ∃ (t : I) (g : i ⟶ t), p x g) : ∃ (t : I) (g : i ⟶ t), ∀ x, p x g := by
  classical
  have : IsFiltered I := { nonempty := ⟨i⟩ }
  have := Fintype.ofFinite ι
  choose k g hg using ex
  obtain ⟨c⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan i k g)
  refine ⟨c.pt, c.ι.app none, fun x => ?_⟩
  rw [← c.w (WidePushoutShape.Hom.init x)]
  exact hp x _ _ (hg x)

end Filtered

/-! ### Tensor products with a filtered colimit of modules -/

section Tensor

variable {A : Type u} [CommRing A] {I : Type*} [Category* I] [IsFilteredOrEmpty I]
  {G : I ⥤ ModuleCat.{v} A} (d : Cocone G)
  (hsurj : ∀ q : d.pt, ∃ (i : I) (y : G.obj i), d.ι.app i y = q)
  (hinj : ∀ (i : I) (y : G.obj i), d.ι.app i y = 0 → ∃ (i' : I) (g : i ⟶ i'), G.map g y = 0)

include hsurj in
/-- Every element of `d.pt ⊗ P` comes from a finite stage. -/
private lemma exists_rTensor_eq (P : Type*) [AddCommMonoid P] [Module A P] (x : d.pt ⊗[A] P) :
    ∃ (i : I) (y : G.obj i ⊗[A] P), (d.ι.app i).hom.rTensor P y = x := by
  induction x using TensorProduct.inductionOn with
  | tmul q p =>
    obtain ⟨i, y, rfl⟩ := hsurj q
    exact ⟨i, y ⊗ₜ p, rfl⟩
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨i₁, y₁, rfl⟩ := h₁
    obtain ⟨i₂, y₂, rfl⟩ := h₂
    refine ⟨IsFiltered.max i₁ i₂, (G.map (IsFiltered.leftToMax i₁ i₂)).hom.rTensor P y₁ +
      (G.map (IsFiltered.rightToMax i₁ i₂)).hom.rTensor P y₂, ?_⟩
    rw [map_add, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, d.w, d.w]

omit [IsFilteredOrEmpty I] in
/-- `finsuppScalarRight` is natural in the left factor. -/
private lemma finsuppScalarRight_rTensor {M M' : Type*} [AddCommMonoid M] [Module A M]
    [AddCommMonoid M'] [Module A M'] (X : Type*) [DecidableEq X] (f : M →ₗ[A] M')
    (y : M ⊗[A] (X →₀ A)) :
    TensorProduct.finsuppScalarRight A A M' X (f.rTensor _ y) =
      Finsupp.mapRange.linearMap f (TensorProduct.finsuppScalarRight A A M X y) := by
  have : (TensorProduct.finsuppScalarRight A A M' X).toLinearMap ∘ₗ f.rTensor _ =
      Finsupp.mapRange.linearMap f ∘ₗ (TensorProduct.finsuppScalarRight A A M X).toLinearMap :=
    TensorProduct.ext' fun m p => by ext x; simp
  exact LinearMap.congr_fun this y

include hinj in
/-- An element of `G.obj i ⊗ (X →₀ A)` vanishing in `d.pt ⊗ (X →₀ A)` vanishes at a later
stage. -/
private lemma exists_rTensor_eq_zero_finsupp (X : Type*) {i : I} (y : G.obj i ⊗[A] (X →₀ A))
    (hy : (d.ι.app i).hom.rTensor _ y = 0) :
    ∃ (i' : I) (g : i ⟶ i'), (G.map g).hom.rTensor _ y = 0 := by
  classical
  set v := TensorProduct.finsuppScalarRight A A (G.obj i) X y with hv_def
  have hv (x : X) : d.ι.app i (v x) = 0 := by
    have := congr($(finsuppScalarRight_rTensor X (d.ι.app i).hom y) x)
    rw [hy, map_zero, ← hv_def] at this
    exact this.symm
  obtain ⟨i', g, hg⟩ := exists_forall_of_finite (ι := v.support)
    (fun x _ g => G.map g (v x) = 0)
    (fun x _ _ g h hg => by rw [G.map_comp, ModuleCat.comp_apply, hg, map_zero])
    (fun x => hinj i (v x) (hv x))
  refine ⟨i', g, (TensorProduct.finsuppScalarRight A A (G.obj i') X).injective ?_⟩
  rw [finsuppScalarRight_rTensor, ← hv_def, map_zero]
  ext x
  rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hx : x ∈ v.support
  · exact hg ⟨x, hx⟩
  · rw [Finsupp.notMem_support_iff.mp hx, map_zero]

/-- `rTensor` and `lTensor` commute. -/
private lemma rTensor_lTensor_comm {M M' N N' : Type*} [AddCommMonoid M] [Module A M]
    [AddCommMonoid M'] [Module A M'] [AddCommMonoid N] [Module A N] [AddCommMonoid N']
    [Module A N']
    (f : M →ₗ[A] M') (g : N →ₗ[A] N') (x : M ⊗[A] N) :
    f.rTensor N' (g.lTensor M x) = g.lTensor M' (f.rTensor N x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor]

include hsurj hinj in
/-- An element of `G.obj i ⊗ P` vanishing in `d.pt ⊗ P` vanishes at a later stage. -/
private lemma exists_rTensor_eq_zero (P : Type*) [AddCommGroup P] [Module A P] {i : I}
    (y : G.obj i ⊗[A] P)
    (hy : (d.ι.app i).hom.rTensor P y = 0) :
    ∃ (i' : I) (g : i ⟶ i'), (G.map g).hom.rTensor P y = 0 := by
  let π : (P →₀ A) →ₗ[A] P := Finsupp.linearCombination A id
  have hπ : Function.Surjective π := Finsupp.linearCombination_id_surjective A P
  let ι := (LinearMap.ker π).subtype
  have hex : Function.Exact ι π := π.exact_subtype_ker_map
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (G.obj i) hπ y
  rw [rTensor_lTensor_comm] at hy
  obtain ⟨z, hz⟩ := (lTensor_exact (M := LinearMap.ker π) (N := P →₀ A) (f := ι) (g := π)
    d.pt hex hπ _).mp hy
  obtain ⟨i₁, z, rfl⟩ := exists_rTensor_eq d hsurj (LinearMap.ker π) z
  let a := IsFiltered.leftToMax i i₁
  let b := IsFiltered.rightToMax i i₁
  obtain ⟨i₃, g, hg⟩ := exists_rTensor_eq_zero_finsupp d hinj P
    ((G.map a).hom.rTensor _ y - ι.lTensor _ ((G.map b).hom.rTensor _ z)) (by
      rw [map_sub, rTensor_lTensor_comm, ← LinearMap.rTensor_comp_apply,
        ← LinearMap.rTensor_comp_apply, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, d.w, d.w]
      exact sub_eq_zero.mpr hz.symm)
  refine ⟨i₃, a ≫ g, ?_⟩
  rw [map_sub, sub_eq_zero] at hg
  rw [G.map_comp, ModuleCat.hom_comp, LinearMap.rTensor_comp_apply, rTensor_lTensor_comm,
    rTensor_lTensor_comm, hg, rTensor_lTensor_comm, ← LinearMap.comp_apply,
    ← LinearMap.lTensor_comp, hex.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

end Tensor

/-! ### The stages of a filtered colimit of rings -/

section Stage

set_option backward.isDefEq.respectTransparency false

variable {J : Type uJ} [Category.{vJ} J] {R : J ⥤ CommRingCat.{u}} (c : Cocone R)

/-- A morphism of commutative rings under `A` as an `A`-linear map. -/
private noncomputable def underLinearMap {A S T : CommRingCat.{u}} (f₁ : A ⟶ S) (f₂ : A ⟶ T)
    (g : S ⟶ T) (h : f₁ ≫ g = f₂) :
    (ModuleCat.restrictScalars f₁.hom).obj (.of S S) ⟶
      (ModuleCat.restrictScalars f₂.hom).obj (.of T T) :=
  ofHom (X := (ModuleCat.restrictScalars f₁.hom).obj (.of S S))
    (Y := (ModuleCat.restrictScalars f₂.hom).obj (.of T T))
    { toFun := g.hom
      map_add' := map_add g.hom
      map_smul' a (x : S) := by
        change g (f₁ a * x) = f₂ a * g x
        rw [map_mul, ← h, CommRingCat.comp_apply] }

private lemma underLinearMap_apply {A S T : CommRingCat.{u}} (f₁ : A ⟶ S) (f₂ : A ⟶ T)
    (g : S ⟶ T) (h : f₁ ≫ g = f₂) (x : S) : underLinearMap f₁ f₂ g h x = g x :=
  rfl

/-- The rings `R.obj s.right` for `s : Under j`, as `R.obj j`-modules. -/
private noncomputable abbrev stage (j : J) : Under j ⥤ ModuleCat.{u} (R.obj j) where
  obj s := (ModuleCat.restrictScalars (R.map s.hom).hom).obj (.of _ (R.obj s.right))
  map {s t} g := underLinearMap (R.map s.hom) (R.map t.hom) (R.map g.right)
    (by rw [← R.map_comp, Under.w g])
  map_id s := ModuleCat.hom_ext (LinearMap.ext fun (x : R.obj s.right) => by
    change R.map (𝟙 s.right) x = x
    rw [R.map_id]
    rfl)
  map_comp {s _ _} g g' := ModuleCat.hom_ext (LinearMap.ext fun (x : R.obj s.right) => by
    change R.map (g.right ≫ g'.right) x = R.map g'.right (R.map g.right x)
    rw [R.map_comp]
    rfl)

/-- The cocone on `stage j` with point `c.pt`. -/
private noncomputable abbrev stageCocone (j : J) : Cocone (stage (R := R) j) where
  pt := (ModuleCat.restrictScalars (c.ι.app j).hom).obj (.of _ (((Functor.const J).obj c.pt).obj j))
  ι :=
    { app s := underLinearMap (R.map s.hom) (c.ι.app j) (c.ι.app s.right) (c.w s.hom)
      naturality s t g := ModuleCat.hom_ext (LinearMap.ext fun (x : R.obj s.right) => by
        change c.ι.app t.right (R.map g.right x) = c.ι.app s.right x
        rw [← CommRingCat.comp_apply, c.w]
        rfl) }

/-- The unit of the stage ring `R.obj s.right`, as an element of `(stage j).obj s`. -/
private abbrev stageOne {j : J} (s : Under j) : (stage (R := R) j).obj s := (1 : R.obj s.right)

/-- The unit of `c.pt`, as an element of `(stageCocone c j).pt`. -/
private abbrev coconeOne (j : J) : (stageCocone c j).pt := (1 : c.pt)

private lemma stage_map_stageOne {j : J} {s t : Under j} (g : s ⟶ t) :
    ((stage (R := R) j).map g).hom (stageOne s) = stageOne t :=
  map_one (R.map g.right).hom

private lemma stageCocone_ι_stageOne {j : J} (s : Under j) :
    ((stageCocone c j).ι.app s).hom (stageOne s) = coconeOne c j :=
  map_one (c.ι.app s.right).hom

/-- The transition maps of `stage j`, tensored with `P`, send `1 ⊗ m` to `1 ⊗ m`. -/
private lemma rTensor_stage_map_stageOne {j : J} {s t : Under j} (g : s ⟶ t) {P : Type*}
    [AddCommMonoid P] [Module (R.obj j) P] (m : P) :
    ((stage (R := R) j).map g).hom.rTensor P (stageOne s ⊗ₜ m) = stageOne t ⊗ₜ m := by
  rw [LinearMap.rTensor_tmul, stage_map_stageOne]

variable {c} [IsFilteredOrEmpty J] (hc : IsColimit ((forget CommRingCat).mapCocone c))
include hc

private lemma stageCocone_surj (j : J) (q : (stageCocone c j).pt) :
    ∃ (s : Under j) (y : (stage j).obj s), (stageCocone c j).ι.app s y = q := by
  obtain ⟨k, y, hy⟩ := Types.jointly_surjective_of_isColimit hc (show c.pt from q)
  obtain ⟨t, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j k
  exact ⟨Under.mk a, R.map b y, (congr($(c.w b) y)).trans hy⟩

private lemma stageCocone_inj (j : J) (s : Under j) (y : (stage j).obj s)
    (hy : (stageCocone c j).ι.app s y = 0) :
    ∃ (t : Under j) (g : s ⟶ t), (stage j).map g y = 0 := by
  obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc (i := s.right)
    (show R.obj s.right from y) (0 : R.obj s.right)).mp (by
      change c.ι.app s.right y = c.ι.app s.right 0
      rw [map_zero]
      exact hy)
  refine ⟨Under.mk (s.hom ≫ f), Under.homMk f, ?_⟩
  change R.map f y = 0
  simpa using hf

end Stage

/-! ### Descent of finitely presented modules and their maps -/

section Descent

set_option backward.isDefEq.respectTransparency false

variable {J : Type uJ} [Category.{vJ} J] [IsFilteredOrEmpty J] {R : J ⥤ CommRingCat.{u}}
  {c : Cocone R} (hc : IsColimit ((forget CommRingCat).mapCocone c))
include hc

/-- **Stacks 05N7 (3).** If `N` is a finite `R.obj j`-module, two maps `N ⟶ N'` that agree after
extension of scalars to `c.pt` agree after extension of scalars to some `R.obj j'` with
`j ⟶ j'`. As in Stacks 05LI (1), the target `N'` is arbitrary.

Finiteness of `N` cannot be dropped. Over a field `k`, let `R₀ = k[z₁, z₂, …]` and
`R.obj n = R₀ ⧸ (z₁, …, zₙ)`, so that `c.pt = k`. Take `j = 0`, `N = ℕ →₀ R₀`, `N' = R₀`,
`ψ₁ eₙ = zₙ` and `ψ₂ = 0`. They agree after extension to `k`, but after extension to `R.obj n`
they differ on `eₙ₊₁`. -/
theorem eventually_eq_of_extended_eq {j : J} {N N' : ModuleCat.{max v u} (R.obj j)}
    [Module.Finite (R.obj j) N] {ψ₁ ψ₂ : N ⟶ N'}
    (h : (extendScalars (c.ι.app j).hom).map ψ₁ = (extendScalars (c.ι.app j).hom).map ψ₂) :
    ∃ (j' : J) (f : j ⟶ j'),
      (extendScalars (R.map f).hom).map ψ₁ = (extendScalars (R.map f).hom).map ψ₂ := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R.obj j) (M := N)
  obtain ⟨t, -, ht⟩ := exists_forall_of_finite (I := Under j) (i := Under.mk (𝟙 j)) (ι := S)
    (fun x t _ => stageOne t ⊗ₜ[R.obj j] (ψ₁ x - ψ₂ x) = 0)
    (fun x t t' g h hx => by rw [← rTensor_stage_map_stageOne h, hx, map_zero])
    (fun x => by
      obtain ⟨t, g, hg⟩ := exists_rTensor_eq_zero (stageCocone c j) (stageCocone_surj hc j)
        (stageCocone_inj hc j) N' (stageOne (Under.mk (𝟙 j)) ⊗ₜ[R.obj j] (ψ₁ x - ψ₂ x)) (by
          rw [LinearMap.rTensor_tmul, stageCocone_ι_stageOne, TensorProduct.tmul_sub, sub_eq_zero]
          exact congr($h ((1 : c.pt) ⊗ₜ[R.obj j, (c.ι.app j).hom] (x : N))))
      exact ⟨t, g, by rw [← rTensor_stage_map_stageOne g, hg]⟩)
  refine ⟨t.right, t.hom, ExtendScalars.hom_ext fun m => ?_⟩
  rw [ExtendScalars.map_tmul, ExtendScalars.map_tmul]
  have key : TensorProduct.mk (R.obj j) ((stage j).obj t) N' (stageOne t) ∘ₗ
      (ψ₁.hom - ψ₂.hom) = 0 :=
    LinearMap.ext_on hS fun x hx => by simpa using ht ⟨x, hx⟩
  have := congr($key m)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, TensorProduct.mk_apply,
    TensorProduct.tmul_sub, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

omit [IsFilteredOrEmpty J] hc in
/-- The inverse of the transitivity isomorphism sends `1 ⊗ y` to the image of `y` at the
colimit. -/
private lemma extendScalarsComp'_inv_app_one_tmul {j : J} (t : Under j)
    (P : ModuleCat.{max v u} (R.obj j)) (y : (extendScalars (R.map t.hom).hom).obj P) :
    (extendScalarsComp' (R.map t.hom).hom (c.ι.app t.right).hom (c.ι.app j).hom
        (congrArg CommRingCat.Hom.hom (c.w t.hom).symm)).inv.app P
      ((1 : ((Functor.const J).obj c.pt).obj t.right) ⊗ₜ[R.obj t.right, (c.ι.app t.right).hom] y) =
    ((stageCocone c j).ι.app t).hom.rTensor P y := by
  induction y using TensorProduct.inductionOn with
  | tmul r m =>
    rw [extendScalarsComp'_inv_app_tmul, one_mul]
    rfl
  | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, h₁, h₂, map_add]

/-- **Stacks 05N7 (1).** Every finitely presented module over the filtered colimit `c.pt` is the
extension of scalars of a finitely presented module over some stage `R.obj j`.

Finite presentation of `M` cannot be weakened to finite generation. Over a field `k`, let
`R.obj n = k[x₁, …, xₙ]` along the inclusions, so that `c.pt = k[x₁, x₂, …]`, and let
`M = c.pt ⧸ (x₁, x₂, …)`. Then `M` is cyclic but not finitely presented, while an extension of
scalars of a finitely presented module is finitely presented. -/
theorem exists_extended (M : ModuleCat.{max v u} c.pt) [Module.FinitePresentation c.pt M] :
    ∃ (j : J) (N : ModuleCat.{max v u} (R.obj j)), Module.FinitePresentation (R.obj j) N ∧
      Nonempty ((extendScalars (c.ι.app j).hom).obj N ≅ M) := by
  classical
  obtain ⟨pres, _, _⟩ : ∃ pres : Module.Presentation.{max v u, max v u} c.pt M,
      Finite pres.G ∧ Finite pres.R :=
    Module.finitePresentation_iff_exists_presentation.mp inferInstance
  have := Fintype.ofFinite pres.G
  -- lift the finitely many coefficients of the relations to a common stage `j`
  obtain ⟨j₀, -, -⟩ := Types.jointly_surjective_of_isColimit hc (show c.pt from 0)
  have : IsFiltered J := { nonempty := ⟨j₀⟩ }
  choose k y hy using fun p : pres.R × pres.G =>
    Types.jointly_surjective_of_isColimit hc (show c.pt from pres.relation p.1 p.2)
  obtain ⟨j, hj⟩ := exists_nonempty_hom (I := J) k
  let ι : R.obj j →+* c.pt := (c.ι.app j).hom
  let a (r : pres.R) (g : pres.G) : R.obj j := R.map (hj (r, g)).some (y (r, g))
  have ha (r : pres.R) (g : pres.G) : ι (a r g) = pres.relation r g :=
    (congr($(c.w (hj (r, g)).some) (y (r, g)))).trans (hy (r, g))
  -- the relations lifted to `R.obj j`, and the module `N` they present
  let rel : Module.Relations (R.obj j) :=
    { G := pres.G
      R := pres.R
      relation r := Finsupp.equivFunOnFinite.symm (a r) }
  have hrel := Module.Relations.Solution.ofQuotient_isPresentation rel
  let N := ModuleCat.of (R.obj j) rel.Quotient
  refine ⟨j, N, ?_, ⟨?_⟩⟩
  · have : Finite (Module.Presentation.ofIsPresentation hrel).G := ‹Finite pres.G›
    have : Finite (Module.Presentation.ofIsPresentation hrel).R := ‹Finite pres.R›
    exact (Module.Presentation.ofIsPresentation hrel).finitePresentation
  -- `N ⟶ M` sends the generators of `N` to those of `M`
  let solA : rel.Solution ((ModuleCat.restrictScalars (c.ι.app j).hom).obj M) :=
    { var := pres.var
      linearCombination_var_relation r := by
        have h0 := pres.linearCombination_var_relation r
        rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h0
        rw [Finsupp.linearCombination_apply
            (M := (ModuleCat.restrictScalars (c.ι.app j).hom).obj M),
          Finsupp.sum_fintype _ _ (by simp)]
        simp only [← ha] at h0
        exact h0 }
  -- `M ⟶ c.pt ⊗ N` sends the generators of `M` to the `1 ⊗ g` for generators `g` of `N`
  let u := (extendRestrictScalarsAdj (c.ι.app j).hom).unit.app N
  let solB : pres.toRelations.Solution ((extendScalars (c.ι.app j).hom).obj N) :=
    { var g := u (rel.toQuotient (Finsupp.single g 1))
      linearCombination_var_relation r := by
        have h0 := congr(u
          $((Module.Relations.Solution.ofQuotient rel).linearCombination_var_relation r))
        rw [map_zero, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp),
          map_sum] at h0
        simp only [map_smul] at h0
        rw [Finsupp.linearCombination_apply (M := (extendScalars (c.ι.app j).hom).obj N),
          Finsupp.sum_fintype _ _ (by simp)]
        simp only [← ha]
        exact h0 }
  let α := ((extendRestrictScalarsAdj (c.ι.app j).hom).homEquiv _ _).symm
    (ofHom (X := N) (Y := (ModuleCat.restrictScalars (c.ι.app j).hom).obj M) (hrel.desc solA))
  let β : M ⟶ (extendScalars (c.ι.app j).hom).obj N := ofHom (pres.toIsPresentation.desc solB)
  have hα (x : N) : α (u x) = hrel.desc solA x := by
    change ((extendRestrictScalarsAdj (c.ι.app j).hom).homEquiv _ _ α) x = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hβ (g : pres.G) : β (pres.var g) = u (rel.toQuotient (Finsupp.single g 1)) := by
    exact pres.toIsPresentation.desc_var solB g
  refine
    { hom := α
      inv := β
      hom_inv_id := ExtendScalars.hom_ext fun x => ?_
      inv_hom_id := ModuleCat.hom_ext (pres.toIsPresentation.postcomp_injective
        (Module.Relations.Solution.ext (funext fun g => ?_))) }
  · change β (α (u x)) = u x
    rw [hα]
    have : ((ModuleCat.restrictScalars (c.ι.app j).hom).map β).hom ∘ₗ hrel.desc solA = u.hom :=
      Module.Relations.Quotient.linearMap_ext fun g => by
        change β (hrel.desc solA ((Module.Relations.Solution.ofQuotient rel).var g)) = _
        rw [hrel.desc_var]
        exact hβ g
    exact congr($this x)
  · change α (β (pres.var g)) = pres.var g
    rw [hβ, hα]
    change hrel.desc solA ((Module.Relations.Solution.ofQuotient rel).var g) = _
    exact hrel.desc_var solA g

/-- **Stacks 05N7 (2).** If `N` is finitely presented over `R.obj j`, every `c.pt`-linear map `φ`
between the extensions of scalars of `N` and `N'` to `c.pt` is, through
`ModuleCat.extendScalarsComp'`, the extension along `c.ι.app j'` of an `R.obj j'`-linear map `ψ`
between the extensions of `N` and `N'` to `R.obj j'`, for some `f : j ⟶ j'`. As in Stacks 05LI (3),
the target `N'` is arbitrary.

Finite presentation of `N` cannot be weakened to finite generation. Over a field `k`, let
`R₀ = k[y₁, y₂, …]` and `R.obj n = R₀[t] ⧸ (t y₁, …, t yₙ)`, so that `t yᵢ = 0` in `c.pt` for
all `i`. Take `j = 0`, `N = R.obj 0 ⧸ (y₁, y₂, …)` and `N' = R.obj 0`. The map
`c.pt ⧸ (y₁, y₂, …) ⟶ c.pt` with `1 ↦ t` is well defined and nonzero. At a stage `n`, the
element `yₙ₊₁` is a nonzerodivisor of `R.obj n`, so the only map
`R.obj n ⧸ (y₁, y₂, …) ⟶ R.obj n` is zero. -/
theorem exists_linearMap_extended {j : J} {N N' : ModuleCat.{max v u} (R.obj j)}
    [Module.FinitePresentation (R.obj j) N]
    (φ : (extendScalars (c.ι.app j).hom).obj N ⟶ (extendScalars (c.ι.app j).hom).obj N') :
    ∃ (j' : J) (f : j ⟶ j')
      (ψ : (extendScalars (R.map f).hom).obj N ⟶ (extendScalars (R.map f).hom).obj N'),
      φ = (extendScalarsComp' (R.map f).hom (c.ι.app j').hom (c.ι.app j).hom
          (congrArg CommRingCat.Hom.hom (c.w f).symm)).hom.app N ≫
        (extendScalars (c.ι.app j').hom).map ψ ≫
        (extendScalarsComp' (R.map f).hom (c.ι.app j').hom (c.ι.app j).hom
          (congrArg CommRingCat.Hom.hom (c.w f).symm)).inv.app N' := by
  classical
  obtain ⟨pres, _, _⟩ : ∃ pres : Module.Presentation.{0, 0} (R.obj j) N,
      Finite pres.G ∧ Finite pres.R :=
    Module.finitePresentation_iff_exists_presentation.mp inferInstance
  have hspan : Submodule.span (R.obj j) (Set.range pres.var) = ⊤ := by
    rw [← pres.range_π, LinearMap.range_eq_top]
    exact pres.surjective_π
  -- `n ↦ φ (1 ⊗ n)`, an `R.obj j`-linear map
  let Φ : N →ₗ[R.obj j] (stageCocone c j).pt ⊗[R.obj j] N' :=
    ((extendRestrictScalarsAdj (c.ι.app j).hom).homEquiv _ _ φ).hom
  have hΦ (n : N) : Φ n = φ ((1 : ((Functor.const J).obj c.pt).obj j) ⊗ₜ n) := rfl
  -- the images of the generators come from a common stage `t`
  choose s y hy using fun g => exists_rTensor_eq (stageCocone c j) (stageCocone_surj hc j) N'
    (Φ (pres.var g))
  obtain ⟨t, ht⟩ := exists_nonempty_hom (I := Under j) s
  let z (g : pres.G) := ((stage j).map (ht g).some).hom.rTensor N' (y g)
  have hz (g : pres.G) : ((stageCocone c j).ι.app t).hom.rTensor N' (z g) = Φ (pres.var g) := by
    rw [← LinearMap.rTensor_comp_apply, ← ModuleCat.hom_comp, (stageCocone c j).w]
    exact hy g
  -- each relation holds at the colimit, hence at a common later stage `t'`
  have hw (r : pres.R) : ((stageCocone c j).ι.app t).hom.rTensor N'
      (Finsupp.linearCombination (R.obj j) z (pres.relation r)) = 0 := by
    rw [Finsupp.apply_linearCombination]
    have : ((stageCocone c j).ι.app t).hom.rTensor N' ∘ z = Φ ∘ pres.var := funext hz
    have h0 := congr(Φ $(pres.linearCombination_var_relation r))
    rw [map_zero, Finsupp.apply_linearCombination] at h0
    rw [this]
    exact h0
  obtain ⟨t', g, hg⟩ := exists_forall_of_finite (I := Under j) (i := t) (ι := pres.R)
    (fun r _ g => ((stage j).map g).hom.rTensor N'
      (Finsupp.linearCombination (R.obj j) z (pres.relation r)) = 0)
    (fun r _ _ g h hg => by
      rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.rTensor_comp_apply, hg, map_zero])
    (fun r => exists_rTensor_eq_zero (stageCocone c j) (stageCocone_surj hc j)
      (stageCocone_inj hc j) N' _ (hw r))
  let z' (k : pres.G) := ((stage j).map g).hom.rTensor N' (z k)
  have hz' (k : pres.G) : ((stageCocone c j).ι.app t').hom.rTensor N' (z' k) =
      Φ (pres.var k) := by
    rw [← LinearMap.rTensor_comp_apply, ← ModuleCat.hom_comp, (stageCocone c j).w]
    exact hz k
  -- the descended map
  let sol : pres.toRelations.Solution ((stage j).obj t' ⊗[R.obj j] N') :=
    { var := z'
      linearCombination_var_relation r := by
        change Finsupp.linearCombination (R.obj j) (((stage j).map g).hom.rTensor N' ∘ z) _ = 0
        rw [← Finsupp.apply_linearCombination]
        exact hg r }
  let lam := pres.toIsPresentation.desc sol
  let ψ := ((extendRestrictScalarsAdj (R.map t'.hom).hom).homEquiv _ _).symm
    (ofHom (Y := (ModuleCat.restrictScalars (R.map t'.hom).hom).obj
      ((extendScalars (R.map t'.hom).hom).obj N')) lam)
  have hψ (n : N) : ψ ((1 : R.obj t'.right) ⊗ₜ[R.obj j, (R.map t'.hom).hom] n) = lam n := by
    rw [← extendRestrictScalarsAdj_homEquiv_apply, Equiv.apply_symm_apply]
    rfl
  have key : Φ = ((stageCocone c j).ι.app t').hom.rTensor N' ∘ₗ lam :=
    LinearMap.ext_on_range hspan fun k => by
      change Φ (pres.var k) = ((stageCocone c j).ι.app t').hom.rTensor N' (lam (pres.var k))
      rw [pres.toIsPresentation.desc_var]
      exact (hz' k).symm
  refine ⟨t'.right, t'.hom, ψ, ExtendScalars.hom_ext fun n => ?_⟩
  let e := extendScalarsComp' (R.map t'.hom).hom (c.ι.app t'.right).hom (c.ι.app j).hom
    (congrArg CommRingCat.Hom.hom (c.w t'.hom).symm)
  refine (congr($key n)).trans ((extendScalarsComp'_inv_app_one_tmul t' N' (lam n)).symm.trans
    (congrArg (fun x => e.inv.app N' x) ?_))
  rw [← hψ n]
  exact (congrArg ((extendScalars (c.ι.app t'.right).hom).map ψ)
    (extendScalarsComp'_hom_app_tmul _ _ _ _ N 1 n)).symm

end Descent

end Module.FinitePresentation
