/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Affine charts of the Grassmannian functor

Mathlib's `Module.Grassmannian.functor` sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`, the
submodules of `A ⊗[R] M` whose quotient is finite projective of constant rank `k`. For
`x : Fin k → M`, a point `N` lies in the chart of `x` when the map `A^k → (A ⊗[R] M) ⧸ N` sending
the `i`-th basis vector to the class of `1 ⊗ₜ x i` is bijective. This file shows that charts are
subfunctors cut out by an open condition, that the coordinate charts of `R^n` are corepresented by
polynomial algebras, and that the coordinate charts cover Zariski-locally. These are the algebraic
steps of Stacks' proof that the Grassmannian functor is representable (Tag 089T); the Zariski sheaf
property and the gluing are not here.

## Main definitions

* `Module.Grassmannian.IsInChart x N`: `N` lies in the chart of `x`.
* `Module.Grassmannian.chartFunctor x`: the chart of `x`, a subfunctor of
  `Module.Grassmannian.functor`.
* `Module.Grassmannian.chartEquivRetraction`: the points of the chart of `x` over `A` are the
  retractions of `A^k → A ⊗[R] M`.
* `Module.Grassmannian.chartCorepresentableBy`: for `e : Fin k ↪ Fin n`, the chart of the standard
  basis vectors `Pi.single (e i) 1` of `R^n` is corepresented by
  `MvPolynomial (Fin k × {j // j ∉ Set.range e}) R`.

## Main results

* `Module.Grassmannian.isInChart_map`: charts are stable under base change.
* `Module.Grassmannian.exists_opens_isInChart_iff`: the chart condition is open.
* `Module.Grassmannian.exists_isInChart_away`: every point of `G(k, A ⊗[R] R^n; A)` is in some
  coordinate chart over a basic open `D(f)` around any given prime.
  `Module.Grassmannian.exists_isInChart_comp_away` is the same statement for the charts of a
  finite family spanning `M`.

## Implementation notes

Mathlib's Grassmannian parametrizes quotients of rank `k`, not subspaces (see the module docstring
of `Mathlib/RingTheory/Grassmannian.lean`), so the chart coordinates are the entries of a
retraction `A ⊗[R] R^n → A^k` of the chart map. Its columns at `range e` are the standard basis
vectors and the other `n - k` columns are free: these are the `k * (n - k)` coordinates
`Fin k × {j // j ∉ Set.range e}`.

Stacks writes `G(k, n)` for the quotients of rank `n - k` and asks for surjectivity in the chart
condition. A surjection `A^k → Q` onto a finite projective module of constant rank `k` is
bijective, so the two conditions agree. Openness and covering go through the support of the
cokernel of the chart map, which is closed, and its fibres at primes.

Of the TODO list in `Mathlib/RingTheory/Grassmannian.lean`, this file does the items `chart x`, as
the predicate `IsInChart x`, and `chartFunctor x`. The subspace convention, Grassmannians of
schemes and quasi-coherent sheaves, and the representability of `Module.Grassmannian.functor`
remain; no scheme appears here.

## References

* [Stacks: Tag 089T](https://stacks.math.columbia.edu/tag/089T)

## Tags

Grassmannian, affine chart, open subfunctor, retraction
-/

universe u v w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

section Auxiliary

/-- A surjection from `A^k` onto a finite projective `A`-module of constant rank `k` is
bijective: its kernel is a direct summand of rank zero. -/
private theorem bijective_of_surjective {A Q : Type*} [CommRing A] [AddCommGroup Q] [Module A Q]
    [Module.Projective A Q] {k : ℕ} (hQ : ∀ p, rankAtStalk (R := A) Q p = k)
    {φ : (Fin k → A) →ₗ[A] Q} (hφ : Function.Surjective φ) : Function.Bijective φ := by
  have : Module.Finite A Q := Module.Finite.of_surjective φ hφ
  obtain ⟨l, hl⟩ := Module.projective_lifting_property φ LinearMap.id hφ
  let e := ((LinearMap.exact_subtype_ker_map φ).splitSurjectiveEquiv
    (LinearMap.ker φ).injective_subtype ⟨l, hl⟩).1
  have : Module.Finite A (LinearMap.ker φ) :=
    Module.Finite.of_surjective (LinearMap.fst A _ Q ∘ₗ e.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  have : Module.Flat A (LinearMap.ker φ) :=
    Module.Flat.of_retract (e.symm.toLinearMap ∘ₗ LinearMap.inl A _ Q)
      (LinearMap.fst A _ Q ∘ₗ e.toLinearMap) (by ext; simp)
  have h0 : rankAtStalk (R := A) (LinearMap.ker φ) = 0 := by
    ext p
    have := p.nontrivial
    have h := congrFun ((rankAtStalk_eq_of_equiv e).trans (rankAtStalk_prod _ Q)) p
    simp only [rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun, Pi.add_apply, hQ p] at h
    simpa using h
  have := rankAtStalk_eq_zero_iff_subsingleton.mp h0
  exact ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker φ).eq_bot_of_subsingleton, hφ⟩

/-- Base change is right exact: `φ ⊗ B` is surjective iff `B ⊗ coker φ` vanishes. -/
private theorem surjective_baseChange_iff {A B F Q : Type*} [CommRing A] [Ring B]
    [Algebra A B] [AddCommGroup F] [Module A F] [AddCommGroup Q] [Module A Q]
    (φ : F →ₗ[A] Q) :
    Function.Surjective (φ.baseChange B) ↔
      Subsingleton (B ⊗[A] (Q ⧸ LinearMap.range φ)) := by
  have hex := lTensor_exact B (LinearMap.exact_map_mkQ_range φ) (Submodule.mkQ_surjective _)
  have hsurj := LinearMap.lTensor_surjective B (Submodule.mkQ_surjective (LinearMap.range φ))
  rw [LinearMap.baseChange_eq_lTensor]
  refine ⟨fun h ↦ ⟨fun a b ↦ ?_⟩, fun h z ↦ (hex z).mp (Subsingleton.elim _ _)⟩
  obtain ⟨a, rfl⟩ := hsurj a
  obtain ⟨b, rfl⟩ := hsurj b
  obtain ⟨a, rfl⟩ := h a
  obtain ⟨b, rfl⟩ := h b
  rw [hex.apply_apply_eq_zero, hex.apply_apply_eq_zero]

/-- For a finite module `C`, a prime of `B` is in the support of `B ⊗[A] C` iff its contraction
is in the support of `C`. -/
private theorem mem_support_baseChange_iff {A B C : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup C] [Module A C] [Module.Finite A C] (q : PrimeSpectrum B) :
    q ∈ Module.support B (B ⊗[A] C) ↔ q.comap (algebraMap A B) ∈ Module.support A C := by
  set p := q.comap (algebraMap A B)
  let ι := Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId A B) rfl
  let _ := ι.toAlgebra
  have : IsScalarTower A p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (AlgebraTensorModule.cancelBaseChange A B q.asIdeal.ResidueField
      q.asIdeal.ResidueField C).nontrivial_congr,
    ← (AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField q.asIdeal.ResidueField
      q.asIdeal.ResidueField C).nontrivial_congr,
    Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]

/-- The base change to `B` of a linear map `g` out of `A^ι`, read on `B^ι`: it sends the `i`-th
basis vector to `1 ⊗ₜ g eᵢ`. -/
private theorem baseChange_comp_piScalarRight_symm {A B F : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [AddCommMonoid F] [Module A F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : (ι → A) →ₗ[A] F) :
    g.baseChange B ∘ₗ (piScalarRight A B B ι).symm.toLinearMap =
      Fintype.linearCombination B (fun i ↦ (1 : B) ⊗ₜ[A] g (Pi.single i 1)) := by
  refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
  simp [piScalarRight_symm_single]

end Auxiliary

section Chart

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

/-- `N` lies in the chart of `x : Fin k → M` when `A^k → A ⊗[R] M → (A ⊗[R] M) ⧸ N`, sending
the `i`-th basis vector to the class of `1 ⊗ₜ x i`, is bijective. -/
def IsInChart {A : Type w} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : G(k, A ⊗[R] M; A)) : Prop :=
  Function.Bijective ((N : Submodule A (A ⊗[R] M)).mkQ ∘ₗ
    Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i))

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The chart map of `x` over `B`, followed by `baseChangeMkQ`, is the base change of the chart
map over `A`. -/
private theorem baseChangeMkQ_comp_linearCombination [Algebra A B] [IsScalarTower R A B]
    (x : Fin k → M) (N : Submodule A (A ⊗[R] M)) :
    baseChangeMkQ B N ∘ₗ Fintype.linearCombination B (fun i ↦ (1 : B) ⊗ₜ[R] x i) =
      (N.mkQ ∘ₗ Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i)).baseChange B ∘ₗ
        (piScalarRight A B B (Fin k)).symm.toLinearMap := by
  rw [baseChange_comp_piScalarRight_symm]
  refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
  simp [baseChangeMkQ]

/-- The chart condition at `map f N`, read off the cokernel of the chart map at `N`. -/
private theorem isInChart_map_iff (x : Fin k → M) (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    IsInChart x (map f N) ↔ ∀ q : PrimeSpectrum B, q.comap (f : A →+* B) ∉
      Module.support A (((A ⊗[R] M) ⧸ (N : Submodule A (A ⊗[R] M))) ⧸ LinearMap.range
        ((N : Submodule A (A ⊗[R] M)).mkQ ∘ₗ
          Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i))) := by
  algebraize [f.toRingHom]
  set φ := (N : Submodule A (A ⊗[R] M)).mkQ ∘ₗ
    Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i)
  have h1 : IsInChart x (map f N) ↔ Function.Surjective
      ((map f N : Submodule B (B ⊗[R] M)).mkQ ∘ₗ
        Fintype.linearCombination B (fun i ↦ (1 : B) ⊗ₜ[R] x i)) :=
    ⟨fun h ↦ h.2, fun h ↦ bijective_of_surjective (map f N).rankAtStalk_eq h⟩
  rw [h1]
  change Function.Surjective ((LinearMap.ker (baseChangeMkQ B N.toSubmodule)).mkQ ∘ₗ _) ↔ _
  rw [← EquivLike.comp_surjective _ (baseChangeMkQEquiv (B := B) N.toSubmodule),
    ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp, ← LinearMap.comp_assoc]
  have : (baseChangeMkQEquiv (B := B) N.toSubmodule).toLinearMap ∘ₗ
      (LinearMap.ker (baseChangeMkQ B N.toSubmodule)).mkQ = baseChangeMkQ B N.toSubmodule := by
    ext z
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ (baseChangeMkQ_surjective _) _
  rw [this, baseChangeMkQ_comp_linearCombination, LinearMap.coe_comp, LinearEquiv.coe_coe,
    EquivLike.surjective_comp, surjective_baseChange_iff, ← Module.support_eq_empty_iff (R := B),
    Set.eq_empty_iff_forall_notMem]
  exact forall_congr' fun q ↦ (mem_support_baseChange_iff q).not

/-- Charts are stable under base change. -/
theorem isInChart_map (x : Fin k → M) (f : A →ₐ[R] B) {N : G(k, A ⊗[R] M; A)}
    (h : IsInChart x N) : IsInChart x (map f N) := by
  have := Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr h.2)
  simp [isInChart_map_iff, Module.support_eq_empty]

/-- The chart condition is open: there is an open `U` of `PrimeSpectrum A` such that, for every
`R`-algebra map `φ : A → B`, the base change `map φ N` lies in the chart of `x` exactly when
`PrimeSpectrum.comap φ` lands in `U`. -/
theorem exists_opens_isInChart_iff (x : Fin k → M) (N : G(k, A ⊗[R] M; A)) :
    ∃ U : TopologicalSpace.Opens (PrimeSpectrum A),
      ∀ (B : Type w) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        IsInChart x (map φ N) ↔ Set.range (PrimeSpectrum.comap (φ : A →+* B)) ⊆ U := by
  let ψ := (N : Submodule A (A ⊗[R] M)).mkQ ∘ₗ
    Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i)
  refine ⟨⟨(Module.support A (_ ⧸ LinearMap.range ψ))ᶜ, Module.isClosed_support.isOpen_compl⟩,
    fun B _ _ φ ↦ ?_⟩
  rw [isInChart_map_iff, Set.range_subset_iff]
  rfl

/-- If `y ∈ N`, its image under `f ⊗ id : A ⊗[R] M → B ⊗[R] M` lies in `map f N`. -/
private theorem rTensor_mem_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) {y : A ⊗[R] M}
    (hy : y ∈ (N : Submodule A (A ⊗[R] M))) :
    f.toLinearMap.rTensor M y ∈ (map f N : Submodule B (B ⊗[R] M)) := by
  algebraize [f.toRingHom]
  change baseChangeMkQ B N.toSubmodule _ = 0
  have key : ∀ z : A ⊗[R] M, baseChangeMkQ B N.toSubmodule (f.toLinearMap.rTensor M z) =
      (1 : B) ⊗ₜ[A] (N : Submodule A (A ⊗[R] M)).mkQ z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      simp only [baseChangeMkQ, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
        Submodule.mkQ_apply]
      rw [show a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) by simp [smul_tmul'], Submodule.Quotient.mk_smul,
        tmul_smul, smul_tmul', Algebra.smul_def, mul_one]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz, tmul_add]
  rw [key, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hy, tmul_zero]

end BaseChange

section Functor

/-- The chart of `x : Fin k → M` as a subfunctor of the Grassmannian functor. -/
def chartFunctor (x : Fin k → M) : Subfunctor (functor.{u, v, w} (R := R) (M := M) k) where
  obj _ := {N | IsInChart x N}
  map f _ hN := isInChart_map x f.hom hN

@[simp]
theorem mem_chartFunctor_obj (x : Fin k → M) {A : CommAlgCat.{w, u} R}
    (N : G(k, A ⊗[R] M; A)) : N ∈ (chartFunctor x).obj A ↔ IsInChart x N :=
  Iff.rfl

end Functor

section Retraction

variable (x : Fin k → M) (A : Type w) [CommRing A] [Algebra R A]

/-- The point of `G(k, A ⊗[R] M; A)` given by the kernel of a surjection onto `A^k`. -/
private noncomputable def ofSurjective {r : A ⊗[R] M →ₗ[A] (Fin k → A)}
    (hr : Function.Surjective r) : G(k, A ⊗[R] M; A) where
  toSubmodule := LinearMap.ker r
  finite_quotient := Module.Finite.equiv (r.quotKerEquivOfSurjective hr).symm
  projective_quotient := Module.Projective.of_equiv (r.quotKerEquivOfSurjective hr).symm
  rankAtStalk_eq p := by
    have := p.nontrivial
    rw [rankAtStalk_eq_of_equiv (r.quotKerEquivOfSurjective hr)]
    simp

private theorem surjective_of_comp_eq_id {r : A ⊗[R] M →ₗ[A] (Fin k → A)}
    (hr : r ∘ₗ Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i) = LinearMap.id) :
    Function.Surjective r :=
  fun v ↦ ⟨_, LinearMap.congr_fun hr v⟩

/-- The points of the chart of `x` over `A` are the retractions of the map `A^k → A ⊗[R] M`
sending the `i`-th basis vector to `1 ⊗ₜ x i`: a point `N` corresponds to the retraction with
kernel `N` (`ker_chartEquivRetraction`). -/
noncomputable def chartEquivRetraction :
    {N : G(k, A ⊗[R] M; A) // IsInChart x N} ≃
      {r : A ⊗[R] M →ₗ[A] (Fin k → A) //
        r ∘ₗ Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i) = LinearMap.id} where
  toFun N := ⟨(LinearEquiv.ofBijective _ N.2).symm.toLinearMap ∘ₗ
      (N.1 : Submodule A (A ⊗[R] M)).mkQ,
    LinearMap.ext fun v ↦ (LinearEquiv.ofBijective _ N.2).symm_apply_apply v⟩
  invFun r := ⟨ofSurjective A (surjective_of_comp_eq_id x A r.2), by
      change Function.Bijective ((LinearMap.ker r.1).mkQ ∘ₗ _)
      rw [← EquivLike.comp_bijective _
        (r.1.quotKerEquivOfSurjective (surjective_of_comp_eq_id x A r.2))]
      convert Function.bijective_id
      funext v
      exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).trans
        (LinearMap.congr_fun r.2 v)⟩
  left_inv N := by
    ext : 2
    change LinearMap.ker (_ ∘ₗ _) = _
    rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
  right_inv r := by
    refine Subtype.ext (LinearMap.ext fun y ↦ ?_)
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq]
    change Submodule.Quotient.mk y =
      Submodule.Quotient.mk (Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i) (r.1 y))
    rw [Submodule.Quotient.eq]
    change r.1 (y - _) = 0
    rw [map_sub, ← LinearMap.comp_apply r.1, r.2, LinearMap.id_apply, sub_self]

@[simp]
theorem ker_chartEquivRetraction (N : {N : G(k, A ⊗[R] M; A) // IsInChart x N}) :
    LinearMap.ker (chartEquivRetraction x A N).1 = N.1 := by
  change LinearMap.ker (_ ∘ₗ _) = _
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

@[simp]
theorem toSubmodule_chartEquivRetraction_symm
    (r : {r : A ⊗[R] M →ₗ[A] (Fin k → A) //
      r ∘ₗ Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i) = LinearMap.id}) :
    ((chartEquivRetraction x A).symm r).1.toSubmodule = LinearMap.ker r.1 :=
  rfl

variable {A} in
/-- The retraction attached to `map f N` is the base change of the retraction attached to `N`:
it sends `1 ⊗ₜ m` to the image under `f` of the value of the retraction of `N` at `1 ⊗ₜ m`. -/
theorem chartEquivRetraction_map_apply_tmul {B : Type w} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (N : {N : G(k, A ⊗[R] M; A) // IsInChart x N}) (m : M) :
    (chartEquivRetraction x B ⟨map f N.1, isInChart_map x f N.2⟩).1 ((1 : B) ⊗ₜ[R] m) =
      f ∘ (chartEquivRetraction x A N).1 ((1 : A) ⊗ₜ[R] m) := by
  set v := (chartEquivRetraction x A N).1 ((1 : A) ⊗ₜ[R] m)
  change (LinearEquiv.ofBijective _ (isInChart_map x f N.2)).symm (Submodule.Quotient.mk _) = _
  rw [LinearEquiv.symm_apply_eq]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk
    (Fintype.linearCombination B (fun i ↦ (1 : B) ⊗ₜ[R] x i) (f ∘ v))
  rw [Submodule.Quotient.eq]
  have h : (1 : B) ⊗ₜ[R] m - Fintype.linearCombination B (fun i ↦ (1 : B) ⊗ₜ[R] x i) (f ∘ v) =
      f.toLinearMap.rTensor M
        ((1 : A) ⊗ₜ[R] m - Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] x i) v) := by
    simp [Fintype.linearCombination_apply, smul_tmul']
  rw [h]
  refine rTensor_mem_map f N.1 ((Submodule.Quotient.eq _).mp ?_)
  exact ((LinearEquiv.ofBijective _ N.2).apply_symm_apply _).symm

end Retraction

end Chart

section Corepresentable

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k n : ℕ}
  (b : Basis (Fin n) R M) (e : Fin k ↪ Fin n)

/-- The matrix of the retraction with coordinates `t`: the identity on `range e`, and the
column `t (·, j)` at `j ∉ range e`. -/
private noncomputable def coordMatrix {Y : Type*} [Zero Y] [One Y]
    (t : Fin k × {j : Fin n // j ∉ Set.range e} → Y) (j : Fin n) : Fin k → Y :=
  if h : j ∈ Set.range e then Pi.single (e.invOfMemRange ⟨j, h⟩) 1 else fun i ↦ t (i, ⟨j, h⟩)

variable {x : Fin k → M} (hx : ∀ i, x i = b (e i))

/-- The coordinates of a retraction of the chart map of `x = b ∘ e` over `Y`: its entries outside
the columns `range e`. -/
private noncomputable def coordEquiv (Y : Type u) [CommRing Y] [Algebra R Y] :
    (Fin k × {j : Fin n // j ∉ Set.range e} → Y) ≃
      {r : Y ⊗[R] M →ₗ[Y] (Fin k → Y) //
        r ∘ₗ Fintype.linearCombination Y (fun i ↦ (1 : Y) ⊗ₜ[R] x i) = LinearMap.id} where
  toFun t := ⟨(b.baseChange Y).constr Y (coordMatrix e t), by
    refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.id_apply,
      Fintype.linearCombination_apply_single, one_smul]
    rw [hx, ← Basis.baseChange_apply, Basis.constr_basis, coordMatrix,
      dite_eq_left_of_eq_true (eq_true (Set.mem_range_self i)),
      Function.Embedding.right_inv_of_invOfMemRange]⟩
  invFun r s := r.1 ((1 : Y) ⊗ₜ[R] b s.2.1) s.1
  left_inv t := by
    funext ⟨i, j, hj⟩
    simp only
    rw [← Basis.baseChange_apply, Basis.constr_basis, coordMatrix,
      dite_eq_right_of_eq_false (eq_false hj)]
  right_inv r := by
    refine Subtype.ext ((b.baseChange Y).ext fun j ↦ ?_)
    rw [Basis.constr_basis, coordMatrix, Basis.baseChange_apply]
    split_ifs with hj
    · obtain ⟨i, rfl⟩ := hj
      rw [Function.Embedding.right_inv_of_invOfMemRange]
      have := LinearMap.congr_fun r.2 (Pi.single i 1)
      rw [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul,
        LinearMap.id_apply, hx] at this
      exact this.symm
    · rfl

/-- Algebra maps out of `MvPolynomial σ R` are their values on the variables. -/
private noncomputable def homEquivFun {σ : Type} (Y : CommAlgCat.{u, u} R) :
    (CommAlgCat.of R (MvPolynomial σ R) ⟶ Y) ≃ (σ → Y) where
  toFun f s := f.hom (MvPolynomial.X s)
  invFun t := CommAlgCat.ofHom (MvPolynomial.aeval t)
  left_inv f := CommAlgCat.hom_ext (MvPolynomial.algHom_ext fun s ↦ by simp)
  right_inv t := funext fun s ↦ by simp

/-- The chart of `x = b ∘ e` is corepresented by the polynomial algebra on
`Fin k × {j // j ∉ Set.range e}`. -/
private noncomputable def corepresentableByAux :
    (chartFunctor.{u, u, u} (R := R) (M := M) (k := k) x).toFunctor.CorepresentableBy
      (CommAlgCat.of R (MvPolynomial (Fin k × {j : Fin n // j ∉ Set.range e}) R)) where
  homEquiv {Y} := (homEquivFun Y).trans ((coordEquiv b e hx Y).trans
    (chartEquivRetraction x Y).symm)
  homEquiv_comp {Y Y'} g f := by
    set N := ((coordEquiv b e hx Y).trans (chartEquivRetraction x Y).symm) (homEquivFun Y f)
    apply (chartEquivRetraction x Y').injective
    refine Subtype.ext ((b.baseChange Y').ext fun j ↦ ?_)
    rw [Basis.baseChange_apply]
    refine Eq.trans ?_ (chartEquivRetraction_map_apply_tmul x g.hom N (b j)).symm
    simp only [N, Equiv.trans_apply, Equiv.apply_symm_apply]
    change (chartEquivRetraction x Y' ((chartEquivRetraction x Y').symm
      (coordEquiv b e hx Y' (homEquivFun Y' (f ≫ g))))).1 (1 ⊗ₜ b j) = _
    rw [Equiv.apply_symm_apply]
    change (b.baseChange Y').constr Y' _ (1 ⊗ₜ b j) =
      g.hom ∘ (b.baseChange Y).constr Y _ (1 ⊗ₜ b j)
    rw [← Basis.baseChange_apply, ← Basis.baseChange_apply, Basis.constr_basis,
      Basis.constr_basis]
    unfold coordMatrix
    split_ifs with hj
    · funext i
      simp only [Function.comp_apply, Pi.single_apply]
      split_ifs <;> simp
    · rfl

private theorem corepresentableByAux_homEquiv {Y : CommAlgCat.{u, u} R}
    (f : CommAlgCat.of R (MvPolynomial (Fin k × {j : Fin n // j ∉ Set.range e}) R) ⟶ Y)
    (s : Fin k × {j : Fin n // j ∉ Set.range e}) :
    (chartEquivRetraction x Y ((corepresentableByAux b e hx).homEquiv f)).1
      ((1 : Y) ⊗ₜ[R] b s.2.1) s.1 = f.hom (MvPolynomial.X s) := by
  change (chartEquivRetraction x Y ((chartEquivRetraction x Y).symm
    (coordEquiv b e hx Y (homEquivFun Y f)))).1 _ _ = _
  rw [Equiv.apply_symm_apply]
  exact congrFun ((coordEquiv b e hx Y).symm_apply_apply (homEquivFun Y f)) s

/-- **Affine charts.** The coordinate chart of `e : Fin k ↪ Fin n` in the Grassmannian of `R^n`
is corepresented by the polynomial algebra in the `k * (n - k)` variables
`Fin k × {j // j ∉ Set.range e}`. See `chartEquivRetraction_chartCorepresentableBy_homEquiv`
for the coordinates. -/
noncomputable def chartCorepresentableBy (e : Fin k ↪ Fin n) :
    (chartFunctor.{u, u, u} (R := R) (M := Fin n → R) (k := k)
        (fun i ↦ Pi.single (e i) 1)).toFunctor.CorepresentableBy
      (CommAlgCat.of R (MvPolynomial (Fin k × {j : Fin n // j ∉ Set.range e}) R)) :=
  corepresentableByAux (Pi.basisFun R (Fin n)) e fun i ↦ (Pi.basisFun_apply R (Fin n) (e i)).symm

/-- The retraction attached to the point of the coordinate chart of `e` classified by `f` has, at
`j ∉ range e`, the column `i ↦ f (X (i, j))`. Its columns at `range e` are the standard basis
vectors, since it is a retraction. -/
theorem chartEquivRetraction_chartCorepresentableBy_homEquiv (e : Fin k ↪ Fin n)
    {Y : CommAlgCat.{u, u} R}
    (f : CommAlgCat.of R (MvPolynomial (Fin k × {j : Fin n // j ∉ Set.range e}) R) ⟶ Y)
    (s : Fin k × {j : Fin n // j ∉ Set.range e}) :
    (chartEquivRetraction (fun i ↦ Pi.single (e i) 1) Y
      ((chartCorepresentableBy e).homEquiv f)).1 ((1 : Y) ⊗ₜ[R] Pi.single s.2.1 1) s.1 =
        f.hom (MvPolynomial.X s) := by
  rw [← Pi.basisFun_apply R (Fin n)]
  exact corepresentableByAux_homEquiv _ e _ f s

end Corepresentable

section Covering

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

/-- **Charts cover.** Let `s : Fin n → M` span `M`. For every point `N` of `G(k, A ⊗[R] M; A)`
and every prime `P` of `A`, there are `e : Fin k ↪ Fin n` and `f ∉ P` such that the base change
of `N` to `A_f` lies in the chart of `s ∘ e`. -/
theorem exists_isInChart_comp_away {n : ℕ} {s : Fin n → M}
    (hs : Submodule.span R (Set.range s) = ⊤) {A : Type w} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) (P : PrimeSpectrum A) :
    ∃ (e : Fin k ↪ Fin n) (f : A), f ∉ P.asIdeal ∧
      IsInChart (s ∘ e) (map (IsScalarTower.toAlgHom R A (Localization.Away f)) N) := by
  let K := P.asIdeal.ResidueField
  let ψ := (N : Submodule A (A ⊗[R] M)).mkQ ∘ₗ
    Fintype.linearCombination A (fun j ↦ (1 : A) ⊗ₜ[R] s j)
  have hψ : Function.Surjective ψ := by
    refine (Submodule.mkQ_surjective _).comp ?_
    have h := baseChange_comp_piScalarRight_symm (B := A) (Fintype.linearCombination R s)
    simp only [Fintype.linearCombination_apply_single, one_smul] at h
    rw [← h, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.surjective_comp]
    exact LinearMap.baseChange_surjective A
      ((span_range_eq_top_iff_surjective_fintypeLinearCombination R s).mp hs)
  -- The images of the `s j` span the fiber at `P`, which has dimension `k`.
  let v : Fin n → K ⊗[A] ((A ⊗[R] M) ⧸ (N : Submodule A (A ⊗[R] M))) :=
    fun j ↦ (1 : K) ⊗ₜ[A] ψ (Pi.single j 1)
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    rw [span_range_eq_top_iff_surjective_fintypeLinearCombination,
      ← baseChange_comp_piScalarRight_symm, LinearMap.coe_comp, LinearEquiv.coe_coe,
      EquivLike.surjective_comp]
    exact LinearMap.baseChange_surjective K hψ
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  rw [hv] at hspan
  have : _root_.Finite κ := _root_.Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k :=
    ((Module.finrank_eq_card_basis (Basis.mk hli hspan.ge)).symm.trans
      (Module.rankAtStalk_eq P).symm).trans (N.rankAtStalk_eq P)
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  let e : Fin k ↪ Fin n := σ.toEmbedding.trans ⟨a, ha⟩
  -- So the cokernel of the chart map of `s ∘ e` vanishes at `P`, hence on some `D(f)`.
  let φ := (N : Submodule A (A ⊗[R] M)).mkQ ∘ₗ
    Fintype.linearCombination A (fun i ↦ (1 : A) ⊗ₜ[R] (s ∘ e) i)
  have hφP : P ∉ Module.support A (((A ⊗[R] M) ⧸ (N : Submodule A (A ⊗[R] M))) ⧸
      LinearMap.range φ) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton, ← surjective_baseChange_iff,
      ← EquivLike.surjective_comp (piScalarRight A K K (Fin k)).symm, ← LinearEquiv.coe_coe,
      ← LinearMap.coe_comp, baseChange_comp_piScalarRight_symm,
      ← span_range_eq_top_iff_surjective_fintypeLinearCombination]
    have : (fun i ↦ (1 : K) ⊗ₜ[A] φ (Pi.single i 1)) = (v ∘ a) ∘ σ := by
      funext i
      simp [φ, ψ, v, e]
    rw [this, EquivLike.range_comp, hspan]
  rw [Module.mem_support_iff_of_finite, IsConcreteLE.not_le_iff_exists] at hφP
  obtain ⟨f, hf, hfP⟩ := hφP
  refine ⟨e, f, hfP, (isInChart_map_iff _ _ _).mpr fun q hq ↦ ?_⟩
  rw [Module.mem_support_iff_of_finite] at hq
  have hfq : algebraMap A (Localization.Away f) f ∈ q.asIdeal := hq hf
  exact q.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hfq (IsLocalization.Away.algebraMap_isUnit f))

/-- **Charts cover**, for `R^n`: for every point `N` of `G(k, A ⊗[R] R^n; A)` and every prime `P`
of `A`, there are `e : Fin k ↪ Fin n` and `f ∉ P` such that the base change of `N` to `A_f` lies
in the coordinate chart of `e`. -/
theorem exists_isInChart_away {n : ℕ} {A : Type w} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] (Fin n → R); A)) (P : PrimeSpectrum A) :
    ∃ (e : Fin k ↪ Fin n) (f : A), f ∉ P.asIdeal ∧
      IsInChart (fun i ↦ Pi.single (e i) 1)
        (map (IsScalarTower.toAlgHom R A (Localization.Away f)) N) := by
  have hs : Submodule.span R (Set.range fun j : Fin n ↦ Pi.single j (1 : R)) = ⊤ := by
    rw [← (Pi.basisFun R (Fin n)).span_eq]
    congr 2
    exact funext fun j ↦ (Pi.basisFun_apply R (Fin n) j).symm
  exact exists_isInChart_comp_away hs N P

end Covering

end Module.Grassmannian
