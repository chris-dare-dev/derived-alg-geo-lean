/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Krull--Akizuki for rings between a one-dimensional Noetherian domain and its fraction field

Let `R` be a one-dimensional Noetherian domain with fraction field `K`. We prove that every
`R`-submodule `M` of `K` satisfies `length_R (M / x M) ≤ length_R (R / x R)` for nonzero `x : R`,
and that every subring of `K` containing `R` is Noetherian.

## Main results

* `Submodule.length_quotient_smul_top_le_ord`: the length bound, Stacks 00PE with `r = 1`.
* `IsNoetherianRing.of_le_of_krullDimLE_one`: every ring between `R` and `K` is Noetherian,
  Stacks 00PG with `L = K`.

## Implementation notes

For a finitely generated `M`, clearing denominators embeds `M` as an ideal `J` of `R`, and
the exact sequences `J/xJ → R/xJ → R/J` and `R/J → R/xJ → R/xR` give
`length (J / x J) = length (R / x R)` once `R / J` has finite length. A general `M` reduces
to this case, because a chain of submodules of `M / x M` is already seen by the quotient of a
finitely generated submodule of `M`.

Neither step uses that `R` is local, so the statements here do not assume it. The extension of
Stacks 00PG to a finite extension `L / K` is not proved.

## References

* [Stacks: Lemma 10.119.9](https://stacks.math.columbia.edu/tag/00PE)
* [Stacks: Lemma 10.119.12](https://stacks.math.columbia.edu/tag/00PG)

## Tags

Krull--Akizuki, Noetherian ring, length, fraction field
-/

open Module Pointwise

section Core

variable {R : Type*} [CommRing R] [IsDomain R] {N : Type*} [AddCommGroup N] [Module R N]

/-- If `g : N → R` is injective and `R / range g` has finite length, then the length of `N / x N`
is the order of vanishing of `x`. -/
private lemma length_quotient_smul_top_eq_ord (g : N →ₗ[R] R) (hg : Function.Injective g)
    {x : R} (hx : x ≠ 0) (hfin : Module.length R (R ⧸ LinearMap.range g) ≠ ⊤) :
    Module.length R (N ⧸ (x • ⊤ : Submodule R N)) = Ring.ord R x := by
  set J : Submodule R R := LinearMap.range g with hJ
  have h1 := Module.length_eq_add_of_exact (Ideal.mulQuot x J) (Ideal.quotOfMul x J)
    (Ideal.mulQuot_injective J (mem_nonZeroDivisors_of_ne_zero hx)) (Ideal.quotOfMul_surjective J)
    (Ideal.exact_mulQuot_quotOfMul J)
  have hle : x • J ≤ J := by
    rintro _ ⟨a, ha, rfl⟩
    exact J.smul_mem x ha
  have hmap : (x • ⊤ : Submodule R N) ≤ (x • J).comap g := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨g a, ⟨a, rfl⟩, by simp⟩
  let ι : (N ⧸ (x • ⊤ : Submodule R N)) →ₗ[R] R ⧸ (x • J) :=
    Submodule.mapQ _ _ g hmap
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ n =>
      change Submodule.Quotient.mk (g n) = 0 at hq
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hq
      obtain ⟨_, ⟨m, rfl⟩, hm⟩ := hq
      have : n = x • m := hg (by simpa using hm.symm)
      rw [Submodule.Quotient.mk_eq_zero, this]
      exact ⟨m, trivial, rfl⟩
  have hex : Function.Exact ι (Submodule.factor hle) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ r =>
      change Submodule.Quotient.mk r = 0 ↔ _
      constructor
      · intro h
        rw [Submodule.Quotient.mk_eq_zero] at h
        obtain ⟨n, rfl⟩ := h
        exact ⟨Submodule.Quotient.mk n, rfl⟩
      · rintro ⟨p, hp⟩
        induction p using Submodule.Quotient.induction_on with
        | _ n =>
          rw [Submodule.Quotient.mk_eq_zero]
          have h3 : Submodule.Quotient.mk (g n) = (Submodule.Quotient.mk r : R ⧸ x • J) := hp
          rw [Submodule.Quotient.eq] at h3
          have := J.sub_mem ⟨n, rfl⟩ (hle h3)
          simpa using this
  have h2 := Module.length_eq_add_of_exact ι (Submodule.factor hle) hι
    (Submodule.factor_surjective hle) hex
  rw [h1] at h2
  rw [add_comm] at h2
  exact (WithTop.add_right_inj hfin).mp h2.symm

end Core

section Chains

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A chain of length `n` in the submodules of `M / x M` is already a chain in `N / x N` for a
finitely generated submodule `N` of `M`. -/
private lemma exists_fg_le_length_quotient_smul_top (x : R) {n : ℕ}
    (hn : (n : ℕ∞) ≤ Module.length R (M ⧸ (x • ⊤ : Submodule R M))) :
    ∃ N : Submodule R M, N.FG ∧
      (n : ℕ∞) ≤ Module.length R (N ⧸ (x • ⊤ : Submodule R N)) := by
  rw [← WithBot.coe_le_coe, Module.coe_length] at hn
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (by simpa using hn)
  subst hl
  have hstep : ∀ i : Fin l.length, ∃ q : M ⧸ (x • ⊤ : Submodule R M),
      q ∈ l i.succ ∧ q ∉ l i.castSucc := fun i => by
    obtain ⟨q, hq, hq'⟩ := IsConcreteLE.exists_of_lt (show l i.castSucc < l i.succ from l.step i)
    exact ⟨q, hq, hq'⟩
  choose q hq hq' using hstep
  choose m hm using fun i => Submodule.Quotient.mk_surjective _ (q i)
  refine ⟨Submodule.span R (Set.range m), Submodule.fg_span (Set.finite_range m), ?_⟩
  set N := Submodule.span R (Set.range m)
  have hmap : (x • ⊤ : Submodule R N) ≤
      LinearMap.ker ((Submodule.mkQ (x • ⊤ : Submodule R M)).comp N.subtype) := by
    rintro _ ⟨a, -, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply]
    change Submodule.Quotient.mk (x • (a : M)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨a, trivial, rfl⟩
  let φ := Submodule.liftQ (x • ⊤ : Submodule R N) _ hmap
  have hφ : ∀ i, φ (Submodule.Quotient.mk ⟨m i, Submodule.subset_span ⟨i, rfl⟩⟩) = q i := by
    intro i
    simp [φ, hm]
  have hmono : StrictMono fun i => (l i).comap φ := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    refine lt_of_le_of_ne (Submodule.comap_mono (l.monotone (Fin.castSucc_le_succ i))) fun h => ?_
    apply hq' i
    have hz : Submodule.Quotient.mk (⟨m i, Submodule.subset_span ⟨i, rfl⟩⟩ : N) ∈
        (l i.succ).comap φ := by
      rw [Submodule.mem_comap, hφ]
      exact hq i
    rw [← h] at hz
    simpa [hφ] using hz
  have := Order.LTSeries.length_le_krullDim (LTSeries.mk l.length (fun i => (l i).comap φ) hmono)
  rw [← Module.coe_length] at this
  exact_mod_cast this
end Chains

section Fraction

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The length bound for a finitely generated module embedded in the fraction field. -/
private lemma length_quotient_smul_top_le_ord_of_finite {N : Type*} [AddCommGroup N]
    [Module R N] [Module.Finite R N] (j : N →ₗ[R] K)
    (hj : Function.Injective j) {x : R} (hx : x ≠ 0) :
    Module.length R (N ⧸ (x • ⊤ : Submodule R N)) ≤ Ring.ord R x := by
  by_cases hN : Subsingleton N
  · rw [Module.length_eq_zero]
    exact zero_le
  classical
  rw [not_subsingleton_iff_nontrivial] at hN
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := N)
  obtain ⟨⟨d, hd⟩, hdint⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) (s.image j)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  let φ : N →ₗ[R] K := d • j
  have hφ : ∀ n, φ n = d • j n := fun n => rfl
  have hrange : ∀ n, φ n ∈ LinearMap.range (Algebra.linearMap R K) := by
    have hle : (⊤ : Submodule R N) ≤
        (LinearMap.range (Algebra.linearMap R K)).comap φ := by
      rw [← hs, Submodule.span_le]
      intro n hn
      obtain ⟨r, hr⟩ := hdint (j n) (Finset.mem_image_of_mem _ hn)
      exact ⟨r, by simpa [hφ] using hr⟩
    intro n
    exact hle (Submodule.mem_top (x := n))
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hj
    have : d • j a = d • j b := hab
    rw [Algebra.smul_def, Algebra.smul_def] at this
    exact mul_left_cancel₀ (by simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0) this
  have hrange' : ∀ n, φ n ∈ LinearMap.range (Algebra.linearMap R K) := hrange
  let e := LinearEquiv.ofInjective (Algebra.linearMap R K) (FaithfulSMul.algebraMap_injective R K)
  let g : N →ₗ[R] R := e.symm ∘ₗ φ.codRestrict _ hrange'
  have hg : Function.Injective g := by
    refine e.symm.injective.comp ?_
    intro a b hab
    exact hφinj (congrArg Subtype.val hab)
  obtain ⟨n₀, hn₀⟩ := exists_ne (0 : N)
  have hy : g n₀ ≠ 0 := fun h => hn₀ (hg (by simpa using h))
  have hfin : Module.length R (R ⧸ LinearMap.range g) ≠ ⊤ := by
    have hsp : Ideal.span {g n₀} ≤ LinearMap.range g := by
      rw [Ideal.span_le]
      simp
    refine ne_top_of_le_ne_top (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy)) ?_
    exact Module.length_le_of_surjective _ (Submodule.factor_surjective hsp)
  exact (length_quotient_smul_top_eq_ord g hg hx hfin).le


/-- The length bound for any module embedded in the fraction field. -/
private lemma length_quotient_smul_top_le_ord_of_injective {M : Type*} [AddCommGroup M]
    [Module R M] (j : M →ₗ[R] K) (hj : Function.Injective j) {x : R} (hx : x ≠ 0) :
    Module.length R (M ⧸ (x • ⊤ : Submodule R M)) ≤ Ring.ord R x := by
  by_contra h
  rw [not_le] at h
  have hne : Ring.ord R x ≠ ⊤ := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hc] at h
  have h1 : ((c + 1 : ℕ) : ℕ∞) ≤ Module.length R (M ⧸ (x • ⊤ : Submodule R M)) := by
    exact_mod_cast Order.add_one_le_of_lt h
  obtain ⟨N, hN, hle⟩ := exists_fg_le_length_quotient_smul_top x h1
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have h2 := length_quotient_smul_top_le_ord_of_finite (j ∘ₗ N.subtype)
    (hj.comp N.injective_subtype) hx
  rw [← hc] at h2
  have := hle.trans h2
  norm_cast at this
  omega

/-- **Krull--Akizuki, length bound** (Stacks 00PE with `r = 1`). If `R` is a one-dimensional
Noetherian domain with fraction field `K`, then for every `R`-submodule `M` of `K` and nonzero
`x : R`, the length of `M / x M` as an `R`-module is at most the length of `R / x R`. The
quotient is by `x • ⊤` in `M`, not by `x M` inside `K`. -/
@[stacks 00PE "r = 1"]
theorem Submodule.length_quotient_smul_top_le_ord (M : Submodule R K) {x : R} (hx : x ≠ 0) :
    Module.length R (M ⧸ (x • ⊤ : Submodule R M)) ≤ Ring.ord R x :=
  length_quotient_smul_top_le_ord_of_injective M.subtype M.injective_subtype hx

section Algebra

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra A K] [IsScalarTower R A K]
  [FaithfulSMul A K]

include R K

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- A nonzero ideal of a ring between `R` and `K` contains the image of a nonzero element
of `R`. -/
private lemma exists_mem_ideal_of_ne_bot (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x : R, x ≠ 0 ∧ algebraMap R A x ∈ I := by
  obtain ⟨y, hyI, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (algebraMap A K y)
  have hb : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hy' : algebraMap A K y ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective A K).ne hy
  have hK : algebraMap R K a = algebraMap A K (y * algebraMap R A b) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact hab.symm
  have hA : algebraMap R A a = y * algebraMap R A b := by
    apply FaithfulSMul.algebraMap_injective A K
    rw [← IsScalarTower.algebraMap_apply, hK]
  refine ⟨a, ?_, hA ▸ I.mul_mem_right _ hyI⟩
  rintro rfl
  rw [map_zero] at hA
  have hA' := congrArg (algebraMap A K) hA.symm
  rw [map_mul, map_zero, ← IsScalarTower.algebraMap_apply, mul_eq_zero] at hA'
  rcases hA' with h | h
  · exact hy' h
  · exact hb ((FaithfulSMul.algebraMap_injective R K) (by rw [h, map_zero]))

/-- Every ring `A` with an `R`-algebra structure and an injective map to `K` is Noetherian. -/
private lemma isNoetherianRing_of_algebra : IsNoetherianRing A := by
  classical
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact Submodule.fg_bot
  obtain ⟨x, hx, hxI⟩ := exists_mem_ideal_of_ne_bot (R := R) (K := K) I hI
  let j : A →ₗ[R] K := (Algebra.linearMap A K).restrictScalars R
  have hj : Function.Injective j := FaithfulSMul.algebraMap_injective A K
  have hlen := length_quotient_smul_top_le_ord_of_injective j hj hx
  have hnoeth : IsNoetherian R (A ⧸ (x • ⊤ : Submodule R A)) := by
    have hfin : IsFiniteLength R (A ⧸ (x • ⊤ : Submodule R A)) := by
      rw [← Module.length_ne_top_iff]
      exact ne_top_of_le_ne_top (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx)) hlen
    exact (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  set P := (I.restrictScalars R).map (Submodule.mkQ (x • ⊤ : Submodule R A)) with hP
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hSP : ∀ s ∈ S, ∃ i ∈ I, Submodule.Quotient.mk i = s := fun s hs => by
    have : s ∈ P := hS ▸ Submodule.subset_span hs
    simpa [hP] using this
  choose! t htI hts using hSP
  let J : Ideal A := Ideal.span (insert (algebraMap R A x) (t '' (S : Set _)))
  have hJI : J ≤ I := by
    rw [Ideal.span_le]
    rintro _ (rfl | ⟨s, hs, rfl⟩)
    · exact hxI
    · exact htI s hs
  have hIJ : I ≤ J := by
    intro z hz
    have hxJ : algebraMap R A x ∈ J := Ideal.subset_span (Set.mem_insert _ _)
    have hzP : (Submodule.mkQ (x • ⊤ : Submodule R A)) z ∈ P := ⟨z, hz, rfl⟩
    have hPJ : P ≤ (J.restrictScalars R).map (Submodule.mkQ (x • ⊤ : Submodule R A)) := by
      rw [← hS, Submodule.span_le]
      intro s hs
      exact ⟨t s, Ideal.subset_span (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩), hts s hs⟩
    obtain ⟨w, hwJ, hw⟩ := hPJ hzP
    have hzw : z - w ∈ (x • ⊤ : Submodule R A) := by
      rw [← Submodule.Quotient.eq]
      exact hw.symm
    obtain ⟨a, -, ha⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzw
    have : z = w + algebraMap R A x * a := by
      rw [Algebra.smul_def] at ha
      rw [ha]; ring
    rw [this]
    exact J.add_mem hwJ (J.mul_mem_right _ hxJ)
  refine ⟨insert (algebraMap R A x) (S.image t), ?_⟩
  rw [Finset.coe_insert, Finset.coe_image]
  exact le_antisymm hJI hIJ

end Algebra

/-- **Krull--Akizuki** (Stacks 00PG with `L = K`). If `R` is a one-dimensional Noetherian domain
with fraction field `K`, then every subring `A` of `K` containing `R` is Noetherian.

Stacks 00PG also covers a finite extension `L / K` in place of `K`; that case is not proved here.
The statement does not assume that `R` is local, because the proof never uses it.

Both hypotheses on `R` are needed:
* Noetherianity. A valuation ring `R` of rank one with value group `ℚ` has dimension one and is
  not Noetherian, and `A = R` is a ring between `R` and `K`.
* Dimension at most one. Take `R = k[x, y]_{(x, y)}`, `K = k(x, y)`, `A₀ = k[x, y, y/x, y/x², …]`
  and `A = S⁻¹ A₀` for `S = k[x, y] ∖ (x, y)`. If the ideal `I = (y/x, y/x², …)` of `A` were
  finitely generated, then `y/x^{n+1} = a · y/xⁿ = a x · y/x^{n+1}` for some `n` and `a ∈ A`, so
  `x` would be a unit of `A`. But `y ↦ 0` maps `A₀` into `k[x]` and `S` into `k[x] ∖ x k[x]`, so
  it extends to `A → k[x]_{(x)}` with `x ↦ x`, and `x` is not a unit there. -/
@[stacks 00PG "L = K"]
theorem IsNoetherianRing.of_le_of_krullDimLE_one (R A : Subring K) (h : R ≤ A)
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsFractionRing R K] :
    IsNoetherianRing A := by
  let : Algebra R A := (Subring.inclusion h).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun r => rfl
  exact isNoetherianRing_of_algebra (R := R) (K := K)

end Fraction
