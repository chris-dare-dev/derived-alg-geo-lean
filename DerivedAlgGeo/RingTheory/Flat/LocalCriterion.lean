/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.LinearCombination

/-!
# The local criterion for flatness

Let `R → S` be a local homomorphism of Noetherian local rings and `M` a finite `S`-module, which
is an `R`-module through `S`. This file proves the local criterion for flatness of `M` over `R`.

For an ideal `I` of `R`, write `I ⊗ M → M` for the map
`TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)`. Its kernel is `Tor₁(R ⧸ I, M)`
(Stacks, Remark 10.75.9, Tag 00M6), so no `Tor` functor is introduced.

## Main results

* `Module.Flat.of_injective_maximalIdeal_of_isLocalHom`: Stacks 00MK. If
  `𝔪_R ⊗ M → M` is injective, then `M` is flat over `R`.
* `Module.Flat.of_injective_of_flat_quotient_of_isLocalHom`: Stacks 00ML. If `I ≠ ⊤`,
  `I ⊗ M → M` is injective and `M ⧸ I M` is flat over `R ⧸ I`, then `M` is flat over `R`.

## Implementation notes

The proof follows Stacks 00MJ, 00MK and 00ML, with two differences.

* The segment of the `Tor` sequence that 00MJ needs is a chase in the exact sequence
  `𝔪 → J × R → J + R a` (right exactness of `- ⊗ M`), and likewise `I ⊓ 𝔪ⁿ → I × 𝔪ⁿ → I + 𝔪ⁿ`
  for 00MK. Both come from one lemma on the sequence `K → A × B → C`.
* Passage to the completion (Stacks 10.97.3) is replaced by Krull's intersection theorem. It is
  applied over `S`, where `M ⊗[R] I` is a finite module, to the ideal `𝔪_R S ≤ 𝔪_S`. Over `R` the
  module `I ⊗[R] M` is not finite and the theorem does not apply.

The hypotheses are all used.

* `Module.Finite S M`: let `k` be a field, `R = S = k[x, y]_{(x, y)}` and `M = (R / y R)[1/x]`.
  The element `x` acts invertibly on `M`, so the Koszul complex of `(x, y)` on `M` is exact and
  `𝔪 ⊗ M → M` is injective. But `y` is a nonzerodivisor with `y M = 0 ≠ M`, so `M` is not
  flat. Here `M` is not finite, since `x M = M ≠ 0` contradicts Nakayama's lemma.
* `IsLocalHom (algebraMap R S)`: take `R = k[x, y]_{(x, y)}`, `S = R_{(y)}` (here `x` becomes a
  unit, so `R → S` is not local) and `M = S / y S`, which is finite over `S`. As above
  `𝔪 ⊗ M → M` is injective and `M` is not flat over `R`.
* `I ≠ ⊤` in Stacks 00ML: for `I = ⊤` both hypotheses hold for every `M`, since `R ⧸ ⊤ = 0` and
  `⊤ ⊗ M → M` is `R ⊗ M ≅ M`. Over `R = S = k[t]_{(t)}` the residue field is finite and not flat.

Noetherianity of `R` (Artin--Rees) and of `S` (Krull) and `IsLocalRing R` are not known to be
necessary.

## References

* [Stacks: Tag 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [Stacks: Tag 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [Stacks: Tag 00MJ](https://stacks.math.columbia.edu/tag/00MJ)
* EGA IV₃, (0_III, 10.2.2)

## Tags

flat, local criterion for flatness, Tor, Artin--Rees, Krull intersection theorem
-/

open TensorProduct LinearMap IsLocalRing

namespace Module.Flat
section MayerVietoris
variable {R : Type*} [CommRing R] {M A B C K : Type*} [AddCommGroup M] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [AddCommGroup K] [Module R M] [Module R A] [Module R B]
  [Module R C] [Module R K]

/-- Right exactness of `- ⊗ M` along `K → A × B → C`: if `f ⊗ M` and `g ⊗ M` send `x` and `y` to
elements summing to zero, then `(x, y)` is the image of one element of `K ⊗ M`. -/
private theorem exists_rTensor_eq_of_coprod
    (f : A →ₗ[R] C) (g : B →ₗ[R] C) (α : K →ₗ[R] A × B)
    (hα : Function.Exact α (f.coprod g)) (hs : Function.Surjective (f.coprod g))
    (x : A ⊗[R] M) (y : B ⊗[R] M) (h : f.rTensor M x + g.rTensor M y = 0) :
    ∃ z : K ⊗[R] M, ((fst R A B).comp α).rTensor M z = x ∧
      ((snd R A B).comp α).rTensor M z = y := by
  have hex := _root_.rTensor_exact M hα hs
  have hX : (f.coprod g).rTensor M ((inl R A B).rTensor M x + (inr R A B).rTensor M y) = 0 := by
    rw [map_add, ← rTensor_comp_apply, ← rTensor_comp_apply, coprod_inl, coprod_inr, h]
  obtain ⟨z, hz⟩ := (hex _).mp hX
  refine ⟨z, ?_, ?_⟩
  · rw [rTensor_comp_apply, hz, map_add, ← rTensor_comp_apply, ← rTensor_comp_apply]
    simp
  · rw [rTensor_comp_apply, hz, map_add, ← rTensor_comp_apply, ← rTensor_comp_apply]
    simp
end MayerVietoris
section InductiveStep
variable {R : Type*} [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The multiplication map `I ⊗ M → M`. -/
private noncomputable abbrev mulMap (I : Ideal R) : I ⊗[R] M →ₗ[R] M :=
  TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)

omit [IsLocalRing R] in
private lemma mulMap_eq_lid_comp (I : Ideal R) :
    mulMap M I = (TensorProduct.lid R M).toLinearMap ∘ₗ I.subtype.rTensor M :=
  (lid_comp_rTensor M I.subtype).symm

omit [IsLocalRing R] in
private lemma mulMap_rTensor {I J : Ideal R} (hIJ : I ≤ J) (x : I ⊗[R] M) :
    mulMap M J ((Submodule.inclusion hIJ).rTensor M x) = mulMap M I x := by
  rw [mulMap_eq_lid_comp, mulMap_eq_lid_comp, comp_apply, comp_apply, ← rTensor_comp_apply]
  rfl

variable {M}

/-- Inductive step: if `a ∉ J` and `𝔪 a ⊆ J`, injectivity for `J + (a)` and for `𝔪` gives it for
`J`. -/
private lemma injective_mulMap_of_mul_mem (J : Ideal R) (a : R) (ha : a ∉ J)
    (hma : ∀ r ∈ maximalIdeal R, r * a ∈ J)
    (hm : Function.Injective (mulMap M (maximalIdeal R)))
    (hJ' : Function.Injective (mulMap M (J ⊔ Ideal.span {a}))) :
    Function.Injective (mulMap M J) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have haJ' : a ∈ J ⊔ Ideal.span {a} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  let f : J →ₗ[R] (J ⊔ Ideal.span {a} : Ideal R) := Submodule.inclusion le_sup_left
  let g : R →ₗ[R] (J ⊔ Ideal.span {a} : Ideal R) := LinearMap.toSpanSingleton R _ ⟨a, haJ'⟩
  let α₁ : maximalIdeal R →ₗ[R] J := LinearMap.codRestrict J
    (-(LinearMap.toSpanSingleton R R a ∘ₗ (maximalIdeal R).subtype)) fun r =>
      J.neg_mem (by simpa [mul_comm] using hma r r.2)
  let α : maximalIdeal R →ₗ[R] J × R := α₁.prod (maximalIdeal R).subtype
  have hα : Function.Exact α (f.coprod g) := by
    rintro ⟨j, r⟩
    constructor
    · intro h
      have h' : (j : R) + r * a = 0 := by
        simpa [f, g, Subtype.ext_iff] using h
      have hr : r ∈ maximalIdeal R := by
        by_contra hr
        have hu : IsUnit r := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hr
        apply ha
        have : r * a ∈ J := by
          have : r * a = -(j : R) := by linear_combination h'
          rw [this]; exact J.neg_mem j.2
        exact (Ideal.unit_mul_mem_iff_mem J hu).mp this
      refine ⟨⟨r, hr⟩, ?_⟩
      ext
      · simp [α, α₁]; linear_combination -h'
      · simp [α]
    · rintro ⟨r, hr⟩
      rw [← hr]
      ext
      simp [f, g, α, α₁]
  have hs : Function.Surjective (f.coprod g) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    exact ⟨(⟨j, hj⟩, r), by ext; simp [f, g, mul_comm]⟩
  have hfx : f.rTensor M x = 0 := by
    apply hJ'
    rw [mulMap_rTensor M le_sup_left, hx, map_zero]
  obtain ⟨z, hz₁, hz₂⟩ := exists_rTensor_eq_of_coprod f g α hα hs x (0 : R ⊗[R] M)
    (by simp [hfx])
  have hz : mulMap M (maximalIdeal R) z = 0 := by
    rw [mulMap_eq_lid_comp, comp_apply]
    have : ((snd R J R).comp α).rTensor M z = 0 := hz₂
    simpa [α] using congrArg (TensorProduct.lid R M) this
  rw [← hz₁, hm (hz.trans (map_zero _).symm)]
  simp

end InductiveStep

section ArtinRees
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Injectivity of `I ⊗ M → M` for the maximal ideal gives it for every ideal containing a power of
the maximal ideal. -/
private lemma injective_mulMap_of_pow_le (hm : Function.Injective (mulMap M (maximalIdeal R)))
    (n : ℕ) (J : Ideal R) : maximalIdeal R ^ n ≤ J → Function.Injective (mulMap M J) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro hnJ
  by_cases hJ : J = ⊤
  · subst hJ
    let e : (⊤ : Ideal R) ≃ₗ[R] R := Submodule.topEquiv
    have : mulMap M ⊤ = (TensorProduct.lid R M).toLinearMap ∘ₗ (e.rTensor M).toLinearMap := by
      rw [mulMap_eq_lid_comp]; rfl
    rw [this]
    exact (TensorProduct.lid R M).injective.comp (e.rTensor M).injective
  · have hex : ∃ k, maximalIdeal R ^ k ≤ J := ⟨n, hnJ⟩
    classical
    set k := Nat.find hex with hk
    have hkJ : maximalIdeal R ^ k ≤ J := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hkJ
      exact hJ hkJ
    have hnot : ¬ maximalIdeal R ^ (k - 1) ≤ J := Nat.find_min hex (by omega)
    obtain ⟨a, ha, haJ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have hma : ∀ r ∈ maximalIdeal R, r * a ∈ J := by
      intro r hr
      refine hkJ ?_
      have : k = (k - 1) + 1 := by omega
      rw [this, pow_succ']
      exact Ideal.mul_mem_mul hr ha
    refine injective_mulMap_of_mul_mem J a haJ hma hm
      (ih _ ?_ (hnJ.trans le_sup_left))
    exact lt_of_le_of_ne le_sup_left fun h =>
      haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))

omit [IsLocalRing R] in
/-- Artin–Rees: the image of `(I ⊓ 𝔪ⁿ) ⊗ M` in `I ⊗ M` lies in `𝔪ⁿ⁻ᶜ (I ⊗ M)`. -/
private lemma exists_rTensor_inf_mem_smul_top (𝔪 : Ideal R) (I : Ideal R) :
    ∃ c : ℕ, ∀ (k : ℕ) (z : ↥(I ⊓ 𝔪 ^ (k + c)) ⊗[R] M),
      (Submodule.inclusion (inf_le_left : I ⊓ 𝔪 ^ (k + c) ≤ I)).rTensor M z ∈
        𝔪 ^ k • (⊤ : Submodule R (I ⊗[R] M)) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔪 (M := R) I
  refine ⟨c, fun k z => ?_⟩
  induction z using TensorProduct.inductionOn with
  | tmul y x =>
    obtain ⟨y, hy⟩ := y
    have hy' : y ∈ 𝔪 ^ (k + c) • (⊤ : Submodule R R) ⊓ I :=
      ⟨by simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hy.2, hy.1⟩
    rw [hc (k + c) (by omega), Nat.add_sub_cancel] at hy'
    have key : ∀ y ∈ 𝔪 ^ k • (𝔪 ^ c • (⊤ : Submodule R R) ⊓ I), ∃ h : y ∈ I,
        (⟨y, h⟩ : I) ⊗ₜ[R] x ∈ 𝔪 ^ k • (⊤ : Submodule R (I ⊗[R] M)) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr q hq
        have hqI : q ∈ I := hq.2
        refine ⟨I.mul_mem_left r hqI, ?_⟩
        have : (⟨r • q, I.mul_mem_left r hqI⟩ : I) ⊗ₜ[R] x = r • ((⟨q, hqI⟩ : I) ⊗ₜ[R] x) := by
          rw [TensorProduct.smul_tmul']; rfl
        rw [this]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro y₁ y₂ h₁ h₂
        obtain ⟨h₁I, h₁⟩ := h₁
        obtain ⟨h₂I, h₂⟩ := h₂
        refine ⟨I.add_mem h₁I h₂I, ?_⟩
        have : (⟨y₁ + y₂, I.add_mem h₁I h₂I⟩ : I) ⊗ₜ[R] x =
            (⟨y₁, h₁I⟩ : I) ⊗ₜ[R] x + (⟨y₂, h₂I⟩ : I) ⊗ₜ[R] x := by
          rw [← TensorProduct.add_tmul]; rfl
        rw [this]
        exact Submodule.add_mem _ h₁ h₂
    obtain ⟨hI, h⟩ := key y hy'
    exact h
  | add z₁ z₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- A kernel element of `I ⊗ M → M` whose image in `(I ⊔ N) ⊗ M` vanishes comes from
`(I ⊓ N) ⊗ M`. -/
private lemma exists_rTensor_inf_eq (I N : Ideal R)
    (hinj : Function.Injective (mulMap M (I ⊔ N))) (x : I ⊗[R] M) (hx : mulMap M I x = 0) :
    ∃ z : ↥(I ⊓ N) ⊗[R] M, (Submodule.inclusion (inf_le_left : I ⊓ N ≤ I)).rTensor M z = x := by
  let f : I →ₗ[R] (I ⊔ N : Ideal R) := Submodule.inclusion le_sup_left
  let g : N →ₗ[R] (I ⊔ N : Ideal R) := Submodule.inclusion le_sup_right
  let α : ↥(I ⊓ N) →ₗ[R] I × N :=
    (Submodule.inclusion inf_le_left).prod (-(Submodule.inclusion inf_le_right))
  have hα : Function.Exact α (f.coprod g) := by
    rintro ⟨i, b⟩
    constructor
    · intro h
      have h' : (i : R) + b = 0 := by simpa [f, g, Subtype.ext_iff] using h
      have hb : (i : R) ∈ N := by
        have : (i : R) = -(b : R) := by linear_combination h'
        rw [this]; exact N.neg_mem b.2
      refine ⟨⟨i, i.2, hb⟩, ?_⟩
      ext
      · simp [α]
      · simp [α]; linear_combination (-1 : R) * h'
    · rintro ⟨c, hc⟩
      rw [← hc]
      ext
      simp [f, g, α]
  have hs : Function.Surjective (f.coprod g) := by
    rintro ⟨y, hy⟩
    obtain ⟨i, hi, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(⟨i, hi⟩, ⟨b, hb⟩), by ext; simp [f, g]⟩
  have hfx : f.rTensor M x = 0 := by
    apply hinj
    rw [mulMap_rTensor M le_sup_left, hx, map_zero]
  obtain ⟨z, hz, -⟩ := exists_rTensor_eq_of_coprod f g α hα hs x (0 : N ⊗[R] M) (by simp [hfx])
  exact ⟨z, hz⟩

end ArtinRees

section Krull
variable {R S M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S]
  [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]

/-- `M ⊗[R] I` is a finite `S`-module. -/
private instance finite_tensor_ideal (I : Ideal R) :
    Module.Finite S (M ⊗[R] I) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R I
  let g : M ⊗[R] (Fin n → R) →ₗ[S] M ⊗[R] I :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : M →ₗ[S] M) f
  have hg : Function.Surjective g := by
    intro p
    induction p using TensorProduct.inductionOn with
    | tmul m i =>
      obtain ⟨v, rfl⟩ := hf i
      exact ⟨m ⊗ₜ v, rfl⟩
    | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add _ _ _⟩
  have : Module.Finite S (M ⊗[R] (Fin n → R)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight R S M (Fin n)).symm
  exact Module.Finite.of_surjective g hg

variable (S) in
include S in
/-- Krull's intersection theorem over `S`, applied to `M ⊗[R] I`. -/
private lemma eq_zero_of_forall_mem_pow_smul_top (I : Ideal R) (x : I ⊗[R] M)
    (hx : ∀ k : ℕ, x ∈ maximalIdeal R ^ k • (⊤ : Submodule R (I ⊗[R] M))) : x = 0 := by
  let e := TensorProduct.comm R I M
  let 𝔞 : Ideal S := (maximalIdeal R).map (algebraMap R S)
  have h𝔞 : 𝔞 ≤ Ideal.jacobson ⊥ := by
    refine le_trans ?_ (maximalIdeal_le_jacobson _)
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hk : ∀ k : ℕ, e x ∈ 𝔞 ^ k • (⊤ : Submodule S (M ⊗[R] I)) := by
    intro k
    refine Submodule.smul_induction_on (p := fun p => e p ∈ 𝔞 ^ k • (⊤ : Submodule S (M ⊗[R] I)))
      (hx k) ?_ ?_
    · intro r hr q _
      rw [map_smul, ← algebraMap_smul S r (e q)]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      show _ ∈ ((maximalIdeal R).map (algebraMap R S)) ^ k
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
    · intro p q hp hq
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  have : e x ∈ (⨅ k : ℕ, 𝔞 ^ k • ⊤ : Submodule S (M ⊗[R] I)) := (Submodule.mem_iInf _).mpr hk
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson 𝔞 h𝔞] at this
  simpa using this

end Krull

section LocalCriterion
variable {R S M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S]
  [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]

include S

/-- **The local criterion for flatness** (Stacks 00MK). Let `R → S` be a local homomorphism of
Noetherian local rings and `M` a finite `S`-module. If `𝔪_R ⊗ M → M` is injective, that is
`Tor₁^R(R ⧸ 𝔪_R, M) = 0` (Stacks, Remark 10.75.9: `Tor₁(R ⧸ I, M)` is the kernel of
`I ⊗ M → M`), then `M` is flat over `R`.

The finiteness of `M` over `S` and the locality of `R → S` are needed: see the module docstring
for the counterexamples. -/
theorem of_injective_maximalIdeal_of_isLocalHom
    (h : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R M).comp (IsLocalRing.maximalIdeal R).subtype))) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := exists_rTensor_inf_mem_smul_top (M := M) (maximalIdeal R) I
  refine eq_zero_of_forall_mem_pow_smul_top S I x fun k => ?_
  obtain ⟨z, hz⟩ := exists_rTensor_inf_eq I (maximalIdeal R ^ (k + c))
    (injective_mulMap_of_pow_le h (k + c) _ le_sup_right) x hx
  rw [← hz]
  exact hc k z

/-- **A variant of the local criterion for flatness** (Stacks 00ML; EGA 0_III, 10.2.2). Let
`R → S` be a local homomorphism of Noetherian local rings, `M` a finite `S`-module and `I ≠ ⊤` an
ideal of `R`. If `I ⊗ M → M` is injective (that is `Tor₁^R(R ⧸ I, M) = 0`) and `M ⧸ I M` is flat
over `R ⧸ I`, then `M` is flat over `R`.

The hypothesis `I ≠ ⊤` is needed: for `I = ⊤` both hypotheses hold for every `M`. -/
theorem of_injective_of_flat_quotient_of_isLocalHom (I : Ideal R) (hI : I ≠ ⊤)
    (htor : Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)))
    (hquot : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Flat R M := by
  refine of_injective_maximalIdeal_of_isLocalHom (S := S) ?_
  have hIm : I ≤ maximalIdeal R := le_maximalIdeal hI
  let ι : I ⊗[R] M →ₗ[R] (maximalIdeal R) ⊗[R] M := (Submodule.inclusion hIm).rTensor M
  have hcomp : ∀ w, mulMap M (maximalIdeal R) (ι w) = mulMap M I w := mulMap_rTensor M hIm
  have key : ∀ z : (maximalIdeal R) ⊗[R] M, mulMap M (maximalIdeal R) z = 0 →
      z ∈ LinearMap.range ι := by
    intro z hz
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset z
    rw [← Finset.sum_coe_sort s] at hz ⊢
    have hmk : ∀ (r : R) (x : M), Ideal.Quotient.mk I r •
        (Submodule.Quotient.mk x : M ⧸ I • (⊤ : Submodule R M)) = Submodule.Quotient.mk (r • x) :=
      fun r x => rfl
    have hmkSum : ∀ {ι : Type _} (t : Finset ι) (v : ι → M),
        (Submodule.Quotient.mk (∑ j ∈ t, v j) : M ⧸ I • (⊤ : Submodule R M)) =
          ∑ j ∈ t, Submodule.Quotient.mk (v j) := fun t v =>
      map_sum (Submodule.mkQ (I • (⊤ : Submodule R M))) v t
    have hrel : ∑ p : s, Ideal.Quotient.mk I ((p.1.1 : maximalIdeal R) : R) •
        (Submodule.Quotient.mk p.1.2 : M ⧸ I • (⊤ : Submodule R M)) = 0 := by
      have h0 : ∑ p : s, ((p.1.1 : maximalIdeal R) : R) • p.1.2 = 0 := by simpa [map_sum] using hz
      have := congrArg (Submodule.Quotient.mk (p := I • (⊤ : Submodule R M))) h0
      rw [hmkSum] at this
      simpa [hmk] using this
    obtain ⟨k, a, y, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
    choose a' ha' using fun i j => Ideal.Quotient.mk_surjective (a i j)
    choose y' hy' using fun j => Submodule.Quotient.mk_surjective _ (y j)
    have hw : ∀ i : s, i.1.2 - ∑ j, a' i j • y' j ∈ I • (⊤ : Submodule R M) := by
      intro i
      rw [← Submodule.Quotient.eq]
      have h1 : (Submodule.Quotient.mk (∑ j, a' i j • y' j) : M ⧸ I • (⊤ : Submodule R M)) =
          ∑ j, a i j • y j := by
        have := map_sum (Submodule.mkQ (I • (⊤ : Submodule R M))) (fun j => a' i j • y' j)
          Finset.univ
        simp only [Submodule.mkQ_apply] at this
        rw [this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← ha' i j, ← hy' j, hmk]
      exact (hx i).trans h1.symm
    have hg : ∀ j, ∑ i : s, ((i.1.1 : maximalIdeal R) : R) * a' i j ∈ I := by
      intro j
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [map_sum, ha'] using hf j
    have hcoef : ∀ j, ∑ i : s, a' i j • (i.1.1 : maximalIdeal R) =
        Submodule.inclusion hIm ⟨∑ i : s, ((i.1.1 : maximalIdeal R) : R) * a' i j, hg j⟩ := by
      intro j
      ext
      simp [mul_comm]
    have hmem : ∀ (i : s), ∀ u ∈ I • (⊤ : Submodule R M),
        ((i.1.1 : maximalIdeal R)) ⊗ₜ[R] u ∈ LinearMap.range ι := by
      intro i u hu
      refine Submodule.smul_induction_on hu ?_ ?_
      · intro h hh q _
        refine ⟨(⟨h * (i.1.1 : R), I.mul_mem_right _ hh⟩ : I) ⊗ₜ[R] q, ?_⟩
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp only [ι, rTensor_tmul]
        congr 1
      · intro p q hp hq
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hp hq
    have hz' : ∀ i : s, (i.1.1 : maximalIdeal R) ⊗ₜ[R] i.1.2 =
        ∑ j, (a' i j • i.1.1) ⊗ₜ[R] y' j + i.1.1 ⊗ₜ[R] (i.1.2 - ∑ j, a' i j • y' j) := by
      intro i
      rw [TensorProduct.tmul_sub, TensorProduct.tmul_sum]
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      abel
    rw [Finset.sum_congr rfl fun i _ => hz' i, Finset.sum_add_distrib]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => hmem i _ (hw i))
    rw [Finset.sum_comm]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← TensorProduct.sum_tmul, hcoef j]
    exact ⟨(⟨_, hg j⟩ : I) ⊗ₜ[R] y' j, by simp [ι]⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨w, rfl⟩ := key z hz
  have : w = 0 := htor (by rw [← hcomp, hz, map_zero])
  simp [this]

end LocalCriterion

end Module.Flat
