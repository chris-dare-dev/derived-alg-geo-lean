/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
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
* `Module.Flat.ker_lift_lsmul_comp_subtype_eq_span`: base change of `Tor₁` (EGA IV₃, Lemme 11.2.4
  with `C = N = A ⧸ J`; Stacks 00MM, 00MN). Let `A → A'` be a ring map, `J` an ideal of `A` and `M`
  an `A`-module with `M ⧸ J M` flat over `A ⧸ J`. Then `ker (J' ⊗ M' → M')` is generated, as an
  `A'`-module, by the image of `ker (J ⊗ M → M)`, where `M'` is a base change of `M` and
  `J' = J A'`.
* `Module.Flat.flat_of_isLocalizedModule_of_tor₁_vanishes`: flatness at a later stage (EGA IV₃,
  Lemme 11.2.5 (b); Stacks 00MO). If, in addition, `A'` is Noetherian, `M'` is a finite module over
  a finite type `A'`-algebra `S'` and the image of `ker (J ⊗ M → M)` in `J' ⊗ M'` is zero, then
  `M'_𝔮` is flat over `A'` for every prime `𝔮` of `S'` containing `J S'`.

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

The two results on base change use a presentation `0 → K → F → M → 0` by the free module `F` on
the underlying set of `M`, and are proved with coordinates in `F`, so no `Tor` functor and no
tensor product over `A ⧸ J` is needed. Flatness of `M ⧸ J M` enters through the equational
criterion, in the form that finitely many relations among elements of `M` are simultaneously
trivial modulo `J M`. The second result is deduced from the first and the local criterion over
the local rings `A'_P → S'_𝔮`, with `P = 𝔮 ∩ A'`; injectivity of `J' ⊗ M' → M'` and flatness of
`M' ⧸ J' M'` over `A' ⧸ J'` pass to `M'_𝔮` because the denominators in `S'` act by automorphisms
over `A'`. Hypothesis `hT` of the second result is the elementwise, global form of EGA's condition
(ii), which only asks for vanishing after localization at `𝔮`.

The hypotheses of the two results on base change are used.

* `M ⧸ J M` flat over `A ⧸ J`, in both results: let `k` be a field, `A = k[x, y]`, `J = (x)`,
  `M = A / (y)` and `A' = S' = A / (x - y) ≅ k[x]`. Here `M ⧸ J M = k` is not flat over
  `A ⧸ J = k[y]`. Since `x, y` is a regular sequence, `Tor₁^A(A ⧸ J, M) = 0`, so the vanishing
  hypothesis holds. But `M' = k[x] / (x)` and `J' = (x)` give `Tor₁^{A'}(A' ⧸ J', M') = k ≠ 0`,
  which breaks the first result, and for `𝔮 = (x)` the module `M'_𝔮 = k` is not flat over `k[x]`,
  which breaks the second.
* `Module.Finite S' M'`, in the second result: let `A = A' = S' = k[x, y]_{(x, y)}`, `J` the
  maximal ideal and `M = M' = (A / y A)[1 / x]`. Then `J M = M`, so `M ⧸ J M = 0` is flat, and
  `Tor₁(A ⧸ J, M) = 0` as in the witness for the local criterion. But `M` is not flat.

Noetherianity of `A'` and finite generation of `S'` are not known to be necessary: EGA's case (a),
with `J` nilpotent, has neither.

## References

* [Stacks: Tag 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [Stacks: Tag 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [Stacks: Tag 00MJ](https://stacks.math.columbia.edu/tag/00MJ)
* [Stacks: Tag 00MM](https://stacks.math.columbia.edu/tag/00MM)
* [Stacks: Tag 00MN](https://stacks.math.columbia.edu/tag/00MN)
* [Stacks: Tag 00MO](https://stacks.math.columbia.edu/tag/00MO)
* EGA IV₃, (0_III, 10.2.2)
* EGA IV₃, §11.2, Lemmes 11.2.4 and 11.2.5

## Tags

flat, local criterion for flatness, Tor, base change, Artin--Rees, Krull intersection theorem
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


section Presentation
variable {A A' M M' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [AddCommGroup M]
  [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']

/-- The kernel of the presentation of `M` by the free module on its underlying set. -/
private noncomputable abbrev presKer (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] :
    Submodule A (M →₀ A) :=
  LinearMap.ker (Finsupp.linearCombination A (id : M → M))

/-- The coefficientwise base change of the free module on `M`. -/
private noncomputable abbrev baseMap (A A' M : Type*) [CommRing A] [CommRing A'] [Algebra A A'] :
    (M →₀ A) →ₗ[A] (M →₀ A') :=
  Finsupp.mapRange.linearMap (Algebra.linearMap A A')

omit [AddCommGroup M] [Module A M] in
private lemma baseMap_single (m : M) (a : A) :
    baseMap A A' M (Finsupp.single m a) = Finsupp.single m (algebraMap A A' a) := by
  simp [baseMap]

private lemma ker_le_span_baseMap {β : M →ₗ[A] M'} (hβ : IsBaseChange A' β) :
    LinearMap.ker (Finsupp.linearCombination A' (β : M → M')) ≤
      Submodule.span A' (baseMap A A' M '' (presKer A M)) := by
  set W : Submodule A' (M →₀ A') := Submodule.span A' (baseMap A A' M '' (presKer A M)) with hW
  have hmem : ∀ f ∈ presKer A M, baseMap A A' M f ∈ W := fun f hf =>
    Submodule.subset_span ⟨f, hf, rfl⟩
  have hK : ∀ f : M →₀ A, f ∈ presKer A M ↔ Finsupp.linearCombination A (id : M → M) f = 0 :=
    fun f => Iff.rfl
  let ℓ : M →ₗ[A] ((M →₀ A') ⧸ W) :=
    { toFun := fun m => Submodule.Quotient.mk (Finsupp.single m 1)
      map_add' := fun m m' => by
        rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
        have := hmem (Finsupp.single (m + m') 1 - Finsupp.single m 1 - Finsupp.single m' 1)
          (by simp [hK])
        simpa [map_sub, map_add, baseMap_single, sub_sub] using this
      map_smul' := fun r m => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        have := hmem (Finsupp.single (r • m) 1 - Finsupp.single m r) (by simp [hK])
        simpa [map_sub, baseMap_single, Finsupp.smul_single, Algebra.smul_def] using this }
  have key : (hβ.lift ℓ) ∘ₗ (Finsupp.linearCombination A' (β : M → M')) = W.mkQ := by
    apply Finsupp.lhom_ext
    intro m a
    have h1 : (Finsupp.single m a : M →₀ A') = a • Finsupp.single m 1 := by
      simp [Finsupp.smul_single]
    rw [h1]
    simp [IsBaseChange.lift_eq, ℓ]
    rw [← Submodule.Quotient.mk_smul, ← h1]
  intro v hv
  have := congr($key v)
  simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hv, map_zero, Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero W).mp this.symm

end Presentation

section Factorization
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (J : Ideal A)

/-- Flatness of `M ⧸ J M` over `A ⧸ J` makes finitely many relations among elements of `M`
simultaneously trivial modulo `J M`. -/
private lemma exists_factorization_of_relations
    [Module.Flat (A ⧸ J) (M ⧸ J • (⊤ : Submodule A M))]
    (S : Finset M) {P : ℕ} (k : Fin P → (M →₀ A)) (hS : ∀ p, (k p).support ⊆ S)
    (hk : ∀ p, Finsupp.linearCombination A (id : M → M) (k p) = 0) :
    ∃ (r : ℕ) (a : Fin r → M → A) (y : Fin r → M),
      (∀ m ∈ S, m - ∑ j, a j m • y j ∈ J • (⊤ : Submodule A M)) ∧
        ∀ (j : Fin r) (p : Fin P), ∑ m ∈ S, a j m * k p m ∈ J := by
  classical
  have hmk : ∀ (r : A) (m : M), Ideal.Quotient.mk J r •
      (Submodule.Quotient.mk m : M ⧸ J • (⊤ : Submodule A M)) = Submodule.Quotient.mk (r • m) :=
    fun _ _ => rfl
  let f : (Fin P → A ⧸ J) →ₗ[A ⧸ J] (S → A ⧸ J) :=
    Matrix.mulVecLin (Matrix.of fun (m : S) (p : Fin P) => Ideal.Quotient.mk J (k p m))
  let x : (S → A ⧸ J) →ₗ[A ⧸ J] (M ⧸ J • (⊤ : Submodule A M)) :=
    ∑ m : S, (LinearMap.proj m).smulRight (Submodule.Quotient.mk (m : M))
  have hxf : x ∘ₗ f = 0 := by
    refine LinearMap.pi_ext' fun p => LinearMap.ext_ring ?_
    have := congr(Submodule.Quotient.mk (p := J • (⊤ : Submodule A M)) $(hk p))
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hS p) _ (by simp)] at this
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearMap.zero_apply]
    simp [x, f]
    rw [Finset.sum_attach S (fun m => (k p m) •
      (Submodule.Quotient.mk m : M ⧸ J • (⊤ : Submodule A M)))]
    simp only [← Submodule.Quotient.mk_smul]
    have h2 := map_sum (Submodule.mkQ (J • (⊤ : Submodule A M))) (fun m => k p m • m) S
    simp only [Submodule.mkQ_apply] at h2
    rw [← h2]
    simpa using this
  obtain ⟨r, a, y, hxy, haf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  have hsurjA : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  let ã : Fin r → S → A := fun j m => Function.surjInv hsurjA (a (Pi.single m 1) j)
  have hã : ∀ j m, Ideal.Quotient.mk J (ã j m) = a (Pi.single m 1) j := fun j m =>
    Function.surjInv_eq hsurjA _
  let y₀ : Fin r → M := fun j =>
    Function.surjInv (Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A M)))
      (y (Finsupp.single j 1))
  have hy₀ : ∀ j, (Submodule.Quotient.mk (y₀ j) : M ⧸ J • (⊤ : Submodule A M)) =
      y (Finsupp.single j 1) := fun j =>
    Function.surjInv_eq (Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A M))) _
  refine ⟨r, fun j m => if h : m ∈ S then ã j ⟨m, h⟩ else 0, y₀, fun m hm => ?_, fun j p => ?_⟩
  · lift m to S using hm
    have hdite : ∀ j, (if h : (m : M) ∈ S then ã j ⟨m, h⟩ else 0) = ã j m := fun j => by
      simp [m.2]
    simp only [hdite]
    rw [← Submodule.Quotient.eq]
    have e1 : x (Pi.single m 1) = Submodule.Quotient.mk (m : M) := by
      simp only [x, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.coe_proj,
        Function.eval]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
      simp
    have e2 : a (Pi.single m 1) = ∑ j, (a (Pi.single m 1) j) • Finsupp.single j 1 := by
      ext j'; simp
    have e3 := congr($hxy (Pi.single m 1))
    rw [e1, LinearMap.comp_apply, e2, map_sum] at e3
    rw [e3]
    have h2 := map_sum (Submodule.mkQ (J • (⊤ : Submodule A M))) (fun j => ã j m • y₀ j)
      Finset.univ
    simp only [Submodule.mkQ_apply] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hy₀, ← hã, hmk]
  · rw [← Finset.sum_coe_sort S]
    have hdite : ∀ (j : Fin r) (m : S), (if h : (m : M) ∈ S then ã j ⟨m, h⟩ else 0) = ã j m :=
      fun j m => by simp [m.2]
    simp only [hdite]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e1 : f (Pi.single p 1) =
        ∑ m : S, Ideal.Quotient.mk J (k p m) • (Pi.single m 1 : S → A ⧸ J) := by
      ext m'
      simp [f, Pi.single_apply]
    have e2 := congr($haf (Pi.single p 1))
    rw [LinearMap.comp_apply, e1, map_sum] at e2
    have e3 := congr(($e2) j)
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at e3
    rw [map_sum]
    simpa [hã, mul_comm] using e3

end Factorization

section Combine
variable {A A' M : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M]

/-- The submodule of the free module on `M` of finitely supported functions with values in `J`. -/
private def coordSub (J : Ideal A) (M : Type*) : Submodule A (M →₀ A) where
  carrier := {f | ∀ m, f m ∈ J}
  add_mem' ha hb m := J.add_mem (ha m) (hb m)
  zero_mem' _ := J.zero_mem
  smul_mem' r f hf m := by simpa using J.mul_mem_left r (hf m)

omit [AddCommGroup M] [Module A M] in
private lemma single_mem_coordSub (J : Ideal A) (m : M) {x : A} (hx : x ∈ J) :
    Finsupp.single m x ∈ coordSub J M := fun m' => by
  classical
  by_cases h : m = m'
  · subst h; simpa using hx
  · simp [h]

omit [AddCommGroup M] [Module A M] in
private lemma smul_mem_coordSub (J : Ideal A) {x : A} (hx : x ∈ J) (f : M →₀ A) :
    x • f ∈ coordSub J M := fun m => by simpa using J.mul_mem_right (f m) hx

private lemma exists_coordSub_of_mem_smul_top (J : Ideal A) {u : M}
    (hu : u ∈ J • (⊤ : Submodule A M)) :
    ∃ g ∈ coordSub J M, Finsupp.linearCombination A (id : M → M) g = u := by
  refine Submodule.smul_induction_on (p := fun u => ∃ g ∈ coordSub J M,
    Finsupp.linearCombination A (id : M → M) g = u) hu ?_ ?_
  · intro x hx n _
    exact ⟨Finsupp.single n x, single_mem_coordSub J n hx, by simp⟩
  · rintro u v ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', add_mem hg hg', by simp⟩


omit [AddCommGroup M] [Module A M] in
private lemma baseMap_apply (f : M →₀ A) (m : M) :
    baseMap A A' M f m = algebraMap A A' (f m) := by
  simp [baseMap]

omit [AddCommGroup M] [Module A M] in
private lemma baseMap_smul (x : A) (f : M →₀ A) :
    baseMap A A' M (x • f) = algebraMap A A' x • baseMap A A' M f := by
  rw [map_smul, algebraMap_smul]

private lemma sum_smul_baseMap_mem_span (J : Ideal A)
    [Module.Flat (A ⧸ J) (M ⧸ J • (⊤ : Submodule A M))]
    {P : ℕ} (a : Fin P → A') (k : Fin P → (M →₀ A)) (hk : ∀ p, k p ∈ presKer A M)
    (hv : ∀ m, (∑ p, a p • baseMap A A' M (k p)) m ∈ J.map (algebraMap A A')) :
    ∑ p, a p • baseMap A A' M (k p) ∈
      Submodule.span A' (baseMap A A' M '' ↑(presKer A M ⊓ coordSub J M)) := by
  classical
  set Z := Submodule.span A' (baseMap A A' M '' ↑(presKer A M ⊓ coordSub J M)) with hZ
  have hZmem : ∀ f ∈ presKer A M ⊓ coordSub J M, baseMap A A' M f ∈ Z :=
    fun f hf => Submodule.subset_span ⟨f, hf, rfl⟩
  let S : Finset M := Finset.univ.biUnion fun p => (k p).support
  have hS : ∀ p, (k p).support ⊆ S := fun p =>
    Finset.subset_biUnion_of_mem (fun p => (k p).support) (Finset.mem_univ p)
  obtain ⟨r, c, yy, h1, h2⟩ := exists_factorization_of_relations J S k hS (fun p => hk p)
  let π : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A (id : M → M)
  let ε : M → (M →₀ A) := fun m => Finsupp.single m 1 - ∑ j, Finsupp.single (yy j) (c j m)
  have hπε : ∀ m, π (ε m) = m - ∑ j, c j m • yy j := by
    intro m; simp [π, ε, map_sub, map_sum]
  have hg : ∀ m ∈ S, ∃ g ∈ coordSub J M, π g = π (ε m) := fun m hm => by
    rw [hπε]; exact exists_coordSub_of_mem_smul_top J (h1 m hm)
  choose! g hgmem hgπ using hg
  let ε' : M → (M →₀ A) := fun m => ε m - g m
  have hε' : ∀ m ∈ S, ε' m ∈ presKer A M := fun m hm => by
    rw [presKer, LinearMap.mem_ker]
    show π (ε m - g m) = 0
    rw [map_sub, hgπ m hm, sub_self]
  let b : Fin P → (M →₀ A) := fun p => k p - ∑ m ∈ S, k p m • ε' m
  have hb : ∀ p, b p = ∑ m ∈ S, k p m • g m +
      ∑ j, Finsupp.single (yy j) (∑ m ∈ S, k p m * c j m) := by
    intro p
    have hkp : k p = ∑ m ∈ S, Finsupp.single m (k p m) :=
      calc k p = (k p).sum Finsupp.single := (Finsupp.sum_single _).symm
        _ = _ := Finsupp.sum_of_support_subset _ (hS p) _ (by simp)
    simp only [b, ε', ε, smul_sub, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, Finsupp.single_finsetSum]
    rw [Finset.sum_comm, ← hkp]
    abel
  have hbK : ∀ p, b p ∈ presKer A M ⊓ coordSub J M := fun p => by
    refine ⟨sub_mem (hk p) (sum_mem fun m hm => Submodule.smul_mem _ _ (hε' m hm)), ?_⟩
    rw [hb p]
    exact add_mem (sum_mem fun m hm => Submodule.smul_mem _ _ (hgmem m hm))
      (sum_mem fun j _ => single_mem_coordSub J _ (by simpa [mul_comm] using h2 j p))
  have hbm : ∀ p, baseMap A A' M (b p) = baseMap A A' M (k p) -
      ∑ m ∈ S, algebraMap A A' (k p m) • baseMap A A' M (ε' m) := fun p => by
    simp only [b, map_sub, map_sum, baseMap_smul]
  have key : ∑ p, a p • baseMap A A' M (k p) = ∑ p, a p • baseMap A A' M (b p) +
      ∑ m ∈ S, (∑ p, a p * algebraMap A A' (k p m)) • baseMap A A' M (ε' m) := by
    simp only [hbm, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm (s := Finset.univ) (t := S)]
    abel
  rw [key]
  refine add_mem (sum_mem fun p _ => Submodule.smul_mem _ _ (hZmem _ (hbK p)))
    (sum_mem fun m hm => ?_)
  have hvm := hv m
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, baseMap_apply] at hvm
  have : ∀ w ∈ J.map (algebraMap A A'), w • baseMap A A' M (ε' m) ∈ Z := fun w hw => by
    refine Submodule.span_induction (p := fun w _ => w • baseMap A A' M (ε' m) ∈ Z) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨x, hx, rfl⟩
      rw [← baseMap_smul]
      exact hZmem _ ⟨Submodule.smul_mem _ _ (hε' m hm), smul_mem_coordSub J hx _⟩
    · simp
    · intro x y _ _ hx hy
      rw [add_smul]; exact add_mem hx hy
    · intro x y _ hy
      rw [smul_assoc]; exact Submodule.smul_mem _ _ hy
  exact this _ hvm

end Combine

section KernelGenerators
variable {A A' M M' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [AddCommGroup M]
  [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']

omit [IsScalarTower A A' M'] in
/-- Finite sums `∑ xᵢ ⊗ β mᵢ` over a finite set, with `∑ xᵢ mᵢ = 0`, are among the generators. -/
private lemma sum_mem_gens (β : M →ₗ[A] M') (J : Ideal A) (s : Finset M) (x : M → J)
    (h : ∑ m ∈ s, (x m : A) • m = 0) :
    ∃ (n : ℕ) (x' : Fin n → J) (m' : Fin n → M), ∑ i, (x' i : A) • m' i = 0 ∧
      ∑ m ∈ s, (⟨algebraMap A A' (x m), Ideal.mem_map_of_mem _ (x m).2⟩ :
        J.map (algebraMap A A')) ⊗ₜ[A'] β m =
      ∑ i, (⟨algebraMap A A' (x' i), Ideal.mem_map_of_mem _ (x' i).2⟩ :
        J.map (algebraMap A A')) ⊗ₜ[A'] β (m' i) := by
  classical
  refine ⟨s.card, fun i => x (s.equivFin.symm i), fun i => (s.equivFin.symm i : M), ?_, ?_⟩
  · rw [← h, ← Finset.sum_coe_sort s (fun m => (x m : A) • m)]
    exact Equiv.sum_comp s.equivFin.symm (fun m : s => (x m : A) • (m : M))
  · rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun m : s => (⟨algebraMap A A' (x m),
      Ideal.mem_map_of_mem _ (x m).2⟩ : J.map (algebraMap A A')) ⊗ₜ[A'] β (m : M))).symm


/-- **Base change of `Tor₁`** (EGA IV₃, Lemme 11.2.4 with `C = N = A ⧸ J`; Stacks, Lemmas 10.99.12
and 10.99.13, Tags 00MM and 00MN). Let `A → A'` be a ring map, `J` an ideal of `A`, `M` an
`A`-module with `M ⧸ J M` flat over `A ⧸ J`, and `β : M → M'` a base change of `M` to `A'`. Put
`J' = J A'`.
Then the kernel of `J' ⊗[A'] M' → M'`, which is `Tor₁^{A'}(A' ⧸ J', M')`, is generated as an
`A'`-module by the image of the kernel `Tor₁^A(A ⧸ J, M)` of `J ⊗[A] M → M`.

The image of that kernel consists of the finite sums `∑ xᵢ ⊗ β mᵢ` with `xᵢ ∈ J`, `mᵢ ∈ M` and
`∑ xᵢ mᵢ = 0`, because every element of `J ⊗ M` is a finite sum of pure tensors.

Flatness of `M ⧸ J M` over `A ⧸ J` is needed, see the module docstring. -/
theorem ker_lift_lsmul_comp_subtype_eq_span {β : M →ₗ[A] M'} (hβ : IsBaseChange A' β) (J : Ideal A)
    [Module.Flat (A ⧸ J) (M ⧸ J • (⊤ : Submodule A M))] :
    LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul A' M').comp
      (J.map (algebraMap A A')).subtype)) =
    Submodule.span A' {z | ∃ (n : ℕ) (x : Fin n → J) (m : Fin n → M),
      ∑ i, (x i : A) • m i = 0 ∧ z = ∑ i, (⟨algebraMap A A' (x i),
        Ideal.mem_map_of_mem _ (x i).2⟩ : J.map (algebraMap A A')) ⊗ₜ[A'] β (m i)} := by
  classical
  set J' : Ideal A' := J.map (algebraMap A A') with hJ'
  set G := Submodule.span A' {z | ∃ (n : ℕ) (x : Fin n → J) (m : Fin n → M),
      ∑ i, (x i : A) • m i = 0 ∧ z = ∑ i, (⟨algebraMap A A' (x i),
        Ideal.mem_map_of_mem _ (x i).2⟩ : J.map (algebraMap A A')) ⊗ₜ[A'] β (m i)} with hG
  apply le_antisymm
  · intro z hz
    let Ω : (M →₀ J') →ₗ[A'] J' ⊗[A'] M' :=
      Finsupp.lsum A' fun m => (TensorProduct.mk A' J' M').flip (β m)
    let ρ : (M →₀ J') →ₗ[A'] (M →₀ A') := Finsupp.mapRange.linearMap J'.subtype
    let π' : (M →₀ A') →ₗ[A'] M' := Finsupp.linearCombination A' (β : M → M')
    have hΩsingle : ∀ m (y : J'), Ω (Finsupp.single m y) = y ⊗ₜ[A'] β m := fun m y => by
      simp [Ω]
    have hρsingle : ∀ m (y : J'), ρ (Finsupp.single m y) = Finsupp.single m (y : A') :=
      fun m y => by simp [ρ]
    have hspan : ∀ n : M', ∃ w : M →₀ A', π' w = n := by
      intro n
      obtain ⟨t, rfl⟩ := (hβ.equiv.surjective n)
      induction t using TensorProduct.inductionOn with
      | tmul a m => exact ⟨Finsupp.single m a, by simp [π', IsBaseChange.equiv_tmul]⟩
      | add t t' h h' =>
        obtain ⟨w, hw⟩ := h
        obtain ⟨w', hw'⟩ := h'
        exact ⟨w + w', by rw [map_add, hw, hw', map_add]⟩
    have hΩ : ∀ z' : J' ⊗[A'] M', ∃ u, Ω u = z' := by
      intro z'
      induction z' using TensorProduct.inductionOn with
      | tmul y n =>
        obtain ⟨w, rfl⟩ := hspan n
        induction w using Finsupp.induction_linear with
        | zero => exact ⟨0, by simp⟩
        | add w w' h h' =>
          obtain ⟨u, hu⟩ := h
          obtain ⟨u', hu'⟩ := h'
          exact ⟨u + u', by rw [map_add, hu, hu', map_add, TensorProduct.tmul_add]⟩
        | single m a =>
          refine ⟨Finsupp.single m (a • y), ?_⟩
          rw [hΩsingle]
          simp [π', TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      | add z₁ z₂ h h' =>
        obtain ⟨u, hu⟩ := h
        obtain ⟨u', hu'⟩ := h'
        exact ⟨u + u', by rw [map_add, hu, hu']⟩
    obtain ⟨u, rfl⟩ := hΩ z
    have hmul : ∀ v, TensorProduct.lift ((LinearMap.lsmul A' M').comp J'.subtype) (Ω v) =
        π' (ρ v) := by
      intro v
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v v' h h' => rw [map_add, map_add, h, h', map_add, map_add]
      | single m y => rw [hΩsingle, hρsingle]; simp [π']
    have hker : π' (ρ u) = 0 := by rw [← hmul]; exact hz
    obtain ⟨P, a, g, hag⟩ := Submodule.mem_span_set'.mp (ker_le_span_baseMap hβ hker)
    choose k hkK hkg using fun i => (g i).2
    have hsum : ρ u = ∑ i, a i • baseMap A A' M (k i) := by
      rw [← hag]; simp only [hkg]
    have hv : ∀ m, (∑ i, a i • baseMap A A' M (k i)) m ∈ J' := fun m => by
      rw [← hsum]; simp [ρ]
    have hZ := sum_smul_baseMap_mem_span J a k hkK hv
    rw [← hsum] at hZ
    set Z := Submodule.span A' (baseMap A A' M '' ↑(presKer A M ⊓ coordSub J M)) with hZdef
    have hmain : ∀ w ∈ Z, ∃ u' : M →₀ J', ρ u' = w ∧ Ω u' ∈ G := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => ∃ u' : M →₀ J', ρ u' = w ∧ Ω u' ∈ G)
        ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨f, hf, rfl⟩
        have hf' : f ∈ presKer A M ⊓ coordSub J M := hf
        let x : M → J := fun m => ⟨f m, hf'.2 m⟩
        have hy : ∀ m, (algebraMap A A' (x m)) ∈ J' := fun m => Ideal.mem_map_of_mem _ (x m).2
        refine ⟨∑ m ∈ f.support, Finsupp.single m (⟨algebraMap A A' (x m), hy m⟩ : J'), ?_, ?_⟩
        · have hkp : f = ∑ m ∈ f.support, Finsupp.single m (f m) :=
            (Finsupp.sum_single f).symm
          calc ρ (∑ m ∈ f.support, Finsupp.single m (⟨algebraMap A A' (x m), hy m⟩ : J'))
              = ∑ m ∈ f.support, Finsupp.single m (algebraMap A A' (f m)) := by
                simp only [map_sum, hρsingle]; rfl
            _ = baseMap A A' M f := by
                conv_rhs => rw [hkp]
                simp only [map_sum, baseMap_single]
        · have hrel : ∑ m ∈ f.support, (x m : A) • m = 0 := by
            have := LinearMap.mem_ker.mp hf'.1
            simpa [Finsupp.linearCombination_apply, Finsupp.sum, x] using this
          obtain ⟨n, x', m', hrel', heq⟩ := sum_mem_gens (A' := A') β J f.support x hrel
          refine Submodule.subset_span ⟨n, x', m', hrel', ?_⟩
          rw [map_sum]
          simp only [hΩsingle]
          exact heq
      · exact ⟨0, map_zero _, by simp⟩
      · rintro x y _ _ ⟨u₁, rfl, h₁⟩ ⟨u₂, rfl, h₂⟩
        exact ⟨u₁ + u₂, map_add _ _ _, by rw [map_add]; exact add_mem h₁ h₂⟩
      · rintro c x _ ⟨u₁, rfl, h₁⟩
        exact ⟨c • u₁, map_smul _ _ _, by rw [map_smul]; exact Submodule.smul_mem _ _ h₁⟩
    obtain ⟨u', hu', hΩu'⟩ := hmain _ hZ
    have hinj : Function.Injective ρ := Finsupp.mapRange_injective _ (map_zero _)
      Subtype.val_injective
    rw [hinj hu'] at hΩu'
    exact hΩu'
  · rw [Submodule.span_le]
    rintro z ⟨n, x, m, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sum, TensorProduct.lift.tmul,
      LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply, algebraMap_smul]
    simpa [map_sum, map_smul] using congr(β $hx)

end KernelGenerators

section Localizing
variable {B N N' : Type*} [CommRing B] [AddCommGroup N] [Module B N] [AddCommGroup N']
  [Module B N']

/-- The multiplication map `𝔟 ⊗ N → N`. -/
private noncomputable abbrev idealMul (B N : Type*) [CommRing B] [AddCommGroup N] [Module B N]
    (𝔟 : Ideal B) : 𝔟 ⊗[B] N →ₗ[B] N :=
  TensorProduct.lift ((LinearMap.lsmul B N).comp 𝔟.subtype)

/-- A `B`-linear map `f : N → N'` behaves like a localization map: every finite set of elements
of `N'` is moved into the range of `f` by a `B`-linear automorphism compatible with a
`B`-linear endomorphism of `N`, and every element killed by `f` is killed by such an
endomorphism. -/
private def IsLocalizing (f : N →ₗ[B] N') : Prop :=
  (∀ s : Finset N', ∃ (τ : N →ₗ[B] N) (σ : N' ≃ₗ[B] N'),
      (∀ n, f (τ n) = σ (f n)) ∧ ∀ y ∈ s, σ y ∈ LinearMap.range f) ∧
    ∀ n, f n = 0 → ∃ (τ : N →ₗ[B] N) (σ : N' ≃ₗ[B] N'), (∀ n', f (τ n') = σ (f n')) ∧ τ n = 0

private lemma idealMul_lTensor {𝔟 : Ideal B} (u : N →ₗ[B] N') (z : 𝔟 ⊗[B] N) :
    idealMul B N' 𝔟 (u.lTensor 𝔟 z) = u (idealMul B N 𝔟 z) := by
  induction z using TensorProduct.inductionOn with
  | tmul y n => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- Injectivity of `𝔟 ⊗ N → N` passes along a localizing map. -/
private lemma injective_idealMul_of_isLocalizing {f : N →ₗ[B] N'} (hf : IsLocalizing f)
    (𝔟 : Ideal B) (h : Function.Injective (idealMul B N 𝔟)) :
    Function.Injective (idealMul B N' 𝔟) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨τ₁, σ₁, -, hσ₁⟩ := hf.1 (S.image Prod.snd)
  have : ∀ i ∈ S, ∃ m : N, f m = σ₁ i.2 := fun i hi =>
    hσ₁ _ (Finset.mem_image_of_mem _ hi)
  choose! m hm using this
  set x₀ : 𝔟 ⊗[B] N := ∑ i ∈ S, i.1 ⊗ₜ[B] m i with hx₀
  have hY : (σ₁ : N' →ₗ[B] N').lTensor 𝔟 (∑ i ∈ S, i.1 ⊗ₜ[B] i.2) = f.lTensor 𝔟 x₀ := by
    simp only [hx₀, map_sum, LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
    exact Finset.sum_congr rfl fun i hi => by rw [hm i hi]
  have h1 : f (idealMul B N 𝔟 x₀) = 0 := by
    rw [← idealMul_lTensor f x₀, ← hY, idealMul_lTensor (σ₁ : N' →ₗ[B] N'), hx, map_zero]
  obtain ⟨τ₂, σ₂, hτσ, hτ⟩ := hf.2 _ h1
  have h2 : τ₂.lTensor 𝔟 x₀ = 0 := by
    apply h
    rw [idealMul_lTensor τ₂, hτ, map_zero]
  have h3 : (σ₂ : N' →ₗ[B] N').lTensor 𝔟 (f.lTensor 𝔟 x₀) = 0 := by
    have : (σ₂ : N' →ₗ[B] N').lTensor 𝔟 (f.lTensor 𝔟 x₀) = f.lTensor 𝔟 (τ₂.lTensor 𝔟 x₀) := by
      rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
      congr 2
      ext n
      exact (hτσ n).symm
    rw [this, h2, map_zero]
  rw [← hY, ← LinearMap.lTensor_comp_apply] at h3
  have h4 : ((σ₂ : N' →ₗ[B] N') ∘ₗ (σ₁ : N' →ₗ[B] N')).lTensor 𝔟
      (∑ i ∈ S, i.1 ⊗ₜ[B] i.2) = 0 := h3
  have hbij : Function.Injective (((σ₂ : N' →ₗ[B] N') ∘ₗ (σ₁ : N' →ₗ[B] N')).lTensor 𝔟) :=
    (LinearEquiv.lTensor 𝔟 (σ₁.trans σ₂)).injective
  exact hbij (h4.trans (map_zero _).symm)


section Quotient
variable (𝔞 : Ideal B)

/-- The map `N ⧸ 𝔞 N → N' ⧸ 𝔞 N'` induced by `f`, linear over `B ⧸ 𝔞`. -/
private noncomputable def quotMap (f : N →ₗ[B] N') :
    N ⧸ 𝔞 • (⊤ : Submodule B N) →ₗ[B ⧸ 𝔞] N' ⧸ 𝔞 • (⊤ : Submodule B N') :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((𝔞 • (⊤ : Submodule B N)).mapQ (𝔞 • (⊤ : Submodule B N')) f
      (Submodule.smul_le.mpr fun r hr n _ => by
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top))

private lemma quotMap_mk (f : N →ₗ[B] N') (x : N) :
    quotMap 𝔞 f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

/-- The automorphism of `N ⧸ 𝔞 N` induced by an automorphism of `N`. -/
private noncomputable def quotEquiv (σ : N ≃ₗ[B] N) :
    (N ⧸ 𝔞 • (⊤ : Submodule B N)) ≃ₗ[B ⧸ 𝔞] (N ⧸ 𝔞 • (⊤ : Submodule B N)) :=
  LinearEquiv.ofLinearMap (quotMap 𝔞 (σ : N →ₗ[B] N)) (quotMap 𝔞 (σ.symm : N →ₗ[B] N))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun n => by
      simp [quotMap_mk])
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun n => by
      simp [quotMap_mk])

private lemma quotEquiv_mk (σ : N ≃ₗ[B] N) (x : N) :
    quotEquiv 𝔞 σ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (σ x) := rfl

variable {𝔞}

private lemma exists_of_apply_mem_smul_top {f : N →ₗ[B] N'} (hf : IsLocalizing f) {x : N}
    (hx : f x ∈ 𝔞 • (⊤ : Submodule B N')) :
    ∃ (τ : N →ₗ[B] N) (σ : N' ≃ₗ[B] N'), (∀ n, f (τ n) = σ (f n)) ∧
      τ x ∈ 𝔞 • (⊤ : Submodule B N) := by
  classical
  have htop : (⊤ : Submodule B N') = Submodule.span B (Set.range (id : N' → N')) := by simp
  rw [htop, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
  obtain ⟨a, ha, hsum⟩ := hx
  obtain ⟨τ₁, σ₁, hτσ₁, hσ₁⟩ := hf.1 a.support
  have : ∀ i ∈ a.support, ∃ m : N, f m = σ₁ i := fun i hi => hσ₁ i hi
  choose! m hm using this
  set w : N := ∑ i ∈ a.support, a i • m i with hw
  have h1 : σ₁ (f x) = ∑ i ∈ a.support, a i • σ₁ i := by
    rw [← hsum, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  have h2 : f w = ∑ i ∈ a.support, a i • σ₁ i := by
    rw [hw, map_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [map_smul, hm i hi]
  have hfw : f w = f (τ₁ x) := by rw [h2, ← h1, hτσ₁]
  obtain ⟨τ₂, σ₂, hτσ₂, hτ₂⟩ := hf.2 (τ₁ x - w) (by rw [map_sub, hfw, sub_self])
  refine ⟨τ₂ ∘ₗ τ₁, σ₁.trans σ₂, fun n => ?_, ?_⟩
  · simp [hτσ₂, hτσ₁]
  · have : τ₂ (τ₁ x) = τ₂ w := by rw [map_sub, sub_eq_zero] at hτ₂; exact hτ₂
    rw [LinearMap.comp_apply, this, hw, map_sum]
    exact Submodule.sum_mem _ fun i hi => by
      rw [map_smul]; exact Submodule.smul_mem_smul (ha i) Submodule.mem_top

private lemma isLocalizing_quotMap {f : N →ₗ[B] N'} (hf : IsLocalizing f) (𝔞 : Ideal B) :
    IsLocalizing (quotMap 𝔞 f) := by
  classical
  refine ⟨fun s0 => ?_, fun n0 hn0 => ?_⟩
  · obtain ⟨τ, σ, hτσ, hσ⟩ := hf.1 (s0.image (Function.surjInv (Submodule.Quotient.mk_surjective
      (𝔞 • (⊤ : Submodule B N')))))
    refine ⟨quotMap 𝔞 τ, quotEquiv 𝔞 σ, fun n0 => ?_, fun y0 hy0 => ?_⟩
    · induction n0 using Submodule.Quotient.induction_on with
      | H n => simp [quotMap_mk, quotEquiv_mk, hτσ]
    · set y := Function.surjInv (Submodule.Quotient.mk_surjective
        (𝔞 • (⊤ : Submodule B N'))) y0 with hy
      obtain ⟨m, hm⟩ := hσ y (Finset.mem_image_of_mem _ hy0)
      refine ⟨Submodule.Quotient.mk m, ?_⟩
      rw [quotMap_mk, hm]
      have : y0 = Submodule.Quotient.mk y := (Function.surjInv_eq _ _).symm
      rw [this, quotEquiv_mk]
  · induction n0 using Submodule.Quotient.induction_on with
    | H n =>
      rw [quotMap_mk, Submodule.Quotient.mk_eq_zero] at hn0
      obtain ⟨τ, σ, hτσ, hτ⟩ := exists_of_apply_mem_smul_top hf hn0
      refine ⟨quotMap 𝔞 τ, quotEquiv 𝔞 σ, fun n0 => ?_, ?_⟩
      · induction n0 using Submodule.Quotient.induction_on with
        | H n => simp [quotMap_mk, quotEquiv_mk, hτσ]
      · rw [quotMap_mk, Submodule.Quotient.mk_eq_zero]
        exact hτ


/-- Flatness of `N ⧸ 𝔞 N` over `B ⧸ 𝔞` passes along a localizing map. -/
private lemma flat_quotient_of_isLocalizing {f : N →ₗ[B] N'} (hf : IsLocalizing f)
    (𝔞 : Ideal B) [Module.Flat (B ⧸ 𝔞) (N ⧸ 𝔞 • (⊤ : Submodule B N))] :
    Module.Flat (B ⧸ 𝔞) (N' ⧸ 𝔞 • (⊤ : Submodule B N')) := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  have h := Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp
    (inferInstance : Module.Flat (B ⧸ 𝔞) (N ⧸ 𝔞 • (⊤ : Submodule B N))) hI
  exact injective_idealMul_of_isLocalizing (isLocalizing_quotMap hf 𝔞) I h

end Quotient

section Localized
variable {S' : Type*} [CommRing S'] [Algebra B S'] [Module S' N] [IsScalarTower B S' N]
  [Module S' N'] [IsScalarTower B S' N']

/-- A localization of `S'`-modules is a localizing map over any subring acting compatibly. -/
private lemma isLocalizing_of_isLocalizedModule (U : Submonoid S') (g : N →ₗ[S'] N')
    [IsLocalizedModule U g] : IsLocalizing (g.restrictScalars B) := by
  classical
  have hunit : ∀ u : U, Function.Bijective (fun y : N' => (u : S') • y) := fun u => by
    have := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g u)
    have h : ⇑(algebraMap S' (Module.End S' N') (u : S')) = fun y => (u : S') • y := by
      ext y; simp
    rwa [h] at this
  let τ : S' → N →ₗ[B] N := fun u => (LinearMap.lsmul S' N u).restrictScalars B
  let σ : U → (N' ≃ₗ[B] N') := fun u =>
    LinearEquiv.ofBijective ((LinearMap.lsmul S' N' (u : S')).restrictScalars B) (hunit u)
  refine ⟨fun s => ?_, fun n hn => ?_⟩
  · obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finset U g s
    exact ⟨τ b, σ b, fun n => by simp [τ, σ]; rfl, fun y hy => hb y hy⟩
  · obtain ⟨b, hb⟩ := (IsLocalizedModule.eq_zero_iff U g).mp hn
    exact ⟨τ b, σ b, fun n => by simp [τ, σ]; rfl, by simpa [τ, Submonoid.smul_def] using hb⟩

end Localized
end Localizing

/-- Injectivity of `𝔟 ⊗ N → N` passes to a localization of the base ring, for an `R`-module `N`. -/
private lemma injective_lift_lsmul_of_isLocalization
    {A' R N : Type*} [CommRing A'] [CommRing R] [Algebra A' R] (P : Submonoid A')
    [IsLocalization P R] [AddCommGroup N] [Module A' N] [Module R N] [IsScalarTower A' R N]
    (𝔟 : Ideal A')
    (h : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A' N).comp 𝔟.subtype))) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul R N).comp
      (𝔟.map (algebraMap A' R)).subtype)) := by
  classical
  let e : 𝔟 → 𝔟.map (algebraMap A' R) := fun y =>
    ⟨algebraMap A' R y.1, Ideal.mem_map_of_mem _ y.2⟩
  have e_zero : e 0 = 0 := by ext; simp [e]
  have e_add : ∀ a b, e (a + b) = e a + e b := fun a b => by ext; simp [e]
  have e_smul : ∀ (a : A') (y : 𝔟), e (a • y) = algebraMap A' R a • e y := fun a y => by
    ext; simp [e, Algebra.smul_def]
  let Φ : 𝔟 ⊗[A'] N →+ (𝔟.map (algebraMap A' R)) ⊗[R] N :=
    TensorProduct.liftAddHom
      { toFun := fun y => AddMonoidHom.mk' (fun n : N => e y ⊗ₜ[R] n)
          (fun a b => by rw [TensorProduct.tmul_add])
        map_zero' := by
          ext n
          simp [e_zero]
        map_add' := fun a b => by
          ext n
          simp [e_add, TensorProduct.add_tmul] }
      (fun a y n => by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.mk'_apply]
        rw [e_smul, TensorProduct.smul_tmul, algebraMap_smul])
  have hΦ : ∀ y n, Φ (y ⊗ₜ[A'] n) = e y ⊗ₜ[R] n := fun y n => by
    simp [Φ]
  have hcomp : ∀ x, TensorProduct.lift ((LinearMap.lsmul R N).comp
      (𝔟.map (algebraMap A' R)).subtype) (Φ x) =
      TensorProduct.lift ((LinearMap.lsmul A' N).comp 𝔟.subtype) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul y n =>
      rw [hΦ]
      simp [e, algebraMap_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hsurj : ∀ z : (𝔟.map (algebraMap A' R)) ⊗[R] N, ∃ x, Φ x = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r n =>
      obtain ⟨⟨y, s⟩, hr⟩ := (IsLocalization.mem_map_algebraMap_iff P R).1 r.2
      obtain ⟨u, hu⟩ := IsLocalization.map_units R s
      refine ⟨y ⊗ₜ[A'] ((↑u⁻¹ : R) • n), ?_⟩
      have hr' : r = (↑u⁻¹ : R) • e y := by
        apply Subtype.ext
        have h1 : (r : R) * algebraMap A' R s = algebraMap A' R y := hr
        have h2 : (r : R) = (r : R) * (algebraMap A' R s * ↑u⁻¹) := by
          rw [← hu]; simp
        simp only [e, Submodule.coe_smul, smul_eq_mul]
        rw [h2, ← mul_assoc, h1, mul_comm]
      rw [hΦ, hr', TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := hsurj z
  rw [hcomp] at hz
  have : x = 0 := h (by rw [hz, map_zero])
  rw [this, map_zero]

/-- The quotient `N ⧸ 𝔞 N` is the base change of `N` to `B ⧸ 𝔞`. -/
private lemma isBaseChange_mkQ (B : Type*) [CommRing B] (𝔞 : Ideal B) (N : Type*)
    [AddCommGroup N] [Module B N] :
    IsBaseChange (B ⧸ 𝔞) (Submodule.mkQ (𝔞 • (⊤ : Submodule B N))) := by
  have hs : Function.Surjective (algebraMap B (B ⧸ 𝔞)) := Ideal.Quotient.mk_surjective
  apply IsBaseChange.of_lift_unique
  intro Z _ _ _ _ φ
  let : AddCommGroup Z := Module.addCommMonoidToAddCommGroup B
  have hker : 𝔞 • (⊤ : Submodule B N) ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro y hy n _
    rw [LinearMap.mem_ker, map_smul, ← algebraMap_smul (B ⧸ 𝔞) y (φ n)]
    have : algebraMap B (B ⧸ 𝔞) y = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hy
    rw [this, zero_smul]
  refine ⟨((𝔞 • (⊤ : Submodule B N)).liftQ φ hker).extendScalarsOfSurjective hs, ?_, ?_⟩
  · ext n
    simp
  · intro g hg
    apply LinearMap.ext
    intro x
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective _ x
    have := LinearMap.congr_fun hg n
    simpa using this

/-- Flatness of `M ⧸ J M` over `A ⧸ J` passes to `M' ⧸ J' M'` over `A' ⧸ J'`. -/
private lemma flat_quotient_of_isBaseChange
    {A A' M M' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [AddCommGroup M]
    [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    {β : M →ₗ[A] M'} (hβ : IsBaseChange A' β) (J : Ideal A)
    [Module.Flat (A ⧸ J) (M ⧸ J • (⊤ : Submodule A M))] :
    Module.Flat (A' ⧸ J.map (algebraMap A A'))
      (M' ⧸ (J.map (algebraMap A A')) • (⊤ : Submodule A' M')) := by
  set J' := J.map (algebraMap A A') with hJ'
  let Q := M' ⧸ J' • (⊤ : Submodule A' M')
  let _ : Module (A ⧸ J) Q := Module.compHom Q (algebraMap (A ⧸ J) (A' ⧸ J'))
  have : IsScalarTower (A ⧸ J) (A' ⧸ J') Q :=
    IsScalarTower.of_algebraMap_smul fun r q => rfl
  have : IsScalarTower A (A ⧸ J) Q := by
    refine IsScalarTower.of_algebraMap_smul fun a q => ?_
    change algebraMap (A ⧸ J) (A' ⧸ J') (algebraMap A (A ⧸ J) a) • q = a • q
    rw [← IsScalarTower.algebraMap_apply]
    exact algebraMap_smul (A' ⧸ J') a q
  let g : M →ₗ[A] Q := (Submodule.mkQ (J' • (⊤ : Submodule A' M'))).restrictScalars A ∘ₗ β
  let h : (M ⧸ J • (⊤ : Submodule A M)) →ₗ[A ⧸ J] Q :=
    (isBaseChange_mkQ A J M).lift g
  have h1 : IsBaseChange (A' ⧸ J') g :=
    hβ.comp (isBaseChange_mkQ A' J' M')
  have h2 : IsBaseChange (A' ⧸ J') h :=
    (isBaseChange_mkQ A J M).of_comp (by
      convert h1 using 1
      exact (isBaseChange_mkQ A J M).lift_comp g)
  exact Module.Flat.isBaseChange (A ⧸ J) (A' ⧸ J') (M ⧸ J • (⊤ : Submodule A M)) Q h2

/-- Flatness of `N ⧸ 𝔟 N` over `A' ⧸ 𝔟` passes to a localization of `A'`. -/
private lemma flat_quotient_of_isLocalization
    {A' R N : Type*} [CommRing A'] [CommRing R] [Algebra A' R] (P : Submonoid A')
    [IsLocalization P R] [AddCommGroup N] [Module A' N] [Module R N] [IsScalarTower A' R N]
    (𝔟 : Ideal A') [Module.Flat (A' ⧸ 𝔟) (N ⧸ 𝔟 • (⊤ : Submodule A' N))] :
    Module.Flat (R ⧸ 𝔟.map (algebraMap A' R))
      (N ⧸ (𝔟.map (algebraMap A' R)) • (⊤ : Submodule R N)) := by
  classical
  set I : Ideal R := 𝔟.map (algebraMap A' R) with hI
  -- the two submodules agree as subsets of `N`
  have hEq : ∀ x : N, x ∈ (I • ⊤ : Submodule R N) ↔ x ∈ (𝔟 • ⊤ : Submodule A' N) := by
    intro x
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ (fun a b ha hb => add_mem ha hb)
      intro r hr n _
      have key : ∀ r ∈ I, ∀ n : N, r • n ∈ (𝔟 • ⊤ : Submodule A' N) := by
        intro r hr
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
        · rintro _ ⟨y, hy, rfl⟩ n
          rw [algebraMap_smul]
          exact Submodule.smul_mem_smul hy trivial
        · intro n; simp
        · intro a b _ _ ha hb n
          rw [add_smul]; exact add_mem (ha n) (hb n)
        · intro a b _ hb n
          rw [smul_eq_mul, mul_comm, mul_smul]; exact hb _
      exact key r hr n
    · intro hx
      refine Submodule.smul_induction_on hx ?_ (fun a b ha hb => add_mem ha hb)
      intro y hy n _
      rw [← algebraMap_smul R y n]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hy) trivial
  let _ : Module (A' ⧸ 𝔟) (N ⧸ I • (⊤ : Submodule R N)) :=
    Module.compHom _ (algebraMap (A' ⧸ 𝔟) (R ⧸ I))
  have : IsScalarTower (A' ⧸ 𝔟) (R ⧸ I) (N ⧸ I • (⊤ : Submodule R N)) :=
    ⟨fun q r x => by
      show (q • r) • x = (algebraMap (A' ⧸ 𝔟) (R ⧸ I) q) • r • x
      rw [Algebra.smul_def, mul_smul]⟩
  let f : (N ⧸ 𝔟 • (⊤ : Submodule A' N)) →ₗ[A' ⧸ 𝔟] (N ⧸ I • (⊤ : Submodule R N)) :=
    { toFun := Submodule.liftQ (𝔟 • (⊤ : Submodule A' N))
        ((Submodule.mkQ (I • (⊤ : Submodule R N))).restrictScalars A')
        (by
          intro x hx
          exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R N))).2 ((hEq x).2 hx))
      map_add' := map_add _
      map_smul' := by
        intro q x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
        obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        have h1 : (Ideal.Quotient.mk 𝔟 a) • (Submodule.Quotient.mk n :
            N ⧸ 𝔟 • (⊤ : Submodule A' N)) = Submodule.Quotient.mk (a • n) := rfl
        have h2 : (Ideal.Quotient.mk 𝔟 a) • (Submodule.Quotient.mk n :
            N ⧸ I • (⊤ : Submodule R N)) = Submodule.Quotient.mk (a • n) := by
          show (algebraMap (A' ⧸ 𝔟) (R ⧸ I) (Ideal.Quotient.mk 𝔟 a)) •
            (Submodule.Quotient.mk n : N ⧸ I • (⊤ : Submodule R N)) = _
          rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
          show Submodule.Quotient.mk (algebraMap A' R a • n) = _
          rw [algebraMap_smul]
        rw [h1, RingHom.id_apply]
        change (Submodule.Quotient.mk (a • n) : N ⧸ I • (⊤ : Submodule R N)) =
          (Ideal.Quotient.mk 𝔟 a) • (Submodule.Quotient.mk n : N ⧸ I • (⊤ : Submodule R N))
        rw [h2] }
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 : f (Submodule.Quotient.mk n) = Submodule.Quotient.mk n := rfl
      rw [h1, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((hEq n).1 hx)
    · intro y
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk n, rfl⟩
  have hflat : Module.Flat (A' ⧸ 𝔟) (N ⧸ I • (⊤ : Submodule R N)) :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective f hf).symm
  exact (Module.flat_iff_of_isLocalization (R ⧸ I)
    (Algebra.algebraMapSubmonoid (A' ⧸ 𝔟) P) _).2 hflat

universe u

section FlatAtLaterStage
variable {A M A' S' M' : Type u} [CommRing A] [AddCommGroup M] [Module A M]
  [CommRing A'] [Algebra A A'] [CommRing S'] [Algebra A' S']
  [AddCommGroup M'] [Module A M'] [Module A' M'] [Module S' M']
  [IsScalarTower A A' M'] [IsScalarTower A' S' M']

/-- **Flatness at a later stage** (EGA IV₃, Lemme 11.2.5 (b); Stacks, Lemma 10.99.14, Tag 00MO,
the local analogue). Let `A → A'` be a ring map, `J` an ideal of `A` and `M` an `A`-module such that
`M ⧸ J M` is flat over `A ⧸ J`. Let `M'` be a base change of `M` to `A'` (`β`, `hβ`), with
`A'` Noetherian and `M'` a finite module over a finite type `A'`-algebra `S'`. Suppose that every
element of `ker (J ⊗[A] M → M)` maps to zero in `J' ⊗[A'] M'`, where `J' = J A'`. Then, for every
prime `𝔮` of `S'` containing `J S'`, the localization `M'_𝔮` (`Mq`, with `g` the localization map)
is flat over `A'`.

The hypothesis `hT` is the global, elementwise form of EGA's condition (ii), that
`Tor₁^A(M, A ⧸ J) → Tor₁^{A'}(M', A' ⧸ J')_{𝔮}` is zero: an element of `ker (J ⊗ M → M)` is a
finite sum `∑ xᵢ ⊗ mᵢ` with `∑ xᵢ mᵢ = 0`, and `hT` asks that its image `∑ xᵢ ⊗ β mᵢ` vanish. It
is stronger than EGA's condition, which is only asked after localization at `𝔮`.

The proof applies `ker_lift_lsmul_comp_subtype_eq_span`, to get `Tor₁^{A'}(A' ⧸ J', M') = 0`, and
the local criterion `of_injective_of_flat_quotient_of_isLocalHom` over `A'_P → S'_𝔮`, `P = 𝔮 ∩ A'`.

The hypotheses on `M ⧸ J M` (flatness over `A ⧸ J`) and on `M'` (finiteness over `S'`) are needed,
see the module docstring for counterexamples. -/
theorem flat_of_isLocalizedModule_of_tor₁_vanishes
    (β : M →ₗ[A] M') (hβ : IsBaseChange A' β) (J : Ideal A)
    (hJ : Module.Flat (A ⧸ J) (M ⧸ J • (⊤ : Submodule A M)))
    [IsNoetherianRing A'] [Algebra.FiniteType A' S'] [Module.Finite S' M']
    (hT : ∀ (n : ℕ) (x : Fin n → J) (m : Fin n → M), ∑ i, (x i : A) • m i = 0 →
      ∑ i, (⟨algebraMap A A' (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
        J.map (algebraMap A A')) ⊗ₜ[A'] β (m i) = 0)
    (q : Ideal S') [q.IsPrime] (hq : (J.map (algebraMap A A')).map (algebraMap A' S') ≤ q)
    (Mq : Type u) [AddCommGroup Mq] [Module S' Mq] [Module A' Mq] [IsScalarTower A' S' Mq]
    (g : M' →ₗ[S'] Mq) [IsLocalizedModule q.primeCompl g] :
    Module.Flat A' Mq := by
  classical
  have := hJ
  set J' : Ideal A' := J.map (algebraMap A A') with hJ'
  -- injectivity of `J' ⊗ M' → M'`
  have hinj : Function.Injective (idealMul A' M' J') := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : z ∈ LinearMap.ker (idealMul A' M' J') := hz
    rw [ker_lift_lsmul_comp_subtype_eq_span hβ J] at hz'
    have hle := Submodule.span_le (R := A') (M := J' ⊗[A'] M') (s := {z | ∃ (n : ℕ)
      (x : Fin n → J) (m : Fin n → M), ∑ i, (x i : A) • m i = 0 ∧ z = ∑ i, (⟨algebraMap A A' (x i),
        Ideal.mem_map_of_mem _ (x i).2⟩ : J.map (algebraMap A A')) ⊗ₜ[A'] β (m i)})
      (p := ⊥)
    have := hle.mpr (by rintro _ ⟨n, x, m, hx, rfl⟩; exact hT n x m hx) hz'
    simpa using this
  have hloc : IsLocalizing (g.restrictScalars A') :=
    isLocalizing_of_isLocalizedModule q.primeCompl g
  have hinjq : Function.Injective (idealMul A' Mq J') :=
    injective_idealMul_of_isLocalizing hloc J' hinj
  have hflatq : Module.Flat (A' ⧸ J') (Mq ⧸ J' • (⊤ : Submodule A' Mq)) := by
    have := flat_quotient_of_isBaseChange hβ J
    exact flat_quotient_of_isLocalizing hloc J'
  -- the local rings
  set P : Ideal A' := q.comap (algebraMap A' S') with hP
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ q
  have : IsNoetherianRing S' := Algebra.FiniteType.isNoetherianRing A' S'
  let algRT : Algebra (Localization.AtPrime P) (Localization.AtPrime q) :=
    (Localization.localRingHom P q (algebraMap A' S') rfl).toAlgebra
  have : IsScalarTower A' (Localization.AtPrime P) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom P q (algebraMap A' S') rfl
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  let : Module (Localization.AtPrime q) Mq := IsLocalizedModule.module q.primeCompl g
  have : IsScalarTower S' (Localization.AtPrime q) Mq :=
    IsLocalizedModule.isScalarTower_module q.primeCompl g
  let : Module (Localization.AtPrime P) Mq :=
    Module.compHom Mq (algebraMap (Localization.AtPrime P) (Localization.AtPrime q))
  have : IsScalarTower (Localization.AtPrime P) (Localization.AtPrime q) Mq :=
    ⟨fun r t m => by
      show (r • t) • m = (algebraMap (Localization.AtPrime P) (Localization.AtPrime q) r) • (t • m)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower A' (Localization.AtPrime P) Mq :=
    .of_algebraMap_smul fun a m => by
      show (algebraMap (Localization.AtPrime P) (Localization.AtPrime q)
        (algebraMap A' (Localization.AtPrime P) a)) • m = a • m
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply A' S' (Localization.AtPrime q), algebraMap_smul,
        algebraMap_smul]
  have : Module.Finite (Localization.AtPrime q) Mq :=
    Module.Finite.of_isLocalizedModule q.primeCompl g
  have hI : J'.map (algebraMap A' (Localization.AtPrime P)) ≠ ⊤ := by
    have hJP : J' ≤ P := Ideal.map_le_iff_le_comap.mp hq
    have hle : J'.map (algebraMap A' (Localization.AtPrime P)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [Ideal.map_le_iff_le_comap]
      exact hJP.trans (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P).symm.le
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle
  have := hflatq
  have hflat : Module.Flat (Localization.AtPrime P) Mq :=
    of_injective_of_flat_quotient_of_isLocalHom (S := Localization.AtPrime q) _ hI
      (injective_lift_lsmul_of_isLocalization P.primeCompl J' hinjq)
      (flat_quotient_of_isLocalization P.primeCompl J')
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl Mq).mp hflat

end FlatAtLaterStage

end Module.Flat
