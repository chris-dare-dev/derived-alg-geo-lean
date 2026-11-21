/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.Flat.LocalCriterion
import DerivedAlgGeo.RingTheory.Localization.Free
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.InvSubmonoid

/-!
# Flatness over a finitely generated subalgebra

Let `R₀` be a Noetherian ring, `S₀` a finite type `R₀`-algebra, `M₀` a finite `S₀`-module and `R` an
`R₀`-algebra. If `R ⊗[R₀] M₀` is flat over `R`, then `R₁ ⊗[R₀] M₀` is flat over `R₁` for some
finitely generated `R₀`-subalgebra `R₁` of `R`.

## Main results

* `Module.Flat.exists_fg_subalgebra_flat_of_isNoetherianRing`: the statement above; Stacks 02JO (1)
  for a Noetherian base, EGA IV₃ (11.2.6.1) (ii) and (11.2.7) a) ⇒ c).

## Implementation notes

For an `R₀`-algebra `A`, the module `A ⊗[R₀] M₀` is a module over `A ⊗[R₀] S₀`, through a module
structure that is a local instance in this file. For an ideal `I` of `R₀`, the property
`ReachedOver I` says that, from some finitely generated subalgebra on, every localization of
`A ⊗ M₀` at a prime of `A ⊗ S₀` lying over `V(I)` is flat over `A`. It holds for every `I` by
Noetherian induction on `I`, and `I = 0` with the maximal ideals of `A ⊗ S₀` gives the theorem.

* If `I = ⊤` there is nothing to prove. If `I` is not prime, `a * b ∈ I` with `a, b ∉ I`, and
  the primes over `V(I)` lie over `V(I + (a))` or `V(I + (b))`; the induction hypothesis applies
  to both.
* If `I = p` is prime, generic freeness (`Module.exists_free_localizedModule_away_of_finiteType`
  for `R₀ ⧸ p`) gives `f ∉ p` such that `M₀_f ⧸ p M₀_f` is flat over `R₀ ⧸ p`. Flatness of
  `R ⊗ M₀` over `R` makes the relations of `M₀` with coefficients in `p` trivial over a
  finitely generated subalgebra, and this persists for larger ones. The local criterion
  `Module.Flat.flat_of_isLocalizedModule_of_tor₁_vanishes`, applied after inverting `f`, then
  gives flatness at the primes over `V(p) ∩ D(f)`. The primes over `V(p) ∖ D(f) = V(p + (f))` are
  covered by the induction hypothesis. Openness of the flat locus is not used.

The hypotheses are load-bearing; see the docstring of the main theorem.

## References

* [Stacks: Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks: Tag 051R](https://stacks.math.columbia.edu/tag/051R)
* EGA IV₃, (11.2.5), (11.2.6.1) and (11.2.7)

## Tags

flat, finitely generated subalgebra, filtered colimit, generic freeness, local criterion
-/

universe u
open TensorProduct

namespace Module.Flat

section StageModule

variable (R₀ S₀ M₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]
variable (A : Type u) [CommRing A] [Algebra R₀ A]

private noncomputable def actS : S₀ →ₐ[R₀] Module.End R₀ (A ⊗[R₀] M₀) :=
  (Module.End.lTensorAlgHom R₀ M₀ A).comp (Algebra.lsmul R₀ R₀ M₀)

private theorem actS_tmul (s : S₀) (b : A) (m : M₀) :
    actS R₀ S₀ M₀ A s (b ⊗ₜ[R₀] m) = b ⊗ₜ[R₀] (s • m) := rfl

private noncomputable def stageAlgHom : A ⊗[R₀] S₀ →ₐ[R₀] Module.End R₀ (A ⊗[R₀] M₀) :=
  Algebra.TensorProduct.lift (Algebra.lsmul R₀ R₀ (A ⊗[R₀] M₀)) (actS R₀ S₀ M₀ A) (fun a s => by
      refine Commute.symm ?_
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul b m =>
        simp only [Module.End.mul_apply, actS_tmul, Algebra.lsmul_coe, TensorProduct.smul_tmul']
      | add x y hx hy => simp only [Module.End.mul_apply, map_add] at hx hy ⊢; rw [hx, hy])

@[instance_reducible] private noncomputable def stageModule : Module (A ⊗[R₀] S₀) (A ⊗[R₀] M₀) :=
  Module.compHom (A ⊗[R₀] M₀) (stageAlgHom R₀ S₀ M₀ A).toRingHom

attribute [local instance] stageModule

private theorem stage_smul (a : A) (s : S₀) (b : A) (m : M₀) :
    (a ⊗ₜ[R₀] s) • (b ⊗ₜ[R₀] m) = (a * b) ⊗ₜ[R₀] (s • m) := by
  show (stageAlgHom R₀ S₀ M₀ A (a ⊗ₜ[R₀] s)) (b ⊗ₜ[R₀] m) = _
  rw [stageAlgHom, Algebra.TensorProduct.lift_tmul]
  simp only [Module.End.mul_apply, actS_tmul, Algebra.lsmul_coe, TensorProduct.smul_tmul']
  rfl

private instance stage_isScalarTower : IsScalarTower A (A ⊗[R₀] S₀) (A ⊗[R₀] M₀) :=
  IsScalarTower.of_algebraMap_smul fun a n => by
    induction n using TensorProduct.inductionOn with
    | tmul b m =>
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        stage_smul, one_smul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]

private instance stage_finite [Module.Finite S₀ M₀] : Module.Finite (A ⊗[R₀] S₀) (A ⊗[R₀] M₀) := by
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := S₀) (M := M₀)
  refine ⟨⟨T.image (fun m => (1 : A) ⊗ₜ[R₀] m), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    have hm : m ∈ Submodule.span S₀ (T : Set M₀) := hT ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem t ht =>
      have : b ⊗ₜ[R₀] t = (b ⊗ₜ[R₀] (1 : S₀)) • ((1 : A) ⊗ₜ[R₀] t) := by
        rw [stage_smul, mul_one, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simpa using ⟨t, ht, rfl⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | smul s m _ hm =>
      have : b ⊗ₜ[R₀] (s • m) = ((1 : A) ⊗ₜ[R₀] s) • (b ⊗ₜ[R₀] m) := by
        rw [stage_smul, one_mul]
      rw [this]; exact Submodule.smul_mem _ _ hm
  | add x y hx hy => exact add_mem hx hy

private instance stage_isScalarTower_base : IsScalarTower R₀ (A ⊗[R₀] S₀) (A ⊗[R₀] M₀) :=
  IsScalarTower.of_algebraMap_smul fun r n => by
    induction n using TensorProduct.inductionOn with
    | tmul b m =>
      rw [Algebra.TensorProduct.algebraMap_apply, stage_smul, one_smul, TensorProduct.smul_tmul',
        Algebra.smul_def]
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]

end StageModule

section BaseChangeLocalization

variable {A T M₀ Z : Type*} [CommRing A] [CommRing T] [Algebra A T] [AddCommGroup M₀]
  [Module A M₀] [AddCommGroup Z] [Module A Z] [Module T Z] [IsScalarTower A T Z]

/-- If `f` becomes a unit in `T`, the base change of `M₀` to `T` is also the base change of
the localization of `M₀` at `f`. -/
private theorem isBaseChange_lift_localizedModule (f : A) (hf : IsUnit (algebraMap A T f))
    (β : M₀ →ₗ[A] Z) (hβ : IsBaseChange T β)
    (h : ∀ x : Submonoid.powers f, IsUnit (algebraMap A (Module.End A Z) x)) :
    IsBaseChange T (LocalizedModule.lift (Submonoid.powers f) β h) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  have hQ : ∀ x : Submonoid.powers f, IsUnit (algebraMap A (Module.End A Q) x) := by
    rintro ⟨_, n, rfl⟩
    have hu : IsUnit (algebraMap A T (f ^ n)) := by simpa using hf.pow n
    obtain ⟨v, hv⟩ := hu
    rw [Module.End.isUnit_iff]
    refine Function.bijective_iff_has_inverse.2 ⟨fun q => (↑v⁻¹ : T) • q, fun q => ?_, fun q => ?_⟩
    · simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul T (f ^ n) q, ← hv, smul_smul, Units.inv_mul, one_smul]
    · simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul T (f ^ n) ((↑v⁻¹ : T) • q), ← hv, smul_smul, Units.mul_inv, one_smul]
  set ι := LocalizedModule.mkLinearMap (Submonoid.powers f) M₀
  have hlift : ∀ m, LocalizedModule.lift (Submonoid.powers f) β h (ι m) = β m := fun m => by
    simp [ι]
  refine ⟨hβ.lift (g ∘ₗ ι), ?_, ?_⟩
  · refine IsLocalizedModule.ext (Submonoid.powers f) ι hQ ?_
    ext m
    simp [hlift, hβ.lift_eq]
  · intro g' hg'
    refine hβ.algHom_ext' _ _ ?_
    ext m
    have := LinearMap.congr_fun hg' (ι m)
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, hlift] at this
    simp [hβ.lift_eq, this]
end BaseChangeLocalization


section LocalizationOfLocalization

variable {S Su N N' Mq : Type*} [CommRing S] [CommRing Su] [Algebra S Su] (u : S)
  [IsLocalization.Away u Su]
  [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S N'] [Module Su N']
  [IsScalarTower S Su N'] [AddCommGroup Mq] [Module S Mq] [Module Su Mq] [IsScalarTower S Su Mq]
  (q : Ideal S) [q.IsPrime] [(q.map (algebraMap S Su)).IsPrime]

include u in
/-- Composing the localization at `u` with the localization of the result at the extension of a
prime `q ∌ u` is the localization at `q`. -/
private theorem isLocalizedModule_comp_map_away (hu : u ∉ q)
    (h : N →ₗ[S] N') [IsLocalizedModule (Submonoid.powers u) h]
    (g : N' →ₗ[Su] Mq) [IsLocalizedModule (q.map (algebraMap S Su)).primeCompl g] :
    IsLocalizedModule q.primeCompl ((g.restrictScalars S) ∘ₗ h) := by
  have hdisj : Disjoint (Submonoid.powers u : Set S) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hu (‹q.IsPrime›.mem_of_pow_mem n hn)
  have hcm : Ideal.under S (q.map (algebraMap S Su)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers u) Su ‹_› hdisj
  have hmem : ∀ s : S, algebraMap S Su s ∈ q.map (algebraMap S Su) ↔ s ∈ q := fun s => by
    rw [← Ideal.mem_comap, ← Ideal.under_def, hcm]
  have hpow : ∀ d : Submonoid.powers u, (d : S) ∈ q.primeCompl := by
    rintro ⟨_, n, rfl⟩ hh
    exact hu (‹q.IsPrime›.mem_of_pow_mem n hh)
  -- every element of the local complement clears to a numerator outside `q`
  have hclear : ∀ t : (q.map (algebraMap S Su)).primeCompl, ∃ (s : S) (d : Submonoid.powers u),
      s ∈ q.primeCompl ∧ (t : Su) * algebraMap S Su d = algebraMap S Su s := by
    intro t
    obtain ⟨⟨s, d⟩, hd⟩ := IsLocalization.surj (Submonoid.powers u) (t : Su)
    refine ⟨s, d, fun hs => ?_, hd⟩
    have h1 := (hmem s).2 hs
    rw [← hd] at h1
    rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
    · exact t.2 h2
    · exact hpow d ((hmem d).1 h2)
  have hsmul : ∀ (s : S) (m : Mq), s • m = algebraMap S Su s • m := fun s m =>
    (algebraMap_smul Su s m).symm
  have hsmul' : ∀ (s : S) (m : N'), s • m = algebraMap S Su s • m := fun s m =>
    (algebraMap_smul Su s m).symm
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have ht : algebraMap S Su t ∈ (q.map (algebraMap S Su)).primeCompl := fun hh =>
      t.2 ((hmem t).1 hh)
    have := IsLocalizedModule.map_units g ⟨_, ht⟩
    rw [Module.End.isUnit_iff] at this ⊢
    have e : ⇑(algebraMap S (Module.End S Mq) t) =
        ⇑(algebraMap Su (Module.End Su Mq) (algebraMap S Su t)) := by
      ext m
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      exact hsmul t m
    rw [e]
    exact this
  · intro y
    obtain ⟨⟨n', t⟩, ht⟩ := IsLocalizedModule.surj (q.map (algebraMap S Su)).primeCompl g y
    obtain ⟨s₁, d, hs₁, hd⟩ := hclear t
    obtain ⟨⟨x, w⟩, hw⟩ := IsLocalizedModule.surj (Submonoid.powers u) h ((d : S) • n')
    have hwq : (w : S) ∈ q.primeCompl := hpow w
    refine ⟨⟨x, ⟨(w : S) * s₁, mul_mem hwq hs₁⟩⟩, ?_⟩
    have ht' : (t : Su) • y = g n' := ht
    have hw' : (w : S) • ((d : S) • n') = h x := hw
    have h1 : s₁ • y = g ((d : S) • n') := by
      rw [hsmul, ← hd, mul_comm, mul_smul, ht', hsmul' (d : S) n']
      exact (map_smul g _ _).symm
    show ((w : S) * s₁) • y = g (h x)
    rw [mul_smul, h1, ← hw']
    exact (map_smul (g.restrictScalars S) _ _).symm
  · intro x₁ x₂ hx
    have hx' : g (h x₁) = g (h x₂) := hx
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := (q.map (algebraMap S Su)).primeCompl)
      (f := g) hx'
    obtain ⟨s₁, d, hs₁, hd⟩ := hclear c
    have hc' : (c : Su) • h x₁ = (c : Su) • h x₂ := hc
    have h2 : h (s₁ • x₁) = h (s₁ • x₂) := by
      rw [map_smul, map_smul, hsmul' s₁ (h x₁), hsmul' s₁ (h x₂), ← hd, mul_comm, mul_smul,
        mul_smul, hc']
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers u) h2
    refine ⟨⟨u ^ k * s₁, mul_mem (hpow ⟨_, k, rfl⟩) hs₁⟩, ?_⟩
    show (u ^ k * s₁) • x₁ = (u ^ k * s₁) • x₂
    rw [mul_smul, mul_smul]
    exact hk
end LocalizationOfLocalization


section HT
variable {A A' B N N' M₀ : Type*} [CommRing A] [CommRing A'] [CommRing B] [Algebra A A']
  [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
  [AddCommGroup N] [Module A N] [Module A' N] [IsScalarTower A A' N]
  [AddCommGroup N'] [Module A N'] [Module A' N'] [Module B N'] [IsScalarTower A' B N']
  [IsScalarTower A A' N'] [IsScalarTower A B N']
  [AddCommGroup M₀] [Module A M₀]

/-- The `A'`-linear inclusion of `J A'` into `J B`. -/
private noncomputable def idealMapInclusion (J : Ideal A) :
    J.map (algebraMap A A') →ₗ[A'] J.map (algebraMap A B) :=
  LinearMap.codRestrict ((J.map (algebraMap A B)).restrictScalars A')
    ((Algebra.linearMap A' B) ∘ₗ (J.map (algebraMap A A')).subtype) (fun ⟨a, ha⟩ => by
      show algebraMap A' B a ∈ J.map (algebraMap A B)
      rw [IsScalarTower.algebraMap_eq A A' B, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ ha)


private theorem idealMapInclusion_apply (J : Ideal A) (a : J.map (algebraMap A A')) :
    ((idealMapInclusion (B := B) J a : J.map (algebraMap A B)) : B) = algebraMap A' B a := rfl

/-- Vanishing of the relations of `M₀` after tensoring with `N` passes to the localization of `M₀`
at `f` and a localization `N'` of `N` in which `f` is invertible. -/
private theorem tor_vanishes_localizedModule (φ : N →ₗ[A'] N') (β₀ : M₀ →ₗ[A] N)
    (J : Ideal A) (f : A) (hf : IsUnit (algebraMap A B f))
    (h : ∀ x : Submonoid.powers f, IsUnit (algebraMap A (Module.End A N') x))
    (hT : ∀ (n : ℕ) (x : Fin n → J) (m : Fin n → M₀), ∑ i, (x i : A) • m i = 0 →
      ∑ i, (⟨algebraMap A A' (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
        J.map (algebraMap A A')) ⊗ₜ[A'] β₀ (m i) = 0) :
    ∀ (n : ℕ) (x : Fin n → J) (m : Fin n → LocalizedModule (Submonoid.powers f) M₀),
      ∑ i, (x i : A) • m i = 0 →
      ∑ i, (⟨algebraMap A B (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
        J.map (algebraMap A B)) ⊗ₜ[B]
          (LocalizedModule.lift (Submonoid.powers f) ((φ.restrictScalars A) ∘ₗ β₀) h) (m i) =
        0 := by
  intro n x m hx
  set β₁ : M₀ →ₗ[A] N' := (φ.restrictScalars A) ∘ₗ β₀ with hβ₁
  set ι := LocalizedModule.mkLinearMap (Submonoid.powers f) M₀ with hι
  set βloc := LocalizedModule.lift (Submonoid.powers f) β₁ h with hβloc
  have hβι : ∀ a, βloc (ι a) = β₁ a := fun a => by simp [hι, hβloc]
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers f) ι m
  choose a ha using hb
  have ha' : ∀ i, ι (a i) = (b : A) • m i := fun i => ha i
  have hsum : ι (∑ i, (x i : A) • a i) = 0 := by
    rw [map_sum]
    have : ∀ i, ι ((x i : A) • a i) = (b : A) • ((x i : A) • m i) := fun i => by
      rw [map_smul, ha', smul_comm]
    simp only [this, ← Finset.smul_sum, hx, smul_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) ι).1 hsum
  let x' : Fin n → J := fun i => ⟨(c : A) * x i, J.mul_mem_left _ (x i).2⟩
  have hrel : ∑ i, (x' i : A) • a i = 0 := by
    have : ∑ i, (x' i : A) • a i = (c : A) • ∑ i, (x i : A) • a i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [x', mul_smul]
    rw [this]; exact hc
  have H0 := hT n x' a hrel
  let Ψ : (J.map (algebraMap A A')) ⊗[A'] N →ₗ[A'] (J.map (algebraMap A B)) ⊗[B] N' :=
    (TensorProduct.mapOfCompatibleSMul B A' A' (J.map (algebraMap A B)) N') ∘ₗ
      (TensorProduct.map (idealMapInclusion (B := B) J) φ)
  have H1 := congrArg Ψ H0
  simp only [map_sum, map_zero] at H1
  have hterm : ∀ i, Ψ ((⟨algebraMap A A' (x' i), Ideal.mem_map_of_mem _ (x' i).2⟩ :
      J.map (algebraMap A A')) ⊗ₜ[A'] β₀ (a i)) =
      ((b : A) * (c : A)) • ((⟨algebraMap A B (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
        J.map (algebraMap A B)) ⊗ₜ[B] βloc (m i)) := fun i => by
    have e2 : φ (β₀ (a i)) = (b : A) • βloc (m i) := by
      rw [← map_smul, ← ha' i, hβι]; rfl
    have e3 : Ψ ((⟨algebraMap A A' (x' i), Ideal.mem_map_of_mem _ (x' i).2⟩ :
        J.map (algebraMap A A')) ⊗ₜ[A'] β₀ (a i)) =
        (idealMapInclusion (B := B) J
          ⟨algebraMap A A' (x' i), Ideal.mem_map_of_mem _ (x' i).2⟩) ⊗ₜ[B]
          φ (β₀ (a i)) := rfl
    rw [e3, e2, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    refine Subtype.ext ?_
    have e4 : ((idealMapInclusion (B := B) J
        ⟨algebraMap A A' (x' i), Ideal.mem_map_of_mem _ (x' i).2⟩ : J.map (algebraMap A B)) : B) =
        algebraMap A B (x' i) := by
      rw [idealMapInclusion_apply, ← IsScalarTower.algebraMap_apply]
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, e4]
    simp only [Algebra.smul_def, x', map_mul]
    ring
  simp only [hterm, ← Finset.smul_sum] at H1
  have hunit : IsUnit (algebraMap A B ((b : A) * (c : A))) := by
    have hu : ∀ t : Submonoid.powers f, IsUnit (algebraMap A B t) := by
      rintro ⟨_, k, rfl⟩
      simpa using hf.pow k
    rw [map_mul]
    exact (hu b).mul (hu c)
  obtain ⟨v, hv⟩ := hunit
  set z := ∑ i, (⟨algebraMap A B (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
        J.map (algebraMap A B)) ⊗ₜ[B] βloc (m i) with hz
  have h3 : (algebraMap A B ((b : A) * (c : A))) • z = 0 := by
    rw [algebraMap_smul]; exact H1
  rw [← hv] at h3
  calc z = (↑v⁻¹ : B) • ((v : B) • z) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = 0 := by rw [h3, smul_zero]
end HT


section PointwiseCriterion

variable {A A' S' N M₀ : Type u} [CommRing A] [CommRing A'] [Algebra A A'] [IsNoetherianRing A']
  [CommRing S'] [Algebra A' S'] [Algebra A S'] [IsScalarTower A A' S'] [Algebra.FiniteType A' S']
  [AddCommGroup N] [Module A' N] [Module S' N] [Module A N]
  [IsScalarTower A' S' N] [IsScalarTower A A' N] [IsScalarTower A S' N] [Module.Finite S' N]
  [AddCommGroup M₀] [Module A M₀]

private theorem flat_of_tor₁_vanishes_of_notMem
    (β₀ : M₀ →ₗ[A] N) (hβ₀ : IsBaseChange A' β₀) (J : Ideal A) (f : A)
    (hJ : Module.Flat (A ⧸ J) (LocalizedModule (Submonoid.powers f) M₀ ⧸
      J • (⊤ : Submodule A (LocalizedModule (Submonoid.powers f) M₀))))
    (hT : ∀ (n : ℕ) (x : Fin n → J) (m : Fin n → M₀), ∑ i, (x i : A) • m i = 0 →
      ∑ i, (⟨algebraMap A A' (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
        J.map (algebraMap A A')) ⊗ₜ[A'] β₀ (m i) = 0)
    (q : Ideal S') [q.IsPrime] (hq : (J.map (algebraMap A A')).map (algebraMap A' S') ≤ q)
    (hf : algebraMap A' S' (algebraMap A A' f) ∉ q)
    (Mq : Type u) [AddCommGroup Mq] [Module S' Mq] [Module A' Mq] [IsScalarTower A' S' Mq]
    (g : N →ₗ[S'] Mq) [IsLocalizedModule q.primeCompl g] : Module.Flat A' Mq := by
  classical
  set f' : A' := algebraMap A A' f with hf'
  set u : S' := algebraMap A' S' f' with hu
  let Af := Localization.Away f'
  let Su := Localization.Away u
  let N' := LocalizedModule (Submonoid.powers u) N
  let _ : Algebra Af Su := (IsLocalization.Away.map Af Su (algebraMap A' S') f').toAlgebra
  have : IsScalarTower A' Af Su := IsScalarTower.of_algebraMap_eq fun a => by
    simp [Af, Su, IsLocalization.Away.map, IsLocalization.map_eq, RingHom.algebraMap_toAlgebra,
      IsScalarTower.algebraMap_apply A' S' Su]
  have : IsScalarTower A Af Su := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A A' Af, ← IsScalarTower.algebraMap_apply A' Af Su,
      ← IsScalarTower.algebraMap_apply A A' Su]
  have : IsNoetherianRing Af :=
    IsLocalization.isNoetherianRing (Submonoid.powers f') Af inferInstance
  have : Algebra.FiniteType A' Su := inferInstance
  have : Algebra.FiniteType Af Su := Algebra.FiniteType.of_restrictScalars_finiteType A' Af Su
  let _ : Module Af N' := Module.compHom N' (algebraMap Af Su)
  have : IsScalarTower Af Su N' := IsScalarTower.of_algebraMap_smul fun a n => rfl
  have : IsScalarTower A' Af N' := IsScalarTower.of_algebraMap_smul fun a n => by
    show algebraMap Af Su (algebraMap A' Af a) • n = a • n
    rw [← IsScalarTower.algebraMap_apply A' Af Su, algebraMap_smul]
  have : IsScalarTower A Af N' := IsScalarTower.of_algebraMap_smul fun a n => by
    show algebraMap Af Su (algebraMap A Af a) • n = a • n
    rw [← IsScalarTower.algebraMap_apply A Af Su, algebraMap_smul]
  have : Module.Finite Su N' :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers u)
      (LocalizedModule.mkLinearMap (Submonoid.powers u) N)
  let mkN : N →ₗ[S'] N' := LocalizedModule.mkLinearMap (Submonoid.powers u) N
  let φ : N →ₗ[A'] N' := mkN.restrictScalars A'
  let β₁ : M₀ →ₗ[A] N' := (φ.restrictScalars A) ∘ₗ β₀
  have hu_eq : algebraMap A S' f = u := (IsScalarTower.algebraMap_apply A A' S' f)
  have hfun : ∀ x : Submonoid.powers f, IsUnit (algebraMap A (Module.End A N') x) := by
    rintro ⟨_, k, rfl⟩
    have h1 := IsLocalizedModule.map_units (S := Submonoid.powers u) mkN ⟨u ^ k, k, rfl⟩
    rw [Module.End.isUnit_iff] at h1 ⊢
    have e : ⇑(algebraMap A (Module.End A N') (f ^ k)) =
        ⇑(algebraMap S' (Module.End S' N') (u ^ k)) := by
      ext n
      have e2 : algebraMap A S' (f ^ k) = u ^ k := by rw [map_pow, hu_eq]
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← e2, algebraMap_smul]
    rw [e]
    exact h1
  let β : LocalizedModule (Submonoid.powers f) M₀ →ₗ[A] N' :=
    LocalizedModule.lift (Submonoid.powers f) β₁ hfun
  have hβ : IsBaseChange Af β := by
    have hmk : IsLocalizedModule (Submonoid.powers f') φ :=
      IsLocalizedModule.restrictScalars_powers (R := A') (A := S') f' mkN
    have h1 : IsBaseChange Af φ := IsLocalizedModule.isBaseChange (Submonoid.powers f') Af φ
    have h2 : IsBaseChange Af β₁ := IsBaseChange.comp hβ₀ h1
    exact isBaseChange_lift_localizedModule f (IsLocalization.Away.algebraMap_isUnit f')
      β₁ h2 hfun
  have hT'' := tor_vanishes_localizedModule (B := Af) φ β₀ J f
    (IsLocalization.Away.algebraMap_isUnit f') hfun hT
  have hdisj : Disjoint (Submonoid.powers u : Set S') q := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hf (‹q.IsPrime›.mem_of_pow_mem n hn)
  have hq''p : (q.map (algebraMap S' Su)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers u) Su q ‹_› hdisj
  have hqJ : J.map (algebraMap A S') ≤ q := by
    have : (J.map (algebraMap A A')).map (algebraMap A' S') = J.map (algebraMap A S') := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact this ▸ hq
  have hq'' : (J.map (algebraMap A Af)).map (algebraMap Af Su) ≤ q.map (algebraMap S' Su) := by
    rw [Ideal.map_map]
    have e : (algebraMap Af Su).comp (algebraMap A Af) =
        (algebraMap S' Su).comp (algebraMap A S') := by
      ext a
      simp [← IsScalarTower.algebraMap_apply]
    rw [e, ← Ideal.map_map]
    exact Ideal.map_mono hqJ
  let Mq'' := LocalizedModule (q.map (algebraMap S' Su)).primeCompl N'
  have hflat'' : Module.Flat Af Mq'' :=
    flat_of_isLocalizedModule_of_tor₁_vanishes (A := A) (A' := Af) (S' := Su)
      (M := LocalizedModule (Submonoid.powers f) M₀) (M' := N') β hβ J hJ hT''
      (q.map (algebraMap S' Su)) hq'' Mq''
      (LocalizedModule.mkLinearMap (q.map (algebraMap S' Su)).primeCompl N')
  have hflatA' : Module.Flat A' Mq'' :=
    (Module.flat_iff_of_isLocalization Af (Submonoid.powers f') Mq'').1 hflat''
  have hcomp : IsLocalizedModule q.primeCompl
      ((LocalizedModule.mkLinearMap (q.map (algebraMap S' Su)).primeCompl N').restrictScalars S'
        ∘ₗ mkN) :=
    isLocalizedModule_comp_map_away u q hf mkN
      (LocalizedModule.mkLinearMap (q.map (algebraMap S' Su)).primeCompl N')
  let e : Mq ≃ₗ[S'] Mq'' := IsLocalizedModule.linearEquiv q.primeCompl g
    ((LocalizedModule.mkLinearMap (q.map (algebraMap S' Su)).primeCompl N').restrictScalars S'
        ∘ₗ mkN)
  exact Module.Flat.of_linearEquiv (e.restrictScalars A')

end PointwiseCriterion

section GenericFreeness
open scoped Pointwise

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
  [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- For an ideal `p` of `R₀`, `(p S₀) • ⊤` and `p • ⊤` agree as subsets of `M₀`. -/
private lemma restrictScalars_map_smul_top (p : Ideal R₀) :
    ((p.map (algebraMap R₀ S₀)) • (⊤ : Submodule S₀ M₀)).restrictScalars R₀ =
      p • (⊤ : Submodule R₀ M₀) := by
  let K : Submodule S₀ M₀ :=
    { (p • ⊤ : Submodule R₀ M₀) with
      smul_mem' := fun c x hx => by
        show c • x ∈ (p • ⊤ : Submodule R₀ M₀)
        refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
        · rw [smul_comm]
          exact Submodule.smul_mem_smul hr trivial
        · rw [smul_add]; exact add_mem hx hy }
  apply le_antisymm
  · intro x hx
    have : (p.map (algebraMap R₀ S₀)) • (⊤ : Submodule S₀ M₀) ≤ K := by
      rw [Submodule.smul_le]
      intro r hr n _
      have hr' : r ∈ Submodule.span S₀ (algebraMap R₀ S₀ '' (p : Set R₀)) := hr
      refine Submodule.span_induction (p := fun r _ => ∀ n : M₀, r • n ∈ (p • ⊤ : Submodule R₀ M₀))
        ?_ ?_ ?_ ?_ hr' n
      · rintro _ ⟨a, ha, rfl⟩ n
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul ha trivial
      · simp
      · intro x y _ _ hx hy n
        rw [add_smul]; exact add_mem (hx n) (hy n)
      · intro c r _ h n
        rw [smul_assoc]; exact K.smul_mem c (h n)
    exact this hx
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.restrictScalars_mem]
    have := Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R₀ S₀) hr)
      (Submodule.mem_top (R := S₀) (x := n))
    rwa [algebraMap_smul] at this

/-- The canonical map `M₀ ⧸ p S₀ • ⊤ → M₀_f ⧸ p • ⊤`, `R₀`-linear; it is a localization at
`powers f` by `isLocalizedModule_quotientMap`. -/
private noncomputable def quotientMap (p : Ideal R₀) (f : R₀) :
    (M₀ ⧸ (p.map (algebraMap R₀ S₀)) • (⊤ : Submodule S₀ M₀)) →ₗ[R₀]
      LocalizedModule (Submonoid.powers f) M₀ ⧸
        p • (⊤ : Submodule R₀ (LocalizedModule (Submonoid.powers f) M₀)) :=
  let L := (p • (⊤ : Submodule R₀ M₀)).localized (Submonoid.powers f)
  have hL : L.restrictScalars R₀ = p • (⊤ : Submodule R₀ (LocalizedModule (Submonoid.powers f) M₀))
    := by
    rw [Submodule.restrictScalars_localized', Submodule.localized₀_smul, Submodule.localized₀_top]
  let e1 : (M₀ ⧸ (p.map (algebraMap R₀ S₀)) • (⊤ : Submodule S₀ M₀)) ≃ₗ[R₀]
      M₀ ⧸ p • (⊤ : Submodule R₀ M₀) :=
    (Submodule.Quotient.restrictScalarsEquiv R₀ _).symm.trans
      (Submodule.quotEquivOfEq _ _ (restrictScalars_map_smul_top p))
  let e2 : (LocalizedModule (Submonoid.powers f) M₀ ⧸ L) ≃ₗ[R₀] LocalizedModule
      (Submonoid.powers f) M₀ ⧸ p • (⊤ : Submodule R₀ (LocalizedModule (Submonoid.powers f) M₀)) :=
    (Submodule.Quotient.restrictScalarsEquiv R₀ _).symm.trans (Submodule.quotEquivOfEq _ _ hL)
  e2.toLinearMap ∘ₗ (p • (⊤ : Submodule R₀ M₀)).toLocalizedQuotient (Submonoid.powers f) ∘ₗ
    e1.toLinearMap

private instance isLocalizedModule_quotientMap (p : Ideal R₀) (f : R₀) :
    IsLocalizedModule (Submonoid.powers f) (quotientMap (S₀ := S₀) (M₀ := M₀) p f) := by
  unfold quotientMap
  dsimp only
  rw [← LinearMap.comp_assoc]
  infer_instance

/-- **Flatness of the fibre after inverting one element.** Let `R₀` be Noetherian, `S₀` a finite
type `R₀`-algebra, `M₀` a finite `S₀`-module and `p` a prime of `R₀`. Then there is `f ∉ p` such
that `M₀_f ⧸ p M₀_f` is flat over `R₀ ⧸ p`.

This is generic freeness (Stacks Lemma 051R) applied to the domain `R₀ ⧸ p`, the finite type
algebra `S₀ ⧸ p S₀` and the finite module `M₀ ⧸ p M₀`. -/
private theorem exists_notMem_flat_quotient_localizedModule
    {R₀ S₀ M₀ : Type u} [CommRing R₀] [IsNoetherianRing R₀]
    [CommRing S₀] [Algebra R₀ S₀] [Algebra.FiniteType R₀ S₀]
    [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]
    [Module.Finite S₀ M₀] (p : Ideal R₀) [p.IsPrime] :
    ∃ f : R₀, f ∉ p ∧
      Module.Flat (R₀ ⧸ p)
        (LocalizedModule (Submonoid.powers f) M₀ ⧸
          p • (⊤ : Submodule R₀ (LocalizedModule (Submonoid.powers f) M₀))) := by
  set P : Ideal S₀ := p.map (algebraMap R₀ S₀)
  have : Algebra.FiniteType R₀ (S₀ ⧸ P) :=
    Algebra.FiniteType.of_surjective (A := S₀) (Ideal.Quotient.mkₐ R₀ P)
      Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (R₀ ⧸ p) (S₀ ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R₀ _ _
  let : Module (R₀ ⧸ p) (M₀ ⧸ P • (⊤ : Submodule S₀ M₀)) :=
    Module.compHom _ (algebraMap (R₀ ⧸ p) (S₀ ⧸ P))
  have : IsScalarTower (R₀ ⧸ p) (S₀ ⧸ P) (M₀ ⧸ P • (⊤ : Submodule S₀ M₀)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨g, hg0, hg⟩ := Module.exists_free_localizedModule_away_of_finiteType (R := R₀ ⧸ p)
    (S₀ ⧸ P) (M := M₀ ⧸ P • (⊤ : Submodule S₀ M₀))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hf : f ∉ p := fun h => hg0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have : IsScalarTower R₀ (R₀ ⧸ p) (M₀ ⧸ P • (⊤ : Submodule S₀ M₀)) := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      show (algebraMap (R₀ ⧸ p) (S₀ ⧸ P) (Ideal.Quotient.mk p r)) •
        (Submodule.Quotient.mk m : M₀ ⧸ P • (⊤ : Submodule S₀ M₀)) = _
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      exact congrArg Submodule.Quotient.mk (algebraMap_smul S₀ r m)
  let φ : (M₀ ⧸ P • (⊤ : Submodule S₀ M₀)) →ₗ[R₀ ⧸ p]
      LocalizedModule (Submonoid.powers f) M₀ ⧸
        p • (⊤ : Submodule R₀ (LocalizedModule (Submonoid.powers f) M₀)) :=
    (quotientMap (S₀ := S₀) p f).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have : IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk p f)) φ := by
    have : IsLocalizedModule (Submonoid.powers f) (φ.restrictScalars R₀) :=
      inferInstanceAs (IsLocalizedModule (Submonoid.powers f) (quotientMap (S₀ := S₀) p f))
    have h := IsLocalizedModule.of_restrictScalars (A := R₀ ⧸ p) (Submonoid.powers f) φ
    rwa [Algebra.algebraMapSubmonoid_powers] at h
  have : Module.Flat (Localization.Away (Ideal.Quotient.mk p f))
      (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk p f))
        (M₀ ⧸ P • (⊤ : Submodule S₀ M₀))) := Module.Flat.of_free
  have : Module.Flat (R₀ ⧸ p) (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk p f))
        (M₀ ⧸ P • (⊤ : Submodule S₀ M₀))) :=
    (Module.flat_iff_of_isLocalization (Localization.Away (Ideal.Quotient.mk p f))
      (Submonoid.powers (Ideal.Quotient.mk p f)) _).1 this
  exact ⟨f, hf, Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers (Ideal.Quotient.mk p f)) φ).symm⟩


end GenericFreeness


section Relations

variable {R₀ M₀ : Type*} [CommRing R₀] [AddCommGroup M₀] [Module R₀ M₀]

/-- The element `c ∈ p` viewed as an element of the extended ideal `p B`. -/
private def idealElt (p : Ideal R₀) (B : Type*) [CommRing B] [Algebra R₀ B] (c : R₀)
    (hc : c ∈ p) : p.map (algebraMap R₀ B) :=
  ⟨algebraMap R₀ B c, Ideal.mem_map_of_mem _ hc⟩

/-- Stage computation: a trivialisation of the relation `∑ gⱼ kⱼ = 0` in `B ⊗ M₀`
makes the corresponding element of `p B ⊗ (B ⊗ M₀)` vanish. -/
private lemma sum_idealElt_tmul_eq_zero {p : Ideal R₀} {B : Type*} [CommRing B] [Algebra R₀ B]
    {r t : ℕ} (g : Fin r → R₀) (hg : ∀ j, g j ∈ p) (k : Fin r → M₀)
    (a : Fin r → Fin t → B) (y : Fin t → B ⊗[R₀] M₀)
    (h₁ : ∀ j, (1 : B) ⊗ₜ[R₀] k j = ∑ l, a j l • y l)
    (h₂ : ∀ l, ∑ j, algebraMap R₀ B (g j) * a j l = 0) :
    ∑ j, idealElt p B (g j) (hg j) ⊗ₜ[B] ((1 : B) ⊗ₜ[R₀] k j) = 0 := by
  simp_rw [h₁, TensorProduct.tmul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have : ∀ j, idealElt p B (g j) (hg j) ⊗ₜ[B] (a j l • y l) =
      (a j l • idealElt p B (g j) (hg j)) ⊗ₜ[B] y l := fun j => by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp_rw [this]
  rw [← TensorProduct.sum_tmul]
  have h0 : ∑ j, a j l • idealElt p B (g j) (hg j) = 0 := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul, idealElt, smul_eq_mul, Submodule.coe_zero]
    rw [← h₂ l]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h0, TensorProduct.zero_tmul]

/-- Base change of an `R₀`-algebra map on `· ⊗ M₀` is semilinear over the algebra map. -/
private lemma rTensor_algHom_smul {A B : Type*} [CommRing A] [Algebra R₀ A] [CommRing B]
    [Algebra R₀ B] (φ : A →ₐ[R₀] B) (a : A) (x : A ⊗[R₀] M₀) :
    LinearMap.rTensor M₀ φ.toLinearMap (a • x) = φ a • LinearMap.rTensor M₀ φ.toLinearMap x := by
  induction x with
  | tmul b m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Pushing a trivialisation along an algebra map gives a trivialisation. -/
private lemma sum_idealElt_tmul_eq_zero_of_algHom {p : Ideal R₀} {A B : Type*} [CommRing A]
    [Algebra R₀ A] [CommRing B] [Algebra R₀ B] (φ : A →ₐ[R₀] B)
    {r t : ℕ} (g : Fin r → R₀) (hg : ∀ j, g j ∈ p) (k : Fin r → M₀)
    (a : Fin r → Fin t → A) (y : Fin t → A ⊗[R₀] M₀)
    (h₁ : ∀ j, (1 : A) ⊗ₜ[R₀] k j = ∑ l, a j l • y l)
    (h₂ : ∀ l, ∑ j, algebraMap R₀ A (g j) * a j l = 0) :
    ∑ j, idealElt p B (g j) (hg j) ⊗ₜ[B] ((1 : B) ⊗ₜ[R₀] k j) = 0 := by
  refine sum_idealElt_tmul_eq_zero g hg k (fun j l => φ (a j l))
    (fun l => LinearMap.rTensor M₀ φ.toLinearMap (y l)) (fun j => ?_) (fun l => ?_)
  · have := congrArg (LinearMap.rTensor M₀ φ.toLinearMap) (h₁ j)
    simpa [map_sum, rTensor_algHom_smul] using this
  · have := congrArg φ (h₂ l)
    simpa [map_sum] using this

section Descent

variable {R : Type*} [CommRing R] [Algebra R₀ R]

/-- A finitely generated submodule of `R` generates a finitely generated subalgebra. -/
private lemma fg_adjoin_of_submodule_fg {N : Submodule R₀ R} (hN : N.FG) :
    (Algebra.adjoin R₀ (N : Set R)).FG := by
  obtain ⟨s, rfl⟩ := hN
  rw [Algebra.adjoin_span]
  exact Subalgebra.fg_adjoin_finset s

/-- Tensor products commute with the directed union of finitely generated subalgebras:
a tensor over a finitely generated subalgebra `A₀` that dies in `R ⊗ M₀` already dies over a
finitely generated subalgebra `A ≥ A₀`. -/
private lemma exists_fg_rTensor_eq_zero {A₀ : Subalgebra R₀ R} (hA₀ : A₀.FG)
    (z : A₀ ⊗[R₀] M₀) (hz : LinearMap.rTensor M₀ A₀.val.toLinearMap z = 0) :
    ∃ (A : Subalgebra R₀ R) (h : A₀ ≤ A), A.FG ∧
      LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap z = 0 := by
  obtain ⟨J, hJ, z₁, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype z
  set f : J →ₗ[R₀] J.map A₀.val.toLinearMap := A₀.val.toLinearMap.submoduleMap J
  have h1 : LinearMap.rTensor M₀ (J.map A₀.val.toLinearMap).subtype
      (LinearMap.rTensor M₀ f z₁) = 0 := by
    rw [← LinearMap.rTensor_comp_apply]
    have : (J.map A₀.val.toLinearMap).subtype ∘ₗ f = A₀.val.toLinearMap ∘ₗ J.subtype := by
      ext x; rfl
    rw [this, LinearMap.rTensor_comp_apply]
    exact hz
  obtain ⟨N', hN', hle, h2⟩ := Submodule.FG.exists_rTensor_fg_inclusion_eq (hJ.map _)
    (x := LinearMap.rTensor M₀ f z₁) (y := 0) (by rw [h1, map_zero])
  have hsub : ∀ x : N', (x : R) ∈ A₀ ⊔ Algebra.adjoin R₀ (N' : Set R) := fun x =>
    (le_sup_right : Algebra.adjoin R₀ (N' : Set R) ≤ _) (Algebra.subset_adjoin x.2)
  let u : N' →ₗ[R₀] ↥(A₀ ⊔ Algebra.adjoin R₀ (N' : Set R)) :=
    { toFun := fun x => ⟨x, hsub x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨A₀ ⊔ Algebra.adjoin R₀ (N' : Set R), le_sup_left, hA₀.sup (fg_adjoin_of_submodule_fg hN'),
    ?_⟩
  have : (Subalgebra.inclusion (le_sup_left : A₀ ≤ A₀ ⊔ Algebra.adjoin R₀ (N' : Set R))).toLinearMap
      ∘ₗ J.subtype = u ∘ₗ (Submodule.inclusion hle) ∘ₗ f := by
    ext x; rfl
  rw [← LinearMap.rTensor_comp_apply, this, LinearMap.rTensor_comp_apply,
    LinearMap.rTensor_comp_apply]
  rw [map_zero] at h2
  rw [h2, map_zero]

private lemma rTensor_inclusion_comp {A B C : Subalgebra R₀ R} (h : A ≤ B) (h' : B ≤ C)
    (z : A ⊗[R₀] M₀) :
    LinearMap.rTensor M₀ (Subalgebra.inclusion h').toLinearMap
      (LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap z) =
    LinearMap.rTensor M₀ (Subalgebra.inclusion (h.trans h')).toLinearMap z := by
  rw [← LinearMap.rTensor_comp_apply]
  rfl

private lemma rTensor_val_inclusion {A B : Subalgebra R₀ R} (h : A ≤ B) (z : A ⊗[R₀] M₀) :
    LinearMap.rTensor M₀ B.val.toLinearMap
      (LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap z) =
    LinearMap.rTensor M₀ A.val.toLinearMap z := by
  rw [← LinearMap.rTensor_comp_apply]
  rfl

/-- Finite-family version of `exists_fg_rTensor_eq_zero`. -/
private lemma exists_fg_rTensor_eq_of_forall {ι : Type*} [Finite ι] {A₀ : Subalgebra R₀ R}
    (hA₀ : A₀.FG) (x y : ι → A₀ ⊗[R₀] M₀)
    (hxy : ∀ i, LinearMap.rTensor M₀ A₀.val.toLinearMap (x i) =
      LinearMap.rTensor M₀ A₀.val.toLinearMap (y i)) :
    ∃ (A : Subalgebra R₀ R) (h : A₀ ≤ A), A.FG ∧ ∀ i,
      LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap (x i) =
      LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap (y i) := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (A : Subalgebra R₀ R) (h : A₀ ≤ A), A.FG ∧ ∀ i ∈ s,
      LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap (x i) =
      LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap (y i) by
    obtain ⟨A, h, hA, H⟩ := H Finset.univ
    exact ⟨A, h, hA, fun i => H i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨A₀, le_rfl, hA₀, by simp⟩
  | insert a s ha ih =>
    obtain ⟨A, h, hA, H⟩ := ih
    obtain ⟨A', h', hA', hz⟩ := exists_fg_rTensor_eq_zero hA
      (LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap (x a - y a))
      (by rw [rTensor_val_inclusion, map_sub, hxy a, sub_self])
    refine ⟨A', h.trans h', hA', fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [rTensor_inclusion_comp, map_sub, sub_eq_zero] at hz
      exact hz
    · have := congrArg (LinearMap.rTensor M₀ (Subalgebra.inclusion h').toLinearMap) (H i hi)
      rwa [rTensor_inclusion_comp, rTensor_inclusion_comp] at this

/-- The relation `∑ gⱼ kⱼ = 0` is trivialised in `A ⊗ M₀`: there are `aⱼₗ ∈ A` and
`yₗ ∈ A ⊗ M₀` with `1 ⊗ kⱼ = ∑ₗ aⱼₗ yₗ` and `∑ⱼ gⱼ aⱼₗ = 0`. -/
private def Trivialises (A : Subalgebra R₀ R) {r : ℕ} (g : Fin r → R₀) (k : Fin r → M₀) : Prop :=
  ∃ (t : ℕ) (a : Fin r → Fin t → A) (y : Fin t → A ⊗[R₀] M₀),
    (∀ j, (1 : A) ⊗ₜ[R₀] k j = ∑ l, a j l • y l) ∧
      ∀ l, ∑ j, algebraMap R₀ A (g j) * a j l = 0

/-- Flatness of `R ⊗ M₀` over `R` trivialises each relation over a finitely generated
subalgebra of `R`. -/
private lemma exists_fg_trivialises [Module.Flat R (R ⊗[R₀] M₀)] {r : ℕ} (g : Fin r → R₀)
    (k : Fin r → M₀) (hk : ∑ j, g j • k j = 0) :
    ∃ A : Subalgebra R₀ R, A.FG ∧ Trivialises A g k := by
  have hrel : ∑ j, algebraMap R₀ R (g j) • ((1 : R) ⊗ₜ[R₀] k j) = 0 := by
    have : ∀ j, algebraMap R₀ R (g j) • ((1 : R) ⊗ₜ[R₀] k j) = (1 : R) ⊗ₜ[R₀] (g j • k j) :=
      fun j => by
        rw [algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    simp_rw [this, ← TensorProduct.tmul_sum, hk, TensorProduct.tmul_zero]
  obtain ⟨t, a, y, h₁, h₂⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨J, hJ, hy⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype (R := R₀)
    (M := M₀) (Set.range y) (Set.finite_range y)
  choose y₁ hy₁ using fun l => hy (Set.mem_range_self l)
  set S : Subalgebra R₀ R := Algebra.adjoin R₀ (J : Set R) ⊔
    Algebra.adjoin R₀ (Set.range fun p : Fin r × Fin t => a p.1 p.2)
  have hSfg : S.FG := (fg_adjoin_of_submodule_fg hJ).sup
    (Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)
  have hJS : ∀ x : J, (x : R) ∈ S := fun x =>
    (le_sup_left : Algebra.adjoin R₀ (J : Set R) ≤ S) (Algebra.subset_adjoin x.2)
  have haS : ∀ j l, a j l ∈ S := fun j l =>
    (le_sup_right : Algebra.adjoin R₀ (Set.range fun p : Fin r × Fin t => a p.1 p.2) ≤ S)
      (Algebra.subset_adjoin ⟨(j, l), rfl⟩)
  let ν : J →ₗ[R₀] S :=
    { toFun := fun x => ⟨x, hJS x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let a₀ : Fin r → Fin t → S := fun j l => ⟨a j l, haS j l⟩
  let y₀ : Fin t → S ⊗[R₀] M₀ := fun l => LinearMap.rTensor M₀ ν (y₁ l)
  have hy₀ : ∀ l, LinearMap.rTensor M₀ S.val.toLinearMap (y₀ l) = y l := fun l => by
    have : S.val.toLinearMap ∘ₗ ν = J.subtype := by ext x; rfl
    rw [← LinearMap.rTensor_comp_apply, this, hy₁]
  obtain ⟨A, h, hA, H⟩ := exists_fg_rTensor_eq_of_forall hSfg
    (fun j => (1 : S) ⊗ₜ[R₀] k j) (fun j => ∑ l, a₀ j l • y₀ l) (fun j => by
      have e1 : LinearMap.rTensor M₀ S.val.toLinearMap ((1 : S) ⊗ₜ[R₀] k j) =
          (1 : R) ⊗ₜ[R₀] k j := by simp
      rw [e1]
      refine (h₁ j).trans ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [rTensor_algHom_smul S.val, hy₀]; rfl)
  refine ⟨A, hA, t, fun j l => Subalgebra.inclusion h (a₀ j l),
    fun l => LinearMap.rTensor M₀ (Subalgebra.inclusion h).toLinearMap (y₀ l), fun j => ?_,
    fun l => ?_⟩
  · have := H j
    simpa [map_sum, rTensor_algHom_smul (Subalgebra.inclusion h)] using this
  · refine Subtype.ext ?_
    have := h₂ l
    simpa using this

end Descent

section Reduction

variable {S₀ : Type*} [CommRing S₀] [Algebra R₀ S₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]
  {B : Type*} [CommRing B] [Algebra R₀ B]

/-- The tensor `∑ gⱼ ⊗ (1 ⊗ kⱼ)` is stable under scaling `k` by `S₀`. -/
private lemma sum_idealElt_tmul_smul_eq_zero {p : Ideal R₀} {r : ℕ} (g : Fin r → R₀)
    (hg : ∀ j, g j ∈ p) (s : S₀) (k : Fin r → M₀)
    (h : ∑ j, idealElt p B (g j) (hg j) ⊗ₜ[B] ((1 : B) ⊗ₜ[R₀] k j) = 0) :
    ∑ j, idealElt p B (g j) (hg j) ⊗ₜ[B] ((1 : B) ⊗ₜ[R₀] (s • k j)) = 0 := by
  have := congrArg (LinearMap.lTensor (p.map (algebraMap R₀ B))
    (TensorProduct.AlgebraTensorModule.lTensor B B
      ((LinearMap.lsmul S₀ M₀ s).restrictScalars R₀))) h
  simpa [map_sum] using this

/-- Moving the `R₀`-coefficients of a decomposition across the tensor product. -/
private lemma sum_idealElt_tmul_eq_sum_of_decomp {p : Ideal R₀} {r n : ℕ} (g : Fin r → R₀)
    (hg : ∀ j, g j ∈ p) (x : Fin n → R₀) (hx : ∀ i, x i ∈ p) (c : Fin n → Fin r → R₀)
    (hxc : ∀ i, ∑ j, c i j • g j = x i) (m : Fin n → M₀) :
    ∑ i, idealElt p B (x i) (hx i) ⊗ₜ[B] ((1 : B) ⊗ₜ[R₀] m i) =
      ∑ j, idealElt p B (g j) (hg j) ⊗ₜ[B] ((1 : B) ⊗ₜ[R₀] (∑ i, c i j • m i)) := by
  have h1 : ∀ i, idealElt p B (x i) (hx i) =
      ∑ j, algebraMap R₀ B (c i j) • idealElt p B (g j) (hg j) := fun i => by
    refine Subtype.ext ?_
    simp only [idealElt, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
    rw [← hxc i]
    simp [map_sum]
  have h2 : ∀ (i : Fin n) (j : Fin r), (1 : B) ⊗ₜ[R₀] (c i j • m i) =
      algebraMap R₀ B (c i j) • ((1 : B) ⊗ₜ[R₀] m i) := fun i j => by
    rw [algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
  simp_rw [TensorProduct.tmul_sum, h2, TensorProduct.tmul_smul, TensorProduct.smul_tmul', h1,
    TensorProduct.sum_tmul]
  exact Finset.sum_comm

end Reduction

end Relations

private lemma fg_finset_sup {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] {ι : Type*}
    (s : Finset ι) (A : ι → Subalgebra R₀ R) (hA : ∀ i, (A i).FG) : (s.sup A).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Subalgebra.fg_bot
  | insert a s _ ih => rw [Finset.sup_insert]; exact (hA a).sup ih

/-- **Relations in `M₀` with coefficients in `p` die over a large finitely generated
subalgebra.** Let `R₀` be Noetherian, `M₀` a finite module over a finite-type `R₀`-algebra `S₀`
and `R` an `R₀`-algebra such that `R ⊗[R₀] M₀` is flat over `R`.  Then there is a finitely
generated `R₀`-subalgebra `R₁` of `R` such that for every subalgebra `R₂ ≥ R₁` (finitely generated
or not) every relation `∑ xᵢ mᵢ = 0` in `M₀` with `xᵢ ∈ p` becomes trivial in
`(p R₂) ⊗[R₂] (R₂ ⊗[R₀] M₀)`.  See Stacks 02JO and EGA IV 11.2.6.1. -/
private theorem exists_fg_subalgebra_tor_vanishes
    {R₀ S₀ M₀ R : Type u} [CommRing R₀] [IsNoetherianRing R₀]
    [CommRing S₀] [Algebra R₀ S₀] [Algebra.FiniteType R₀ S₀]
    [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]
    [Module.Finite S₀ M₀] [CommRing R] [Algebra R₀ R]
    (h : Module.Flat R (R ⊗[R₀] M₀)) (p : Ideal R₀) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ ∀ R₂ : Subalgebra R₀ R, R₁ ≤ R₂ →
      ∀ (n : ℕ) (x : Fin n → p) (m : Fin n → M₀), ∑ i, (x i : R₀) • m i = 0 →
        ∑ i, (⟨algebraMap R₀ R₂ (x i), Ideal.mem_map_of_mem _ (x i).2⟩ :
            p.map (algebraMap R₀ R₂)) ⊗ₜ[R₂] ((1 : R₂) ⊗ₜ[R₀] m i) = 0 := by
  classical
  have := h
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  -- generators of `p`
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian p)
  have hgp : ∀ j, g j ∈ p := fun j => hg ▸ Submodule.subset_span ⟨j, rfl⟩
  -- the kernel of `(mⱼ) ↦ ∑ gⱼ mⱼ`
  let φ : (Fin r → M₀) →ₗ[S₀] M₀ :=
    ∑ j, algebraMap R₀ S₀ (g j) • (LinearMap.proj j : (Fin r → M₀) →ₗ[S₀] M₀)
  have hφ : ∀ k, φ k = ∑ j, g j • k j := fun k => by
    simp [φ, algebraMap_smul]
  obtain ⟨T, hT⟩ : (LinearMap.ker φ).FG := IsNoetherian.noetherian _
  have hTK : ∀ k ∈ T, ∑ j, g j • k j = 0 := fun k hk => by
    have : k ∈ LinearMap.ker φ := hT ▸ Submodule.subset_span hk
    rwa [LinearMap.mem_ker, hφ] at this
  choose A hAfg hAtriv using fun k : T => exists_fg_trivialises (R := R) g k.1 (hTK k.1 k.2)
  refine ⟨Finset.univ.sup A, fg_finset_sup _ _ hAfg, fun R₂ hR₂ n x m hxm => ?_⟩
  -- vanishing for the generators, hence for all of the kernel
  have hgen : ∀ k : T, ∑ j, idealElt p R₂ (g j) (hgp j) ⊗ₜ[R₂] ((1 : R₂) ⊗ₜ[R₀] k.1 j) = 0 := by
    intro k
    obtain ⟨t, a, y, h₁, h₂⟩ := hAtriv k
    exact sum_idealElt_tmul_eq_zero_of_algHom (Subalgebra.inclusion
      ((Finset.le_sup (Finset.mem_univ k)).trans hR₂)) g hgp k.1 a y h₁ h₂
  have hker : ∀ k ∈ LinearMap.ker φ,
      ∑ j, idealElt p R₂ (g j) (hgp j) ⊗ₜ[R₂] ((1 : R₂) ⊗ₜ[R₀] k j) = 0 := by
    intro k hk
    rw [← hT] at hk
    induction hk using Submodule.span_induction with
    | mem k hk => exact hgen ⟨k, hk⟩
    | zero => simp
    | add k k' _ _ hk hk' =>
      simp only [Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib, hk, hk',
        add_zero]
    | smul s k _ hk => exact sum_idealElt_tmul_smul_eq_zero g hgp s k hk
  -- reduction of the given relation to the generators
  have hc : ∀ i, ∃ c : Fin r → R₀, ∑ j, c j • g j = (x i : R₀) := fun i => by
    have : (x i : R₀) ∈ Submodule.span R₀ (Set.range g) := by rw [hg]; exact (x i).2
    exact (Submodule.mem_span_range_iff_exists_fun R₀).mp this
  choose c hxc using hc
  refine (sum_idealElt_tmul_eq_sum_of_decomp g hgp (fun i => (x i : R₀)) (fun i => (x i).2) c
    hxc m).trans (hker _ ?_)
  rw [LinearMap.mem_ker, hφ]
  calc ∑ j, g j • ∑ i, c i j • m i = ∑ i, (∑ j, c i j • g j) • m i := by
        simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [mul_comm, smul_eq_mul]
    _ = ∑ i, (x i : R₀) • m i := by simp_rw [hxc]
    _ = 0 := hxm











section Localizations

variable {A S N : Type u} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup N] [Module A N]
  [Module S N] [IsScalarTower A S N]

/-- An `S`-module is flat over `A` when all its localizations at primes of `S` are. -/
private theorem flat_of_flat_localizations
    (H : ∀ (P : Ideal S) [P.IsPrime] (Mq : Type u) [AddCommGroup Mq] [Module S Mq] [Module A Mq]
      [IsScalarTower A S Mq] (g : N →ₗ[S] Mq) [IsLocalizedModule P.primeCompl g],
      Module.Flat A Mq) : Module.Flat A N :=
  Module.flat_of_isLocalized_maximal (R := A) (S := S) N
    (fun P _ => LocalizedModule P.primeCompl N)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl N)
    (fun P _ => H P (LocalizedModule P.primeCompl N) (LocalizedModule.mkLinearMap P.primeCompl N))

end Localizations

section Induction

variable {R₀ S₀ M₀ R : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
  [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]
  [CommRing R] [Algebra R₀ R]

attribute [local instance] stageModule

variable (R₀ S₀ M₀) in
/-- Every localization of `A ⊗ M₀` at a prime of `A ⊗ S₀` lying over `V(I)` is flat over `A`. -/
private def FlatOver (I : Ideal R₀) (A : Type u) [CommRing A] [Algebra R₀ A] : Prop :=
  ∀ (q : Ideal (A ⊗[R₀] S₀)) [q.IsPrime], I ≤ q.comap (algebraMap R₀ (A ⊗[R₀] S₀)) →
    ∀ (Mq : Type u) [AddCommGroup Mq] [Module (A ⊗[R₀] S₀) Mq] [Module A Mq]
      [IsScalarTower A (A ⊗[R₀] S₀) Mq] (g : A ⊗[R₀] M₀ →ₗ[A ⊗[R₀] S₀] Mq)
      [IsLocalizedModule q.primeCompl g], Module.Flat A Mq

variable (R₀ S₀ M₀ R) in
/-- Flatness over `V(I)` is reached on every larger finitely generated subalgebra from some
finitely generated subalgebra on. -/
private def ReachedOver (I : Ideal R₀) : Prop :=
  ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ ∀ R₂ : Subalgebra R₀ R, R₁ ≤ R₂ → R₂.FG →
    FlatOver R₀ S₀ M₀ I R₂

private theorem reachedOver_all [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀]
    [Module.Finite S₀ M₀] (h : Module.Flat R (R ⊗[R₀] M₀)) (I : Ideal R₀) :
    ReachedOver R₀ S₀ M₀ R I := by
  classical
  refine IsNoetherian.induction (P := fun I : Ideal R₀ => ReachedOver R₀ S₀ M₀ R I)
    (fun (I : Ideal R₀) IH => ?_) I
  by_cases hprime : I.IsPrime
  · -- generic freeness gives `f ∉ I` and the local criterion handles `D(f)`
    obtain ⟨f, hfI, hJ⟩ := exists_notMem_flat_quotient_localizedModule (S₀ := S₀) (M₀ := M₀) I
    have hlt : I < I ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun e =>
      hfI ((Ideal.span_singleton_le_iff_mem _).1 (sup_eq_left.1 e.symm))
    obtain ⟨R₁, hR₁, H₁⟩ := IH _ hlt
    obtain ⟨R₃, hR₃, H₃⟩ := exists_fg_subalgebra_tor_vanishes (S₀ := S₀) h I
    refine ⟨R₁ ⊔ R₃, hR₁.sup hR₃, fun R₂ hR₂ hR₂fg q _ hq Mq _ _ _ _ g _ => ?_⟩
    by_cases hfq : f ∈ q.comap (algebraMap R₀ (R₂ ⊗[R₀] S₀))
    · exact H₁ R₂ (le_sup_left.trans hR₂) hR₂fg q
        (sup_le hq ((Ideal.span_singleton_le_iff_mem _).2 hfq)) Mq g
    · have : IsNoetherianRing R₂ := isNoetherianRing_of_fg hR₂fg
      refine flat_of_tor₁_vanishes_of_notMem (A := R₀) (A' := R₂) (S' := R₂ ⊗[R₀] S₀)
        (N := R₂ ⊗[R₀] M₀) (M₀ := M₀) (TensorProduct.mk R₀ R₂ M₀ 1)
        (TensorProduct.isBaseChange R₀ M₀ R₂) I f hJ
        (fun n x m hx => H₃ R₂ (le_sup_right.trans hR₂) n x m hx) q ?_ ?_ Mq g
      · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
        exact Ideal.map_le_iff_le_comap.2 hq
      · rw [← IsScalarTower.algebraMap_apply]
        exact hfq
  · obtain hI | ⟨a, ha, b, hb, hab⟩ := Ideal.not_isPrime_iff.1 hprime
    · subst hI
      refine ⟨⊥, Subalgebra.fg_bot, fun R₂ _ _ q _ hq => ?_⟩
      have h1 : (1 : R₀) ∈ q.comap (algebraMap R₀ (R₂ ⊗[R₀] S₀)) := hq Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1
      exact absurd ((Ideal.eq_top_iff_one q).2 h1) ‹q.IsPrime›.ne_top
    · have hlta : I < I ⊔ Ideal.span {a} := lt_of_le_of_ne le_sup_left fun e =>
        ha ((Ideal.span_singleton_le_iff_mem _).1 (sup_eq_left.1 e.symm))
      have hltb : I < I ⊔ Ideal.span {b} := lt_of_le_of_ne le_sup_left fun e =>
        hb ((Ideal.span_singleton_le_iff_mem _).1 (sup_eq_left.1 e.symm))
      obtain ⟨R₁, hR₁, H₁⟩ := IH _ hlta
      obtain ⟨R₃, hR₃, H₃⟩ := IH _ hltb
      refine ⟨R₁ ⊔ R₃, hR₁.sup hR₃, fun R₂ hR₂ hR₂fg q _ hq Mq _ _ _ _ g _ => ?_⟩
      have hab' : algebraMap R₀ (R₂ ⊗[R₀] S₀) a * algebraMap R₀ (R₂ ⊗[R₀] S₀) b ∈ q := by
        rw [← map_mul]; exact hq hab
      rcases ‹q.IsPrime›.mem_or_mem hab' with h1 | h1
      · exact H₁ R₂ (le_sup_left.trans hR₂) hR₂fg q
          (sup_le hq ((Ideal.span_singleton_le_iff_mem _).2 h1)) Mq g
      · exact H₃ R₂ (le_sup_right.trans hR₂) hR₂fg q
          (sup_le hq ((Ideal.span_singleton_le_iff_mem _).2 h1)) Mq g

/-- **Flatness is reached on a finitely generated subalgebra** (EGA IV₃, Corollaire 11.2.6.1 (ii)
and Corollaire 11.2.7 a) ⇒ c); Stacks, Lemma 02JO (1) relative to a Noetherian base).

Let `R₀` be a Noetherian ring, `S₀` a finite type `R₀`-algebra, `M₀` a finite `S₀`-module and
`R` an `R₀`-algebra such that `R ⊗[R₀] M₀` is flat over `R`. Then `R₁ ⊗[R₀] M₀` is flat over `R₁`
for some finitely generated `R₀`-subalgebra `R₁` of `R`.

The proof is a Noetherian induction on the ideals of `R₀`, using generic freeness and the local
criterion for flatness; it does not use the openness of the flat locus. For an ideal `I`, one
shows that flatness at all primes of `R₁ ⊗ S₀` over `V(I)` holds on every large enough finitely
generated subalgebra. For a prime `p`, generic freeness gives `f ∉ p` with `M₀_f ⧸ p M₀_f` flat
over `R₀ ⧸ p`, the local criterion (flatness at a later stage) covers the primes over `D(f)`
once the relations of `M₀` with coefficients in `p` have become trivial, and the induction
hypothesis for `p + (f)` covers the rest.

Both finiteness hypotheses are load-bearing. Let `k = ℚ`, `R₀ = k[t]` and `R = k(t)`; a finitely
generated `R₁ ⊆ k(t)` lies in `k[t][1/h]` for some `h ≠ 0`, and for each `a ∈ k` with `h(a) ≠ 0`
the element `t - a` is not a unit of `R₁`, so `R₁ ⧸ (t - a) ≠ 0` is torsion over `R₁`.
* `Module.Finite S₀ M₀` cannot be dropped: take `S₀ = R₀` and `M₀ = ⊕ₐ k[t] ⧸ (t - a)`. Then
  `R ⊗ M₀ = 0` is flat, but `R₁ ⊗ M₀` has a nonzero torsion summand for every `R₁`.
* `Algebra.FiniteType R₀ S₀` cannot be dropped: take
  `S₀ = M₀ = k[t][xₐ : a ∈ k] ⧸ (xₐ (t - a), xₐ x_b)`, which is `k[t] ⊕ ⊕ₐ k[t] ⧸ (t - a)` as a
  `k[t]`-module, and argue as before. The field `k` must be infinite here.

`IsNoetherianRing R₀` is used by this proof, through finite generation of the ideals of `R₀` and
of the kernels of relations, and through Noetherian stages for the local criterion. -/
theorem exists_fg_subalgebra_flat_of_isNoetherianRing
    {R₀ S₀ M₀ R : Type u} [CommRing R₀] [IsNoetherianRing R₀]
    [CommRing S₀] [Algebra R₀ S₀] [Algebra.FiniteType R₀ S₀]
    [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]
    [Module.Finite S₀ M₀] [CommRing R] [Algebra R₀ R]
    (h : Module.Flat R (R ⊗[R₀] M₀)) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ Module.Flat R₁ (R₁ ⊗[R₀] M₀) := by
  obtain ⟨R₁, hfg, H⟩ := reachedOver_all (S₀ := S₀) h ⊥
  refine ⟨R₁, hfg, ?_⟩
  have hflat := H R₁ le_rfl hfg
  exact flat_of_flat_localizations fun P _ Mq _ _ _ _ g _ => hflat P bot_le Mq g

end Induction

end Module.Flat
