/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Clearing a denominator against a radical membership

`Submodule.exists_pow_smul_mem_of_isLocalized_radical` is the commutative-algebra step behind
"a section over a basic open extends after multiplying by a power of the defining element".
If an element is in a submodule after localizing at every member of a family `s`, then some
power of any element of `(span s).radical` carries it into the submodule on the nose.

## Main definitions

This file introduces no new definitions.

## Main results

* `Submodule.exists_pow_smul_mem_of_isLocalized_radical` — if `m` is in `N` after localizing
  away from every element of `s`, then `d ^ n • m ∈ N` for some `n`, for every `d` in the
  radical of `Ideal.span s`.

## Implementation notes

The proof is a single observation: the set of ring elements carrying `m` into `N` is the ideal
`N.comap (toSpanSingleton R M m)`, localizing at `r` says exactly that some power of `r` lies in
that ideal, and radical membership then transports the conclusion from `span s` to `d`.

The statement is pure commutative algebra with no Čech content, so it is stated here rather than
beside its consumer, the Čech affine-vanishing argument. It is not in Mathlib at the current pin
under this or any neighbouring name, and is a candidate for upstreaming.

## References

Mathlib's `IsLocalizedModule.Away`, `Submodule.localized₀` and `Ideal.radical`.

## Tags

localization, radical, submodule, denominator clearing
-/

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- If an element lands in a submodule after localization at every element of `s`, then a power
of every element of `(span s).radical` carries it into the submodule.

The family `s` is the one a basic-open cover produces, and `d` is the element whose basic open is
being covered; radical membership is what "the cover is a cover" supplies. -/
theorem exists_pow_smul_mem_of_isLocalized_radical
    (s : Set R) {d : R} (hd : d ∈ (Ideal.span s).radical)
    (Mₚ : ∀ _ : s, Type*) [∀ r : s, AddCommMonoid (Mₚ r)]
    [∀ r : s, Module R (Mₚ r)] (f : ∀ r : s, M →ₗ[R] Mₚ r)
    [∀ r : s, IsLocalizedModule.Away r.1 (f r)]
    {m : M} {N : Submodule R M}
    (h : ∀ r : s, f r m ∈ N.localized₀ (.powers r.1) (f r)) :
    ∃ n : ℕ, d ^ n • m ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  have hrs : Ideal.span s ≤ I.radical := by
    apply Ideal.span_le.2
    intro r hr
    let r' : s := ⟨r, hr⟩
    obtain ⟨a, ha, t, e⟩ := h r'
    rw [← IsLocalizedModule.mk'_one (.powers r'.1),
      IsLocalizedModule.mk'_eq_mk'_iff] at e
    obtain ⟨u, hu⟩ := e
    simp_rw [smul_smul] at hu
    obtain ⟨k, hk⟩ := (u * t).2
    refine ⟨k, ?_⟩
    change r'.1 ^ k • m ∈ N
    have hpow : r'.1 ^ k = (u * t : Submonoid.powers r'.1).1 := by
      simpa only using hk
    rw [hpow]
    exact hu ▸ N.smul_mem (u * 1 : Submonoid.powers r'.1).1 ha
  have hdI : d ∈ I.radical :=
    (I.radical_isRadical.radical_le_iff.2 hrs) hd
  obtain ⟨n, hn⟩ := hdI
  exact ⟨n, hn⟩

end Submodule
