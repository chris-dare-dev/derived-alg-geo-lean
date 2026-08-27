/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Clearing a denominator against a radical membership

`Submodule.exists_pow_smul_mem_of_isLocalized_radical` is the commutative-algebra step behind
"a section over a basic open extends after multiplying by a power of the defining element".
If an element lands in a submodule after localizing at every member of a family `s`, then some
power of any element of `(span s).radical` carries it into the submodule on the nose.

The proof is a single observation: the set of ring elements carrying `m` into `N` is the ideal
`N.comap (toSpanSingleton R M m)`, localizing at `r` says exactly that some power of `r` lies in
that ideal, and radical membership then transports the conclusion from `span s` to `d`.

## Provenance

This statement was proved as a `private` lemma inside the Čech affine-vanishing file, where it
was needed once. It is stated here instead because it is pure commutative algebra with no Čech
content, and because the projective-space section-extension argument (#585) was expected to need it
without wanting the cohomology stack it was buried in. Nothing about the proof changed in the move.

That expectation did not hold: `#585` closed without using this lemma at all — the overlap step it
was meant for is settled by separatedness on the degree-two chart of `gᵢ gⱼ` instead. The Čech
affine-vanishing argument remains its live consumer, and the statement is still worth having on its
own terms.

It is not in Mathlib at the current pin under this or any neighbouring name, and it is
`upstream-candidate` material.

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
