/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Clearing a denominator on an affine

A section of a quasi-coherent sheaf over a basic open `D(r)`, multiplied by a high enough power of
`r`, is the restriction of a **global** section. This is the chart-local engine of `#585`: on
`Proj 𝒜` a degree-one chart is `Spec (A_{(g)})`, `D₊(f)` meets it in the basic open of `f / g`
(`Proj.awayι_preimage_basicOpen`), and this is what clears that denominator.

## Why it is six lines, and what that changes

Not by an argument but by an instance. Mathlib carries

    instance (f : R) : IsLocalizedModule.Away f (tilde.toOpen M (basicOpen f)).hom

so `Γ(D(r), M~)` **is** the localization `M_r`, and clearing the denominator is
`IsLocalizedModule.surj`: a section is `m / rⁿ` by the definition of the localization rather than
by a theorem about it. The passage from "comes from `M`" to "restricts from a *global* section" is
then `tilde.toOpen_res`, which is `rfl`.

Worth recording against the plan `#585` was written to.
`Submodule.exists_pow_smul_mem_of_isLocalized_radical` — extracted into
`Algebra/Module/LocalizedRadical.lean` for this very issue — is **not** needed here. It stays the
tool for reconciling two charts on their overlap, where the denominators come from a cover and
radical membership is what makes the cover a cover. The chart-local step never reaches for it.

## Both halves, and dropping the tilde hypothesis

Extension makes a local section global; `exists_pow_smul_res_eq_zero` is its injectivity
companion — a global section restricting to `0` on `D(r)` is killed by a power of `r` — and the two
together are what a gluing argument over a cover needs. The second rests on Mathlib's
`isIso_toOpen_top`, so every section over `⊤` is `toOpen M ⊤ m` and the elementwise statement
applies directly.

Both are stated for a tilde, and `#585` needs them for an arbitrary quasi-coherent sheaf. The
transport is the same both times, so it is done **once**, as a linear equivalence on sections
(`tildeΓSectionEquiv`) with its two restriction laws, rather than twice by hand.

That is not a stylistic preference; the by-hand version does not scale, and the second attempt at
it did not go through at all. Two hazards, both worth knowing before writing in this file:

* **`rw` does not see proof irrelevance.** Transporting the injectivity statement by rewriting
  fails on patterns that print *character-identical* to the goal: the difference is inside the
  elided `⋯`, where two elaborations of `le_top` give different proof terms. `simp only` does not
  match either. What works is abandoning rewriting — `congrArg … |>.trans`, since `exact` unifies
  up to defeq and proof irrelevance is definitional. Naming the transport as a `LinearEquiv`
  confines this to one place.
* **`_root_` shadowing.** Inside `AlgebraicGeometry.tilde` and `AlgebraicGeometry.Scheme.Modules`,
  the bare names `map_smul` and `map_zero` resolve to *other* lemmas — about `presheaf.map` and
  about `tilde.map`. Both must be written `_root_.map_smul` / `_root_.map_zero`. This cost four
  cycles across the file. Same class of hazard as `references/instance-transparency.md`: a name
  that silently resolves to the wrong thing.

## Scope

One affine, one basic open. The `Proj` chart application, the choice of one `n` across a finite
cover, and the passage from `(f / g)ⁿ ·` to multiplication into the twist `F(n)` are not here, so
`#585` is not closed.
-/

universe u

open CategoryTheory Opposite TopologicalSpace PrimeSpectrum

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- **A section of `M~` over a basic open extends after clearing one power of the defining
element.** -/
theorem exists_pow_smul_eq_toOpen (r : R)
    (s : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen r))) :
    ∃ (n : ℕ) (m : M), r ^ n • s = toOpen M (basicOpen r) m := by
  obtain ⟨⟨m, t⟩, ht⟩ :=
    IsLocalizedModule.surj (Submonoid.powers r) (toOpen M (basicOpen r)).hom s
  obtain ⟨n, hn⟩ := t.2
  exact ⟨n, m, by rw [show r ^ n = (t : R) from hn]; exact ht⟩

/-- **The same, as an extension statement**: a power of `r` times a section over `D(r)` is the
restriction of a *global* section. -/
theorem exists_pow_smul_eq_res_of_top (r : R)
    (s : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen r))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE le_top).op t = r ^ n • s := by
  obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_toOpen M r s
  refine ⟨n, toOpen M ⊤ m, ?_⟩
  rw [hm]
  rfl

/-- **A global section vanishing on `D(r)` is killed by a power of `r`.**

The injectivity companion of `exists_pow_smul_eq_toOpen`, and the other half of what a gluing
argument needs: extension makes local sections global, this makes two of them agree. -/
theorem exists_pow_smul_eq_zero (r : R) (m : M)
    (h : toOpen M (basicOpen r) m = 0) :
    ∃ n : ℕ, r ^ n • m = 0 := by
  obtain ⟨t, ht⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers r)
      (toOpen M (basicOpen r)).hom).mp h
  obtain ⟨n, hn⟩ := t.2
  exact ⟨n, by rw [show r ^ n = (t : R) from hn]; exact ht⟩

/-- **The same on sections**: a global section restricting to `0` on `D(r)` is killed by a power
of `r`. -/
theorem exists_pow_smul_res_eq_zero (r : R)
    (t : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤))
    (h : (modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE (le_top (a := basicOpen r))).op t = 0) :
    ∃ n : ℕ, r ^ n • t = 0 := by
  obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso (toOpen M ⊤)).2 t
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero M r m h
  refine ⟨n, ?_⟩
  rw [← _root_.map_smul, hn, _root_.map_zero]

end AlgebraicGeometry.tilde

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-! ### Transporting across quasi-coherence

Both statements above are about a tilde, and `#585` needs them for an arbitrary quasi-coherent
sheaf. The transport is the same both times, so it is done once here as a **linear equivalence on
sections** rather than twice by hand as natural-transformation rewriting.

That is not a stylistic preference. Written inline, the transport is three `rw`s against a natural
transformation, and they refuse to fire on patterns that *print identically* to the goal — the
`le_top` proofs inside `homOfLE ⋯` differ, and `rw` matches syntactically. Named as a
`LinearEquiv`, the same steps are `map_smul` and `map_zero` from the `LinearEquiv` API, which
carry no such hazard. -/

/-- **The quasi-coherence isomorphism on the sections over one open**, as a linear equivalence. -/
noncomputable def tildeΓSectionEquiv (N : (Spec R).Modules) [IsIso (fromTildeΓ N)]
    (U : (Spec R).Opens) :
    (modulesSpecToSheaf.obj
        (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)))).presheaf.obj (op U) ≃ₗ[R]
      (modulesSpecToSheaf.obj N).presheaf.obj (op U) :=
  (((modulesSpecToSheaf ⋙ TopCat.Sheaf.forget (ModuleCat R) (Spec R)).mapIso
    (asIso (fromTildeΓ N))).app (op U)).toLinearEquiv

/-- **The equivalence commutes with restriction.** The one fact the transports need, proved once
where the spelling is under this file's control. -/
@[simp]
theorem tildeΓSectionEquiv_res (N : (Spec R).Modules) [IsIso (fromTildeΓ N)]
    {U V : (Spec R).Opens} (i : V ⟶ U)
    (x : (modulesSpecToSheaf.obj
      (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)))).presheaf.obj (op U)) :
    tildeΓSectionEquiv N V
        ((modulesSpecToSheaf.obj
          (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)))).presheaf.map i.op x) =
      (modulesSpecToSheaf.obj N).presheaf.map i.op (tildeΓSectionEquiv N U x) :=
  NatTrans.naturality_apply
    ((modulesSpecToSheaf ⋙ TopCat.Sheaf.forget (ModuleCat R) (Spec R)).mapIso
      (asIso (fromTildeΓ N))).hom i.op x

/-- **The inverse equivalence commutes with restriction**, which is the direction the injectivity
transport needs. -/
theorem tildeΓSectionEquiv_symm_res (N : (Spec R).Modules) [IsIso (fromTildeΓ N)]
    {U V : (Spec R).Opens} (i : V ⟶ U)
    (x : (modulesSpecToSheaf.obj N).presheaf.obj (op U)) :
    (tildeΓSectionEquiv N V).symm ((modulesSpecToSheaf.obj N).presheaf.map i.op x) =
      (modulesSpecToSheaf.obj
          (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)))).presheaf.map i.op
        ((tildeΓSectionEquiv N U).symm x) := by
  apply (tildeΓSectionEquiv N V).injective
  rw [LinearEquiv.apply_symm_apply, tildeΓSectionEquiv_res, LinearEquiv.apply_symm_apply]

/-- **The affine extension lemma for any quasi-coherent module sheaf**, not only a tilde. -/
theorem exists_pow_smul_eq_res_of_top_of_isQuasicoherent (N : (Spec R).Modules)
    [IsIso (fromTildeΓ N)] (r : R)
    (s : (modulesSpecToSheaf.obj N).presheaf.obj (op (PrimeSpectrum.basicOpen r))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj N).presheaf.map (homOfLE le_top).op t = r ^ n • s := by
  obtain ⟨n, t', ht'⟩ :=
    AlgebraicGeometry.tilde.exists_pow_smul_eq_res_of_top _ r
      ((tildeΓSectionEquiv N (PrimeSpectrum.basicOpen r)).symm s)
  refine ⟨n, tildeΓSectionEquiv N ⊤ t', ?_⟩
  rw [← tildeΓSectionEquiv_res N (homOfLE le_top) t', ht', _root_.map_smul,
    LinearEquiv.apply_symm_apply]

/-- **The injectivity companion for any quasi-coherent module sheaf.** -/
theorem exists_pow_smul_res_eq_zero_of_isQuasicoherent (N : (Spec R).Modules)
    [IsIso (fromTildeΓ N)] (r : R)
    (t : (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤))
    (h : (modulesSpecToSheaf.obj N).presheaf.map
      (homOfLE (le_top (a := PrimeSpectrum.basicOpen r))).op t = 0) :
    ∃ n : ℕ, r ^ n • t = 0 := by
  obtain ⟨n, hn⟩ :=
    AlgebraicGeometry.tilde.exists_pow_smul_res_eq_zero _ r ((tildeΓSectionEquiv N ⊤).symm t) (by
      have hnat := tildeΓSectionEquiv_symm_res N
        (homOfLE (le_top (a := PrimeSpectrum.basicOpen r))) t
      have h' : (modulesSpecToSheaf.obj N).presheaf.map
          (homOfLE (le_top (a := PrimeSpectrum.basicOpen r))).op t = 0 := h
      exact hnat.symm.trans
        ((congrArg (⇑(tildeΓSectionEquiv N (PrimeSpectrum.basicOpen r)).symm) h').trans
          (_root_.map_zero _)))
  refine ⟨n, ?_⟩
  have h2 := congrArg (⇑(tildeΓSectionEquiv N ⊤)) hn
  rwa [_root_.map_smul, LinearEquiv.apply_symm_apply, _root_.map_zero] at h2

end AlgebraicGeometry.Scheme.Modules
