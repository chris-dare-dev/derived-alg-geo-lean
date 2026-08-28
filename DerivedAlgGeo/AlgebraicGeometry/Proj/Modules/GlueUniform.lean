/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.Glue

/-!
# One twist exponent for a whole finite family of sections

`exists_globalSection_twistBy` produces **an** exponent `N`, one per section. Serre's global
generation needs a **single** `N` serving every generator of every chart at once, because the
surjection it builds, `free I ⟶ F(N)`, has one target sheaf.

This file supplies that: `exists_globalSection_twistBy_forall_ge` upgrades the existential to
"every sufficiently large `N` works", and `exists_globalSection_twistBy_uniform` takes the maximum
over a finite family.

## Where the raising happens, and why not at the sheaf level

The obvious way to raise a global section of `F(N)` to one of `F(N')` is to multiply by
`f ^ (N' - N)` and then transport along `F(N)(N' - N) ≅ F(N')`. That isomorphism **does not exist
for an arbitrary `F`**, and `TensorTwist.lean`'s "What is not here, and why it cannot be got the
easy way" is where the repository already records it: `tensorAssocIso` requires *both* outer
factors invertible, and no rearrangement of `(F ⊗ O(d)) ⊗ O(e)` under `tensorCommIso` gets the
non-invertible `F` off an outer slot. `TwistComparison.lean`'s `tensorTwistAddIso` supplies the
composition only for `F` an associated sheaf, which is not the hypothesis here.

Even granting the isomorphism the argument would still have to compute what it does to a *section*,
and these witnesses are built by "sheafification inverts `W`" — which is exactly what `#585`
established they cannot do.

Raising is done one level down instead, on the **chart extensions**, where it is plain algebra.
`exists_globalSection_twistBy`'s recipe has two exponents: `n` extends `s` across each chart and
`m` forces agreement on the pairwise overlaps, with `N = 2m + n`. Both steps take place in
`Γ(F, -)` on `Proj 𝒜`, and:

* the extension at exponent `n + k` is the extension at exponent `n` multiplied by `(f / gᵢ)ᵏ`,
  a section of the structure sheaf over the whole of `D₊(gᵢ)` because `f` and `gᵢ` both have
  degree one;
* consequently the overlap discrepancy at exponent `n + k` is the discrepancy at exponent `n`
  scaled by that same unit, so **one `m` serves every `n' ≥ n`**.

So `N = 2m + n'` ranges over every integer `≥ 2m + n` with `m` held fixed, and no sheaf-level
twist comparison is needed anywhere.

This is the same move as `exists_pow_smul_eq_res_chart_of_le`, which raises the extension exponent
in the chart's own coordinates by `isLocalizationElem ^ (m - n) • t`. Two differences matter:
`ChartExtension.lean` is one chart at a time and in away-ring coordinates, and — the reason its
existential form cannot be used here — it returns *some* extension at the larger exponent, while
holding one overlap exponent `m` fixed needs the raised family to be the original one times a known
unit. Discard that relation and `m` has to be re-derived at each `n`, which puts `N = 2m(n) + n`
back out of reach.

## The multiplier is `(f / gᵢ)ᵏ`, not a fixed monomial

`gᵢ` is inverted on `D₊(gᵢ)` and nowhere else, and `D₊(gᵢ)` is the only open where the extension
`tᵢ` is asked to say anything. Raising by a fraction with a *different* denominator would produce
a statement that still typechecks — the fraction is a legitimate section wherever its denominator
is invertible — but that vanishes somewhere on `D₊(gᵢ)`, and the raised family would no longer
extend `s`. The denominator here is fixed by the chart, not chosen.

## Scope

The exponent only. Nothing here mentions generation, local surjectivity, or `free I`; those need
the chart-local half of Serre's theorem, which is not in this file.
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-! ### The two fraction identities raising costs

Both are `fracSection_mul` followed by `fracSection_eq`; they are named because the degree
bookkeeping is unreadable inline and because each is used under a `•`, where the ascription at
`Γ(Proj 𝒜, U)` is mandatory. -/

/-- **Raising the extension exponent, on the scalar.**

`(f / g)ᵏ · (f / g)ⁿ = (f / g)ⁿ⁺ᵏ`, with the right-hand fractions in the spelling
`isLocalizationFrac` produces. -/
theorem fracSection_pow_mul_isLocalizationFrac {e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 1)
    (n k : ℕ) {U : (Proj 𝒜).Opens} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    (show Γ(Proj 𝒜, U) from fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 hg (e * k))
        (hU.trans (basicOpen_le_basicOpen_pow 𝒜 g (e * k)))) *
        (show Γ(Proj 𝒜, U) from isLocalizationFrac 𝒜 hf hg n hU)
      = (show Γ(Proj 𝒜, U) from isLocalizationFrac 𝒜 hf hg (n + k) hU) :=
  (fracSection_mul 𝒜 _ _ _ _ _ _
      (le_basicOpen_mul 𝒜 (hU.trans (basicOpen_le_basicOpen_pow 𝒜 g (e * k)))
        (hU.trans ((basicOpen_le_basicOpen_pow 𝒜 g e).trans
          (basicOpen_le_basicOpen_pow 𝒜 (g ^ e) n))))).trans
    (fracSection_eq 𝒜 _ _ _ _ _ _ (by ring))

/-- **Raising commutes with the overlap comparison.**

`(f / g₁)ᵏ · (g₂ / g₁)ⁿ = (g₂ / g₁)ⁿ⁺ᵏ · (f / g₂)ᵏ`. This is why one overlap exponent `m` serves
every raised family: the two sides of the agreement are raised by *different* multipliers, one per
chart, and this identity is exactly the statement that the difference between them is absorbed by
the comparison fraction. -/
theorem fracSection_pow_mul_comm {e : ℕ} {f g₁ g₂ : A} (hf : f ∈ 𝒜 e) (h₁ : g₁ ∈ 𝒜 1)
    (h₂ : g₂ ∈ 𝒜 1)
    (n k : ℕ) {U : (Proj 𝒜).Opens} (hU₁ : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g₁)
    (hU₂ : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g₂) :
    (show Γ(Proj 𝒜, U) from fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 h₁ (e * k))
        (hU₁.trans (basicOpen_le_basicOpen_pow 𝒜 g₁ (e * k)))) *
        (show Γ(Proj 𝒜, U) from fracSection 𝒜 (pow_mem_deg 𝒜 h₂ (e * n))
          (pow_mem_deg 𝒜 h₁ (e * n))
          (hU₁.trans (basicOpen_le_basicOpen_pow 𝒜 g₁ (e * n))))
      = (show Γ(Proj 𝒜, U) from fracSection 𝒜 (pow_mem_deg 𝒜 h₂ (e * (n + k)))
          (pow_mem_deg 𝒜 h₁ (e * (n + k)))
          (hU₁.trans (basicOpen_le_basicOpen_pow 𝒜 g₁ (e * (n + k))))) *
        (show Γ(Proj 𝒜, U) from fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 h₂ (e * k))
          (hU₂.trans (basicOpen_le_basicOpen_pow 𝒜 g₂ (e * k)))) := by
  refine (fracSection_mul 𝒜 _ _ _ _ _ _
    (le_basicOpen_mul 𝒜 (hU₁.trans (basicOpen_le_basicOpen_pow 𝒜 g₁ (e * k)))
      (hU₁.trans (basicOpen_le_basicOpen_pow 𝒜 g₁ (e * n))))).trans ?_
  refine Eq.trans ?_ (fracSection_mul 𝒜 _ _ _ _ _ _
    (le_basicOpen_mul 𝒜 (hU₁.trans (basicOpen_le_basicOpen_pow 𝒜 g₁ (e * (n + k))))
      (hU₂.trans (basicOpen_le_basicOpen_pow 𝒜 g₂ (e * k))))).symm
  exact fracSection_eq 𝒜 _ _ _ _ _ _ (by ring)

/-- **The twist exponent can be taken as large as one likes.**

`exists_globalSection_twistBy` with the existential over `N` replaced by "every `N` from some
point on". This is the form a family of sections can be given a *common* exponent in, and it is
the missing ingredient between `#585` and Serre's global generation.

The proof holds the overlap exponent `m` fixed and raises the chart extensions: the family
`(f / gᵢ)ᵏ · tᵢ` extends `s` with exponent `n + k`, and the overlap agreement survives because
`fracSection_pow_mul_comm` absorbs the difference between the two charts' multipliers. So
`N = 2m + (n + k)` is reachable for every `k`, which is every `N ≥ 2m + n`. -/
theorem exists_globalSection_twistBy_forall_ge (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {ι : Type u} [Finite ι] {g : ι → A}
    (hg : ∀ i, g i ∈ 𝒜 1)
    (hcov : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤)
    (s : Γ(F, basicOpen 𝒜 f)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ σ : Γ(Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * N : ℕ) : ℤ)), ⊤),
        (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * N : ℕ) : ℤ))).presheaf.map
            (homOfLE (le_top (a := basicOpen 𝒜 f))).op σ
          = Scheme.Modules.Hom.app (twistBy 𝒜 (e * N) (pow_mem_mul 𝒜 hf N) F)
              (basicOpen 𝒜 f) s := by
  classical
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_res_image_uniform 𝒜 F hf hg Nat.one_pos
    (W := fun i => basicOpen 𝒜 (g i))
    (V := fun i => basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f)
    (funext fun i => awayι_image_top 𝒜 (hg i) Nat.one_pos)
    (funext fun i => awayι_image_basicOpen 𝒜 (hg i) Nat.one_pos hf he)
    (fun i => inf_le_left) (fun i => inf_le_left)
    (fun i => F.presheaf.map (homOfLE (inf_le_right :
      basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 f)).op s)
  choose t ht using hn
  obtain ⟨m, hm⟩ := exists_overlap_exponent 𝒜 F hf he hg s n t ht
  refine ⟨2 * m + n, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = 2 * m + (n + k) := ⟨N - (2 * m + n), by omega⟩
  -- the raised family: `tᵢ` multiplied by `(f / gᵢ)ᵏ`, a unit on the whole of `D₊(gᵢ)`
  refine exists_globalSection_twistBy_of_data 𝒜 F hf hg hcov s (n + k) m
    (fun i => (show Γ(Proj 𝒜, basicOpen 𝒜 (g i)) from
      fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg i) (e * k))
        (basicOpen_le_basicOpen_pow 𝒜 (g i) (e * k))) • t i) (fun i => ?_) (fun p => ?_)
  · -- the raised family still extends `s`, now with exponent `n + k`
    refine (resSection_smul 𝒜 F (inf_le_left :
      basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 (g i)) _ (t i)).trans ?_
    refine (congrArg₂ (fun (r : Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f))
      (y : Γ(F, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f)) => r • y)
      (resΓ_fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg i) (e * k)) _
        (basicOpen_le_basicOpen_pow 𝒜 (g i) (e * k))
        (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g i) (e * k)))) (ht i)).trans ?_
    rw [smul_smul]
    exact congrArg (fun r : Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) =>
        r • F.presheaf.map (homOfLE (inf_le_right :
          basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 f)).op s)
      (fracSection_pow_mul_isLocalizationFrac 𝒜 hf (hg i) n k inf_le_left)
  · -- and the overlap agreement survives, with the *same* `m`
    have hres₁ := resSection_smul 𝒜 F (inf_le_left :
        basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1)) from
        fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg p.1) (e * k))
          (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * k))) (t p.1)
    have hres₂ := resSection_smul 𝒜 F (inf_le_right :
        basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.2)) from
        fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg p.2) (e * k))
          (basicOpen_le_basicOpen_pow 𝒜 (g p.2) (e * k))) (t p.2)
    have hc₁ := resΓ_fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg p.1) (e * k))
      (inf_le_left : basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))
      (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * k))
      (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * k)))
    have hc₂ := resΓ_fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg p.2) (e * k))
      (inf_le_right : basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))
      (basicOpen_le_basicOpen_pow 𝒜 (g p.2) (e * k))
      (inf_le_right.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.2) (e * k)))
    rw [hres₁, hres₂, hc₁, hc₂, smul_smul, smul_smul, smul_smul, mul_comm _
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
        fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg p.1) (e * k))
          (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * k)))), ← smul_smul,
      hm p, smul_smul, smul_smul]
    refine congrArg (fun r : Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) =>
      r • F.presheaf.map (homOfLE (inf_le_right :
        basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))).op (t p.2)) ?_
    rw [mul_comm (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
        fracSection 𝒜 (pow_mem_mul 𝒜 hf k) (pow_mem_deg 𝒜 (hg p.1) (e * k))
          (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * k)))),
      mul_assoc, mul_assoc]
    exact congrArg (fun r : Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) =>
        (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
          isLocalizationFrac 𝒜 hf (SetLike.mul_mem_graded (hg p.1) (hg p.2)) m
            (le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm)) * r)
      (fracSection_pow_mul_comm 𝒜 hf (hg p.1) (hg p.2) n k inf_le_left inf_le_right)

/-- **One twist exponent for a finite family of sections.**

Every `sₐ`, defined on its own degree-one chart `D₊(fₐ)`, becomes the restriction of a global
section of the *same* `F(N)`. This is the form Serre's global generation consumes: the generators
of `Γ(F, D₊(gᵢ))` for every `i` form one finite family, and `free I ⟶ F(N)` needs them all in one
sheaf.

The exponent is the maximum of the thresholds `exists_globalSection_twistBy_forall_ge` supplies,
which exists because the family is finite. -/
theorem exists_globalSection_twistBy_uniform (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {ι : Type u} [Finite ι] {g : ι → A} (hg : ∀ i, g i ∈ 𝒜 1)
    (hcov : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤)
    {e : ℕ} {κ : Type u} [Finite κ] {f : κ → A} (hf : ∀ a, f a ∈ 𝒜 e) (he : 0 < e)
    (s : ∀ a, Γ(F, basicOpen 𝒜 (f a))) :
    ∃ N : ℕ, ∀ a : κ,
      ∃ σ : Γ(Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * N : ℕ) : ℤ)), ⊤),
        (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * N : ℕ) : ℤ))).presheaf.map
            (homOfLE (le_top (a := basicOpen 𝒜 (f a)))).op σ
          = Scheme.Modules.Hom.app (twistBy 𝒜 (e * N) (pow_mem_mul 𝒜 (hf a) N) F)
              (basicOpen 𝒜 (f a)) (s a) := by
  classical
  choose N₀ hN₀ using fun a =>
    exists_globalSection_twistBy_forall_ge 𝒜 F (hf a) he hg hcov (s a)
  obtain ⟨N, hN⟩ := (Set.finite_range N₀).bddAbove
  exact ⟨N, fun a => hN₀ a N (hN (Set.mem_range_self a))⟩

end AlgebraicGeometry.Proj
