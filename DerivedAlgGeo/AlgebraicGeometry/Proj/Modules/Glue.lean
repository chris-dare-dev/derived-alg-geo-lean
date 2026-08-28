/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ChartProj

/-!
# `#585`: a section over `D₊(f)` becomes a global section of a twist

`exists_globalSection_twistBy` is the deliverable of `#585`. For `F` quasi-coherent on `Proj 𝒜`
and `s` a section over `D₊(f)`, some `f ᴺ · s` is the restriction of a **global** section of
`F(N)`.

## The two exponents, and why they cannot be one

`ChartProj.exists_pow_smul_eq_res_image_uniform` gives an `n` and, over each `D₊(gᵢ)`, a section
`tᵢ` restricting to `(f / gᵢ)ⁿ · s` where `D₊(f)` reaches. That is all the geometry there is, and
it is not enough: `TopCat.Sheaf.IsCompatible` wants the `tᵢ` to agree on the *whole* overlap
`D₊(gᵢ) ⊓ D₊(gⱼ)`, and `D₊(f)` is not contained in it.

The second exponent closes that. `tᵢ` and `(gⱼ / gᵢ)ⁿ · tⱼ` **do** agree on
`D₊(gᵢ) ⊓ D₊(gⱼ) ⊓ D₊(f)` -- that is the computation `hagree` below, and it is where the two
charts' different denominators cancel -- so separatedness on the overlap gives an `m` with
`(f² / (gᵢgⱼ)ᵉ)ᵐ` killing the difference on the whole overlap. The overlap is the chart of `gᵢ gⱼ`,
which has degree two; that is why `AwayChart.lean` exists.

The `e` in that denominator is the degree of `f`. `isLocalizationFrac` balances a degree-`e`
numerator against a degree-`d` denominator by raising each to the other's degree, so every
`g`-side exponent below carries a factor of `e` that the degree-one statement cannot see.

## What is twisted, and with which element

Not `gᵢ ᴺ`. The section that glues is `twistBy (f²ᵐ gᵢⁿ)` of `tᵢ`, a section of `F(N)` for
`N = 2m + n`. Two facts fall out of `FracSection.twistBy_app_eq_smul'` and no others are needed:

* over `D₊(gᵢ) ⊓ D₊(gⱼ)`, `f²ᵐ gᵢⁿ / (gᵢgⱼ)ᵐ gᵢⁿ` is exactly the scalar the agreement supplies, so
  the two twisted sections differ by applying one map to the two sides of the agreement;
* over `D₊(gᵢ) ⊓ D₊(f)`, `f ᴺ / f²ᵐ gᵢⁿ` is exactly `(f / gᵢ)ⁿ`, so every twisted section restricts
  to `twistBy (f ᴺ)` of `s` there -- which is what identifies the glued section.

Choosing `twistBy (gᵢ ᴺ)` instead would put the comparison in `F(n)` and force a passage from
`F(n)(2m)` to `F(N)`; nothing provides that, and it is not needed.

## The three-step shape

The theorem is assembled from two lemmas that take the exponents as *data*, because a downstream
caller needs to choose them rather than accept whatever the chart lemmas happen to produce.

* `exists_overlap_exponent` takes the extension exponent `n` and the family `t` and produces the
  overlap exponent `m`;
* `exists_globalSection_twistBy_of_data` takes both exponents and the family and does the gluing.
  It does **not** need quasi-coherence -- that hypothesis is spent entirely on producing `n`, `t`
  and `m`, and nothing in the gluing itself uses it.

`GlueUniform.lean` reuses the same two lemmas with `m` held fixed and `n` raised, which is how a
single exponent is reached for a whole finite family.

## Scope

The theorem and its two halves. The hypotheses are the honest ones: `F` quasi-coherent, the cover
given by finitely many degree-one elements generating `A` over `𝒜 0`, and `f` homogeneous of any
positive degree.

Generation in degree one is **not** a convenience and must not be weakened: it is Hartshorne
II.5.12's hypothesis, and without it `O(n)` is not locally free. It is `f` alone that `#823`
lifted off degree one, which is what Hartshorne II.5.14(a) and Stacks 01PW state.
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-! ### Restriction of sections, spelled out

Three one-line facts about restricting a section of a module sheaf on `Proj 𝒜`. They are named
because the proof below composes restrictions constantly and `rw` cannot be used on goals carrying
`show`-ascription residue. -/

/-- **Restriction composes.** -/
theorem resSection_trans (F : (Proj 𝒜).Modules) {U V W : (Proj 𝒜).Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(F, U)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op x)
      = F.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Restriction is semilinear over restriction of scalars.** -/
theorem resSection_smul (F : (Proj 𝒜).Modules) {U V : (Proj 𝒜).Opens} (h : V ≤ U)
    (r : Γ(Proj 𝒜, U)) (x : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op (r • x)
      = (Proj 𝒜).presheaf.map (homOfLE h).op r • F.presheaf.map (homOfLE h).op x :=
  Scheme.Modules.map_smul F _ r x

/-- **A fraction restricts to the same fraction**, because it is defined pointwise. -/
theorem resΓ_fracSection {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {U V : (Proj 𝒜).Opens} (h : V ≤ U) (hUb : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b)
    (hVb : V ≤ ProjectiveSpectrum.basicOpen 𝒜 b) :
    (Proj 𝒜).presheaf.map (homOfLE h).op (show Γ(Proj 𝒜, U) from fracSection 𝒜 ha hb hUb)
      = (show Γ(Proj 𝒜, V) from fracSection 𝒜 ha hb hVb) := rfl

/-- **A morphism of module sheaves commutes with restriction.** -/
theorem homApp_res {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (φ.app U x) = φ.app V (M.presheaf.map (homOfLE h).op x) :=
  (NatTrans.naturality_apply φ.mapPresheaf (homOfLE h).op x).symm

/-- **An open inside two basic opens is inside the basic open of the product.** -/
theorem le_basicOpen_mul {U : (Proj 𝒜).Opens} {a b : A}
    (ha : U ≤ ProjectiveSpectrum.basicOpen 𝒜 a) (hb : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) :
    U ≤ ProjectiveSpectrum.basicOpen 𝒜 (a * b) := by
  rw [ProjectiveSpectrum.basicOpen_mul]
  exact le_inf ha hb


/-- **The glue, from the two exponents and the chart extensions as data.**

The mathematical content of `exists_globalSection_twistBy`, with the two exponents and the family
of chart extensions taken as *inputs* rather than produced inside. `n`, `t` and `ht` are what
`exists_pow_smul_eq_res_image_uniform` supplies; `m` and `hm` are what
`exists_pow_smul_eq_of_res_eq_image_uniform` supplies once the overlap agreement is derived from
`ht`.

Splitting it out is what makes the exponent controllable. The theorem below instantiates it at the
exponents those two lemmas happen to produce, and `GlueUniform.lean` instantiates it at a
*prescribed* `n`, which is how a single `N` is reached for a whole finite family of sections. -/
theorem exists_globalSection_twistBy_of_data (F : (Proj 𝒜).Modules)
    {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) {ι : Type u} {g : ι → A} (hg : ∀ i, g i ∈ 𝒜 1)
    (hcov : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤)
    (s : Γ(F, basicOpen 𝒜 f)) (n m : ℕ) (t : ∀ i, Γ(F, basicOpen 𝒜 (g i)))
    (ht : ∀ i, F.presheaf.map (homOfLE (inf_le_left :
        basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 (g i))).op (t i)
      = (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) from
          isLocalizationFrac 𝒜 hf (hg i) n inf_le_left) •
        F.presheaf.map (homOfLE (inf_le_right :
          basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 f)).op s)
    (hm : ∀ p : ι × ι,
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
          isLocalizationFrac 𝒜 hf (SetLike.mul_mem_graded (hg p.1) (hg p.2)) m
            (le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm)) •
        F.presheaf.map (homOfLE (inf_le_left :
          basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))).op (t p.1)
      = (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
          isLocalizationFrac 𝒜 hf (SetLike.mul_mem_graded (hg p.1) (hg p.2)) m
            (le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm)) •
        ((show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
            fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n))
              (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * n)))) •
          F.presheaf.map (homOfLE (inf_le_right :
            basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))).op (t p.2))) :
    ∃ σ : Γ(Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ)), ⊤),
      (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ))).presheaf.map
          (homOfLE (le_top (a := basicOpen 𝒜 f))).op σ
        = Scheme.Modules.Hom.app
            (twistBy 𝒜 (e * (2 * m + n)) (pow_mem_mul 𝒜 hf (2 * m + n)) F) (basicOpen 𝒜 f) s := by
  classical
  have hcover : ⨆ i, basicOpen 𝒜 (g i) = ⊤ :=
    iSup_basicOpen_eq_top' 𝒜 g (fun i => ⟨1, hg i⟩) hcov
  have hb2 : ∀ p : ι × ι, g p.1 * g p.2 ∈ 𝒜 2 := fun p =>
    SetLike.mul_mem_graded (hg p.1) (hg p.2)
  have hgn : ∀ p : ι × ι, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)
      ≤ ProjectiveSpectrum.basicOpen 𝒜 (g p.1 ^ (e * n)) := fun p =>
    inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * n))
  -- The twist is by `f ^ (2m + n)`, which sits in degree `e * (2m + n)`. The `g`-side exponents
  -- carry the matching factor of `e`, because `isLocalizationFrac` balances a degree-`e` numerator
  -- against a degree-one denominator by raising the denominator to the `e`.
  have hA : ∀ i, f ^ (2 * m) * g i ^ (e * n) ∈ 𝒜 (e * (2 * m + n)) := fun i => by
    have h := SetLike.mul_mem_graded (pow_mem_mul 𝒜 hf (2 * m)) (pow_mem_deg 𝒜 (hg i) (e * n))
    rwa [show e * (2 * m) + e * n = e * (2 * m + n) by ring] at h
  have hBm : ∀ p : ι × ι, (g p.1 * g p.2) ^ (e * m) ∈ 𝒜 (2 * (e * m)) := fun p =>
    pow_mem_mul 𝒜 (hb2 p) (e * m)
  have hB : ∀ p : ι × ι,
      (g p.1 * g p.2) ^ (e * m) * g p.1 ^ (e * n) ∈ 𝒜 (e * (2 * m + n)) := fun p => by
    have h := SetLike.mul_mem_graded (hBm p) (pow_mem_deg 𝒜 (hg p.1) (e * n))
    rwa [show 2 * (e * m) + e * n = e * (2 * m + n) by ring] at h
  have hWb : ∀ p : ι × ι, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)
      ≤ ProjectiveSpectrum.basicOpen 𝒜 ((g p.1 * g p.2) ^ (e * m) * g p.1 ^ (e * n)) := fun p =>
    le_basicOpen_mul 𝒜
      ((le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm).trans
        (basicOpen_le_basicOpen_pow 𝒜 (g p.1 * g p.2) (e * m)))
      (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * n)))
  -- the twisted local sections are compatible
  have hcompat : TopCat.Presheaf.IsCompatible
      (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ))).presheaf
      (fun i => basicOpen 𝒜 (g i))
      (fun i => Scheme.Modules.Hom.app (twistBy 𝒜 (e * (2 * m + n)) (hA i) F)
        (basicOpen 𝒜 (g i)) (t i)) := by
    intro i j
    have hfracL :
        (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) from
            fracSection 𝒜 (hA i) (hB (i, j)) (hWb (i, j)))
          = (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) from
            isLocalizationFrac 𝒜 hf (hb2 (i, j)) m
              (le_of_eq (basicOpen_mul 𝒜 (g i) (g j)).symm)) :=
      fracSection_eq 𝒜 _ _ _ _ _ _ (by ring)
    have hfracR :
        (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) from
            fracSection 𝒜 (hA j) (hB (i, j)) (hWb (i, j)))
          = (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) from
              isLocalizationFrac 𝒜 hf (hb2 (i, j)) m
                (le_of_eq (basicOpen_mul 𝒜 (g i) (g j)).symm)) *
            (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) from
              fracSection 𝒜 (pow_mem_deg 𝒜 (hg j) (e * n)) (pow_mem_deg 𝒜 (hg i) (e * n))
                (hgn (i, j))) :=
      (fracSection_eq 𝒜 _ _ _ _ _
        (le_basicOpen_mul 𝒜
          (((le_of_eq (basicOpen_mul 𝒜 (g i) (g j)).symm).trans
            (basicOpen_le_basicOpen_pow 𝒜 (g i * g j) e)).trans
              (basicOpen_le_basicOpen_pow 𝒜 ((g i * g j) ^ e) m))
          (hgn (i, j)))
        (by ring)).trans (fracSection_mul 𝒜 _ _ _ _ _ _ _).symm
    have hLfinal :=
      (homApp_res (twistBy 𝒜 (e * (2 * m + n)) (hA i) F)
        (inf_le_left : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j) ≤ basicOpen 𝒜 (g i)) (t i)).trans
      (((twistBy_app_eq_smul' 𝒜 (hA i) (hB (i, j)) F (hWb (i, j)) _).trans
        (congrArg (fun r : Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) =>
          r • Scheme.Modules.Hom.app (twistBy 𝒜 (e * (2 * m + n)) (hB (i, j)) F)
            (basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j))
            (F.presheaf.map (homOfLE (inf_le_left : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)
              ≤ basicOpen 𝒜 (g i))).op (t i))) hfracL)).trans
        (Scheme.Modules.Hom.app_smul _ _ _).symm)
    have hRfinal :=
      (homApp_res (twistBy 𝒜 (e * (2 * m + n)) (hA j) F)
        (inf_le_right : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j) ≤ basicOpen 𝒜 (g j)) (t j)).trans
      (((twistBy_app_eq_smul' 𝒜 (hA j) (hB (i, j)) F (hWb (i, j)) _).trans
        (congrArg (fun r : Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) =>
          r • Scheme.Modules.Hom.app (twistBy 𝒜 (e * (2 * m + n)) (hB (i, j)) F)
            (basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j))
            (F.presheaf.map (homOfLE (inf_le_right : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)
              ≤ basicOpen 𝒜 (g j))).op (t j))) hfracR)).trans
        (((Scheme.Modules.Hom.app_smul _ _ _).trans
          (congrArg (fun y : Γ(Scheme.Modules.tensorObj F
              (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ)), basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) =>
            (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j)) from
              isLocalizationFrac 𝒜 hf (hb2 (i, j)) m
                (le_of_eq (basicOpen_mul 𝒜 (g i) (g j)).symm)) • y)
            (Scheme.Modules.Hom.app_smul _ _ _))).trans (mul_smul _ _ _).symm).symm)
    exact hLfinal.trans ((congrArg
      (Scheme.Modules.Hom.app (twistBy 𝒜 (e * (2 * m + n)) (hB (i, j)) F)
        (basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 (g j))) (hm (i, j))).trans hRfinal.symm)
  -- glue
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := (⟨(Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ))).presheaf,
      Scheme.Modules.isSheaf _⟩ : TopCat.Sheaf Ab (Proj 𝒜)))
    (fun i => basicOpen 𝒜 (g i)) ⊤ (fun i => homOfLE le_top) (le_of_eq hcover.symm) _ hcompat
  refine ⟨σ, ?_⟩
  -- the glued section restricts to the twist of `s`
  have hDcover : ⨆ i, (basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) = basicOpen 𝒜 f := by
    rw [← iSup_inf_eq, hcover, top_inf_eq]
  refine TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨(Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ))).presheaf,
      Scheme.Modules.isSheaf _⟩ : TopCat.Sheaf Ab (Proj 𝒜)))
    (fun i => basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) (basicOpen 𝒜 f)
    (fun i => homOfLE inf_le_right) (le_of_eq hDcover.symm) _ _ ?_
  intro i
  have hAle : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f
      ≤ ProjectiveSpectrum.basicOpen 𝒜 (f ^ (2 * m) * g i ^ (e * n)) :=
    le_basicOpen_mul 𝒜 (inf_le_right.trans (basicOpen_le_basicOpen_pow 𝒜 f (2 * m)))
      (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g i) (e * n)))
  have hfracN :
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) from
          fracSection 𝒜 (pow_mem_mul 𝒜 hf (2 * m + n)) (hA i) hAle)
        = (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) from
          isLocalizationFrac 𝒜 hf (hg i) n inf_le_left) :=
    fracSection_eq 𝒜 _ _ _ _ _ _ (by ring)
  have hLeft :=
    (resSection_trans 𝒜 (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ)))
      (le_top (a := basicOpen 𝒜 f)) (inf_le_right :
        basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 f) σ).trans
    ((resSection_trans 𝒜 (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ)))
      (le_top (a := basicOpen 𝒜 (g i))) (inf_le_left :
        basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 (g i)) σ).symm.trans
      ((congrArg (fun y : Γ(Scheme.Modules.tensorObj F
          (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ)), basicOpen 𝒜 (g i)) =>
        (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * (2 * m + n) : ℕ) : ℤ))).presheaf.map
          (homOfLE (inf_le_left : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f
            ≤ basicOpen 𝒜 (g i))).op y) (hσ i)).trans
        ((homApp_res (twistBy 𝒜 (e * (2 * m + n)) (hA i) F) (inf_le_left :
          basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 (g i)) (t i)).trans
          ((congrArg (Scheme.Modules.Hom.app (twistBy 𝒜 (e * (2 * m + n)) (hA i) F)
            (basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f)) (ht i)).trans
            (Scheme.Modules.Hom.app_smul _ _ _)))))
  have hRight :=
    (homApp_res (twistBy 𝒜 (e * (2 * m + n)) (pow_mem_mul 𝒜 hf (2 * m + n)) F)
      (inf_le_right : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 f) s).trans
    ((twistBy_app_eq_smul' 𝒜 (pow_mem_mul 𝒜 hf (2 * m + n)) (hA i) F hAle _).trans
      (congrArg (fun r : Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) =>
        r • Scheme.Modules.Hom.app (twistBy 𝒜 (e * (2 * m + n)) (hA i) F)
          (basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f)
          (F.presheaf.map (homOfLE (inf_le_right : basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f
            ≤ basicOpen 𝒜 f)).op s)) hfracN))
  exact hLeft.trans hRight.symm

/-- **The overlap exponent, from the chart extensions as data.**

The second half of `exists_globalSection_twistBy`'s recipe: given the family `t` extending `s`
across each chart with exponent `n`, this is the exponent `m` that forces the extensions to agree
on the *whole* pairwise overlap, not only where `D₊(f)` reaches.

Like `exists_globalSection_twistBy_of_data`, it takes `n`, `t` and `ht` as inputs. That is what
lets `GlueUniform.lean` fix one `m` and then vary `n` freely: the agreement at exponent `n + k` is
the agreement at exponent `n` scaled by `(f / gᵢ)ᵏ`, so the same `m` serves every larger
exponent. -/
theorem exists_overlap_exponent (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {ι : Type u} [Finite ι] {g : ι → A} (hg : ∀ i, g i ∈ 𝒜 1)
    (s : Γ(F, basicOpen 𝒜 f)) (n : ℕ) (t : ∀ i, Γ(F, basicOpen 𝒜 (g i)))
    (ht : ∀ i, F.presheaf.map (homOfLE (inf_le_left :
        basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 (g i))).op (t i)
      = (show Γ(Proj 𝒜, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) from
          isLocalizationFrac 𝒜 hf (hg i) n inf_le_left) •
        F.presheaf.map (homOfLE (inf_le_right :
          basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f ≤ basicOpen 𝒜 f)).op s) :
    ∃ m : ℕ, ∀ p : ι × ι,
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
          isLocalizationFrac 𝒜 hf (SetLike.mul_mem_graded (hg p.1) (hg p.2)) m
            (le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm)) •
        F.presheaf.map (homOfLE (inf_le_left :
          basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))).op (t p.1)
      = (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
          isLocalizationFrac 𝒜 hf (SetLike.mul_mem_graded (hg p.1) (hg p.2)) m
            (le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm)) •
        ((show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
            fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n))
              (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * n)))) •
          F.presheaf.map (homOfLE (inf_le_right :
            basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))).op (t p.2)) := by
  classical
  -- the extension property, restricted to any smaller open
  have key : ∀ (i : ι) (Z : (Proj 𝒜).Opens) (hZ : Z ≤ basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f),
      F.presheaf.map (homOfLE (hZ.trans inf_le_left)).op (t i)
        = (show Γ(Proj 𝒜, Z) from isLocalizationFrac 𝒜 hf (hg i) n (hZ.trans inf_le_left)) •
          F.presheaf.map (homOfLE (hZ.trans inf_le_right)).op s := by
    intro i Z hZ
    refine (resSection_trans 𝒜 F inf_le_left hZ (t i)).symm.trans ?_
    refine (congrArg (fun y : Γ(F, basicOpen 𝒜 (g i) ⊓ basicOpen 𝒜 f) =>
      F.presheaf.map (homOfLE hZ).op y) (ht i)).trans ?_
    refine (resSection_smul 𝒜 F hZ _ _).trans ?_
    exact congrArg₂ (fun (r : Γ(Proj 𝒜, Z)) (y : Γ(F, Z)) => r • y)
      (resΓ_fracSection 𝒜 _ _ hZ _ _) (resSection_trans 𝒜 F inf_le_right hZ s)
  -- the pairwise overlaps are the charts of the products, which have degree two
  have hb2 : ∀ p : ι × ι, g p.1 * g p.2 ∈ 𝒜 2 := fun p =>
    SetLike.mul_mem_graded (hg p.1) (hg p.2)
  have h2 : (0 : ℕ) < 2 := by norm_num
  have hWeq : ∀ p : ι × ι, awayι 𝒜 (g p.1 * g p.2) (hb2 p) h2 ''ᵁ ⊤
      = basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) := fun p =>
    (awayι_image_top 𝒜 (hb2 p) h2).trans (basicOpen_mul 𝒜 _ _)
  have hVeq : ∀ p : ι × ι, awayι 𝒜 (g p.1 * g p.2) (hb2 p) h2 ''ᵁ
        PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem (hb2 p) hf)
      = (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f := fun p => by
    rw [awayι_image_basicOpen 𝒜 (hb2 p) h2 hf he, basicOpen_mul]
  have hgn : ∀ p : ι × ι, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)
      ≤ ProjectiveSpectrum.basicOpen 𝒜 (g p.1 ^ (e * n)) := fun p =>
    inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.1) (e * n))
  -- on an overlap, `tᵢ` and `(gⱼ/gᵢ)ⁿ · tⱼ` agree where `D₊(f)` reaches
  have hagree : ∀ p : ι × ι,
      F.presheaf.map (homOfLE (inf_le_left :
          (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
            ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2))).op
        (F.presheaf.map (homOfLE (inf_le_left :
          basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))).op (t p.1))
      = F.presheaf.map (homOfLE (inf_le_left :
          (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
            ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2))).op
        ((show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
            fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n)) (hgn p)) •
          F.presheaf.map (homOfLE (inf_le_right :
            basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))).op (t p.2)) := by
    intro p
    have hZi : (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
        ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 f :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hZj : (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
        ≤ basicOpen 𝒜 (g p.2) ⊓ basicOpen 𝒜 f :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hL := (resSection_trans 𝒜 F
      (inf_le_left : basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))
      (inf_le_left : (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
        ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) (t p.1)).trans (key p.1 _ hZi)
    have hR2 := (resSection_trans 𝒜 F
      (inf_le_right : basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))
      (inf_le_left : (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
        ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) (t p.2)).trans (key p.2 _ hZj)
    have hR1 := resSection_smul 𝒜 F
      (inf_le_left : (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
        ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2))
      (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
        fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n)) (hgn p))
      (F.presheaf.map (homOfLE (inf_le_right :
        basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))).op (t p.2))
    have hratio := resΓ_fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n))
      (inf_le_left : (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f
        ≤ basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2))
      (hgn p) (inf_le_left.trans (hgn p))
    have hfrac :
        (show Γ(Proj 𝒜, (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f) from
            isLocalizationFrac 𝒜 hf (hg p.1) n (hZi.trans inf_le_left))
          = (show Γ(Proj 𝒜, (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f) from
              fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n))
                (inf_le_left.trans (hgn p))) *
            (show Γ(Proj 𝒜, (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f) from
              isLocalizationFrac 𝒜 hf (hg p.2) n (hZj.trans inf_le_left)) :=
      (fracSection_eq 𝒜 _ _ _ _ _
        (le_basicOpen_mul 𝒜 (inf_le_left.trans (hgn p))
          ((hZj.trans (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 (g p.2) e))).trans
            (basicOpen_le_basicOpen_pow 𝒜 (g p.2 ^ e) n)))
        (by ring)).trans (fracSection_mul 𝒜 _ _ _ _ _ _ _).symm
    refine hL.trans (Eq.symm (hR1.trans ?_))
    refine (congrArg₂ (fun (r : Γ(Proj 𝒜, (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓
      basicOpen 𝒜 f)) (y : Γ(F, (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f)) =>
      r • y) hratio hR2).trans ?_
    rw [smul_smul]
    exact congrArg (fun r : Γ(Proj 𝒜, (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓
      basicOpen 𝒜 f) => r • F.presheaf.map (homOfLE (hZi.trans inf_le_right)).op s) hfrac.symm
  -- one exponent forcing agreement on every overlap
  exact exists_pow_smul_eq_of_res_eq_image_uniform 𝒜 F
    (f := fun _ : ι × ι => f) (b := fun p : ι × ι => g p.1 * g p.2)
    (fun _ => hf) hb2 h2
    (W := fun p : ι × ι => basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2))
    (V := fun p : ι × ι => (basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) ⊓ basicOpen 𝒜 f)
    (funext hWeq) (funext hVeq)
    (fun p => inf_le_left)
    (fun p => le_of_eq (basicOpen_mul 𝒜 (g p.1) (g p.2)).symm)
    (t := fun p => F.presheaf.map (homOfLE (inf_le_left :
      basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.1))).op (t p.1))
    (t' := fun p => (show Γ(Proj 𝒜, basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2)) from
        fracSection 𝒜 (pow_mem_deg 𝒜 (hg p.2) (e * n)) (pow_mem_deg 𝒜 (hg p.1) (e * n)) (hgn p)) •
      F.presheaf.map (homOfLE (inf_le_right :
        basicOpen 𝒜 (g p.1) ⊓ basicOpen 𝒜 (g p.2) ≤ basicOpen 𝒜 (g p.2))).op (t p.2))
    (h := hagree)

/-- **`#585`: a section over `D₊(f)`, twisted, is the restriction of a global section.**

For `F` quasi-coherent on `Proj 𝒜`, `f` homogeneous of any positive degree `e`, and a finite
family of degree-one elements generating `A` over `𝒜 0`, every `s ∈ Γ(F, D₊(f))` has a `k` with
`twistBy (f ᵏ) s` the restriction of a global section of `F(e · k)`.

This is Hartshorne II.5.14(a) / Stacks 01PW. It is **not** Serre's theorem (II.5.17), which is
`#570`; this is one of its three steps.

The twist degree is `e * k` rather than `k` because `f ᵏ` has degree `e * k`. At `e = 1` the two
agree, which is the form `#585` proved and `GlueUniform.lean` still consumes.

The two exponents are independent: `n` extends `s` across each chart, `m` forces agreement on the
pairwise overlaps, and `k = 2m + n`. The section over `D₊(gᵢ)` that glues is `twistBy (f²ᵐ gᵢᵉⁿ)`
of the chart extension, not `twistBy (gᵢ ᴺ)`; that choice is what keeps the whole comparison inside
`F(e · k)` and avoids a passage from `F(e n)(2 e m)` that nothing provides.

The `g`-side exponents carry a factor of `e` that the degree-one statement cannot see:
`isLocalizationFrac` balances a degree-`e` numerator against a degree-one denominator by raising
the denominator to the `e`, so `gᵢ ⁿ` becomes `gᵢ ᵉⁿ` everywhere below. -/
theorem exists_globalSection_twistBy (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {ι : Type u} [Finite ι] {g : ι → A}
    (hg : ∀ i, g i ∈ 𝒜 1)
    (hcov : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤)
    (s : Γ(F, basicOpen 𝒜 f)) :
    ∃ (k : ℕ) (σ : Γ(Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * k : ℕ) : ℤ)), ⊤)),
      (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 ((e * k : ℕ) : ℤ))).presheaf.map
          (homOfLE (le_top (a := basicOpen 𝒜 f))).op σ
        = Scheme.Modules.Hom.app (twistBy 𝒜 (e * k) (pow_mem_mul 𝒜 hf k) F)
            (basicOpen 𝒜 f) s := by
  classical
  -- one exponent extending `s` across every degree-one chart
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
  exact ⟨2 * m + n, exists_globalSection_twistBy_of_data 𝒜 F hf hg hcov s n m t ht hm⟩

end AlgebraicGeometry.Proj
