/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.AwayChart
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.FracSection

/-!
# The chart's scalar, read on `Proj`

`#585`'s two halves speak different languages. `ChartExtension.lean` produces sections of a
degree-one chart and clears the chart ring's element `f / g`
(`HomogeneousLocalization.Away.isLocalizationElem`); `TwistApp.lean` compares twists of sections of
`F` on `Proj 𝒜` and scales by the structure-sheaf section `fracPowSection`. This file is the
dictionary, and it is the last genuinely open step of the issue.

## What has to be identified

Nothing has to move on the module side: `Scheme.Modules.restrictAppIso` is `Iso.refl`, so
`Γ(chartRestrict 𝒜 F hg, U)` **is** `Γ(F, awayι 𝒜 g hg hd ''ᵁ U)`. What differs is the ring
acting. The chart's sections are a module over the away ring `A_{(g)}`; the same elements as
sections on `Proj` are a module over `Γ(Proj 𝒜, D₊(g))`. The comparison map between those two rings
is Mathlib's `Proj.awayToSection`, and `awayToSection_isLocalizationElem_pow` says it sends
`(f / g)ⁿ` to `fracPowSection`.

## Two independent facts, and why the second one is the hard one

`awayToSection_isLocalizationElem_pow` is elementary once the shapes line up: the degree-one case is
`rfl`, `awayToSection` is a ring hom so it commutes with `^ n`, and the structure sheaf's ring
operations are pointwise, so the whole statement reduces to
`(fⁿ / gⁿ) = (f / g)ⁿ` inside one homogeneous localization.

`ΓSpecIso_inv_appIso_inv` is the one that costs something. The scalar action on the chart's sections
runs `A_{(g)} → Γ(Spec A_{(g)}, ⊤) → Γ(Proj 𝒜, D₊(g))` through `Scheme.ΓSpecIso` and the open
immersion's `Scheme.Hom.appIso`, and nothing in Mathlib says that composite is `awayToSection`. It
is proved here by unfolding `awayι` into `basicOpenIsoSpec.inv ≫ ι` and using
`basicOpenToSpec_app_top`, which is the only place Mathlib pins `awayToSection` against the scheme
structure.

## Elaboration notes

`ΓSpecIso_inv_appIso_inv` needs `backward.isDefEq.respectTransparency false`, as Mathlib's own
`basicOpenIsoAway` does. Without it the goal is reported as "not type-correct under the `instances`
transparency level" after the first rewrite and every later `rw` — including `Category.assoc` —
silently fails to match. With it the associativity normalises and the `reassoc` forms of
`Scheme.Hom.naturality` apply.

Transports between opens of `Proj 𝒜` are collapsed by `Subsingleton.elim`: `Opens` is a poset, so
parallel morphisms are equal and `congrArg presheaf.map` closes what `rw [← Functor.map_comp]`
cannot see through.

## Scope

The dictionary only. The Proj-side restatements of the chart lemmas, the cover, the single
exponent, and the gluing are not here.
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-! ### The structure sheaf's powers, pointwise -/

/-- **A power of a section of the structure sheaf is the pointwise power.**

Mathlib records `Proj.mul_apply` and `Proj.one_apply` but no power law; the ring structure on
sections is pointwise, so this is those two and an induction. -/
theorem structureSheaf_pow_apply {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (n : ℕ)
    (x : U) : (s ^ n).1 x = (s.1 x) ^ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

/-! ### `awayToSection` on the chart's distinguished element -/

/-- **The fraction the chart's distinguished element becomes on `Proj 𝒜`.**

`HomogeneousLocalization.Away.isLocalizationElem hg hf` is `f ^ d / g ^ e` for `f ∈ 𝒜 e` and
`g ∈ 𝒜 d`; this is its `n`-th power as a section of the structure sheaf over any open inside
`D₊(g)`. Named because the degree bookkeeping -- both numerator and denominator sit in
`(e • d) • n` -- is unreadable inline, and `fracSection_eq` turns it into whatever spelling a use
site wants. -/
def isLocalizationFrac {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (n : ℕ)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U) :=
  fracSection 𝒜 (pow_mem_smul 𝒜 (pow_mem_smul 𝒜 hf d) n)
    (pow_mem_smul 𝒜 (SetLike.pow_mem_graded e hg) n)
    (hU.trans ((basicOpen_le_basicOpen_pow 𝒜 g e).trans
      (basicOpen_le_basicOpen_pow 𝒜 (g ^ e) n)))

/-- **The base case, and it is definitional.**

`awayToSection` sends `f ^ d / g ^ e` to the section `x ↦ f ^ d / g ^ e`, by the definition of
`HomogeneousLocalization.mapId` on a representative. -/
theorem awayToSection_isLocalizationElem_apply {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d)
    (x : ProjectiveSpectrum.basicOpen 𝒜 g) :
    ((awayToSection 𝒜 g).hom (HomogeneousLocalization.Away.isLocalizationElem hg hf)).1 x
      = frac 𝒜 (pow_mem_smul 𝒜 hf d) (SetLike.pow_mem_graded e hg)
        (basicOpen_le_basicOpen_pow 𝒜 g e x.2) :=
  rfl

/-- **`awayToSection` carries `(f ^ d / g ^ e) ^ n` to the section of the same name.**

This is the dictionary entry `#585` needs: the chart lemmas clear the away-ring element
`isLocalizationElem hg hf`, and every statement on `Proj 𝒜` is scaled by a `fracSection`. -/
theorem awayToSection_isLocalizationElem_pow {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d)
    (n : ℕ) :
    (awayToSection 𝒜 g).hom (HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n)
      = isLocalizationFrac 𝒜 hf hg n (le_refl _) := by
  refine Subtype.ext (funext fun x => ?_)
  show _ = frac 𝒜 _ _ _
  rw [map_pow, structureSheaf_pow_apply, awayToSection_isLocalizationElem_apply, frac_pow]

/-! ### The chart's structure map is `awayToSection` -/

/-- **A chart of any positive degree covers exactly its own basic open.**

`degreeOneChart_image_top` is the case `d = 1`; `#585`'s pairwise overlaps are cut out by a product
of two degree-one elements, so the degree-two case is needed as well. -/
theorem awayι_image_top {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d) :
    awayι 𝒜 g hg hd ''ᵁ ⊤ = basicOpen 𝒜 g := by
  rw [show (⊤ : (Spec (.of <| HomogeneousLocalization.Away 𝒜 g)).Opens) =
      awayι 𝒜 g hg hd ⁻¹ᵁ ⊤ from rfl,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_top_eq, opensRange_awayι 𝒜 g hg hd]

/-- **A chart meets another basic open in the intersection of the two.**

`degreeOneChart_image_basicOpen` at arbitrary positive degrees, which is what `#585` needs on a
pairwise overlap: the chart is that of `gᵢ gⱼ` and the second element is `f`. -/
theorem awayι_image_basicOpen {d e : ℕ} {a b : A} (hb : b ∈ 𝒜 d) (hd : 0 < d)
    (ha : a ∈ 𝒜 e) (he : 0 < e) :
    awayι 𝒜 b hb hd ''ᵁ
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hb ha) =
      basicOpen 𝒜 b ⊓ basicOpen 𝒜 a := by
  rw [← awayι_preimage_basicOpen 𝒜 hb hd ha he,
    Scheme.Hom.image_preimage_eq_opensRange_inf, opensRange_awayι 𝒜 b hb hd]

/-- **Every open of the chart lands inside `D₊(g)`.** -/
theorem awayι_image_le {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (U : (Spec (chartRing 𝒜 g)).Opens) :
    awayι 𝒜 g hg hd ''ᵁ U ≤ basicOpen 𝒜 g :=
  le_trans (Scheme.Hom.image_mono _ le_top) (le_of_eq (awayι_image_top 𝒜 hg hd))

set_option backward.isDefEq.respectTransparency false in
/-- **The chart's ring map is Mathlib's `awayToSection`.**

The scalar acting on a chart section reaches `Γ(Proj 𝒜, D₊(g))` through `Scheme.ΓSpecIso` and the
open immersion's `Scheme.Hom.appIso`; this says that composite is `awayToSection`, transported
along `degreeOneChart_image_top`.

Proved by unfolding `awayι` into `basicOpenIsoSpec.inv ≫ (basicOpen 𝒜 g).ι` and quoting
`basicOpenToSpec_app_top`, the single place Mathlib pins `awayToSection` against the scheme
structure. Everything else cancels: the two halves of `basicOpenIsoSpec` on the chart, and poset
transports on `Proj 𝒜`. -/
theorem ΓSpecIso_inv_appIso_inv {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (chartRing 𝒜 g)).inv ≫ (Scheme.Hom.appIso (awayι 𝒜 g hg hd) ⊤).inv
      = awayToSection 𝒜 g ≫ (Proj 𝒜).presheaf.map
          (eqToHom (awayι_image_top 𝒜 hg hd)).op := by
  have h1 : Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).hom
      = (Scheme.ΓSpecIso (chartRing 𝒜 g)).hom ≫
        awayToSection 𝒜 g ≫ (basicOpen 𝒜 g).topIso.inv := by
    rw [basicOpenIsoSpec_hom]
    exact basicOpenToSpec_app_top 𝒜 g
  have key : awayToSection 𝒜 g ≫ (basicOpen 𝒜 g).topIso.inv =
      (Scheme.ΓSpecIso (chartRing 𝒜 g)).inv ≫
        Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).hom :=
    (Iso.inv_hom_id_assoc _ _).symm.trans
      (congrArg (fun φ => (Scheme.ΓSpecIso (chartRing 𝒜 g)).inv ≫ φ) h1).symm
  have key' : ∀ {Z : CommRingCat.{u}} (φ : Γ((basicOpen 𝒜 g : (Proj 𝒜).Opens), ⊤) ⟶ Z),
      awayToSection 𝒜 g ≫ (basicOpen 𝒜 g).topIso.inv ≫ φ =
        (Scheme.ΓSpecIso (chartRing 𝒜 g)).inv ≫
          Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).hom ≫ φ := fun φ => by
    rw [← Category.assoc, key, Category.assoc]
  have hcancel : Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).hom ≫
      Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).inv = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  have hcancel' : ∀ {Z : CommRingCat.{u}}
      (φ : Γ(Spec (chartRing 𝒜 g), ⊤) ⟶ Z),
      Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).hom ≫
        Scheme.Hom.appTop (basicOpenIsoSpec 𝒜 g hg hd).inv ≫ φ = φ := fun φ => by
    rw [← Category.assoc, hcancel, Category.id_comp]
  have hself : Scheme.Hom.app (basicOpen 𝒜 g).ι (basicOpen 𝒜 g)
      = (basicOpen 𝒜 g).topIso.inv ≫ (basicOpen 𝒜 g).toScheme.presheaf.map
          (eqToHom (Scheme.Opens.ι_preimage_self (basicOpen 𝒜 g))).op := by
    rw [Scheme.Opens.ι_app_self, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
    exact (congrArg (Proj 𝒜).presheaf.map (Subsingleton.elim _ _)).trans
      ((Proj 𝒜).presheaf.map_comp _ _)
  rw [← cancel_mono (Scheme.Hom.app (awayι 𝒜 g hg hd) (awayι 𝒜 g hg hd ''ᵁ ⊤)),
    Category.assoc, Scheme.Hom.appIso_inv_app, Category.assoc, Scheme.Hom.naturality,
    show Scheme.Hom.app (awayι 𝒜 g hg hd) (basicOpen 𝒜 g)
      = Scheme.Hom.app (basicOpen 𝒜 g).ι (basicOpen 𝒜 g) ≫
        Scheme.Hom.app (basicOpenIsoSpec 𝒜 g hg hd).inv
          ((basicOpen 𝒜 g).ι ⁻¹ᵁ basicOpen 𝒜 g) from rfl,
    hself]
  simp only [Category.assoc]
  rw [Scheme.Hom.naturality_assoc, key', hcancel']
  refine congrArg (fun φ => (Scheme.ΓSpecIso (chartRing 𝒜 g)).inv ≫ φ) ?_
  exact (congrArg (Spec (chartRing 𝒜 g)).presheaf.map
    (Subsingleton.elim _ _)).trans (Functor.map_comp _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- **The chart ring acts through `awayToSection`, over every open of the chart.**

`ΓSpecIso_inv_appIso_inv` is the case `U = ⊤`; `Scheme.Hom.appIso_inv_naturality` spreads it over
the rest, and the two transports on `Proj 𝒜` collapse because `Opens` is a poset. -/
theorem ΓSpecIso_inv_res_appIso_inv {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (U : (Spec (chartRing 𝒜 g)).Opens) :
    (Scheme.ΓSpecIso (chartRing 𝒜 g)).inv ≫
        (Spec (chartRing 𝒜 g)).presheaf.map (homOfLE (le_top (a := U))).op ≫
        (Scheme.Hom.appIso (awayι 𝒜 g hg hd) U).inv
      = awayToSection 𝒜 g ≫
        (Proj 𝒜).presheaf.map (homOfLE (awayι_image_le 𝒜 hg hd U)).op := by
  rw [Scheme.Hom.appIso_inv_naturality, ← Category.assoc, ΓSpecIso_inv_appIso_inv 𝒜 hg hd,
    Category.assoc]
  refine congrArg (fun φ => awayToSection 𝒜 g ≫ φ) ?_
  exact ((Proj 𝒜).presheaf.map_comp _ _).symm.trans
    (congrArg (Proj 𝒜).presheaf.map (Subsingleton.elim _ _))

/-- **The chart's scalar action, rewritten on `Proj 𝒜`.**

The elements are the same on both sides -- `Scheme.Modules.restrictAppIso` is `Iso.refl` -- and
only the acting ring changes: `a : A_{(g)}` acts as the structure-sheaf section
`awayToSection 𝒜 g a`, restricted to the chart's image. -/
theorem chart_smul_eq (F : (Proj 𝒜).Modules) {d : ℕ} {g : A} (hg : g ∈ 𝒜 d) (hd : 0 < d)
    (a : HomogeneousLocalization.Away 𝒜 g) {U : (Spec (chartRing 𝒜 g)).Opens}
    (t : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op U)) :
    a • t = (show Γ(Proj 𝒜, awayι 𝒜 g hg hd ''ᵁ U) from
        ((Proj 𝒜).presheaf.map (homOfLE (awayι_image_le 𝒜 hg hd U)).op).hom
          ((awayToSection 𝒜 g).hom a)) •
      (show Γ(F, awayι 𝒜 g hg hd ''ᵁ U) from t) := by
  have hscalar := congrArg (fun φ : chartRing 𝒜 g ⟶ Γ(Proj 𝒜, awayι 𝒜 g hg hd ''ᵁ U) =>
    φ.hom a) (ΓSpecIso_inv_res_appIso_inv 𝒜 hg hd U)
  exact (Scheme.Modules.restrict_smul_eq (awayι 𝒜 g hg hd) F U _ t).trans
    (congrArg (fun r : Γ(Proj 𝒜, awayι 𝒜 g hg hd ''ᵁ U) =>
      r • (show Γ(F, awayι 𝒜 g hg hd ''ᵁ U) from t)) hscalar)

/-- **The chart's distinguished scalar is `fⁿ / gⁿ` on `Proj 𝒜`.**

`chart_smul_eq` and `awayToSection_isLocalizationElem_pow` together: this is the single lemma the
Proj-side restatements of `ChartExtension.lean` consume. -/
theorem isLocalizationElem_pow_smul_eq (F : (Proj 𝒜).Modules) {d e : ℕ} {f g : A}
    (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 d) (hd : 0 < d) (n : ℕ) {U : (Spec (chartRing 𝒜 g)).Opens}
    (t : (modulesSpecToSheaf.obj (awayRestrict 𝒜 F hg hd)).presheaf.obj (op U)) :
    HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • t
      = (show Γ(Proj 𝒜, awayι 𝒜 g hg hd ''ᵁ U) from
          isLocalizationFrac 𝒜 hf hg n (awayι_image_le 𝒜 hg hd U)) •
        (show Γ(F, awayι 𝒜 g hg hd ''ᵁ U) from t) := by
  refine (chart_smul_eq 𝒜 F hg hd _ t).trans ?_
  refine congrArg (fun r : Γ(Proj 𝒜, awayι 𝒜 g hg hd ''ᵁ U) =>
    r • (show Γ(F, awayι 𝒜 g hg hd ''ᵁ U) from t)) ?_
  rw [awayToSection_isLocalizationElem_pow]
  rfl

end AlgebraicGeometry.Proj
