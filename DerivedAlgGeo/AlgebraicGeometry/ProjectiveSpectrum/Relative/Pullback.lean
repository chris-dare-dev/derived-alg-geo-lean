/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Basic

/-!
# Pullback of a quasi-coherent graded algebra

For a morphism `g : S' ⟶ S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`, given as
`AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData`, this file constructs its pullback
`g^*𝒜` as a quasi-coherent graded `𝒪_{S'}`-algebra.

The carrier asks for the sections over every affine open `U'` of `S'`. They are
`Γ(S', U') ⊗_{Γ(S, U)} 𝒜(U)` only when `g` maps `U'` into an affine open `U` of `S`, so the
sections are glued:

* an *affine pair* `(V', V)` is an affine open `V'` of `S'` and an affine open `V` of `S` with
  `g(V') ⊆ V`; the sources `V'` form a locally directed open cover of `S'`;
* over an affine pair the *local model* is `Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V)`, graded by base change;
  over a refinement it is the base change of the local model along the restriction of `S'`
  (`isPushout_localModelMap`);
* the spectra of the local models glue to a scheme `pullbackSpec` affine over `S'` (Stacks 01LH),
  and the sections of `g^*𝒜` over `U'` are those of `pullbackSpec` over the preimage of `U'`;
* a section has degree `d` if its image in the local model of every affine pair below `U'` has
  degree `d`.

## Main definitions

* `QuasicoherentGradedAlgebraData.AffinePair g`: the affine pairs of `g`, and
  `AffinePair.cover g`, the open cover of `S'` by their sources.
* `QuasicoherentGradedAlgebraData.localModel 𝒜 p`: the local model over an affine pair, with
  `localModelMap` along a refinement.
* `QuasicoherentGradedAlgebraData.pullbackSpec 𝒜 g`: the scheme glued from the spectra of the
  local models, with `pullbackSpecToBase : pullbackSpec 𝒜 g ⟶ S'`.
* `QuasicoherentGradedAlgebraData.chartIso 𝒜 p`: the sections of `pullbackSpec` over the source of
  an affine pair are its local model.
* `QuasicoherentGradedAlgebraData.pullback 𝒜 g`: the pullback `g^*𝒜`.
* `QuasicoherentGradedAlgebraData.pullbackChartHom 𝒜 p`: the graded map
  `𝒜(V) → (g^*𝒜)(V')` of an affine pair `(V', V)`.

## Main results

* `QuasicoherentGradedAlgebraData.isPushout_localModelMap`: the local models are compatible
  under refinement.
* `QuasicoherentGradedAlgebraData.localModel_ext` and `mem_localGrading_of_forall`: elements and
  degrees in a local model are determined on a cover by refinements.
* `QuasicoherentGradedAlgebraData.isInternal_pullbackGrading`: the degree-`d` sections form a
  direct sum decomposition.
* `QuasicoherentGradedAlgebraData.isPushout_pullbackChartHom`: over the source of an affine pair
  `(V', V)`, `(g^*𝒜)(V')` is the pushout `Γ(S', V') ⊔_{Γ(S, V)} 𝒜(V)`.

## Implementation notes

Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.comap` defines a pullback of affine-local data
geometrically, as the kernel of `𝒪_{S'}` onto a fibre product. A graded algebra is not a quotient
of `𝒪_S`, so the pullback is glued instead, and the relative spectrum `pullbackSpec` supplies the
sheaf condition and the localization field: the preimage of an affine open is affine.

That the degree-`d` sections form a grading is a gluing argument. The degree-`d` component of a
section is glued from the degree-`d` components of its images in the local models
(`exists_component`), and only finitely many components are nonzero because an affine open is
quasi-compact.

`pullback` is not compared with a pullback of module sheaves, and `(sym E).pullback g` is not
identified with `sym (g^*E)`.

## References

* [Stacks, Lemma 17.10.4 (Tag 01BG)](https://stacks.math.columbia.edu/tag/01BG): the pullback of a
  quasi-coherent module is quasi-coherent.
* [Stacks, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH): the relative gluing of
  `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

## Tags

pullback, base change, quasi-coherent graded algebra, relative spectrum, gluing
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData

open AffineZariskiSite

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- An affine open `V'` of `S'` together with an affine open `V` of `S` with `g(V') ⊆ V`. These
index the charts of the pullback of a quasi-coherent graded algebra along `g`. -/
structure AffinePair where
  /-- The affine open `V'` of `S'`. -/
  src : S'.AffineZariskiSite
  /-- An affine open `V` of `S` containing `g(V')`. -/
  tgt : S.AffineZariskiSite
  le_preimage : src.toOpens ≤ g ⁻¹ᵁ tgt.toOpens

namespace AffinePair

variable {g}

/-- `q ≤ p` when the source and target of `q` are basic opens of those of `p`. -/
instance : Preorder (AffinePair g) where
  le q p := q.src ≤ p.src ∧ q.tgt ≤ p.tgt
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem src_le {p q : AffinePair g} (h : q ≤ p) : q.src ≤ p.src := h.1

theorem tgt_le {p q : AffinePair g} (h : q ≤ p) : q.tgt ≤ p.tgt := h.2

/-- Every point of `S'` lies in the source of an affine pair. -/
theorem exists_mem (x : S') : ∃ p : AffinePair g, x ∈ p.src.toOpens := by
  obtain ⟨V, hV⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top S).ge (Set.mem_univ (g x)))
  obtain ⟨V', hV'⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top S').ge (Set.mem_univ x))
  obtain ⟨f, hf, hxf⟩ := V'.2.exists_basicOpen_le (V := g ⁻¹ᵁ V.1) ⟨x, hV⟩ hV'
  exact ⟨⟨AffineZariskiSite.basicOpen ⟨V'.1, V'.2⟩ f, ⟨V.1, V.2⟩, hf⟩, hxf⟩

/-- Two affine pairs whose sources contain `x` have a common refinement whose source
contains `x`. -/
theorem exists_le_le (p q : AffinePair g) (x : S') (hp : x ∈ p.src.toOpens)
    (hq : x ∈ q.src.toOpens) : ∃ r : AffinePair g, r ≤ p ∧ r ≤ q ∧ x ∈ r.src.toOpens := by
  obtain ⟨a, b, hab, hgx⟩ := exists_basicOpen_le_affine_inter p.tgt.2 q.tgt.2 (g x)
    ⟨p.le_preimage hp, q.le_preimage hq⟩
  obtain ⟨c, d, hcd, hxc⟩ := exists_basicOpen_le_affine_inter p.src.2 q.src.2 x ⟨hp, hq⟩
  obtain ⟨e, he, hxe⟩ := (p.src.basicOpen c).2.exists_basicOpen_le
    (V := g ⁻¹ᵁ S.basicOpen a) ⟨x, hgx⟩ hxc
  have hsrc : p.src.basicOpen c = q.src.basicOpen d := Subtype.ext hcd
  have htgt : p.tgt.basicOpen a = q.tgt.basicOpen b := Subtype.ext hab
  refine ⟨⟨(p.src.basicOpen c).basicOpen e, p.tgt.basicOpen a, he⟩,
    ⟨(AffineZariskiSite.basicOpen_le _ e).trans (AffineZariskiSite.basicOpen_le _ c),
      AffineZariskiSite.basicOpen_le _ a⟩,
    ⟨(AffineZariskiSite.basicOpen_le _ e).trans
        (hsrc.le.trans (AffineZariskiSite.basicOpen_le _ d)),
      htgt.le.trans (AffineZariskiSite.basicOpen_le _ b)⟩, hxe⟩

variable (g) in
/-- The sources of the affine pairs of `g`, as an open cover of `S'`. -/
@[simps] abbrev cover : S'.OpenCover where
  I₀ := AffinePair g
  X p := p.src.toOpens
  f p := p.src.toOpens.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨p, hp⟩ := exists_mem (g := g) x
    exact ⟨p, ⟨x, hp⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (cover g).LocallyDirected where
  trans {q p} h := S'.homOfLE (toOpens_mono (src_le (leOfHom h)))
  directed {p q} x := by
    let a := (pullback.fst _ _ ≫ p.src.toOpens.ι) x
    have hap : a ∈ p.src.toOpens := (pullback.fst p.src.toOpens.ι q.src.toOpens.ι x).2
    have haq : a ∈ q.src.toOpens := by
      unfold a
      rw [pullback.condition]
      exact (pullback.snd p.src.toOpens.ι q.src.toOpens.ι x).2
    obtain ⟨r, hrp, hrq, har⟩ := exists_le_le p q a hap haq
    refine ⟨r, homOfLE hrp, homOfLE hrq, ⟨a, har⟩, ?_⟩
    apply (pullback.fst _ _ ≫ p.src.toOpens.ι).isOpenEmbedding.injective
    dsimp
    change (pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ p.src.toOpens.ι) _ = _
    simp only [pullback.lift_fst_assoc, homOfLE_ι, Opens.ι_apply]
    rfl

/-- `Γ(S', V')`, as a `Γ(S, V)`-algebra through `g`, for an affine pair `(V', V)`. -/
abbrev Sections (p : AffinePair g) : Type u := Γ(S', p.src.toOpens)

noncomputable instance (p : AffinePair g) : Algebra Γ(S, p.tgt.toOpens) p.Sections :=
  (g.appLE p.tgt.toOpens p.src.toOpens p.le_preimage).hom.toAlgebra

theorem algebraMap_sections (p : AffinePair g) (r : Γ(S, p.tgt.toOpens)) :
    algebraMap Γ(S, p.tgt.toOpens) p.Sections r =
      g.appLE p.tgt.toOpens p.src.toOpens p.le_preimage r :=
  rfl

/-- The restriction `Γ(S', V'_p) → Γ(S', V'_q)` for `q ≤ p`. -/
noncomputable def sectionsMap {p q : AffinePair g} (h : q ≤ p) : p.Sections →+* q.Sections :=
  (S'.presheaf.map (homOfLE (toOpens_mono (src_le h))).op).hom

theorem sectionsMap_algebraMap {p q : AffinePair g} (h : q ≤ p) (r : Γ(S, p.tgt.toOpens)) :
    sectionsMap h (algebraMap _ _ r) =
      algebraMap Γ(S, q.tgt.toOpens) q.Sections
        (S.presheaf.map (homOfLE (toOpens_mono (tgt_le h))).op r) := by
  change (g.appLE _ _ _ ≫ S'.presheaf.map _) r = (S.presheaf.map _ ≫ g.appLE _ _ _) r
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

end AffinePair

variable (𝒜 : S.QuasicoherentGradedAlgebraData) {g}

/-- The local model `Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V)` of the pullback over an affine pair `(V', V)`. -/
abbrev localModel (p : AffinePair g) : Type u :=
  p.Sections ⊗[Γ(S, p.tgt.toOpens)] 𝒜.carrier p.tgt

/-- The local model is the pushout `Γ(S', V') ⊔_{Γ(S, V)} 𝒜(V)`. -/
theorem isPushout_localModel (p : AffinePair g) :
    IsPushout (CommRingCat.ofHom (algebraMap Γ(S, p.tgt.toOpens) p.Sections))
      (CommRingCat.ofHom (algebraMap Γ(S, p.tgt.toOpens) (𝒜.carrier p.tgt)))
      (CommRingCat.ofHom (S := 𝒜.localModel p) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := 𝒜.localModel p) Algebra.TensorProduct.includeRight.toRingHom) :=
  CommRingCat.isPushout_tensorProduct _ _ _

/-- `Γ(S', V'_p) → Γ(S', V'_q) → Γ(S', V'_q) ⊗ 𝒜(V_q)`. -/
private noncomputable def localModelMapLeft {p q : AffinePair g} (h : q ≤ p) :
    CommRingCat.of p.Sections ⟶ CommRingCat.of (𝒜.localModel q) :=
  CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom (R := Γ(S, q.tgt.toOpens))
    (A := q.Sections) (B := 𝒜.carrier q.tgt)).comp (AffinePair.sectionsMap h))

/-- `𝒜(V_p) → 𝒜(V_q) → Γ(S', V'_q) ⊗ 𝒜(V_q)`. -/
private noncomputable def localModelMapRight {p q : AffinePair g} (h : q ≤ p) :
    CommRingCat.of (𝒜.carrier p.tgt) ⟶ CommRingCat.of (𝒜.localModel q) :=
  CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := Γ(S, q.tgt.toOpens))
    (A := q.Sections) (B := 𝒜.carrier q.tgt)).toRingHom.comp
      (𝒜.restrict (AffinePair.tgt_le h)).toRingHom)

private lemma localModelMap_w {p q : AffinePair g} (h : q ≤ p) :
    CommRingCat.ofHom (algebraMap Γ(S, p.tgt.toOpens) p.Sections) ≫ 𝒜.localModelMapLeft h =
      CommRingCat.ofHom (algebraMap Γ(S, p.tgt.toOpens) (𝒜.carrier p.tgt)) ≫
        𝒜.localModelMapRight h := by
  ext r
  change AffinePair.sectionsMap h (algebraMap _ _ r) ⊗ₜ[Γ(S, q.tgt.toOpens)]
      (1 : 𝒜.carrier q.tgt) = (1 : q.Sections) ⊗ₜ 𝒜.restrict _ (algebraMap _ _ r)
  rw [AffinePair.sectionsMap_algebraMap, 𝒜.restrict_algebraMap,
    Algebra.TensorProduct.tmul_one_eq_one_tmul]

/-- The transition map `Γ(S', V'_p) ⊗ 𝒜(V_p) → Γ(S', V'_q) ⊗ 𝒜(V_q)` for `q ≤ p`. -/
noncomputable def localModelMap {p q : AffinePair g} (h : q ≤ p) :
    𝒜.localModel p →+* 𝒜.localModel q :=
  ((𝒜.isPushout_localModel p).desc (𝒜.localModelMapLeft h) (𝒜.localModelMapRight h)
    (𝒜.localModelMap_w h)).hom

@[simp]
theorem localModelMap_tmul {p q : AffinePair g} (h : q ≤ p) (x : p.Sections)
    (a : 𝒜.carrier p.tgt) :
    𝒜.localModelMap h (x ⊗ₜ a) =
      AffinePair.sectionsMap h x ⊗ₜ 𝒜.restrict (AffinePair.tgt_le h) a := by
  have hx := congr($((𝒜.isPushout_localModel p).inl_desc (𝒜.localModelMapLeft h)
    (𝒜.localModelMapRight h) (𝒜.localModelMap_w h)).hom x)
  have ha := congr($((𝒜.isPushout_localModel p).inr_desc (𝒜.localModelMapLeft h)
    (𝒜.localModelMapRight h) (𝒜.localModelMap_w h)).hom a)
  have : x ⊗ₜ[Γ(S, p.tgt.toOpens)] a = (x ⊗ₜ 1) * (1 ⊗ₜ a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [localModelMap, this, map_mul]
  erw [hx, ha]
  change (AffinePair.sectionsMap h x ⊗ₜ 1) * (1 ⊗ₜ 𝒜.restrict _ a) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem localModelMap_id (p : AffinePair g) (x : 𝒜.localModel p) :
    𝒜.localModelMap (le_refl p) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul y a =>
    rw [localModelMap_tmul, 𝒜.restrict_id]
    congr 1
    change S'.presheaf.map (𝟙 _) y = y
    rw [CategoryTheory.Functor.map_id]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem localModelMap_comp {p q r : AffinePair g} (hqp : q ≤ p) (hrq : r ≤ q)
    (x : 𝒜.localModel p) :
    𝒜.localModelMap hrq (𝒜.localModelMap hqp x) = 𝒜.localModelMap (hrq.trans hqp) x := by
  induction x using TensorProduct.inductionOn with
  | tmul y a =>
    rw [localModelMap_tmul, localModelMap_tmul, localModelMap_tmul, 𝒜.restrict_comp]
    congr 1
    change (S'.presheaf.map _ ≫ S'.presheaf.map _) y = S'.presheaf.map _ y
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The grading `Γ(S', V') ⊗ 𝒜(V)_d` of the local model. -/
noncomputable abbrev localGrading (p : AffinePair g) (d : ℕ) :
    Submodule p.Sections (𝒜.localModel p) :=
  (𝒜.grading p.tgt d).baseChange p.Sections

theorem localModelMap_mem {p q : AffinePair g} (h : q ≤ p) {d : ℕ} {x : 𝒜.localModel p}
    (hx : x ∈ 𝒜.localGrading p d) : 𝒜.localModelMap h x ∈ 𝒜.localGrading q d := by
  rw [localGrading, Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [TensorProduct.mk_apply, localModelMap_tmul, map_one]
    exact Submodule.tmul_mem_baseChange_of_mem _ ((𝒜.restrict _).map_mem ha)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    have hc : 𝒜.localModelMap h (algebraMap p.Sections (𝒜.localModel p) c) =
        algebraMap q.Sections (𝒜.localModel q) (AffinePair.sectionsMap h c) := by
      change 𝒜.localModelMap h (c ⊗ₜ 1) = AffinePair.sectionsMap h c ⊗ₜ 1
      rw [localModelMap_tmul, map_one]
    rw [Algebra.smul_def, map_mul, hc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hy

/-- The transition map, as a graded ring map. -/
noncomputable def localModelGradedMap {p q : AffinePair g} (h : q ≤ p) :
    𝒜.localGrading p →+*ᵍ 𝒜.localGrading q where
  toRingHom := 𝒜.localModelMap h
  map_mem := 𝒜.localModelMap_mem h

/-- Over a basic open `V` of an affine open `U` of `S`, the square
`Γ(S, U) → Γ(S, V)`, `𝒜(U) → 𝒜(V)` is a pushout of rings. -/
theorem isPushout_restrict {U V : S.AffineZariskiSite} (h : V ≤ U) :
    IsPushout (S.presheaf.map (homOfLE (toOpens_mono h)).op)
      (CommRingCat.ofHom (algebraMap Γ(S, U.toOpens) (𝒜.carrier U)))
      (CommRingCat.ofHom (algebraMap Γ(S, V.toOpens) (𝒜.carrier V)))
      (CommRingCat.ofHom (𝒜.restrict h).toRingHom) := by
  obtain ⟨f, hf⟩ := id h
  obtain rfl : U.basicOpen f = V := Subtype.ext hf
  let _ : Algebra (𝒜.carrier U) (𝒜.carrier (U.basicOpen f)) :=
    (𝒜.restrict (U.basicOpen_le f)).toRingHom.toAlgebra
  let _ : Algebra Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens) :=
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom.toAlgebra
  let _ : Algebra Γ(S, U.toOpens) (𝒜.carrier (U.basicOpen f)) :=
    ((algebraMap Γ(S, (U.basicOpen f).toOpens) (𝒜.carrier (U.basicOpen f))).comp
      (algebraMap Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens))).toAlgebra
  have : IsScalarTower Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens)
      (𝒜.carrier (U.basicOpen f)) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, U.toOpens) (𝒜.carrier U) (𝒜.carrier (U.basicOpen f)) :=
    .of_algebraMap_eq fun r ↦ (𝒜.restrict_algebraMap (U.basicOpen_le f) r).symm
  have : IsLocalization.Away f Γ(S, (U.basicOpen f).toOpens) := U.2.isLocalization_basicOpen f
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝒜.carrier U) (Submonoid.powers f))
      (𝒜.carrier (U.basicOpen f)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact 𝒜.isLocalization_basicOpen U f
  have : Algebra.IsPushout Γ(S, U.toOpens) Γ(S, (U.basicOpen f).toOpens) (𝒜.carrier U)
      (𝒜.carrier (U.basicOpen f)) :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers f) Γ(S, (U.basicOpen f).toOpens)
      (𝒜.carrier U) (𝒜.carrier (U.basicOpen f))).symm
  exact CommRingCat.isPushout_of_isPushout _ _ _ _

/-- **The local models are compatible**: for `q ≤ p`, the local model over `q` is the base change
of the local model over `p` along `Γ(S', V'_p) → Γ(S', V'_q)`. -/
theorem isPushout_localModelMap {p q : AffinePair g} (h : q ≤ p) :
    IsPushout (CommRingCat.ofHom (AffinePair.sectionsMap h))
      (CommRingCat.ofHom (S := 𝒜.localModel p) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := 𝒜.localModel q) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (𝒜.localModelMap h)) := by
  have hL := 𝒜.isPushout_restrict (AffinePair.tgt_le h)
  have hout := hL.paste_horiz (𝒜.isPushout_localModel q)
  refine IsPushout.of_left ?_ ?_ (𝒜.isPushout_localModel p)
  · convert hout using 1
    · ext r
      exact (AffinePair.sectionsMap_algebraMap h r)
    · ext a
      change 𝒜.localModelMap h (1 ⊗ₜ a) = 1 ⊗ₜ 𝒜.restrict _ a
      rw [localModelMap_tmul, map_one]
  · ext x
    change AffinePair.sectionsMap h x ⊗ₜ 1 = 𝒜.localModelMap h (x ⊗ₜ 1)
    rw [localModelMap_tmul, map_one]

namespace AffinePair

variable (g) in
/-- The source of an affine pair, as a functor to the affine Zariski site of `S'`. -/
abbrev srcFunctor : AffinePair g ⥤ S'.AffineZariskiSite :=
  Monotone.functor (f := AffinePair.src) fun _ _ h ↦ src_le h

variable (g) in
/-- The sections `Γ(S', V')` over the sources of affine pairs, as a functor. -/
abbrev sectionsFunctor : (AffinePair g)ᵒᵖ ⥤ CommRingCat.{u} :=
  (srcFunctor g ⋙ toOpensFunctor S').op ⋙ S'.presheaf

end AffinePair

variable (g) in
/-- The local models `Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V)`, as a functor on the affine pairs. -/
@[simps]
noncomputable def localModelFunctor : (AffinePair g)ᵒᵖ ⥤ CommRingCat.{u} where
  obj p := CommRingCat.of (𝒜.localModel p.unop)
  map f := CommRingCat.ofHom (𝒜.localModelMap (leOfHom f.unop))
  map_id p := CommRingCat.hom_ext (RingHom.ext fun x ↦ 𝒜.localModelMap_id p.unop x)
  map_comp _ _ :=
    CommRingCat.hom_ext (RingHom.ext fun x ↦ (𝒜.localModelMap_comp _ _ x).symm)

variable (g) in
/-- The structure maps `Γ(S', V') → Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V)`. -/
@[simps]
noncomputable def localModelι : AffinePair.sectionsFunctor g ⟶ 𝒜.localModelFunctor g where
  app p := CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
    (R := Γ(S, p.unop.tgt.toOpens)) (A := p.unop.Sections) (B := 𝒜.carrier p.unop.tgt))
  naturality {p q} f := by
    ext x
    have := 𝒜.localModelMap_tmul (leOfHom f.unop) x 1
    rw [map_one] at this
    exact this.symm

theorem coequifibered_localModelι : NatTrans.Coequifibered (𝒜.localModelι g) :=
  fun _ _ f ↦ 𝒜.isPushout_localModelMap (leOfHom f.unop)

variable (g) in
/-- The relative gluing datum of the spectra `Spec (Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V))` over the cover
of `S'` by the sources of affine pairs (Stacks 01LH). -/
noncomputable def gluingData : (AffinePair.cover g).RelativeGluingData where
  functor := (𝒜.localModelFunctor g).rightOp ⋙ Scheme.Spec
  natTrans := Functor.whiskerRight (𝒜.localModelι g).rightOp Scheme.Spec ≫
    (Functor.isoWhiskerLeft (AffinePair.srcFunctor g) (restrictIsoSpec S')).inv
  equifibered := ((𝒜.coequifibered_localModelι (g := g)).rightOp.whiskerRight _).comp
    (NatTrans.Equifibered.of_isIso
      (Functor.isoWhiskerLeft (AffinePair.srcFunctor g) (restrictIsoSpec S')).inv)

instance : ((𝒜.gluingData g).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

variable (g) in
/-- The relative spectrum of the pullback of `𝒜` along `g`, glued from the spectra of the local
models. -/
noncomputable def pullbackSpec : Scheme.{u} :=
  (𝒜.gluingData g).glued

variable (g) in
/-- The structure morphism of `pullbackSpec` to `S'`. -/
noncomputable def pullbackSpecToBase : 𝒜.pullbackSpec g ⟶ S' :=
  (𝒜.gluingData g).toBase

/-- The chart `Spec (Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V)) → pullbackSpec` over an affine pair. -/
noncomputable def pullbackSpecι (p : AffinePair g) :
    Spec (CommRingCat.of (𝒜.localModel p)) ⟶ 𝒜.pullbackSpec g :=
  colimit.ι (𝒜.gluingData g).functor p

instance (p : AffinePair g) : IsOpenImmersion (𝒜.pullbackSpecι p) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (𝒜.gluingData g).functor p))

@[reassoc (attr := simp)]
theorem pullbackSpecι_toBase (p : AffinePair g) :
    𝒜.pullbackSpecι p ≫ 𝒜.pullbackSpecToBase g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Γ(S, p.tgt.toOpens)) (A := p.Sections) (B := 𝒜.carrier p.tgt))) ≫
        p.src.2.fromSpec := by
  refine ((𝒜.gluingData g).ι_toBase p).trans ?_
  change (Spec.map _ ≫ p.src.2.isoSpec.inv) ≫ p.src.toOpens.ι = _
  rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  rfl

theorem opensRange_pullbackSpecι (p : AffinePair g) :
    (𝒜.pullbackSpecι p).opensRange = 𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens := by
  have := (𝒜.gluingData g).toBase_preimage_eq_opensRange_ι p
  simp only [Opens.opensRange_ι] at this
  exact this.symm

theorem isPullback_pullbackSpecι (p : AffinePair g) :
    IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Γ(S, p.tgt.toOpens)) (A := p.Sections) (B := 𝒜.carrier p.tgt))) ≫
        p.src.2.isoSpec.inv) (𝒜.pullbackSpecι p) p.src.toOpens.ι (𝒜.pullbackSpecToBase g) :=
  (𝒜.gluingData g).isPullback_natTrans_ι_toBase p

set_option backward.isDefEq.respectTransparency false in
/-- `pullbackSpec` is affine over `S'`: over the source of an affine pair it is the spectrum of
the local model. -/
instance : IsAffineHom (𝒜.pullbackSpecToBase g) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom) (AffinePair.cover g)
    fun p ↦ ?_
  have h := (𝒜.isPullback_pullbackSpecι p).flip
  have : IsAffineHom (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := Γ(S, p.tgt.toOpens)) (A := p.Sections) (B := 𝒜.carrier p.tgt))) ≫
        p.src.2.isoSpec.inv) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk h.isoPullback (Iso.refl _)
    (by simp [Cover.pullbackHom]))).mp this

theorem top_le_preimage_pullbackSpecι (p : AffinePair g) :
    ⊤ ≤ 𝒜.pullbackSpecι p ⁻¹ᵁ (𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens) := by
  rw [← opensRange_pullbackSpecι, Scheme.Hom.preimage_opensRange]

instance (p : AffinePair g) : IsIso ((𝒜.pullbackSpecι p).appLE
    (𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens) ⊤ (𝒜.top_le_preimage_pullbackSpecι p)) := by
  have hi : 𝒜.pullbackSpecι p ''ᵁ ⊤ = 𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens := by
    rw [Scheme.Hom.image_top_eq_opensRange, opensRange_pullbackSpecι]
  rw [← Scheme.Hom.map_appLE' _ _ hi, ← Scheme.Hom.appIso_hom']
  infer_instance

private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- The sections of `pullbackSpec` over the source of an affine pair are the local model. -/
noncomputable def chartIso (p : AffinePair g) :
    Γ(𝒜.pullbackSpec g, 𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens) ≅
      CommRingCat.of (𝒜.localModel p) :=
  asIso ((𝒜.pullbackSpecι p).appLE _ ⊤ (𝒜.top_le_preimage_pullbackSpecι p)) ≪≫
    Scheme.ΓSpecIso _

private lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chart isomorphism sends a section `a` of `S'` to `a ⊗ 1`. -/
theorem chartIso_hom_app (p : AffinePair g) (a : Γ(S', p.src.toOpens)) :
    (𝒜.chartIso p).hom ((𝒜.pullbackSpecToBase g).app p.src.toOpens a) =
      (a : p.Sections) ⊗ₜ (1 : 𝒜.carrier p.tgt) := by
  rw [← ConcreteCategory.comp_apply, chartIso, Iso.trans_hom, asIso_hom, ← Category.assoc,
    ← Scheme.Hom.comp_appLE, appLE_eq_of_eq (𝒜.pullbackSpecι_toBase p), Scheme.Hom.comp_appLE,
    IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc, Scheme.Hom.map_appLE_assoc,
    appLE_top_top, Scheme.ΓSpecIso_naturality]
  change Algebra.TensorProduct.includeLeftRingHom
    (((Scheme.ΓSpecIso Γ(S', p.src.toOpens)).inv ≫
      (Scheme.ΓSpecIso Γ(S', p.src.toOpens)).hom) a) = _
  rw [Iso.inv_hom_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chart isomorphisms intertwine restriction with the transition maps of the local
models. -/
theorem chartIso_hom_map {p q : AffinePair g} (h : q ≤ p)
    (x : Γ(𝒜.pullbackSpec g, 𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens)) :
    (𝒜.chartIso q).hom ((𝒜.pullbackSpec g).presheaf.map
        (homOfLE ((𝒜.pullbackSpecToBase g).preimage_mono
          (toOpens_mono (AffinePair.src_le h)))).op x) =
      𝒜.localModelMap h ((𝒜.chartIso p).hom x) := by
  have hw : Spec.map (CommRingCat.ofHom (𝒜.localModelMap h)) ≫ 𝒜.pullbackSpecι p =
      𝒜.pullbackSpecι q :=
    colimit.w (𝒜.gluingData g).functor (homOfLE h)
  have key : (Spec.map (CommRingCat.ofHom (𝒜.localModelMap h))).appLE
      (𝒜.pullbackSpecι p ⁻¹ᵁ (𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens)) ⊤
        ((Spec.map _).preimage_mono (𝒜.top_le_preimage_pullbackSpecι p)) =
      (Spec (CommRingCat.of (𝒜.localModel p))).presheaf.map
        (homOfLE (𝒜.top_le_preimage_pullbackSpecι p)).op ≫
        (Spec.map (CommRingCat.ofHom (𝒜.localModelMap h))).appTop := by
    rw [← appLE_top_top _ le_top, Scheme.Hom.map_appLE]
  rw [← ConcreteCategory.comp_apply, chartIso, chartIso, Iso.trans_hom, Iso.trans_hom, asIso_hom,
    asIso_hom, Scheme.Hom.map_appLE_assoc, appLE_eq_of_eq hw.symm, Scheme.Hom.comp_appLE, key,
    Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

/-! ### Sections over affine opens -/

variable (g) in
/-- The sections `Γ(S', U', g^*𝒜)` over an affine open `U'` of `S'`: the sections of
`pullbackSpec` over the preimage of `U'`. -/
noncomputable abbrev pullbackSections (U' : S'.AffineZariskiSite) : CommRingCat.{u} :=
  Γ(𝒜.pullbackSpec g, 𝒜.pullbackSpecToBase g ⁻¹ᵁ U'.toOpens)

noncomputable instance (U' : S'.AffineZariskiSite) :
    Algebra Γ(S', U'.toOpens) (𝒜.pullbackSections g U') :=
  ((𝒜.pullbackSpecToBase g).app U'.toOpens).hom.toAlgebra

/-- Restriction of sections of `pullbackSpec` to a smaller affine open. -/
noncomputable def pullbackRes {U' V' : S'.AffineZariskiSite} (h : V' ≤ U') :
    𝒜.pullbackSections g U' →+* 𝒜.pullbackSections g V' :=
  ((𝒜.pullbackSpec g).presheaf.map
    (homOfLE ((𝒜.pullbackSpecToBase g).preimage_mono (toOpens_mono h))).op).hom

theorem pullbackRes_id (U' : S'.AffineZariskiSite) (x : 𝒜.pullbackSections g U') :
    𝒜.pullbackRes (le_refl U') x = x := by
  change (𝒜.pullbackSpec g).presheaf.map (𝟙 _) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem pullbackRes_comp {U' V' W' : S'.AffineZariskiSite} (hVU : V' ≤ U') (hWV : W' ≤ V')
    (x : 𝒜.pullbackSections g U') :
    𝒜.pullbackRes hWV (𝒜.pullbackRes hVU x) = 𝒜.pullbackRes (hWV.trans hVU) x := by
  change ((𝒜.pullbackSpec g).presheaf.map _ ≫ (𝒜.pullbackSpec g).presheaf.map _) x = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem pullbackRes_algebraMap {U' V' : S'.AffineZariskiSite} (h : V' ≤ U')
    (r : Γ(S', U'.toOpens)) :
    𝒜.pullbackRes h (algebraMap _ _ r) =
      algebraMap Γ(S', V'.toOpens) (𝒜.pullbackSections g V')
        (S'.presheaf.map (homOfLE (toOpens_mono h)).op r) := by
  change ((𝒜.pullbackSpecToBase g).app _ ≫ (𝒜.pullbackSpec g).presheaf.map _) r =
    (S'.presheaf.map _ ≫ (𝒜.pullbackSpecToBase g).app _) r
  rw [Scheme.Hom.naturality]
  rfl

/-- The local model of an affine pair `p` below `U'`, reached from the sections over `U'`. -/
noncomputable def chartRes {U' : S'.AffineZariskiSite} (p : AffinePair g) (hp : p.src ≤ U') :
    𝒜.pullbackSections g U' →+* 𝒜.localModel p :=
  (𝒜.chartIso p).hom.hom.comp (𝒜.pullbackRes hp)

theorem chartRes_pullbackRes {U' V' : S'.AffineZariskiSite} (h : V' ≤ U') (p : AffinePair g)
    (hp : p.src ≤ V') (x : 𝒜.pullbackSections g U') :
    𝒜.chartRes p hp (𝒜.pullbackRes h x) = 𝒜.chartRes p (hp.trans h) x := by
  rw [chartRes, RingHom.comp_apply, pullbackRes_comp]
  rfl

theorem chartRes_le {U' : S'.AffineZariskiSite} {p q : AffinePair g} (h : q ≤ p)
    (hp : p.src ≤ U') (x : 𝒜.pullbackSections g U') :
    𝒜.chartRes q ((AffinePair.src_le h).trans hp) x = 𝒜.localModelMap h (𝒜.chartRes p hp x) := by
  rw [chartRes, chartRes, RingHom.comp_apply, RingHom.comp_apply, ← pullbackRes_comp _ hp
    (AffinePair.src_le h)]
  exact 𝒜.chartIso_hom_map h _

theorem chartRes_algebraMap {U' : S'.AffineZariskiSite} (p : AffinePair g) (hp : p.src ≤ U')
    (r : Γ(S', U'.toOpens)) :
    𝒜.chartRes p hp (algebraMap _ _ r) =
      ((S'.presheaf.map (homOfLE (toOpens_mono hp)).op r : Γ(S', p.src.toOpens)) : p.Sections)
        ⊗ₜ (1 : 𝒜.carrier p.tgt) := by
  rw [chartRes, RingHom.comp_apply, pullbackRes_algebraMap]
  exact 𝒜.chartIso_hom_app p _

/-- Every point of an affine open `U'` of `S'` lies in the source of an affine pair whose
source is a basic open of `U'`. -/
theorem AffinePair.exists_le_mem
    (U' : S'.AffineZariskiSite) (x : S') (hx : x ∈ U'.toOpens) :
    ∃ p : AffinePair g, p.src ≤ U' ∧ x ∈ p.src.toOpens := by
  obtain ⟨V, hV⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top S).ge (Set.mem_univ (g x)))
  obtain ⟨f, hf, hxf⟩ := U'.2.exists_basicOpen_le (V := g ⁻¹ᵁ V.1) ⟨x, hV⟩ hx
  exact ⟨⟨U'.basicOpen f, ⟨V.1, V.2⟩, hf⟩, U'.basicOpen_le f, hxf⟩

/-- **Separation**: sections over `U'` that agree on the local models of a family of affine pairs
covering `U'` are equal. -/
theorem pullbackSections_ext {U' : S'.AffineZariskiSite} {ι : Type*} (P : ι → AffinePair g)
    (hP : ∀ i, (P i).src ≤ U') (hcov : ∀ x ∈ U'.toOpens, ∃ i, x ∈ (P i).src.toOpens)
    {s t : 𝒜.pullbackSections g U'} (h : ∀ i, 𝒜.chartRes (P i) (hP i) s =
      𝒜.chartRes (P i) (hP i) t) : s = t := by
  refine (𝒜.pullbackSpec g).sheaf.eq_of_locally_eq'
    (fun i ↦ 𝒜.pullbackSpecToBase g ⁻¹ᵁ (P i).src.toOpens)
    (𝒜.pullbackSpecToBase g ⁻¹ᵁ U'.toOpens)
    (fun i ↦ homOfLE ((𝒜.pullbackSpecToBase g).preimage_mono (toOpens_mono (hP i)))) ?_ s t
    fun i ↦ (𝒜.chartIso (P i)).commRingCatIsoToRingEquiv.injective (h i)
  intro x hx
  obtain ⟨i, hi⟩ := hcov _ hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem chartRes_self (q : AffinePair g) (y : 𝒜.pullbackSections g q.src) :
    𝒜.chartRes q (le_refl q.src) y = (𝒜.chartIso q).hom y := by
  rw [chartRes, RingHom.comp_apply, pullbackRes_id]

theorem chartIso_hom_map' {p q : AffinePair g} (h : q ≤ p)
    (i : 𝒜.pullbackSpecToBase g ⁻¹ᵁ q.src.toOpens ⟶ 𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens)
    (x : Γ(𝒜.pullbackSpec g, 𝒜.pullbackSpecToBase g ⁻¹ᵁ p.src.toOpens)) :
    (𝒜.chartIso q).hom ((𝒜.pullbackSpec g).presheaf.map i.op x) =
      𝒜.localModelMap h ((𝒜.chartIso p).hom x) := by
  obtain rfl : i = homOfLE ((𝒜.pullbackSpecToBase g).preimage_mono
    (toOpens_mono (AffinePair.src_le h))) := Subsingleton.elim _ _
  exact 𝒜.chartIso_hom_map h x

/-- **Separation in a local model**: elements of the local model of `q` that agree on the local
models of a family of refinements covering the source of `q` are equal. -/
theorem localModel_ext {q : AffinePair g} {ι : Type*} (P : ι → AffinePair g)
    (hP : ∀ i, P i ≤ q) (hcov : ∀ x ∈ q.src.toOpens, ∃ i, x ∈ (P i).src.toOpens)
    {z w : 𝒜.localModel q}
    (h : ∀ i, 𝒜.localModelMap (hP i) z = 𝒜.localModelMap (hP i) w) : z = w := by
  let e := (𝒜.chartIso q).commRingCatIsoToRingEquiv
  obtain ⟨y, rfl⟩ := e.surjective z
  obtain ⟨y', rfl⟩ := e.surjective w
  congr 1
  refine 𝒜.pullbackSections_ext P (fun i ↦ AffinePair.src_le (hP i)) hcov fun i ↦ ?_
  have h1 := 𝒜.chartRes_le (hP i) (le_refl q.src) y
  have h2 := 𝒜.chartRes_le (hP i) (le_refl q.src) y'
  rw [chartRes_self] at h1 h2
  exact h1.trans ((h i).trans h2.symm)

/-- **The degree is local**: an element of the local model of `q` whose images in the local
models of a family of refinements covering the source of `q` have degree `d` has degree `d`. -/
theorem mem_localGrading_of_forall {q : AffinePair g} {ι : Type*} (P : ι → AffinePair g)
    (hP : ∀ i, P i ≤ q) (hcov : ∀ x ∈ q.src.toOpens, ∃ i, x ∈ (P i).src.toOpens) {d : ℕ}
    {z : 𝒜.localModel q} (h : ∀ i, 𝒜.localModelMap (hP i) z ∈ 𝒜.localGrading (P i) d) :
    z ∈ 𝒜.localGrading q d := by
  have hz : z = (DirectSum.decompose (𝒜.localGrading q) z d : 𝒜.localModel q) := by
    refine 𝒜.localModel_ext P hP hcov fun i ↦ ?_
    change _ = 𝒜.localModelGradedMap (hP i) _
    rw [GradedRingHom.map_directSumDecompose]
    exact (DirectSum.decompose_of_mem_same _ (h i)).symm
  rw [hz]
  exact SetLike.coe_mem _

/-! ### The grading -/

variable (g) in
/-- The degree-`d` sections over an affine open `U'`: those whose image in the local model of
every affine pair below `U'` has degree `d`. -/
noncomputable def pullbackGrading (U' : S'.AffineZariskiSite) (d : ℕ) :
    Submodule Γ(S', U'.toOpens) (𝒜.pullbackSections g U') where
  carrier := {s | ∀ (p : AffinePair g) (hp : p.src ≤ U'),
    𝒜.chartRes p hp s ∈ 𝒜.localGrading p d}
  add_mem' hs ht p hp := by
    rw [map_add]
    exact add_mem (hs p hp) (ht p hp)
  zero_mem' p hp := by
    rw [map_zero]
    exact zero_mem _
  smul_mem' c s hs p hp := by
    rw [Algebra.smul_def, map_mul, chartRes_algebraMap]
    change algebraMap p.Sections (𝒜.localModel p) _ * _ ∈ _
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hs p hp)

theorem mem_pullbackGrading {U' : S'.AffineZariskiSite} {d : ℕ} {s : 𝒜.pullbackSections g U'} :
    s ∈ 𝒜.pullbackGrading g U' d ↔
      ∀ (p : AffinePair g) (hp : p.src ≤ U'), 𝒜.chartRes p hp s ∈ 𝒜.localGrading p d :=
  Iff.rfl

instance (U' : S'.AffineZariskiSite) : SetLike.GradedMonoid (𝒜.pullbackGrading g U') where
  one_mem p hp := by
    rw [map_one]
    exact SetLike.GradedOne.one_mem
  mul_mem _ _ _ _ hx hy p hp := by
    rw [map_mul]
    exact SetLike.GradedMul.mul_mem (hx p hp) (hy p hp)

theorem exists_le_mem_preimage {U' : S'.AffineZariskiSite} :
    𝒜.pullbackSpecToBase g ⁻¹ᵁ U'.toOpens ≤
      ⨆ i : {p : AffinePair g // p.src ≤ U'}, 𝒜.pullbackSpecToBase g ⁻¹ᵁ i.1.src.toOpens := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := AffinePair.exists_le_mem U' _ hx
  exact Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxp⟩

/-- **Components**: the degree-`d` component of a section over `U'`, glued from the degree-`d`
components of its images in the local models. -/
theorem exists_component (U' : S'.AffineZariskiSite) (s : 𝒜.pullbackSections g U') (d : ℕ) :
    ∃ t : 𝒜.pullbackSections g U', ∀ (p : AffinePair g) (hp : p.src ≤ U'),
      𝒜.chartRes p hp t = DirectSum.decompose (𝒜.localGrading p) (𝒜.chartRes p hp s) d := by
  let F := (𝒜.pullbackSpec g).sheaf
  let U : {p : AffinePair g // p.src ≤ U'} → (𝒜.pullbackSpec g).Opens := fun i ↦
    𝒜.pullbackSpecToBase g ⁻¹ᵁ i.1.src.toOpens
  let sf : ∀ i, ToType (F.1.obj (op (U i))) := fun i ↦
    (𝒜.chartIso i.1).inv (DirectSum.decompose (𝒜.localGrading i.1) (𝒜.chartRes i.1 i.2 s) d)
  have key (i : {p : AffinePair g // p.src ≤ U'}) (r : AffinePair g) (hr : r ≤ i.1)
      (j : 𝒜.pullbackSpecToBase g ⁻¹ᵁ r.src.toOpens ⟶ U i) :
      (𝒜.chartIso r).hom (F.1.map j.op (sf i)) =
        DirectSum.decompose (𝒜.localGrading r)
          (𝒜.chartRes r ((AffinePair.src_le hr).trans i.2) s) d := by
    refine (𝒜.chartIso_hom_map' hr j (sf i)).trans ?_
    change 𝒜.localModelGradedMap hr ((𝒜.chartIso i.1).hom ((𝒜.chartIso i.1).inv _)) = _
    rw [Iso.inv_hom_id_apply, GradedRingHom.map_directSumDecompose]
    exact congr(((DirectSum.decompose (𝒜.localGrading r) $((𝒜.chartRes_le hr i.2 s).symm)) d :
      𝒜.localModel r))
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' U (𝒜.pullbackSpecToBase g ⁻¹ᵁ U'.toOpens)
    (fun i ↦ homOfLE ((𝒜.pullbackSpecToBase g).preimage_mono (toOpens_mono i.2)))
    𝒜.exists_le_mem_preimage sf (by
      intro i j
      refine F.eq_of_locally_eq'
        (fun r : {r : AffinePair g // r ≤ i.1 ∧ r ≤ j.1} ↦
          𝒜.pullbackSpecToBase g ⁻¹ᵁ r.1.src.toOpens) (U i ⊓ U j)
        (fun r ↦ homOfLE (le_inf
          ((𝒜.pullbackSpecToBase g).preimage_mono (toOpens_mono (AffinePair.src_le r.2.1)))
          ((𝒜.pullbackSpecToBase g).preimage_mono (toOpens_mono (AffinePair.src_le r.2.2)))))
        ?_ _ _ fun r ↦ ?_
      · intro x hx
        obtain ⟨r, hri, hrj, hxr⟩ := AffinePair.exists_le_le i.1 j.1 _ hx.1 hx.2
        exact Opens.mem_iSup.mpr ⟨⟨r, hri, hrj⟩, hxr⟩
      · apply (𝒜.chartIso r.1).commRingCatIsoToRingEquiv.injective
        change (𝒜.chartIso r.1).hom (F.1.map _ (F.1.map _ (sf i))) =
          (𝒜.chartIso r.1).hom (F.1.map _ (F.1.map _ (sf j)))
        rw [← ConcreteCategory.comp_apply, ← F.1.map_comp, ← ConcreteCategory.comp_apply,
          ← F.1.map_comp, ← op_comp, ← op_comp, key i r.1 r.2.1, key j r.1 r.2.2])
  refine ⟨t, fun p hp ↦ ?_⟩
  have h := ht ⟨p, hp⟩
  rw [chartRes, RingHom.comp_apply]
  change (𝒜.chartIso p).hom (F.1.map _ t) = _
  rw [h]
  exact Iso.inv_hom_id_apply _ _

theorem isInternal_pullbackGrading (U' : S'.AffineZariskiSite) :
    DirectSum.IsInternal (𝒜.pullbackGrading g U') := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    ext d : 1
    refine Subtype.ext (𝒜.pullbackSections_ext (U' := U') Subtype.val (fun p ↦ p.2)
      (fun y hy ↦ (AffinePair.exists_le_mem U' y hy).elim fun p hp ↦ ⟨⟨p, hp.1⟩, hp.2⟩)
      fun p ↦ ?_)
    -- the degreewise image of `x` in the local model of `p`
    let φ : ∀ e, 𝒜.pullbackGrading g U' e →+ 𝒜.localGrading p.1 e := fun e ↦
      { toFun := fun y ↦ ⟨𝒜.chartRes p.1 p.2 y, y.2 p.1 p.2⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }
    have hcomm : (DirectSum.coeAddMonoidHom (𝒜.localGrading p.1)).comp (DirectSum.map φ) =
        (𝒜.chartRes p.1 p.2).toAddMonoidHom.comp
          (DirectSum.coeAddMonoidHom (𝒜.pullbackGrading g U')) := by
      ext e y
      simp [φ]
    have h0 : DirectSum.map φ x = 0 := by
      apply (DirectSum.Decomposition.isInternal (𝒜.localGrading p.1)).injective
      rw [map_zero]
      exact (congr($hcomm x)).trans (by simp [hx])
    have := congr($h0 d)
    rw [DirectSum.map_apply, DirectSum.zero_apply] at this
    simpa [φ] using congr(($this : 𝒜.localModel p.1))
  · intro s
    obtain ⟨T, hT⟩ := U'.2.isCompact.elim_finite_subcover
      (fun i : {p : AffinePair g // p.src ≤ U'} ↦ (i.1.src.toOpens : Set S'))
      (fun i ↦ i.1.src.toOpens.isOpen)
      (fun y hy ↦ (AffinePair.exists_le_mem U' y hy).elim fun p hp ↦
        Set.mem_iUnion.mpr ⟨⟨p, hp.1⟩, hp.2⟩)
    let D : Finset ℕ := T.biUnion fun i ↦
      (DirectSum.decompose (𝒜.localGrading i.1) (𝒜.chartRes i.1 i.2 s)).support
    choose c hc using 𝒜.exists_component U' s
    refine ⟨∑ d ∈ D, DirectSum.of (fun d ↦ 𝒜.pullbackGrading g U' d) d
      ⟨c d, fun p hp ↦ by rw [hc d p hp]; exact SetLike.coe_mem _⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    refine 𝒜.pullbackSections_ext (U' := U') (fun i : T ↦ i.1.1) (fun i ↦ i.1.2) (fun y hy ↦ ?_)
      fun i ↦ ?_
    · obtain ⟨j, hj⟩ := Set.mem_iUnion₂.mp (hT hy)
      exact ⟨⟨j, hj.1⟩, hj.2⟩
    · rw [map_sum]
      simp only [hc]
      conv_rhs => rw [← DirectSum.sum_support_decompose (𝒜.localGrading i.1.1)
        (𝒜.chartRes i.1.1 i.1.2 s)]
      refine (Finset.sum_subset (Finset.subset_biUnion_of_mem _ i.2) fun d _ hd ↦ ?_).symm
      rw [DFinsupp.notMem_support_iff.mp hd, ZeroMemClass.coe_zero]

noncomputable instance (U' : S'.AffineZariskiSite) :
    GradedAlgebra (𝒜.pullbackGrading g U') where
  toGradedMonoid := inferInstance
  toDecomposition := (𝒜.isInternal_pullbackGrading U').chooseDecomposition

/-- Restriction of sections to a basic open, as a graded ring map. -/
noncomputable def pullbackRestrict {U' V' : S'.AffineZariskiSite} (h : V' ≤ U') :
    𝒜.pullbackGrading g U' →+*ᵍ 𝒜.pullbackGrading g V' where
  toRingHom := 𝒜.pullbackRes h
  map_mem {_ _} hx p hp := by
    rw [chartRes_pullbackRes]
    exact hx p (hp.trans h)

variable (g) in
/-- **The pullback of a quasi-coherent graded algebra** along `g : S' ⟶ S`. Over an affine open
`U'` of `S'` its sections are those of the relative spectrum `pullbackSpec` glued from the local
models `Γ(S', V') ⊗_{Γ(S, V)} 𝒜(V)`, graded by degree in the local models. Over the source of an
affine pair `(V', V)` it is the pushout `Γ(S', V') ⊔_{Γ(S, V)} 𝒜(V)`
(`QuasicoherentGradedAlgebraData.isPushout_pullbackChartHom`). -/
noncomputable def pullback : S'.QuasicoherentGradedAlgebraData where
  carrier U' := 𝒜.pullbackSections g U'
  grading U' := 𝒜.pullbackGrading g U'
  restrict h := 𝒜.pullbackRestrict h
  restrict_id U' x := 𝒜.pullbackRes_id U' x
  restrict_comp hVU hWV x := 𝒜.pullbackRes_comp hVU hWV x
  restrict_algebraMap h r := 𝒜.pullbackRes_algebraMap h r
  isLocalization_basicOpen U' f :=
    (U'.2.preimage (𝒜.pullbackSpecToBase g)).isLocalization_of_eq_basicOpen
      ((𝒜.pullbackSpecToBase g).app U'.toOpens f)
      (homOfLE ((𝒜.pullbackSpecToBase g).preimage_mono (S'.basicOpen_le f)))
      (Scheme.preimage_basicOpen _ f)

/-- The graded map `𝒜(V) → (g^*𝒜)(V')` of an affine pair `(V', V)`, `a ↦ 1 ⊗ a` in the local
model. -/
noncomputable def pullbackChartHom (p : AffinePair g) :
    𝒜.grading p.tgt →+*ᵍ (𝒜.pullback g).grading p.src where
  toRingHom := (𝒜.chartIso p).inv.hom.comp (Algebra.TensorProduct.includeRight
    (R := Γ(S, p.tgt.toOpens)) (A := p.Sections) (B := 𝒜.carrier p.tgt)).toRingHom
  map_mem {d a} ha q hq := by
    refine 𝒜.mem_localGrading_of_forall (q := q)
      (fun r : {r : AffinePair g // r ≤ q ∧ r ≤ p} ↦ r.1) (fun r ↦ r.2.1) (fun x hx ↦ ?_)
      fun r ↦ ?_
    · obtain ⟨r, hrq, hrp, hxr⟩ := AffinePair.exists_le_le q p x hx (toOpens_mono hq hx)
      exact ⟨⟨r, hrq, hrp⟩, hxr⟩
    · let y : 𝒜.pullbackSections g p.src :=
        (𝒜.chartIso p).inv ((1 : p.Sections) ⊗ₜ[Γ(S, p.tgt.toOpens)] a)
      have h1 := 𝒜.chartRes_le r.2.1 hq y
      have h2 := 𝒜.chartRes_le r.2.2 (le_refl p.src) y
      rw [chartRes_self, Iso.inv_hom_id_apply, localModelMap_tmul, map_one] at h2
      change 𝒜.localModelMap r.2.1 (𝒜.chartRes q hq y) ∈ _
      rw [← h1, h2]
      exact Submodule.tmul_mem_baseChange_of_mem _ ((𝒜.restrict _).map_mem ha)

theorem chartIso_hom_pullbackChartHom (p : AffinePair g) (a : 𝒜.carrier p.tgt) :
    (𝒜.chartIso p).hom (𝒜.pullbackChartHom p a) = (1 : p.Sections) ⊗ₜ a :=
  Iso.inv_hom_id_apply _ _

theorem pullbackChartHom_restrict {p q : AffinePair g} (h : q ≤ p) (a : 𝒜.carrier p.tgt) :
    (𝒜.pullback g).restrict (AffinePair.src_le h) (𝒜.pullbackChartHom p a) =
      𝒜.pullbackChartHom q (𝒜.restrict (AffinePair.tgt_le h) a) := by
  apply (𝒜.chartIso q).commRingCatIsoToRingEquiv.injective
  change (𝒜.chartIso q).hom (𝒜.pullbackRes (AffinePair.src_le h) _) =
    (𝒜.chartIso q).hom (𝒜.pullbackChartHom q _)
  rw [chartIso_hom_pullbackChartHom]
  refine (𝒜.chartIso_hom_map h _).trans ?_
  rw [chartIso_hom_pullbackChartHom, localModelMap_tmul, map_one]

/-- The algebra structure `Γ(S', V') → (g^*𝒜)(V')`, read in the local model, is `x ↦ x ⊗ 1`. -/
theorem chartIso_hom_algebraMap (p : AffinePair g) (x : Γ(S', p.src.toOpens)) :
    (𝒜.chartIso p).hom (algebraMap Γ(S', p.src.toOpens) ((𝒜.pullback g).carrier p.src) x) =
      (x : p.Sections) ⊗ₜ (1 : 𝒜.carrier p.tgt) :=
  𝒜.chartIso_hom_app p x

/-- Over an affine pair `(V', V)`, `(g^*𝒜)(V')` is the pushout `Γ(S', V') ⊔_{Γ(S, V)} 𝒜(V)`. -/
theorem isPushout_pullbackChartHom (p : AffinePair g) :
    IsPushout (CommRingCat.ofHom (algebraMap Γ(S, p.tgt.toOpens) p.Sections))
      (CommRingCat.ofHom (algebraMap Γ(S, p.tgt.toOpens) (𝒜.carrier p.tgt)))
      (CommRingCat.ofHom (algebraMap Γ(S', p.src.toOpens) ((𝒜.pullback g).carrier p.src)))
      (CommRingCat.ofHom (𝒜.pullbackChartHom p).toRingHom) := by
  refine (𝒜.isPushout_localModel p).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (𝒜.chartIso p).symm (by simp) (by simp) ?_ ?_
  · ext x
    apply (𝒜.chartIso p).commRingCatIsoToRingEquiv.injective
    change (𝒜.chartIso p).hom ((𝒜.chartIso p).inv _) =
      (𝒜.chartIso p).hom (algebraMap Γ(S', p.src.toOpens) ((𝒜.pullback g).carrier p.src) x)
    rw [Iso.inv_hom_id_apply, chartIso_hom_algebraMap]
    rfl
  · ext a
    rfl

end AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData
