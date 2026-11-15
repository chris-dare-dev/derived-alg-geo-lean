/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.AffineChart
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.RingTheory.Localization.Free

/-!
# Generic flatness

Let `p : X ⟶ S` be quasi-compact and locally of finite type over a locally Noetherian base, and
`F` a coherent sheaf on `X`. If `S` is reduced, `F` is flat over a dense open of `S`. If `S` is
Noetherian, `S` is the disjoint union of finitely many reduced locally closed subschemes over each
of which the pullback of `F` is flat.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_dense_isFlatOver`: generic flatness over a reduced
  locally Noetherian base (Stacks 052B, EGA IV 6.9.1).
* `AlgebraicGeometry.Scheme.Modules.exists_flatStratification`: the generic flatness
  stratification over a Noetherian base (EGA IV 6.9.3, the Noetherian case of Stacks 0ASY).

## Proof

Flatness over the base is the stalkwise `Scheme.Modules.IsFlatOver`. Let `V ⊆ S` be affine
and `𝔭` a minimal prime of `Γ(S, V)`. The finitely many affine opens `U` covering `p⁻¹ V` have
sections `Γ(U, F)` finite over `Γ(X, U)`, which is of finite type over the reduced Noetherian
ring `Γ(S, V)`. Generic freeness at a minimal prime
(`Module.exists_notMem_free_localizedModule_away_of_mem_minimalPrimes`) gives `f ∉ 𝔭` with each
`Γ(U, F)_f` free, hence flat, over `Γ(S, V)_f`, and
`Scheme.Modules.flat_stalk_of_isLocalizedModule` turns this into flatness of the stalks of `F`
at the points over `D(f)`. Every nonempty open of `S` contains the point of a minimal prime of
an affine open inside it, so the union of these `D(f)` is dense. The restricted morphism
`p ∣_ U` is a base change of `p`, and `Scheme.Modules.flat_stalk_of_isPullback` carries the
stalkwise flatness to it.

The stratification is a Noetherian induction on closed subsets `Z ⊆ S`. Give `Z` its reduced
induced structure, the subscheme of `Scheme.IdealSheafData.vanishingIdeal Z`, and apply generic
flatness to the pullback of `F` to `X ×_S Z`. The dense open so obtained is the next stratum,
and its complement in `Z` is a smaller closed subset. Pasting the pullback squares over
`U ⊆ Z ⊆ S` identifies the pullback of `F` to `X ×_S U` as the base change of its pullback to
`X ×_S Z`.

## Hypotheses

The docstring of each theorem says which of its hypotheses are load-bearing. Local
Noetherianity of the base is used by the proof, through generic freeness, and is not
load-bearing for generic flatness itself: Stacks 052B holds over any reduced base.

## Implementation notes

"Flat over `U`" is `IsFlatOver (p ∣_ U) (F.restrict (p ⁻¹ᵁ U).ι)`: the restriction of `F` to
`p⁻¹ U` over the restricted morphism. Keeping `p` as the structure map and restricting `F`
alone would test flatness over the wrong local rings. In the stratification, flatness is of
the pullback of `F` along `X ×_S W ⟶ X`, over `W`.

`IsCoherent` is finite presentation. On `X` locally of finite type over a locally Noetherian
`S` this is the usual coherence, and Stacks 052B asks only for a quasi-coherent `F` of finite
type.

## References

* [Stacks, Tag 052B](https://stacks.math.columbia.edu/tag/052B): generic flatness, reduced
  case.
* [Stacks, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY): the generic flatness
  stratification, for morphisms of finite presentation between qcqs schemes.
* A. Grothendieck, *EGA IV₂*, Théorème 6.9.1 (an integral locally Noetherian base), Lemme 6.9.2
  (generic freeness) and Corollaire 6.9.3 (the stratification).
* N. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590, Theorem 4.2.

## Tags

generic flatness, flattening stratification, coherent sheaf, Noetherian induction
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The sections of a coherent sheaf over an affine open form a finite module. -/
private theorem moduleFinite_sections {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (hF : IsCoherent X F) : Module.Finite Γ(X, U) Γ(F, U) := by
  let A₀ := Γ(Spec Γ(X, U), ⊤)
  have h₁ : Module.Finite A₀ Γ(F.restrict hU.fromSpec, ⊤) := by
    let : Algebra Γ(X, U) A₀ := (Scheme.ΓSpecIso Γ(X, U)).inv.hom.toAlgebra
    let : Module Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso Γ(X, U)).inv.hom
    have : Module.Finite Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
      moduleFinite_sections_restrict_of_isCoherent F U hU hF
    have : IsScalarTower Γ(X, U) A₀ Γ(F.restrict hU.fromSpec, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.Finite.of_restrictScalars_finite Γ(X, U) A₀ _
  let ρ := (hU.fromSpec.appIso ⊤).inv.hom
  let : Algebra A₀ Γ(X, hU.fromSpec ''ᵁ ⊤) := ρ.toAlgebra
  let : Module A₀ Γ(F, hU.fromSpec ''ᵁ ⊤) := Module.compHom _ ρ
  have : IsScalarTower A₀ Γ(X, hU.fromSpec ''ᵁ ⊤) Γ(F, hU.fromSpec ''ᵁ ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : Γ(F.restrict hU.fromSpec, ⊤) ≃ₗ[A₀] Γ(F, hU.fromSpec ''ᵁ ⊤) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ Scheme.Modules.smul_restrictAppIso_hom_apply hU.fromSpec F ⊤ r m }
  have : Module.Finite A₀ Γ(F, hU.fromSpec ''ᵁ ⊤) := Module.Finite.equiv e
  have h := Module.Finite.of_restrictScalars_finite A₀ Γ(X, hU.fromSpec ''ᵁ ⊤)
    Γ(F, hU.fromSpec ''ᵁ ⊤)
  rwa [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec] at h

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- Generic flatness on one affine open `U` of `X` over an affine open `V` of `S`, at a
minimal prime of `Γ(S, V)`. -/
private theorem exists_notMem_flat_stalk_of_le [IsReduced S] [IsLocallyNoetherian S]
    [LocallyOfFiniteType p] (F : X.Modules) (hF : IsCoherent X F) {V : S.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ p ⁻¹ᵁ V)
    (𝔭 : Ideal Γ(S, V)) (h𝔭 : 𝔭 ∈ minimalPrimes Γ(S, V)) :
    ∃ f ∉ 𝔭, ∀ x ∈ U, p x ∈ S.basicOpen f →
      Module.Flat (S.presheaf.stalk (p x))
        ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj ((moduleStalkFunctor X x).obj F)) := by
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from F) := by
    have : SheafOfModules.IsFinitePresentation.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from F) := hF
    infer_instance
  let R := Γ(S, V)
  let B := Γ(X, U)
  let φ := p.appLE V U hUV
  let : Algebra R B := φ.hom.toAlgebra
  have : Algebra.FiniteType R B :=
    HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have : Module.Finite B Γ(F, U) := moduleFinite_sections F hU hF
  let : Module R Γ(F, U) := Module.compHom _ (algebraMap R B)
  have : IsScalarTower R B Γ(F, U) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨f, hf𝔭, hfree⟩ :=
    Module.exists_notMem_free_localizedModule_away_of_mem_minimalPrimes B (M := Γ(F, U)) 𝔭 h𝔭
  refine ⟨f, hf𝔭, fun x hxU hxf ↦ ?_⟩
  let N := LocalizedModule (Submonoid.powers (φ f)) Γ(F, U)
  let g := LocalizedModule.mkLinearMap (Submonoid.powers (φ f)) Γ(F, U)
  have : IsLocalizedModule (Submonoid.powers f) (g.restrictScalars R) :=
    IsLocalizedModule.restrictScalars_powers f g
  have : Module.Flat R (LocalizedModule (Submonoid.powers f) Γ(F, U)) :=
    Module.Flat.trans R (Localization.Away f) _
  have : Module.Flat R N := Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers f) (g.restrictScalars R)).symm
  let e : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B N) ≃ₗ[R] N :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change algebraMap R B r • (show N from m) = r • (show N from m)
        exact algebraMap_smul B r (show N from m) }
  refine flat_stalk_of_isLocalizedModule p F hU hV hUV hxU (Submonoid.powers (φ f)) ?_ g
    (Module.Flat.of_linearEquiv e)
  rintro _ ⟨n, rfl⟩
  have hx : x ∈ X.basicOpen (φ f) := by
    rw [Scheme.basicOpen_appLE]
    exact ⟨hxU, hxf⟩
  rcases n with _ | n
  · simpa using hxU
  · rwa [Scheme.basicOpen_pow _ _ n.succ_pos]

/-- Generic flatness over an affine open `V` of `S`, at a minimal prime of `Γ(S, V)`: one
`f` serves for the finitely many affine opens covering `p⁻¹ V`. -/
private theorem exists_notMem_flat_stalk [IsReduced S] [IsLocallyNoetherian S]
    [LocallyOfFiniteType p] [QuasiCompact p] (F : X.Modules) (hF : IsCoherent X F)
    {V : S.Opens} (hV : IsAffineOpen V) (𝔭 : Ideal Γ(S, V)) (h𝔭 : 𝔭 ∈ minimalPrimes Γ(S, V)) :
    ∃ f ∉ 𝔭, ∀ x : X, p x ∈ S.basicOpen f →
      Module.Flat (S.presheaf.stalk (p x))
        ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj ((moduleStalkFunctor X x).obj F)) := by
  have : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨s, hs, hcover⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (p.isCompact_preimage hV.isCompact)
  have hle : ∀ U ∈ s, (U : X.Opens) ≤ p ⁻¹ᵁ V := fun U hU ↦
    hcover ▸ le_iSup₂ (f := fun i (_ : i ∈ s) ↦ (i : X.Opens)) U hU
  choose! f hf𝔭 hflat using fun (U : X.affineOpens) (hU : U ∈ s) ↦
    exists_notMem_flat_stalk_of_le p F hF hV U.2 (hle U hU) 𝔭 h𝔭
  refine ⟨∏ U ∈ hs.toFinset, f U,
    Submonoid.prod_mem 𝔭.primeCompl fun U hU ↦ hf𝔭 U (hs.mem_toFinset.mp hU), fun x hx ↦ ?_⟩
  have hxV : x ∈ p ⁻¹ᵁ V := S.basicOpen_le _ hx
  rw [hcover] at hxV
  simp only [Opens.mem_iSup] at hxV
  obtain ⟨U, hU, hxU⟩ := hxV
  refine hflat U hU x hxU ?_
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (hs.mem_toFinset.mpr hU)
  rw [hc, Scheme.basicOpen_mul] at hx
  exact hx.1

/-- Generic flatness, pointwise: over a reduced locally Noetherian base, the stalks of a
coherent sheaf are flat over the base at every point lying over some dense open. -/
private theorem exists_dense_flat_stalk [IsReduced S] [IsLocallyNoetherian S]
    [LocallyOfFiniteType p] [QuasiCompact p] (F : X.Modules) (hF : IsCoherent X F) :
    ∃ U : S.Opens, Dense (U : Set S) ∧ ∀ x : X, p x ∈ U →
      Module.Flat (S.presheaf.stalk (p x))
        ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj ((moduleStalkFunctor X x).obj F)) := by
  let G : Set S.Opens := {W | ∀ x : X, p x ∈ W →
    Module.Flat (S.presheaf.stalk (p x))
      ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj ((moduleStalkFunctor X x).obj F))}
  refine ⟨sSup G, ?_, fun x hx ↦ ?_⟩
  · rw [dense_iff_inter_open]
    rintro O hO ⟨s₀, hs₀⟩
    obtain ⟨V, hV, hs₀V, hVO⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show s₀ ∈ (⟨O, hO⟩ : S.Opens) from hs₀)
    have : Nonempty V := ⟨⟨s₀, hs₀V⟩⟩
    obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal Γ(S, V)
    obtain ⟨𝔭, h𝔭, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ 𝔪)
    have : 𝔭.IsPrime := h𝔭.1.1
    obtain ⟨f, hf, hflat⟩ := exists_notMem_flat_stalk p F hF hV 𝔭 h𝔭
    let y : PrimeSpectrum Γ(S, V) := ⟨𝔭, ‹_›⟩
    have hyV : hV.fromSpec y ∈ (V : Set S) := hV.range_fromSpec ▸ Set.mem_range_self y
    have hyf : hV.fromSpec y ∈ S.basicOpen f := by
      have : y ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen f := by
        rw [hV.fromSpec_preimage_basicOpen]
        exact hf
      exact this
    exact ⟨hV.fromSpec y, hVO hyV, Opens.mem_sSup.mpr ⟨S.basicOpen f, hflat, hyf⟩⟩
  · obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hx
    exact hW x hxW

/-- **Generic flatness** (Stacks 052B). Let `S` be a reduced locally Noetherian scheme,
`p : X ⟶ S` quasi-compact and locally of finite type, and `F` a coherent sheaf on `X`. Then
there is a dense open `U ⊆ S` over which `F` is flat: the restriction of `F` to `p⁻¹ U` is flat
over `U` along the restricted morphism `p ∣_ U`.

The hypotheses on `S` and `p` other than local Noetherianity are load-bearing:
* `IsReduced S`: take `S = X = Spec k[ε]/(ε²)`, `p = 𝟙`, and `F = k`. The stalk of `F` at the
  only point is `k`, which is not flat over `k[ε]/(ε²)` since `Tor₁(k, k) ≠ 0`, and `S` is the
  only nonempty open.
* `QuasiCompact p`: take `X = ∐_ℓ Spec 𝔽_ℓ` over `S = Spec ℤ`, with `F = 𝒪_X`. The stalk `𝔽_ℓ`
  is not flat over `ℤ_(ℓ)`, and a dense open of `Spec ℤ` contains `(ℓ)` for all but finitely
  many primes `ℓ`.
* `LocallyOfFiniteType p`: take `X = Spec ∏_ℓ 𝔽_ℓ` over `S = Spec ℤ`, with `F = 𝒪_X`. After
  inverting any `n ≠ 0`, the idempotent of `𝔽_ℓ` for a prime `ℓ ∤ n` is nonzero and killed by
  `ℓ`, so the ring is not flat over `ℤ[1/n]`. -/
@[stacks 052B]
theorem exists_dense_isFlatOver [IsReduced S] [IsLocallyNoetherian S] [LocallyOfFiniteType p]
    [QuasiCompact p] (F : X.Modules) (hF : IsCoherent X F) :
    ∃ U : S.Opens, Dense (U : Set S) ∧ IsFlatOver (p ∣_ U) (F.restrict (p ⁻¹ᵁ U).ι) := by
  obtain ⟨U, hU, hflat⟩ := exists_dense_flat_stalk p F hF
  refine ⟨U, hU, ?_⟩
  have : IsFlatOver (p ∣_ U) ((pullback (p ⁻¹ᵁ U).ι).obj F) := fun z ↦
    flat_stalk_of_isPullback (isPullback_morphismRestrict p U).flip F z (hflat _ z.2)
  exact this.of_iso ((restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).app F).symm

omit p in
/-- The reduced induced subscheme structure on a closed subset is reduced: on an affine open
`U` it is `Spec (Γ(S, U) / I(U))` for a radical ideal `I(U)`. -/
private theorem isReduced_subscheme_vanishingIdeal (Z : Closeds S) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred : ∀ U : S.affineOpens, _root_.IsReduced (Γ(S, U) ⧸ I.ideal U) := fun U ↦
    (Ideal.isRadical_iff_quotient_reduced _).mp (by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _)
  refine @isReduced_of_isReduced_stalk _ fun x ↦ ?_
  obtain ⟨y, hy⟩ := I.subschemeCover.covers x
  have : _root_.IsReduced (I.subschemeCover.X (I.subschemeCover.idx x)) := hred _
  have := isReduced_of_injective ((I.subschemeCover.f _).stalkMap y).hom
    (ConcreteCategory.bijective_of_isIso _).1
  rwa [hy] at this

/-- The new stratum in the Noetherian induction: an open `U` of the reduced closed subscheme
`Z`, over whose points the pullback of `F` to `X ×_S Z` is flat. The pullback of `F` to
`X ×_S U` is then flat over `U`, by base change along `U ⟶ Z` and pasting of pullbacks. -/
private theorem isFlatOver_pullback_comp {Z : Scheme.{u}} (i : Z ⟶ S) (U : Z.Opens)
    (F : X.Modules)
    (hflat : ∀ x : ↑(Limits.pullback p i), pullback.snd p i x ∈ U →
      Module.Flat (Z.presheaf.stalk (pullback.snd p i x))
        ((ModuleCat.restrictScalars ((pullback.snd p i).stalkMap x).hom).obj
          ((moduleStalkFunctor _ x).obj ((Scheme.Modules.pullback (pullback.fst p i)).obj F)))) :
    IsFlatOver (pullback.snd p (U.ι ≫ i))
      ((Scheme.Modules.pullback (pullback.fst p (U.ι ≫ i))).obj F) := by
  let ℓ : Limits.pullback p (U.ι ≫ i) ⟶ Limits.pullback p i :=
    pullback.lift (pullback.fst p (U.ι ≫ i)) (pullback.snd p (U.ι ≫ i) ≫ U.ι)
      (by rw [pullback.condition, Category.assoc])
  have hℓ₁ : ℓ ≫ pullback.fst p i = pullback.fst p (U.ι ≫ i) := pullback.lift_fst _ _ _
  have hℓ₂ : ℓ ≫ pullback.snd p i = pullback.snd p (U.ι ≫ i) ≫ U.ι := pullback.lift_snd _ _ _
  have H : IsPullback ℓ (pullback.snd p (U.ι ≫ i)) (pullback.snd p i) U.ι :=
    IsPullback.of_right (hℓ₁ ▸ IsPullback.of_hasPullback p (U.ι ≫ i)) hℓ₂
      (IsPullback.of_hasPullback p i)
  have : IsFlatOver (pullback.snd p (U.ι ≫ i))
      ((Scheme.Modules.pullback ℓ).obj ((Scheme.Modules.pullback (pullback.fst p i)).obj F)) :=
    fun z ↦ flat_stalk_of_isPullback H _ z (hflat (ℓ z) (by
      rw [← Scheme.Hom.comp_apply, hℓ₂, Scheme.Hom.comp_apply]
      exact (pullback.snd p (U.ι ≫ i) z).2))
  exact this.of_iso ((Scheme.Modules.pullbackComp ℓ (pullback.fst p i)).app F ≪≫
    (Scheme.Modules.pullbackCongr hℓ₁).app F)

/-- The stratification of a closed subset `Z ⊆ S`, by Noetherian induction on `Z`. -/
private theorem exists_flatStratification_closeds [IsNoetherian S] [LocallyOfFiniteType p]
    [QuasiCompact p] (F : X.Modules) (hF : IsCoherent X F) (Z : Closeds S) :
    ∃ (J : Type u) (_ : Finite J) (W : J → Scheme.{u}) (ι : ∀ j, W j ⟶ S),
      (∀ j, IsImmersion (ι j)) ∧ (∀ j, IsReduced (W j)) ∧
      (⋃ j, Set.range (ι j)) = Z ∧
      Pairwise (fun j k ↦ Disjoint (Set.range (ι j)) (Set.range (ι k))) ∧
      ∀ j, IsFlatOver (pullback.snd p (ι j)) ((Scheme.Modules.pullback (pullback.fst p (ι j))).obj F) := by
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  rcases (Z : Set S).eq_empty_or_nonempty with hZ | hZ
  · exact ⟨PEmpty, inferInstance, fun j ↦ j.elim, fun j ↦ j.elim, fun j ↦ j.elim, fun j ↦ j.elim,
      by simp [hZ], fun j ↦ j.elim, fun j ↦ j.elim⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let i := I.subschemeι
  have hri : Set.range i = Z := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : IsReduced I.subscheme := isReduced_subscheme_vanishingIdeal Z
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨U, hU, hflat⟩ := exists_dense_flat_stalk (pullback.snd p i)
    ((Scheme.Modules.pullback (pullback.fst p i)).obj F)
    (isCoherent_pullback (pullback.fst p i) F hF)
  have : Nonempty I.subscheme := by
    obtain ⟨z, hz⟩ := hZ
    rw [← hri] at hz
    exact ⟨hz.choose⟩
  obtain ⟨u, hu⟩ := hU.nonempty
  obtain ⟨O, hO, hOU⟩ := i.isEmbedding.isOpen_iff.mp U.isOpen
  have himage : Set.range (U.ι ≫ i) = (Z : Set S) ∩ O := by
    have : Set.range (U.ι ≫ i) = i '' Set.range U.ι := by
      ext s
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨U.ι y, ⟨y, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
    rw [this, Scheme.Opens.range_ι, ← hOU, Set.image_preimage_eq_inter_range, hri,
      Set.inter_comm]
  let Z' : Closeds S := ⟨(Z : Set S) \ O, Z.isClosed.sdiff hO⟩
  have hZ' : Z' < Z := by
    refine lt_of_le_of_ne (fun s hs ↦ hs.1) fun h ↦ ?_
    have hiu : i u ∈ (Z : Set S) ∩ O := himage ▸ ⟨⟨u, hu⟩, rfl⟩
    have : i u ∈ (Z' : Set S) := by rw [h]; exact hiu.1
    exact this.2 hiu.2
  obtain ⟨J, _, W, ι, himm, hred, hcov, hdisj, hflat'⟩ := ih Z' hZ'
  let W' : Option J → Scheme.{u} := fun o ↦ Option.rec (U : Scheme.{u}) W o
  let ι' : ∀ o, W' o ⟶ S := fun o ↦
    Option.rec (motive := fun o ↦ W' o ⟶ S) (U.ι ≫ i) ι o
  refine ⟨Option J, inferInstance, W', ι', ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | j)
    · change IsImmersion (U.ι ≫ i); infer_instance
    · exact himm j
  · rintro (_ | j)
    · change IsReduced U; infer_instance
    · exact hred j
  · rw [Set.iUnion_option]
    change Set.range (U.ι ≫ i) ∪ ⋃ j, Set.range (ι j) = Z
    rw [himage, hcov]
    exact Set.inter_union_sdiff _ _
  · have hsub : ∀ j, Set.range (ι j) ⊆ (Z : Set S) \ O := fun j ↦
      (Set.subset_iUnion (fun j ↦ Set.range (ι j)) j).trans hcov.le
    rintro (_ | j) (_ | k) hjk
    · exact absurd rfl hjk
    · change Disjoint (Set.range (U.ι ≫ i)) (Set.range (ι k))
      rw [himage]
      exact Set.disjoint_sdiff_right.mono Set.inter_subset_right (hsub k)
    · change Disjoint (Set.range (ι j)) (Set.range (U.ι ≫ i))
      rw [himage]
      exact (Set.disjoint_sdiff_right.mono Set.inter_subset_right (hsub j)).symm
    · exact hdisj fun h ↦ hjk (congrArg some h)
  · rintro (_ | j)
    · exact isFlatOver_pullback_comp p i U F hflat
    · exact hflat' j

/-- **The generic flatness stratification** (EGA IV 6.9.3; the Noetherian case of Stacks
0ASY). Let `S` be a Noetherian scheme, `p : X ⟶ S` quasi-compact and locally of finite type,
and `F` a coherent sheaf on `X`. Then `S` is the disjoint union of the images of finitely many
immersions `ι j : W j ⟶ S` of reduced schemes, and the pullback of `F` to `X ×_S W j` is flat
over `W j` for every `j`.

The strata are reduced, and need to be: for `S = X = Spec k[ε]/(ε²)` and `F = k`, the only
non-reduced stratum available is `S` itself, over which `F` is not flat. Noetherianity of `S` makes
the induction on closed subsets terminate, so that there are finitely many strata.

This is the sheaf input to Lemma 8.3(2) of Li, Liu, Liu, Macrì, Perry, Stellari and Zhao
(arXiv:2607.28411), which applies Stacks 052B repeatedly to the cohomology sheaves of an
`S`-perfect complex and is used in the proof of their Theorem 9.1(iv′). The statement of
Lemma 8.3 for `S`-perfect complexes belongs to their paper's development, not to this file. -/
theorem exists_flatStratification [IsNoetherian S] [LocallyOfFiniteType p] [QuasiCompact p]
    (F : X.Modules) (hF : IsCoherent X F) :
    ∃ (J : Type u) (_ : Finite J) (W : J → Scheme.{u}) (ι : ∀ j, W j ⟶ S),
      (∀ j, IsImmersion (ι j)) ∧ (∀ j, IsReduced (W j)) ∧
      (⋃ j, Set.range (ι j)) = Set.univ ∧
      Pairwise (fun j k ↦ Disjoint (Set.range (ι j)) (Set.range (ι k))) ∧
      ∀ j, IsFlatOver (pullback.snd p (ι j))
        ((Scheme.Modules.pullback (pullback.fst p (ι j))).obj F) := by
  simpa using exists_flatStratification_closeds p F hF ⊤

end AlgebraicGeometry.Scheme.Modules
